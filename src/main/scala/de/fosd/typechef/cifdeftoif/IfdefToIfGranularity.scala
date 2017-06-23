package de.fosd.typechef.cifdeftoif

import java.io.{File, PrintWriter}
import java.util
import java.util.IdentityHashMap
import java.nio.file.{Files, Paths}

import de.fosd.typechef.conditional.{Choice, One, Opt}
import de.fosd.typechef.featureexpr._
import de.fosd.typechef.parser.c._

import scala.io.Source

trait IfdefToIfGranularityInterface {

    protected var statementMapping: IdentityHashMap[Any, String] = new IdentityHashMap[Any, String]()
    protected var featureModel: FeatureModel = _
    protected var dir: String = ""

    def getStatementMapping(): IdentityHashMap[Any, String] = {
        statementMapping
    }

    def calculateGranularity(ast: TranslationUnit, fm: FeatureModel, outputDir: String, threshold: Int): IdentityHashMap[Any, Boolean]
}

trait IfdefToIfGranularityExecCode extends IfdefToIfGranularityInterface with IOUtilities {

    class FuncCall(var functionName: String, var block: String, var condition: FeatureExpr, var weight: Double) {}
    class IfCall(var statement: Any, var block: String, var condition: FeatureExpr, var weight: Double) {}

    private var BUCKET_SIZE: Int = 5
    private var DEFAULT_FUNCTION_WEIGHT = 1.0

    private var FOR_WEIGHT: Double = 1.0
    private var WHILE_WEIGHT: Double = 1.0
    private var DO_WEIGHT: Double = 1.0
    private var BREAK_WEIGHT: Double = 1.0
    private var CONTINUE_WEIGHT: Double = 1.0
    private var GOTO_WEIGHT: Double = 1.0
    private var RECURSIVE_WEIGHT: Double = 1.0

    private var FUNCTION_ACCUMULATION: Boolean = false
    private var FUNCTION_ACCUMULATION_DEPTH: Int = 5
    private var FUNCTION_CALL_WEIGHT: Double = 1.0

    private var predefinedFunctionScores: Map[String, Double] = Map.empty[String, Double]
    private var functionCallOffsets: Map[String, Double] = Map.empty[String, Double]

    private var loopScores: Map[Int, Double] = Map.empty[Int, Double]
    private var functionDefs: Set[String] = Set.empty[String]
    private var functionScores: Map[String, Double] = Map.empty[String, Double]
    private var functionBlocks: Map[String, Set[String]] = Map.empty[String, Set[String]]
    // in which function is the call? -> (what function is called?, which condition?, which weight?)
    private var globalFunctionCalls: Map[String, List[FuncCall]] = Map.empty[String, List[FuncCall]]
    private var globalIfStatements: Map[Any, Set[IfCall]] = Map.empty[Any, Set[IfCall]]
    private var blockToExpr: Map[String, FeatureExpr] = Map.empty[String, FeatureExpr]
    private val statementToBlock: IdentityHashMap[Statement, String] = new IdentityHashMap[Statement, String]()
    private var blockToStatements: Map[String, IdentityHashMap[Statement, Statement]] = Map.empty[String, IdentityHashMap[Statement, Statement]]
    private var blockCapsuling: Map[String, Set[String]] = Map.empty[String, Set[String]]
    private var blockScores: Map[String, Double] = Map.empty[String, Double]
    private var singleBlockScores: Map[String, Double] = Map.empty[String, Double]
    private var featureCounter: Map[FeatureExpr, Int] = Map.empty[FeatureExpr, Int]
    private var loopCounter: Int = 0

    private var additionGeneralCounter: Int = 0
    private var subtractionGeneralCounter: Int = 0
    private var multiplicationGeneralCounter: Int = 0
    private var divisionGeneralCounter: Int = 0
    private var additionBlockCounter: Int = 0
    private var subtractionBlockCounter: Int = 0
    private var multiplicationBlockCounter: Int = 0
    private var divisionBlockCounter: Int = 0

    private var scoreCauses: Map[String, Set[String]] = Map.empty[String, Set[String]]

    override def calculateGranularity(ast: TranslationUnit, fm: FeatureModel, outputDir: String, threshold: Int = 2): IdentityHashMap[Any, Boolean] = {
        val ignoredStatements: IdentityHashMap[Any, Boolean] = new IdentityHashMap[Any, Boolean]

        featureModel = fm
        dir = outputDir
        readConfigFile()
        readFunctionConfigFile()
        readFunctionOffsetFile()

        codeAnalysis(ast)

        // Order is important, blockMapping -> loopScores -> generalGranularity -> blocks -> functions -> function calls
        println(" - Calculating block mapping")
        calculateBlockMapping(ast)
        println(" - Calculating loop scores")
        calculateLoopScores(ast)
        loopCounter = 0
        println(" - Running general statement counting")
        granularity(ast)
        println(" - Calculating combined block scores")
        calculateBlockScores() // Calculates accumulated block scores for function scores
        println(" - Calculating function scores")
        calculateFunctionScores()
        println(" - Calculating recursions and adding function influence to blocks")
        careFunctionCalls() // Adds function scores to blocks
        println(" - Finalizing block scores")
        finalizeBlockScores()

        blockScores.foreach(block => {
            if (block._1 != null && blockToStatements.contains(block._1) && block._2 < threshold) {
                val statements = blockToStatements(block._1)

                statements.keySet().toArray.foreach({
                    case i@IfStatement(_, One(CompoundStatement(list)), _, _) =>
                        ignoredStatements.put(i, block._2 < threshold)

                        if (list.size == 1) {
                            ignoredStatements.put(list.head.entry, block._2 < threshold)
                        }
                    case s: Statement =>
                        ignoredStatements.put(s, block._2 < threshold)
                })
            }
        })

        writeDataFile()
        writeMapFile()
        writeOperatorFile()

        ignoredStatements
    }

    private def readConfigFile(): Unit = {
        if (Files.exists(Paths.get("./granularity_config.txt"))) {
            for (c <- Source.fromFile("granularity_config.txt").getLines()) {
                val configParts = c.split("=")

                if (configParts.size == 2) {
                    configParts(0) match {
                        case "for_weight" =>
                            FOR_WEIGHT = configParts(1).toDouble
                        case "while_weight" =>
                            WHILE_WEIGHT = configParts(1).toDouble
                        case "do_weight" =>
                            DO_WEIGHT = configParts(1).toDouble
                        case "break_weight" =>
                            BREAK_WEIGHT = configParts(1).toDouble
                        case "continue_weight" =>
                            CONTINUE_WEIGHT = configParts(1).toDouble
                        case "goto_weight" =>
                            GOTO_WEIGHT = configParts(1).toDouble
                        case "recursive_weight" =>
                            RECURSIVE_WEIGHT = configParts(1).toDouble
                        case "default_function_value" =>
                            DEFAULT_FUNCTION_WEIGHT = configParts(1).toDouble
                        case "function_accumulation" =>
                            FUNCTION_ACCUMULATION = configParts(1).toBoolean
                        case "function_accumulation_depth" =>
                            FUNCTION_ACCUMULATION_DEPTH = configParts(1).toInt
                        case "function_call_weight" =>
                            FUNCTION_CALL_WEIGHT = configParts(1).toDouble
                        case "bucket_size" =>
                            BUCKET_SIZE = configParts(1).toInt
                        case _ =>
                    }
                }
            }
        }
    }

    private def readFunctionConfigFile(): Unit = {
        if (Files.exists(Paths.get("./predefined_function_scores.txt"))) {
            for (c <- Source.fromFile("predefined_function_scores.txt").getLines()) {
                val configParts = c.split(" ")

                if (configParts.size == 2 && !predefinedFunctionScores.contains(configParts(0))) {
                    predefinedFunctionScores += (configParts(0) -> configParts(1).toDouble)
                }
            }
        }
    }

    private def readFunctionOffsetFile(): Unit = {
        if (Files.exists(Paths.get("./function_offsets.txt"))) {
            for (c <- Source.fromFile("function_offsets.txt").getLines()) {
                val configParts = c.split(" ")

                if (configParts.size == 2 && !functionCallOffsets.contains(configParts(0))) {
                    functionCallOffsets += (configParts(0) -> configParts(1).toDouble)
                }
            }
        }
    }

    private def writeDataFile(): Unit = {
        val pw = new PrintWriter(new File(dir + "data.csv"))

        var map: Map[Int, Int] = Map.empty[Int, Int]
        var string = ""

        for ((k, v) <- blockScores) {
            val divide = (v/BUCKET_SIZE).floor.toInt

            if (map.contains(divide)) {
                val counter = map(divide)
                map -= divide
                map += (divide -> (counter+1))
            } else {
                map += (divide -> 1)
            }
        }

        for ((k, v) <- map) {
            string = string + k.toString + "," + v.toString + "\n"
        }

        pw.write(string)
        pw.close()
    }

    private def writeMapFile(): Unit = {
        val pw = new PrintWriter(new File(dir + "map.csv"))

        var string = ""

        for ((k, v) <- blockScores) {
            val id = k.split("_").last
            var causesString = ""
            val causes = collection.immutable.SortedSet(scoreCauses(k).toList: _*)

            if (causes.isEmpty) {
                causesString = "None"
            } else {
                causesString = causes.mkString(";")
            }

            string = string + id + "," + k.substring(0, k.length-id.length-1) + "," + v.toString + "," + causesString + "\n"
        }

        pw.write(string)
        pw.close()
    }

    private def writeOperatorFile(): Unit = {
        val pw = new PrintWriter(new File(dir + "operators.csv"))

        var string = ""

        string += "Addition," + additionGeneralCounter + "," + additionBlockCounter + "\n"
        string += "Subtraction," + subtractionGeneralCounter + "," + subtractionBlockCounter + "\n"
        string += "Multiplication," + multiplicationGeneralCounter + "," + multiplicationBlockCounter + "\n"
        string += "Division," + divisionGeneralCounter + "," + divisionBlockCounter + "\n"

        pw.write(string)
        pw.close()
    }

    private def codeAnalysis(obj: Any, currentBlock: FeatureExpr = FeatureExprFactory.True): Unit = {
        obj match {
            case "+" | "++" | "+=" | "=+" =>
                additionGeneralCounter += + 1

                if (currentBlock != FeatureExprFactory.True) {
                    additionBlockCounter += 1
                }
            case "-" | "--" | "-=" | "=-" =>
                subtractionGeneralCounter += 1

                if (currentBlock != FeatureExprFactory.True) {
                    subtractionBlockCounter += 1
                }
            case "*" | "*=" | "=*" =>
                multiplicationGeneralCounter += 1

                if (currentBlock != FeatureExprFactory.True) {
                    multiplicationBlockCounter += 1
                }
            case "/" | "/=" | "=/" =>
                divisionGeneralCounter += 1

                if (currentBlock != FeatureExprFactory.True) {
                    divisionBlockCounter += 1
                }
            case x: AST =>
                if (x.productArity > 0) {
                    for (y <- x.productIterator.toList) {
                        codeAnalysis(y, currentBlock)
                    }
                }
            case x: Opt[_] =>
                codeAnalysis(x.entry, x.condition)
            case One(x) =>
                codeAnalysis(x, currentBlock)
            case x: Choice[_] =>
                codeAnalysis(x.thenBranch, x.condition)
                codeAnalysis(x.elseBranch, x.condition.not())
            case x: List[_] =>
                for (elem <- x) {
                    codeAnalysis(elem, currentBlock)
                }
            case Some(x) =>
                codeAnalysis(x, currentBlock)
            case None =>
            case _ =>
        }
    }

    // Global for block mapping calculation
    var currentBlockMapping: Map[FeatureExpr, String] = Map.empty[FeatureExpr, String]

    private def calculateBlockMapping(obj: Any, currentBlock: FeatureExpr = FeatureExprFactory.True, currentFunction: String = null): Unit = {
        obj match {
            case x: AST =>

                var function = currentFunction

                if (function == null) {
                    currentBlockMapping = Map.empty[FeatureExpr, String]
                }

                obj match {
                    case funcDef: FunctionDef =>
                        function = funcDef.getName
                    case o =>
                }

                if (x.productArity > 0) {
                    for (y <- x.productIterator.toList) {
                        calculateBlockMapping(y, currentBlock, function)
                    }
                }
            case x: Opt[_] =>
                if (currentFunction != null || x.condition == FeatureExprFactory.True) {

                    // There are no measurement functions for DeclarationStatements in general. We have to filter them
                    // to look at only the important blocks
                    x.entry match {
                        case _: DeclarationStatement =>
                            calculateBlockMapping(x.entry, currentBlock, currentFunction)
                        case s: Statement =>
                            var cond = currentBlock.&(x.condition)

                            x.entry match {
                                case i: IfStatement =>
                                    i.condition match {
                                        case c: Choice[_] =>
                                            cond = cond.&(c.condition)
                                        case One(n: NAryExpr) =>
                                            var optFound = false
                                            for (i <- n.others
                                                    if !optFound) {
                                                if (i.condition != FeatureExprFactory.True) {
                                                    cond = cond.&(i.condition)
                                                    optFound = true
                                                }
                                            }
                                        case _ =>
                                    }
                                case e: ElifStatement => // ElifStatement is no Statement (?!?)
                                    e.condition match {
                                        case c: Choice[_] =>
                                            cond = cond.&(c.condition)
                                        case One(n: NAryExpr) =>
                                            var optFound = false
                                            for (i <- n.others
                                                 if !optFound) {
                                                if (i.condition != FeatureExprFactory.True) {
                                                    cond = cond.&(i.condition)
                                                    optFound = true
                                                }
                                            }
                                        case _ =>
                                    }
                                case w: WhileStatement =>
                                    w.s match {
                                        case c: Choice[_] =>
                                            cond = cond.&(c.condition)
                                        case One(n: NAryExpr) =>
                                            var optFound = false
                                            for (i <- n.others
                                                 if !optFound) {
                                                if (i.condition != FeatureExprFactory.True) {
                                                    cond = cond.&(i.condition)
                                                    optFound = true
                                                }
                                            }
                                        case _ =>
                                    }
                                case d: DoStatement =>
                                    d.s match {
                                        case c: Choice[_] =>
                                            cond = cond.&(c.condition)
                                        case One(n: NAryExpr) =>
                                            var optFound = false
                                            for (i <- n.others
                                                 if !optFound) {
                                                if (i.condition != FeatureExprFactory.True) {
                                                    cond = cond.&(i.condition)
                                                    optFound = true
                                                }
                                            }
                                        case _ =>
                                    }
                                case _ =>

                            }

                            updateBlockMapping(cond, s)

                            if (cond != FeatureExprFactory.True) {
                                val block = currentBlockMapping(cond)

                                if (blockToStatements.contains(block)) {
                                    val map = blockToStatements(block)
                                    map.put(s, s)

                                    blockToStatements -= block
                                    blockToStatements += (block -> map)
                                } else {
                                    val map = new IdentityHashMap[Statement, Statement]()
                                    map.put(s, s)

                                    blockToStatements += (block -> map)
                                }

                                if (functionBlocks.contains(currentFunction)) {
                                    if (!functionBlocks(currentFunction).contains(block)) {
                                        var funcBlocks = functionBlocks(currentFunction)
                                        funcBlocks += block

                                        functionBlocks -= currentFunction
                                        functionBlocks += (currentFunction -> funcBlocks)
                                    }
                                } else {
                                    var funcBlocks = Set.empty[String]
                                    funcBlocks += block

                                    functionBlocks += (currentFunction -> funcBlocks)
                                }

                                calculateBlockMapping(x.entry, cond, currentFunction)
                            } else {
                                calculateBlockMapping(x.entry, cond, currentFunction)
                            }
                        case e: ElifStatement =>
                            var cond = currentBlock
                            e.condition match {
                                case c: Choice[_] =>
                                    cond = cond.&(c.condition)
                                case _ =>
                            }
                            calculateBlockMapping(x.entry, cond, currentFunction)
                        case o =>
                            calculateBlockMapping(x.entry, currentBlock, currentFunction)
                    }
                }
            case One(x) =>
                calculateBlockMapping(x, currentBlock, currentFunction)
            case x: Choice[_] =>
                calculateBlockMapping(x.thenBranch, currentBlock.&(x.condition), currentFunction)
                calculateBlockMapping(x.elseBranch, currentBlock.&(x.condition.not()), currentFunction)
            case x: List[_] =>
                for (elem <- x) {
                    calculateBlockMapping(elem, currentBlock, currentFunction)
                }
            case Some(x) =>
                calculateBlockMapping(x, currentBlock, currentFunction)
            case None =>
            case o =>
        }
    }

    private def createBlockName(expr: FeatureExpr): String = {
        var id = 0
        if(featureCounter.contains(expr)) {
            id = featureCounter(expr)
        }

        contextToReadableString(expr) + "_" + id
        //expr.toString() + "_" + java.util.UUID.randomUUID.toString
    }

    private def contextToReadableString(context: FeatureExpr): String = {
        val regexPattern = "(defined|definedEx)\\(([a-zA-Z_0-9]+)\\)".r
        return regexPattern replaceAllIn(context.toTextExpr, "$2")
    }

    private def updateBlockMapping(currentExpr: FeatureExpr, stmt: Statement): Unit = {
        if (currentExpr == FeatureExprFactory.True) {
            currentBlockMapping = Map.empty[FeatureExpr, String]
        } else {
            var keysToRemove = Set.empty[FeatureExpr]

            for (key <- currentBlockMapping.keySet.filter(p => p != currentExpr)) {
                // Check if currentExpr is new block in currentBlocks
                if (!(key.collectDistinctFeatureObjects subsetOf currentExpr.collectDistinctFeatureObjects)
                    || !currentExpr.and(key).implies(key).isTautology() || key.implies(currentExpr.and(key)).isTautology()) {
                    keysToRemove += key
                }
            }

            for (key <- keysToRemove) {
                currentBlockMapping -= key
            }

            if (!currentBlockMapping.contains(currentExpr)) {
                val newBlock = createBlockName(currentExpr)
                currentBlockMapping += (currentExpr -> newBlock)
                blockToExpr += (newBlock -> currentExpr)
            }

            val currBlock = currentBlockMapping(currentExpr)

            //exprToBlock.put(currentExpr, currBlock)
            statementToBlock.put(stmt, currBlock)

            // Update statementMapping
            val blockNameParts = currBlock.split("_")
            statementMapping.put(stmt, blockNameParts(blockNameParts.size - 1))

            // Update blockCapsuling
            for(key <- currentBlockMapping.keySet.filter(p => p != currentExpr)) {
                val block = currentBlockMapping(key)

                if (blockCapsuling.contains(block)) {
                    var set = blockCapsuling(block)

                    if (!set.contains(currBlock)) {
                        set += currBlock
                        blockCapsuling -= block
                        blockCapsuling += (block -> set)
                    }
                } else {
                    var set = Set.empty[String]
                    set += currBlock

                    blockCapsuling += (block -> set)
                }
            }

            // Update feature counter
            if (keysToRemove.nonEmpty || !blockToStatements.contains(currBlock)) {
                var ftCounter = 0

                if (featureCounter.contains(currentExpr)) {
                    ftCounter = featureCounter(currentExpr)

                    featureCounter -= currentExpr
                }

                featureCounter += (currentExpr -> (ftCounter + 1))
            }
        }
    }

    // Global for current status of loops for loop score calculation and granularity
    private var loopExited: Map[Int, Boolean] = Map.empty[Int, Boolean]

    private def calculateLoopScores(obj: Any, currentLoopSet: Set[Int] = Set.empty[Int], currentLoop: Int = null.asInstanceOf[Int]): Unit = {
        obj match {
            case x: ForStatement =>
                val counter: Int = loopCounter
                loopScores += (loopCounter -> FOR_WEIGHT)
                loopExited += (loopCounter -> false)

                loopCounter += 1

                if (x.productArity > 0) {
                    for (y <- x.productIterator.toList) {
                        if (!loopExited(counter)) {
                            calculateLoopScores(y, currentLoopSet + counter, counter)
                        }
                    }
                }
            case x: WhileStatement =>
                val counter: Int = loopCounter
                loopScores += (loopCounter -> WHILE_WEIGHT)
                loopExited += (loopCounter -> false)

                loopCounter += 1

                if (x.productArity > 0) {
                    for (y <- x.productIterator.toList) {
                        if (!loopExited(counter)) {
                            calculateLoopScores(y, currentLoopSet + counter, counter)
                        }
                    }
                }
            case x: DoStatement =>
                val counter: Int = loopCounter
                loopScores += (loopCounter -> DO_WEIGHT)
                loopExited += (loopCounter -> false)

                loopCounter += 1

                if (x.productArity > 0) {
                    for (y <- x.productIterator.toList) {
                        if (!loopExited(counter)) {
                            calculateLoopScores(y, currentLoopSet + counter, counter)
                        }
                    }
                }
            case x: BreakStatement =>
                if (currentLoop != null.asInstanceOf[Int]) {
                    val score = loopScores(currentLoop) * BREAK_WEIGHT
                    loopScores -= currentLoop
                    loopExited -= currentLoop
                    loopScores += (currentLoop -> score)
                    loopExited += (currentLoop -> true)
                }
            case x: ContinueStatement =>
                val score = loopScores(currentLoop) * CONTINUE_WEIGHT
                loopScores -= currentLoop
                loopExited -= currentLoop
                loopScores += (currentLoop -> score)
                loopExited += (currentLoop -> true)
            case x: GotoStatement =>
                for (y <- currentLoopSet) {
                    val score = loopScores(y) * GOTO_WEIGHT
                    loopScores -= y
                    loopExited -= y
                    loopScores += (y -> score)
                    loopExited += (y -> true)
                }
            case x: AST =>
                if (x.productArity > 0) {
                    for (y <- x.productIterator.toList) {
                        calculateLoopScores(y, currentLoopSet, currentLoop)
                    }
                }
            case x: Opt[_] =>
                calculateLoopScores(x.entry, currentLoopSet, currentLoop)
            case One(x) =>
                calculateLoopScores(x, currentLoopSet, currentLoop)
            case x: Choice[_] =>
                calculateLoopScores(x.thenBranch, currentLoopSet, currentLoop)
                calculateLoopScores(x.elseBranch, currentLoopSet, currentLoop)
            case x: List[_] =>
                for (elem <- x) {
                    calculateLoopScores(elem, currentLoopSet, currentLoop)
                }
            case Some(x) =>
                calculateLoopScores(x, currentLoopSet, currentLoop)
            case None =>
            case o =>
        }
    }

    private def granularity(obj: Any, currentBlocks: Set[String] = Set.empty[String], currentFunction: String = null,
                            weight: Double = 1.0, causes: Set[String] = Set.empty[String]): Unit = {
        var newCauses = causes

        obj match {
            case x: ForStatement =>
                val currentLoop: Int = loopCounter
                var blocks: Set[String] = currentBlocks

                newCauses += "For-Loop"

                if (statementToBlock.containsKey(x)) {
                    blocks = blocks + statementToBlock.get(x)

                    for (block <- blocks) {
                        if (!blockScores.contains(block)) {
                            blockScores += (block -> 0)
                        }
                    }
                }

                for (c <- newCauses) {
                    for (b <- blocks) {
                        addScoreCause(b, c)
                    }
                }

                increaseScore(blocks, currentFunction, weight * loopScores(currentLoop))

                loopCounter += 1
                if (x.productArity > 0) {
                    for (y <- x.productIterator.toList) {
                        granularity(y, blocks, currentFunction, weight * loopScores(currentLoop), newCauses)
                    }
                }
            case x: WhileStatement =>
                val currentLoop: Int = loopCounter
                var blocks: Set[String] = currentBlocks

                newCauses += "While-Loop"

                if (statementToBlock.containsKey(x)) {
                    blocks = blocks + statementToBlock.get(x)

                    for (block <- blocks) {
                        if (!blockScores.contains(block)) {
                            blockScores += (block -> 0)
                        }
                    }
                }

                for (c <- newCauses) {
                    for (b <- blocks) {
                        addScoreCause(b, c)
                    }
                }

                increaseScore(blocks, currentFunction, weight * loopScores(currentLoop))

                loopCounter += 1
                if (x.productArity > 0) {
                    for (y <- x.productIterator.toList) {
                        granularity(y, blocks, currentFunction, weight * loopScores(currentLoop), newCauses)
                    }
                }
            case x: DoStatement =>
                val currentLoop: Int = loopCounter
                var blocks: Set[String] = currentBlocks

                newCauses += "Do-Loop"

                if (statementToBlock.containsKey(x)) {
                    blocks = blocks + statementToBlock.get(x)

                    for (block <- blocks) {
                        if (!blockScores.contains(block)) {
                            blockScores += (block -> 0)
                        }
                    }
                }

                for (c <- newCauses) {
                    for (b <- blocks) {
                        addScoreCause(b, c)
                    }
                }

                increaseScore(blocks, currentFunction, weight * loopScores(currentLoop))

                loopCounter += 1
                if (x.productArity > 0) {
                    for (y <- x.productIterator.toList) {
                        granularity(y, blocks, currentFunction, weight * loopScores(currentLoop), newCauses)
                    }
                }

            case x: AST =>

                var functionDef = currentFunction
                var blocks = currentBlocks
                var adjustedWeight = weight

                obj match {
                    case funcDef: FunctionDef =>
                        functionDef = funcDef.getName
                        functionDefs = functionDefs + functionDef
                    case funcCall: PostfixExpr =>
                        var funcName: String = null

                        funcCall.p match {
                            case i: Id =>
                                funcName = i.name
                            case _ =>
                        }

                        if (funcName != null) {
                            funcCall.s match {
                                case t: FunctionCall =>
                                    for (block <- currentBlocks) {
                                        val tuple = new FuncCall(funcName, block, blockToExpr(block), weight)
                                        if (globalFunctionCalls.contains(currentFunction)) {
                                            val list = globalFunctionCalls(currentFunction)

                                            globalFunctionCalls -= currentFunction
                                            globalFunctionCalls += (currentFunction -> (list ::: List(tuple)))
                                        } else {
                                            globalFunctionCalls += (currentFunction -> List(tuple))
                                        }
                                    }

                                    if (currentBlocks.isEmpty) {
                                        val tuple = new FuncCall(funcName, "True", FeatureExprFactory.True, weight)
                                        if (globalFunctionCalls.contains(currentFunction)) {
                                            val list = globalFunctionCalls(currentFunction)

                                            globalFunctionCalls -= currentFunction
                                            globalFunctionCalls += (currentFunction -> (list ::: List(tuple)))
                                        } else {
                                            globalFunctionCalls += (currentFunction -> List(tuple))
                                        }
                                    }
                                case _ =>
                            }
                        }
                    case s: Statement =>
                        if (statementToBlock.containsKey(s)) {
                            blocks = blocks + statementToBlock.get(s)

                            for (block <- blocks) {
                                if (!blockScores.contains(block)) {
                                    blockScores += (block -> 0)
                                }
                            }
                        }
                        obj match {
                            case _: EmptyStatement | _: BreakStatement | _: ContinueStatement | _: GotoStatement => // Filtering statements that should not be counted
                            case _ =>
                                for (c <- newCauses) {
                                    for (b <- blocks) {
                                        addScoreCause(b, c)
                                    }
                                }

                                increaseScore(blocks, currentFunction, weight)
                        }
                        obj match {
                            case i: IfStatement =>
                                adjustedWeight = weight/(i.elifs.size + 2)
                            case SwitchStatement(_, One(CompoundStatement(list))) =>
                                var amountCases = 0

                                // Count amount of case statements and default statement
                                for (elem <- list) {
                                    elem.entry match {
                                        case _: CaseStatement | _: DefaultStatement =>
                                            amountCases += 1
                                        case _ =>
                                    }
                                }

                                if (amountCases != 0)
                                    adjustedWeight = weight/amountCases

                            case _ =>
                        }
                    case _ =>
                }

                if (x.productArity > 0) {
                    for (y <- x.productIterator.toList) {
                        granularity(y, blocks, functionDef, adjustedWeight, newCauses)
                    }
                }
            case x: Opt[_] =>
                granularity(x.entry, currentBlocks, currentFunction, weight, newCauses)
            case x: List[_] =>
                for (elem <- x) {
                    granularity(elem, currentBlocks, currentFunction, weight, newCauses)
                }
            case Some(x) =>
                granularity(x, currentBlocks, currentFunction, weight, newCauses)
            case x: One[_] =>
                granularity(x.value, currentBlocks, currentFunction, weight, newCauses)
            case x: Choice[_] =>
                granularity(x.thenBranch, currentBlocks, currentFunction, weight, newCauses)
                granularity(x.elseBranch, currentBlocks, currentFunction, weight, newCauses)
            case None =>
            case o =>
        }
    }

    private def increaseScore(currentBlocks: Set[String], currentFunction: String, weight: Double): Unit = {
        if (currentFunction != null) {

            // Update loc of blocks
            for (block <- currentBlocks) {
                if (blockScores.contains(block)) {
                    val w = blockScores(block)

                    blockScores -= block
                    blockScores += (block -> (w + weight))
                } else {
                    blockScores += (block -> weight)
                }
            }

            // Update score of functions (True only)
            if (currentBlocks.isEmpty) {
                if (functionScores.contains(currentFunction)) {
                    val score = functionScores(currentFunction)

                    functionScores -= currentFunction
                    functionScores += (currentFunction -> (score + weight))
                } else {
                    functionScores = functionScores + (currentFunction -> weight)
                }
            }
        }
    }

    private def calculateBlockScores(): Unit = {
        var blockScoreChange: Map[String, Double] = Map.empty[String, Double]

        singleBlockScores = blockScores

        blockScores.foreach(block => {
            var sum = blockScores(block._1)

            if (blockCapsuling.contains(block._1)) {
                for (subBlock <- blockCapsuling(block._1)) {
                    if (blockScores.contains(subBlock)) {
                        sum += blockScores(subBlock)
                    }
                }
            }

            blockScoreChange += (block._1 -> sum)
        })

        blockScores = blockScoreChange
    }

    private def calculateFunctionScores(): Unit = {
        for (func <- functionDefs) {
            var sum: Double = 0.0

            if (functionScores.contains(func)) {
                sum += functionScores(func)
            }

            if (functionBlocks.contains(func)) {
                for (block <- functionBlocks(func)) {
                    if (blockScores.contains(block))
                        sum += blockScores(block)
                }
            }

            if (functionScores.contains(func)) {
                functionScores -= func
            }

            functionScores += (func -> sum)
        }

        // Setting scores for functions which are not defined in this AST
        for (calls <- globalFunctionCalls.values) {
            for (c <- calls) {
                if (!functionScores.contains(c.functionName)) {
                    functionScores += (c.functionName -> DEFAULT_FUNCTION_WEIGHT)
                }
            }
        }
    }

    private def getRecSet(call: FuncCall): Option[Set[String]] = {
        var visitedFunctions: Map[String, Boolean] = Map.empty[String, Boolean]
        var nextFunctionCalls: Set[FuncCall] = Set.empty[FuncCall]

        nextFunctionCalls += call

        while (nextFunctionCalls.nonEmpty) {
            var functionCalls: Set[FuncCall] = Set.empty[FuncCall]

            for (func <- nextFunctionCalls) {
                if (!predefinedFunctionScores.contains(func.functionName)) {
                    if (globalFunctionCalls.contains(func.functionName)
                        && (!visitedFunctions.contains(func.functionName) || !visitedFunctions(func.functionName))) {
                        for (call <- globalFunctionCalls(func.functionName)) {
                            functionCalls += call
                        }
                    }

                    if (!visitedFunctions.contains(func.functionName)) {
                        visitedFunctions += (func.functionName -> false)
                    } else if (!visitedFunctions(func.functionName)) {
                        visitedFunctions -= func.functionName
                        visitedFunctions += (func.functionName -> true)
                    }
                }
            }

            nextFunctionCalls = functionCalls
        }

        var recSet = visitedFunctions.filter(p => p._2).keySet

        // Removing all function calls that are no part of any recursion, Result: Set of (possibly multiple) recursions
        for ((startFunc, calls) <- functionCalledBy) {
            var functionSet: Set[String] = Set.empty[String]
            var nextFunctions: Set[String] = calls

            while(nextFunctions.nonEmpty) {
                var set: Set[String] = Set.empty[String]

                for (f <- nextFunctions) {
                    if (!functionSet.contains(f) && functionCalledBy.contains(f)) {
                        functionSet += f
                        set = set.union(functionCalledBy(f))
                    }
                }

                nextFunctions = set
            }

            if (!functionSet.contains(startFunc)) {
                recSet -= startFunc
            }
        }

        if (recSet.contains(call.functionName)) {
            // Get the one recursion that contains the call parameter

            var functionSet: Set[String] = Set.empty[String]
            var nextFunctions: Set[String] = Set(call.functionName)

            while(nextFunctions.nonEmpty) {
                var set: Set[String] = Set.empty[String]

                for (f <- nextFunctions) {
                    if (!functionSet.contains(f) && functionCalledBy.contains(f)) {
                        functionSet += f
                        set = set.union(functionCalledBy(f))
                    }
                }

                nextFunctions = set
            }

            Some(recSet.intersect(functionSet))

        } else {
            None
        }

    }

    var functionCalledBy: Map[String, Set[String]] = Map.empty[String, Set[String]]

    private def calculateFunctionsCalledBy(): Unit = {
        for ((func, calls) <- globalFunctionCalls) {
            for (call <- calls) {
                if (functionCalledBy.contains(call.functionName)) {
                    var set = functionCalledBy(call.functionName)
                    set += func
                    functionCalledBy -= call.functionName
                    functionCalledBy += (call.functionName -> set)
                } else {
                    functionCalledBy += (call.functionName -> Set(func))
                }
            }
        }
    }

    var visitedCalledFunctions: Set[String] = Set.empty[String]
    var callCauses: Set[String] = Set.empty[String]

    private def careFunctionCalls(): Unit = {
        var functionRecSets: Set[Set[String]] = Set.empty[Set[String]]
        var functionRecSetMapping: Map[String, Set[String]] = Map.empty[String, Set[String]]
        var recSetValue: Map[String, Double] = Map.empty[String, Double]

        if (!FUNCTION_ACCUMULATION) {
            calculateFunctionsCalledBy()

            println("     -- Calculating recursions")
            var i = 1
            var visitedFunctions: Set[String] = Set.empty[String]

            for ((funcLocation, funcCalls) <- globalFunctionCalls) {
                println("         --- Attempting to calculate recursion: Evaluating calls of function  " + i.toString + " of " +  globalFunctionCalls.size)
                for (call <- funcCalls) {
                    if (!visitedFunctions.contains(call.functionName) && functionRecSets.forall(set => !set.contains(call.functionName))) {
                        visitedFunctions += call.functionName

                        getRecSet(call) match {
                            case Some(x) =>
                                functionRecSets += x
                            case None =>
                        }
                    }
                }
                i += 1
            }

            // If there are still intersections take the most general one
            while (functionRecSets.exists(set1 => functionRecSets.exists(set2 => set1 != set2 && set1.intersect(set2).nonEmpty))) {
                var recSets: Set[Set[String]] = functionRecSets

                for (set1 <- functionRecSets) {
                    for (set2 <- functionRecSets) {
                        val intersection = set1.intersect(set2)

                        if (set1 != set2 && intersection.nonEmpty) {
                            recSets -= set1
                            recSets -= set2
                            recSets += intersection
                        }
                    }
                }

                functionRecSets = recSets
            }

            val pw = new PrintWriter(new File(dir + "recursions.txt"))
            var string = ""

            for (rec <- functionRecSets) {
                string = string + rec.toString + "\n"
            }

            pw.write(string)
            pw.close()

            println("     -- Calculating recursion values")
            // Calculate the score of each recursion set
            for (recSet <- functionRecSets) {
                var sum: Double = 0.0

                for (func <- recSet) {
                    sum += functionScores(func)
                }

                for (func <- recSet) {
                    functionRecSetMapping += (func -> recSet)
                    recSetValue += (func -> sum)
                }
            }
        }

        // Calculate the accumulated costs of a function call
        def getCallValue(call: FuncCall, cond: FeatureExpr, currentDepth: Int): Double = {
            if (predefinedFunctionScores.contains(call.functionName)) {
                var sum: Double = predefinedFunctionScores(call.functionName)

                if (functionCallOffsets.contains(call.functionName)) {
                    sum += functionCallOffsets(call.functionName)
                }

                return call.weight * sum
            }

            if (!FUNCTION_ACCUMULATION) {
                var sum: Double = 0.0

                if (visitedCalledFunctions.contains(call.functionName)) {
                    return sum
                }

                if (recSetValue.contains(call.functionName)) {
                    val recSet = functionRecSetMapping(call.functionName)

                    callCauses += "Recursion"

                    for (func <- recSet.filter(f => functionBlocks.contains(f))) {
                        for (block <- functionBlocks(func).filter(b => scoreCauses.contains(b))) {
                            callCauses = callCauses.union(scoreCauses(block))
                        }
                    }

                    sum += RECURSIVE_WEIGHT * recSetValue(call.functionName)
                    visitedCalledFunctions = visitedCalledFunctions.union(recSet)

                    for (func <- recSet) {
                        for (c <- globalFunctionCalls(func)) {
                            if (!recSet.contains(c.functionName)) {
                                sum += getCallValue(c, cond.and(call.condition), currentDepth)
                            }
                        }
                    }

                    call.weight * sum
                } else {
                    if (call.condition.and(cond).isSatisfiable(featureModel)) {
                        var sum: Double = functionScores(call.functionName)

                        callCauses += "Function"

                        if (functionBlocks.contains(call.functionName)) {
                            for (block <- functionBlocks(call.functionName).filter(b => scoreCauses.contains(b))) {
                                callCauses = callCauses.union(scoreCauses(block))
                            }
                        }

                        if (functionCallOffsets.contains(call.functionName)) {
                            sum += functionCallOffsets(call.functionName)
                        }

                        if (globalFunctionCalls.contains(call.functionName)) {
                            for (furtherCall <- globalFunctionCalls(call.functionName)) {
                                sum += getCallValue(furtherCall, cond.and(call.condition), currentDepth)
                            }
                        }

                        call.weight * sum
                    } else {
                        0
                    }
                }
            } else {
                if (call.condition.and(cond).isSatisfiable(featureModel)) {
                    var sum: Double = 0.0

                    callCauses += "Function"

                    if (functionBlocks.contains(call.functionName)) {
                        for (block <- functionBlocks(call.functionName).filter(b => scoreCauses.contains(b))) {
                            callCauses = callCauses.union(scoreCauses(block))
                        }
                    }


                    if (currentDepth < FUNCTION_ACCUMULATION_DEPTH) {
                        sum = functionScores(call.functionName)

                        if (functionCallOffsets.contains(call.functionName)) {
                            sum += functionCallOffsets(call.functionName)
                        }

                        if (globalFunctionCalls.contains(call.functionName)) {
                            for (furtherCall <- globalFunctionCalls(call.functionName)) {
                                sum += getCallValue(furtherCall, cond.and(call.condition), currentDepth + 1)
                            }
                        }

                    } else {
                        sum = DEFAULT_FUNCTION_WEIGHT
                    }

                    call.weight * sum
                } else {
                    0
                }
            }
        }

        // Add function call costs to the corresponding blocks (single score)
        println("     -- Adding functions calls to single blocks")
        var i = 1
        for (value <- globalFunctionCalls.values) {
            println("         --- Adding function calls of function " + i.toString + " of " +  globalFunctionCalls.size)
            for (call <- value) {
                if (call.condition != FeatureExprFactory.True) {
                    visitedCalledFunctions = Set.empty[String]
                    callCauses = Set.empty[String]
                    if (singleBlockScores.contains(call.block)) {
                        val w = singleBlockScores(call.block)

                        singleBlockScores -= call.block
                        singleBlockScores += (call.block -> (w + FUNCTION_CALL_WEIGHT * getCallValue(call, FeatureExprFactory.True, 0)))
                    } else {
                        singleBlockScores += (call.block -> FUNCTION_CALL_WEIGHT * getCallValue(call, FeatureExprFactory.True, 0))
                    }

                    for (cause <- callCauses) {
                        addScoreCause(call.block, cause)
                    }
                }
            }
            i += 1
        }
    }

    private def finalizeBlockScores() : Unit = {
        var blockScoreChange: Map[String, Double] = Map.empty[String, Double]

        blockScores = singleBlockScores

        blockScores.foreach(block => {
            var sum = blockScores(block._1)
            var causes = Set.empty[String]

            if (scoreCauses.contains(block._1)) {
                causes = scoreCauses(block._1)
            }

            if (blockCapsuling.contains(block._1)) {
                for (subBlock <- blockCapsuling(block._1)) {
                    if (blockScores.contains(subBlock)) {
                        sum += blockScores(subBlock)
                    }
                    if (scoreCauses.contains(subBlock)) {
                        causes = causes.union(scoreCauses(subBlock))
                    }
                }
            }

            if (scoreCauses.contains(block._1)) {
                scoreCauses -= block._1
            }

            scoreCauses += (block._1 -> causes)

            blockScoreChange += (block._1 -> sum)
        })

        blockScores = blockScoreChange
    }

    private def addScoreCause(block: String, scoreCause: String) : Unit = {

        if (scoreCauses.contains(block)) {
            var set: Set[String] = scoreCauses(block)
            set += scoreCause

            scoreCauses -= block
            scoreCauses += (block -> set)
        } else {
            scoreCauses += (block -> Set(scoreCause))
        }
    }

}

class IfdefToIfGranularity extends IfdefToIfGranularityInterface with IfdefToIfGranularityExecCode {

}
