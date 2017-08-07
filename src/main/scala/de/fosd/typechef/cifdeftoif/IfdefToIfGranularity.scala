package de.fosd.typechef.cifdeftoif

import java.io.{File, PrintWriter}
import java.util.IdentityHashMap
import java.nio.file.{Files, Paths}

import de.fosd.typechef.conditional.{Choice, One, Opt}
import de.fosd.typechef.featureexpr._
import de.fosd.typechef.parser.c._

import scala.io.Source

trait IfdefToIfGranularityInterface {

    class FuncCall(var functionName: String, var block: String, var condition: FeatureExpr, var weight: Double) {}

    protected var BUCKET_SIZE: Int = 5

    protected var IF_WEIGHT: Double = 1.0
    protected var SWITCH_WEIGHT: Double = 1.0
    protected var LOOP_WEIGHT: Double = 1.0
    protected var FOR_WEIGHT: Double = -1.0
    protected var WHILE_WEIGHT: Double = -1.0
    protected var DO_WEIGHT: Double = -1.0
    protected var CONTROL_FLOW_WEIGHT: Double = 1.0
    protected var BREAK_WEIGHT: Double = -1.0
    protected var CONTINUE_WEIGHT: Double = -1.0
    protected var GOTO_WEIGHT: Double = -1.0
    protected var RECURSIVE_WEIGHT: Double = 1.0
    protected var DEFAULT_FUNCTION_WEIGHT = 1.0
    protected var FUNCTION_CALL_WEIGHT: Double = 1.0

    protected var predefinedFunctionScores: Map[String, Double] = Map.empty[String, Double]
    protected var functionCallOffsets: Map[String, Double] = Map.empty[String, Double]

    // in which function is the call? -> (what function is called?, which condition?, which weight?)
    protected var globalFunctionCalls: Map[String, List[FuncCall]] = Map.empty[String, List[FuncCall]]
    protected var statementMapping: IdentityHashMap[Any, String] = new IdentityHashMap[Any, String]()
    protected val statementToBlock: IdentityHashMap[Statement, String] = new IdentityHashMap[Statement, String]()
    protected var blockToStatements: Map[String, IdentityHashMap[Statement, Statement]] = Map.empty[String, IdentityHashMap[Statement, Statement]]
    protected var functionBlocks: Map[String, Set[String]] = Map.empty[String, Set[String]]
    protected var blockToExpr: Map[String, FeatureExpr] = Map.empty[String, FeatureExpr]
    protected var blockCapsuling: Map[String, Set[String]] = Map.empty[String, Set[String]]
    protected var featureCounter: Map[FeatureExpr, Int] = Map.empty[FeatureExpr, Int]
    protected var featureModel: FeatureModel = _
    protected var dir: String = ""

    private var functionCalledBy: Map[String, Set[String]] = Map.empty[String, Set[String]]

    def getStatementMapping(): IdentityHashMap[Any, String] = {
        statementMapping
    }

    /**
      * Reads the configuration file for the weights.
      */
    protected def readConfigFile(): Unit = {
        if (Files.exists(Paths.get("./granularity_config.txt"))) {
            for (c <- Source.fromFile("granularity_config.txt").getLines()) {
                val configParts = c.split("=")

                if (configParts.size == 2) {
                    configParts(0) match {
                        case "if_weight" =>
                            IF_WEIGHT = configParts(1).toDouble
                        case "switch_weight" =>
                            SWITCH_WEIGHT = configParts(1).toDouble
                        case "loop_weight" =>
                            LOOP_WEIGHT = configParts(1).toDouble
                        case "for_weight" =>
                            FOR_WEIGHT = configParts(1).toDouble
                        case "while_weight" =>
                            WHILE_WEIGHT = configParts(1).toDouble
                        case "do_weight" =>
                            DO_WEIGHT = configParts(1).toDouble
                        case "control_flow_weight" =>
                            CONTROL_FLOW_WEIGHT = configParts(1).toDouble
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

    /**
      * Reads the configuration file for the predefined function scores.
      */
    protected def readFunctionConfigFile(): Unit = {
        if (Files.exists(Paths.get("./predefined_function_scores.txt"))) {
            for (c <- Source.fromFile("predefined_function_scores.txt").getLines()) {
                val configParts = c.split(" ")

                if (configParts.size == 2 && !predefinedFunctionScores.contains(configParts(0))) {
                    predefinedFunctionScores += (configParts(0) -> configParts(1).toDouble)
                }
            }
        }
    }

    /**
      * Reads the configuration file for the function offsets.
      */
    protected def readFunctionOffsetFile(): Unit = {
        if (Files.exists(Paths.get("./function_offsets.txt"))) {
            for (c <- Source.fromFile("function_offsets.txt").getLines()) {
                val configParts = c.split(" ")

                if (configParts.size == 2 && !functionCallOffsets.contains(configParts(0))) {
                    functionCallOffsets += (configParts(0) -> configParts(1).toDouble)
                }
            }
        }
    }

    // Global for block mapping calculation
    private var currentBlockMapping: Map[FeatureExpr, String] = Map.empty[FeatureExpr, String]
    private var conditionalVariables: Map[String, FeatureExpr] = Map.empty[String, FeatureExpr]
    private val conditionalVariablesExpr: FeatureExpr = FeatureExprFactory.createDefinedExternal("COND_VAR")

    /**
      * Calculates the blocks of the code and saves the statements of the code.
      */
    protected def calculateBlockMapping(obj: Any, currentBlock: FeatureExpr = FeatureExprFactory.True, currentFunction: String = null): Unit = {
        obj match {
            case x: InitDeclarator =>
                // Only look at declarations which take place outside functions
                if (currentFunction == null) {
                    val setOfConditions: Set[FeatureExpr] = getAllConditionsFromTree(x)
                    var cond = FeatureExprFactory.True

                    for (c <- setOfConditions) {
                        cond = cond.&(c)
                    }

                    if (cond != FeatureExprFactory.True) {
                        conditionalVariables += (x.getName -> conditionalVariablesExpr)
                    }
                }
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
                                            cond = cond.&(createChoiceVariable(c.condition))
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

                                    val setOfVariables = getUsedVariablesFromTree(i.condition)

                                    for (v <- setOfVariables) {
                                        if (conditionalVariables.contains(v)) {
                                            cond = cond.&(conditionalVariables(v))
                                        }
                                    }
                                case e: ElifStatement => // ElifStatement is no Statement (?!?)
                                    e.condition match {
                                        case c: Choice[_] =>
                                            cond = cond.&(createChoiceVariable(c.condition))
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

                                    val setOfVariables = getUsedVariablesFromTree(e.condition)

                                    for (v <- setOfVariables) {
                                        if (conditionalVariables.contains(v)) {
                                            cond = cond.&(conditionalVariables(v))
                                        }
                                    }
                                case w: WhileStatement =>
                                    w.s match {
                                        case c: Choice[_] =>
                                            cond = cond.&(createChoiceVariable(c.condition))
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

                                    val setOfVariables = getUsedVariablesFromTree(w.expr)

                                    for (v <- setOfVariables) {
                                        if (conditionalVariables.contains(v)) {
                                            cond = cond.&(conditionalVariables(v))
                                        }
                                    }
                                case d: DoStatement =>
                                    d.s match {
                                        case c: Choice[_] =>
                                            cond = cond.&(createChoiceVariable(c.condition))
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

                                    val setOfVariables = getUsedVariablesFromTree(d.expr)

                                    for (v <- setOfVariables) {
                                        if (conditionalVariables.contains(v)) {
                                            cond = cond.&(conditionalVariables(v))
                                        }
                                    }
                                case s: SwitchStatement =>
                                    val setOfVariables = getUsedVariablesFromTree(s.expr)

                                    for (v <- setOfVariables) {
                                        if (conditionalVariables.contains(v)) {
                                            cond = cond.&(conditionalVariables(v))
                                        }
                                    }
                                case r: ReturnStatement =>
                                    val condSet = getAllConditionsFromTree(r.expr)

                                    if (condSet.nonEmpty) {
                                        cond = cond.&(condSet.head)
                                    }

                                    val setOfVariables = getUsedVariablesFromTree(r.expr)

                                    for (v <- setOfVariables) {
                                        if (conditionalVariables.contains(v)) {
                                            cond = cond.&(conditionalVariables(v))
                                        }
                                    }
                                case s: Statement =>
                                    // Check if statement contains further statements
                                    var containsStatements = false

                                    if (s.productArity > 0) {
                                        for (y <- s.productIterator.toList if !containsStatements) {
                                            containsStatements = containsStatements & checkIfContainsStatements(y)
                                        }
                                    }

                                    if (!containsStatements) {
                                        val condSet = getAllConditionsFromTree(s)

                                        if (condSet.nonEmpty) {
                                            cond = cond.&(condSet.head)
                                        }

                                        val setOfVariables = getUsedVariablesFromTree(s)

                                        for (v <- setOfVariables) {
                                            if (conditionalVariables.contains(v)) {
                                                cond = cond.&(conditionalVariables(v))
                                            }
                                        }
                                    }
                                case _ => // All other statements
                                    val setOfVariables = getUsedVariablesFromTree(x.entry)

                                    for (v <- setOfVariables) {
                                        if (conditionalVariables.contains(v)) {
                                            cond = cond.&(conditionalVariables(v))
                                        }
                                    }
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
                                    cond = cond.&(createChoiceVariable(c.condition))
                                case _ =>
                                    val set = getAllConditionsFromTree(e.condition)

                                    if (set.nonEmpty) {
                                        cond = cond.&(set.head)
                                    }
                            }
                            calculateBlockMapping(x.entry, cond, currentFunction)
                        case o =>
                            calculateBlockMapping(x.entry, currentBlock, currentFunction)
                    }
                } else {
                    x.entry match {
                        case funcDef: FunctionDef =>
                            calculateBlockMapping(x.entry, currentBlock.&(x.condition), null)
                        case o =>
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

    private def createChoiceVariable(expr: FeatureExpr): FeatureExpr = {
        FeatureExprFactory.createDefinedExternal(contextToReadableString(expr) + "_CHOICE_VAR")
    }

    private def checkIfContainsStatements(obj: Any): Boolean = {
        var check = false

        obj match {
            case s: Statement =>
                check = true
            case x: AST =>
                if (x.productArity > 0) {
                    for (y <- x.productIterator.toList if !check) {
                        check = check && checkIfContainsStatements(y)
                    }
                }
            case x: Opt[_] =>
                check = check & checkIfContainsStatements(x.entry)
            case One(x) =>
                check = check & checkIfContainsStatements(x)
            case x: Choice[_] =>
                check = check & checkIfContainsStatements(x.thenBranch)
                if (!check) {
                    check = check & checkIfContainsStatements(x.elseBranch)
                }
            case x: List[_] =>
                for (elem <- x if !check) {
                    check = check & checkIfContainsStatements(elem)
                }
            case Some(x) =>
                check = check & checkIfContainsStatements(x)
            case None =>
            case o =>
        }

        check
    }

    private def getAllConditionsFromTree(obj: Any): Set[FeatureExpr] = {
        var set: Set[FeatureExpr] = Set.empty[FeatureExpr]

        obj match {
            case x: AST =>
                if (x.productArity > 0) {
                    for (y <- x.productIterator.toList) {
                        set = set.union(getAllConditionsFromTree(y))
                    }
                }
            case x: Opt[_] =>
                if (x.condition != FeatureExprFactory.True || x.condition != FeatureExprFactory.False) {
                    set += x.condition
                }

                set = set.union(getAllConditionsFromTree(x.entry))
            case One(x) =>
                set = set.union(getAllConditionsFromTree(x))
            case x: Choice[_] =>
                if (x.condition != FeatureExprFactory.True || x.condition != FeatureExprFactory.False) {
                    set += x.condition
                }

                set = set.union(getAllConditionsFromTree(x.thenBranch))
                set = set.union(getAllConditionsFromTree(x.elseBranch))
            case x: List[_] =>
                for (elem <- x) {
                    set = set.union(getAllConditionsFromTree(elem))
                }
            case Some(x) =>
                set = set.union(getAllConditionsFromTree(x))
            case None =>
            case o =>
        }

        set.filter(e => e != FeatureExprFactory.True)
    }

    private def getUsedVariablesFromTree(obj: Any): Set[String] = {
        var set: Set[String] = Set.empty[String]

        obj match {
            case x: Id =>
                set += x.name
            case x: AST =>
                if (x.productArity > 0) {
                    for (y <- x.productIterator.toList) {
                        set = set.union(getUsedVariablesFromTree(y))
                    }
                }
            case x: Opt[_] =>
                set = set.union(getUsedVariablesFromTree(x.entry))
            case One(x) =>
                set = set.union(getUsedVariablesFromTree(x))
            case x: Choice[_] =>
                set = set.union(getUsedVariablesFromTree(x.thenBranch))
                set = set.union(getUsedVariablesFromTree(x.elseBranch))
            case x: List[_] =>
                for (elem <- x) {
                    set = set.union(getUsedVariablesFromTree(elem))
                }
            case Some(x) =>
                set = set.union(getUsedVariablesFromTree(x))
            case None =>
            case o =>
        }

        set
    }

    /**
      * Creates and returns a block name for the specified expression.
      */
    private def createBlockName(expr: FeatureExpr): String = {
        var id = 0

        if(featureCounter.contains(expr)) {
            id = featureCounter(expr)

            featureCounter -= expr
        }

        featureCounter += (expr -> (id + 1))

        contextToReadableString(expr) + "_" + id
    }

    private def contextToReadableString(context: FeatureExpr): String = {
        val regexPattern = "(defined|definedEx)\\(([a-zA-Z_0-9]+)\\)".r
        return regexPattern replaceAllIn(context.toTextExpr, "$2")
    }

    /**
      * Updates the current block mapping.
      */
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
                } else if (!currentExpr.and(key).isSatisfiable()) {
                    keysToRemove += key
                }
            }

            for (key <- keysToRemove) {
                currentBlockMapping -= key
            }

            // Create a new block if the current block was not looked at yet
            if (!currentBlockMapping.contains(currentExpr)) {
                val newBlock = createBlockName(currentExpr)
                currentBlockMapping += (currentExpr -> newBlock)
                blockToExpr += (newBlock -> currentExpr)
            }

            val currBlock = currentBlockMapping(currentExpr)
            statementToBlock.put(stmt, currBlock)

            // Update statementMapping
            statementMapping.put(stmt, currBlock)

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
        }
    }

    /**
      * Calculates the recursion set in which the specified function is contained. The specified function call is
      * the start call.
      */
    private def getRecSet(initFunction: String): Option[Set[String]] = {
        var visitedFunctions: Map[String, Boolean] = Map.empty[String, Boolean]
        var nextFunctions: Set[String] = Set.empty[String]

        nextFunctions += initFunction

        while (nextFunctions.nonEmpty) {
            var functionCalls: Set[String] = Set.empty[String]

            for (func <- nextFunctions) {
                if (globalFunctionCalls.contains(func)
                    && (!visitedFunctions.contains(func) || !visitedFunctions(func))) {
                    for (call <- globalFunctionCalls(func)) {
                        functionCalls += call.functionName
                    }
                }

                if (!visitedFunctions.contains(func)) {
                    visitedFunctions += (func -> false)
                } else if (!visitedFunctions(func)) {
                    visitedFunctions -= func
                    visitedFunctions += (func -> true)
                }
            }

            nextFunctions = functionCalls
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

        if (recSet.contains(initFunction)) {
            // Get the one recursion that contains the call parameter

            var functionSet: Set[String] = Set.empty[String]
            var nextFunctions: Set[String] = Set(initFunction)

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

    /**
      * Calculates the functions that are called in other functions.
      */
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

    /**
      * Calculates all recursions based on the global function calls.
      */
    protected def calculateRecursiveSets(): Set[Set[String]] = {
        var functionRecSets: Set[Set[String]] = Set.empty[Set[String]]

        calculateFunctionsCalledBy()

        println("     -- Calculating recursions")
        var i = 1

        for (func <- globalFunctionCalls.keySet) {
            println("         --- Attempting to calculate recursion: Evaluating calls of function  " + i.toString + " of " +  globalFunctionCalls.size)

            if (functionRecSets.forall(set => !set.contains(func))) {
                getRecSet(func) match {
                    case Some(x) =>
                        functionRecSets += x
                    case None =>
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

        functionRecSets
    }

    /**
      * Initial function of the granularity algorithm.
      *
      * Calculates the score of each block and filters the blocks which have a lower score than the specified threshold.
      * Returns an IdentityHashMap of statements which are going to be ignored.
      */
    def calculateGranularity(ast: TranslationUnit, fm: FeatureModel, outputDir: String, threshold: Double): IdentityHashMap[Any, Boolean]
}

trait IfdefToIfGranularityExecCode extends IfdefToIfGranularityInterface with IOUtilities {

    private var loopCounter: Int = 0
    private var loopScores: Map[Int, Double] = Map.empty[Int, Double]
    private var functionModifiers: Map[String, Double] = Map.empty[String, Double]
    private var functionDefs: Set[String] = Set.empty[String]
    private var functionScores: Map[String, Double] = Map.empty[String, Double]
    private var singleBlockScores: Map[String, Double] = Map.empty[String, Double]
    private var blockScores: Map[String, Double] = Map.empty[String, Double]
    private var scoreCauses: Map[String, Set[String]] = Map.empty[String, Set[String]]

    override def calculateGranularity(ast: TranslationUnit, fm: FeatureModel, outputDir: String, threshold: Double = 2.0): IdentityHashMap[Any, Boolean] = {
        val ignoredStatements: IdentityHashMap[Any, Boolean] = new IdentityHashMap[Any, Boolean]

        featureModel = fm
        dir = outputDir
        readConfigFile()
        readFunctionConfigFile()
        readFunctionOffsetFile()

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
        println(" - Filtering blocks")
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

        writeMapFile()

        ignoredStatements
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

            string = string + id + "," + k.substring(0, k.length - id.length - 1) + "," + v.toString + "," + causesString + "\n"
        }

        pw.write(string)
        pw.close()
    }

    // Global for current status of loops for loop score calculation and granularity
    private var loopExited: Map[Int, Boolean] = Map.empty[Int, Boolean]

    /**
      * Calculates the modifiers for the loops and functions. Breaks, continues and gotos within loops only influence
      * the modifier of the loops. If a goto is not inside a loop, it affects the modifier of the current function.
      */
    private def calculateLoopScores(obj: Any, currentLoopSet: Set[Int] = Set.empty[Int],
                                    currentLoop: Int = null.asInstanceOf[Int], currentFunction: String = null): Unit = {
        obj match {
            case x: ForStatement =>
                val counter: Int = loopCounter

                if (FOR_WEIGHT < 0) {
                    loopScores += (loopCounter -> LOOP_WEIGHT)
                } else {
                    loopScores += (loopCounter -> FOR_WEIGHT)
                }

                loopExited += (loopCounter -> false)

                loopCounter += 1

                if (x.productArity > 0) {
                    for (y <- x.productIterator.toList) {
                        if (!loopExited(counter)) {
                            calculateLoopScores(y, currentLoopSet + counter, counter, currentFunction)
                        }
                    }
                }
            case x: WhileStatement =>
                val counter: Int = loopCounter

                if (WHILE_WEIGHT < 0) {
                    loopScores += (loopCounter -> LOOP_WEIGHT)
                } else {
                    loopScores += (loopCounter -> WHILE_WEIGHT)
                }

                loopExited += (loopCounter -> false)

                loopCounter += 1

                if (x.productArity > 0) {
                    for (y <- x.productIterator.toList) {
                        if (!loopExited(counter)) {
                            calculateLoopScores(y, currentLoopSet + counter, counter, currentFunction)
                        }
                    }
                }
            case x: DoStatement =>
                val counter: Int = loopCounter

                if (DO_WEIGHT < 0) {
                    loopScores += (loopCounter -> LOOP_WEIGHT)
                } else {
                    loopScores += (loopCounter -> DO_WEIGHT)
                }

                loopExited += (loopCounter -> false)

                loopCounter += 1

                if (x.productArity > 0) {
                    for (y <- x.productIterator.toList) {
                        if (!loopExited(counter)) {
                            calculateLoopScores(y, currentLoopSet + counter, counter, currentFunction)
                        }
                    }
                }
            case x: BreakStatement =>
                if (currentLoop != null.asInstanceOf[Int]) {
                    var score = loopScores(currentLoop)

                    if (BREAK_WEIGHT < 0) {
                        score = score * CONTROL_FLOW_WEIGHT
                    } else {
                        score = score * BREAK_WEIGHT
                    }

                    loopScores -= currentLoop
                    loopExited -= currentLoop
                    loopScores += (currentLoop -> score)
                    loopExited += (currentLoop -> true)
                }
            case x: ContinueStatement =>
                if (currentLoop != null.asInstanceOf[Int]) {
                    var score = loopScores(currentLoop)

                    if (CONTINUE_WEIGHT < 0) {
                        score = score * CONTROL_FLOW_WEIGHT
                    } else {
                        score = score * CONTINUE_WEIGHT
                    }

                    loopScores -= currentLoop
                    loopExited -= currentLoop
                    loopScores += (currentLoop -> score)
                    loopExited += (currentLoop -> true)
                }
            case x: GotoStatement =>
                for (y <- currentLoopSet) {
                    var score = loopScores(currentLoop)

                    if (GOTO_WEIGHT < 0) {
                        score = score * CONTROL_FLOW_WEIGHT
                    } else {
                        score = score * GOTO_WEIGHT
                    }

                    loopScores -= y
                    loopExited -= y
                    loopScores += (y -> score)
                    loopExited += (y -> true)
                }

                // If there is currently no loop, add the modifier to the current function
                if (currentLoopSet.isEmpty && currentFunction != null) {
                    var value = 1.0

                    if (functionModifiers.contains(currentFunction)) {
                        value = functionModifiers(currentFunction)
                        functionModifiers -= currentFunction
                    }

                    functionModifiers += (currentFunction -> value*GOTO_WEIGHT)
                }
            case funcDef: FunctionDef =>
                if (funcDef.productArity > 0) {
                    for (y <- funcDef.productIterator.toList) {
                        calculateLoopScores(y, currentLoopSet, currentLoop, funcDef.getName)
                    }
                }
            case x: AST =>
                if (x.productArity > 0) {
                    for (y <- x.productIterator.toList) {
                        calculateLoopScores(y, currentLoopSet, currentLoop, currentFunction)
                    }
                }
            case x: Opt[_] =>
                calculateLoopScores(x.entry, currentLoopSet, currentLoop, currentFunction)
            case One(x) =>
                calculateLoopScores(x, currentLoopSet, currentLoop, currentFunction)
            case x: Choice[_] =>
                calculateLoopScores(x.thenBranch, currentLoopSet, currentLoop, currentFunction)
                calculateLoopScores(x.elseBranch, currentLoopSet, currentLoop, currentFunction)
            case x: List[_] =>
                for (elem <- x) {
                    calculateLoopScores(elem, currentLoopSet, currentLoop, currentFunction)
                }
            case Some(x) =>
                calculateLoopScores(x, currentLoopSet, currentLoop, currentFunction)
            case None =>
            case o =>
        }
    }

    /**
      * Calculates the general score of each block and function. Iterates through each AST element and increases the
      * score of the current statement and current function dependent on the current weight. The weight is adjusted
      * by special structures in the code like for-loops.
      */
    private def granularity(obj: Any, currentBlock: String = null, currentFunction: String = null,
                            weight: Double = 1.0, causes: Set[String] = Set.empty[String]): Unit = {
        var newCauses = causes

        obj match {
            case x: ForStatement =>
                val currentLoop: Int = loopCounter
                var block: String = currentBlock

                newCauses += "For-Loop"

                if (statementToBlock.containsKey(x)) {
                    block = statementToBlock.get(x)

                    if (!blockScores.contains(block)) {
                        blockScores += (block -> 0)
                    }
                }

                for (c <- newCauses) {
                    addScoreCause(block, c)
                }

                increaseScore(block, currentFunction, weight * loopScores(currentLoop))

                loopCounter += 1
                if (x.productArity > 0) {
                    for (y <- x.productIterator.toList) {
                        granularity(y, block, currentFunction, weight * loopScores(currentLoop), newCauses)
                    }
                }
            case x: WhileStatement =>
                val currentLoop: Int = loopCounter
                var block: String = currentBlock

                newCauses += "While-Loop"

                if (statementToBlock.containsKey(x)) {
                    block = statementToBlock.get(x)

                    if (!blockScores.contains(block)) {
                        blockScores += (block -> 0)
                    }
                }

                for (c <- newCauses) {
                    addScoreCause(block, c)
                }

                increaseScore(block, currentFunction, weight * loopScores(currentLoop))

                loopCounter += 1
                if (x.productArity > 0) {
                    for (y <- x.productIterator.toList) {
                        granularity(y, block, currentFunction, weight * loopScores(currentLoop), newCauses)
                    }
                }
            case x: DoStatement =>
                val currentLoop: Int = loopCounter
                var block: String = currentBlock

                newCauses += "Do-Loop"

                if (statementToBlock.containsKey(x)) {
                    block = statementToBlock.get(x)

                    if (!blockScores.contains(block)) {
                        blockScores += (block -> 0)
                    }
                }

                for (c <- newCauses) {
                    addScoreCause(block, c)
                }

                increaseScore(block, currentFunction, weight * loopScores(currentLoop))

                loopCounter += 1
                if (x.productArity > 0) {
                    for (y <- x.productIterator.toList) {
                        granularity(y, block, currentFunction, weight * loopScores(currentLoop), newCauses)
                    }
                }

            case x: AST =>

                var functionDef: String = currentFunction
                var block: String = currentBlock
                var adjustedWeight: Double = weight

                obj match {
                    case funcDef: FunctionDef =>
                        functionDef = funcDef.getName
                        functionDefs = functionDefs + functionDef
                    case PostfixExpr(p: Id, s: FunctionCall) =>
                        val funcName: String = p.name

                        if (currentBlock != null) {
                            if (currentBlock == "SQLITE_COVERAGE_TEST_60") {
                                println(currentFunction)
                            }

                            val tuple = new FuncCall(funcName, block, blockToExpr(block), weight)
                            if (globalFunctionCalls.contains(currentFunction)) {
                                val list = globalFunctionCalls(currentFunction)

                                globalFunctionCalls -= currentFunction
                                globalFunctionCalls += (currentFunction -> (list ::: List(tuple)))
                            } else {
                                globalFunctionCalls += (currentFunction -> List(tuple))
                            }
                        } else {
                            val tuple = new FuncCall(funcName, "True", FeatureExprFactory.True, weight)
                            if (globalFunctionCalls.contains(currentFunction)) {
                                val list = globalFunctionCalls(currentFunction)

                                globalFunctionCalls -= currentFunction
                                globalFunctionCalls += (currentFunction -> (list ::: List(tuple)))
                            } else {
                                globalFunctionCalls += (currentFunction -> List(tuple))
                            }
                        }
                    case s: Statement =>
                        if (statementToBlock.containsKey(s)) {
                            block = statementToBlock.get(s)

                            if (!blockScores.contains(block)) {
                                blockScores += (block -> 0)
                            }
                        }
                        obj match {
                            case _: EmptyStatement | _: BreakStatement | _: ContinueStatement | _: GotoStatement => // Filtering statements that should not be counted
                            case _ =>
                                for (c <- newCauses) {
                                    addScoreCause(block, c)
                                }

                                increaseScore(block, currentFunction, weight)
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
                        granularity(y, block, functionDef, adjustedWeight, newCauses)
                    }
                }
            case x: Opt[_] =>
                granularity(x.entry, currentBlock, currentFunction, weight, newCauses)
            case x: List[_] =>
                for (elem <- x) {
                    granularity(elem, currentBlock, currentFunction, weight, newCauses)
                }
            case Some(x) =>
                granularity(x, currentBlock, currentFunction, weight, newCauses)
            case x: One[_] =>
                granularity(x.value, currentBlock, currentFunction, weight, newCauses)
            case x: Choice[_] =>
                granularity(x.thenBranch, currentBlock, currentFunction, weight, newCauses)
                granularity(x.elseBranch, currentBlock, currentFunction, weight, newCauses)
            case None =>
            case o =>
        }
    }

    /**
      * Increases the score of the specified block and the specified function by the specified weight.
      */
    private def increaseScore(block: String, currentFunction: String, weight: Double): Unit = {
        if (currentFunction != null) {

            if (block != null) {
                // Update score of block
                if (blockScores.contains(block)) {
                    val w = blockScores(block)

                    blockScores -= block
                    blockScores += (block -> (w + weight))
                } else {
                    blockScores += (block -> weight)
                }
            } else {
                // Update score of functions (True only)
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

    /**
      * Temporarily calculates the scores of all nested blocks. The score of inner blocks is added to the score
      * of the outer blocks.
      */
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

    /**
      * Calculates the general function scores. The score of each block is added to the function score in which the
      * block is located.
      */
    private def calculateFunctionScores(): Unit = {
        for (func <- functionDefs) {
            var sum: Double = 0.0
            var modifier: Double = 1.0

            if (functionModifiers.contains(func)) {
                // Goto modifiers do not have the same impact on functions than on loops. Thus, we will double the modifier here.
                modifier = 2*functionModifiers(func)
            }

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

            functionScores += (func -> sum*modifier)
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

    var visitedCalledFunctions: Set[String] = Set.empty[String]
    var callCauses: Set[String] = Set.empty[String]

    /**
      * Cares about the function calls. For each function call we calculate a value consisting of all called functions.
      * Recursions get their own value and won't be entered a second time.
      */
    private def careFunctionCalls(): Unit = {
        var functionRecSetMapping: Map[String, Set[String]] = Map.empty[String, Set[String]]
        var recSetValue: Map[String, Double] = Map.empty[String, Double]

        val functionRecSets = calculateRecursiveSets()

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

        // Calculate the accumulated costs of a function call
        def getCallValue(call: FuncCall, cond: FeatureExpr, currentDepth: Int): Double = {
            if (predefinedFunctionScores.contains(call.functionName)) {
                var sum: Double = predefinedFunctionScores(call.functionName)

                if (functionCallOffsets.contains(call.functionName)) {
                    sum += functionCallOffsets(call.functionName)
                }

                return call.weight * sum
            }

            var sum: Double = 0.0

            if (visitedCalledFunctions.contains(call.functionName)) {
                return sum
            }

            if (recSetValue.contains(call.functionName) /*&& call.condition.and(cond).isSatisfiable(featureModel)*/ ) {
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

    /**
      * Finalizes the score calculation. Summarizes all influences of each block.
      */
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

    /**
      * Adds a cause to the block why the score of the specified block was created like it is.
      */
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

trait IfdefToIfGranularityBinScore extends IfdefToIfGranularityInterface with IOUtilities {

    var functionDefs: Set[String] = Set.empty[String]
    var recSets: Set[Set[String]] = Set.empty[Set[String]]

    var ifStatementsBlocks: Map[String, Set[Int]] = Map.empty[String, Set[Int]]
    var switchStatementsBlocks: Map[String, Set[Int]] = Map.empty[String, Set[Int]]
    var loopsBlocks: Map[String, Int] = Map.empty[String, Int]
    var funcCallsBlocks: Map[String, Set[FuncCall]] = Map.empty[String, Set[FuncCall]]
    var flowIrregulationsBlocks: Map[String, Int] = Map.empty[String, Int]

    var ifStatementsFunctions: Map[String, Set[Int]] = Map.empty[String, Set[Int]]
    var switchStatementsFunctions: Map[String, Set[Int]] = Map.empty[String, Set[Int]]
    var loopsFunctions: Map[String, Int] = Map.empty[String, Int]
    var funcCallsFunctions: Map[String, Set[FuncCall]] = Map.empty[String, Set[FuncCall]]
    var flowIrregulationsFunctions: Map[String, Int] = Map.empty[String, Int]

    var ifBinBlocks: Map[String, Int] = Map.empty[String, Int]
    var switchBinBlocks: Map[String, Int] = Map.empty[String, Int]
    var loopsBinBlocks: Map[String, Int] = Map.empty[String, Int]
    var callBinBlocks: Map[String, Int] = Map.empty[String, Int]
    var flowBinBlocks: Map[String, Int] = Map.empty[String, Int]

    var ifBinFunctions: Map[String, Int] = Map.empty[String, Int]
    var switchBinFunctions: Map[String, Int] = Map.empty[String, Int]
    var loopsBinFunctions: Map[String, Int] = Map.empty[String, Int]
    var callBinFunctions: Map[String, Int] = Map.empty[String, Int]
    var flowBinFunctions: Map[String, Int] = Map.empty[String, Int]

    var binScoreBlocks: Map[String, Int] = Map.empty[String, Int]
    var binScoreFunctions: Map[String, Int] = Map.empty[String, Int]

    override def calculateGranularity(ast: TranslationUnit, fm: FeatureModel, outputDir: String, threshold: Double = 2.0): IdentityHashMap[Any, Boolean] = {
        val ignoredStatements: IdentityHashMap[Any, Boolean] = new IdentityHashMap[Any, Boolean]
        dir = outputDir

        readConfigFile()
        println(" - Calculating block mapping")
        calculateBlockMapping(ast)
        println(" - Analyzing the code")
        granularity(ast)
        println(" - Calculating recursions")
        recSets = calculateRecursiveSets()
        println(" - Analyzing if statements")
        analyzeIfStatements()
        println(" - Analyzing switch statements")
        analyzeSwitchStatements()
        println(" - Analyzing loops")
        analyzeLoops()
        println(" - Analyzing control flow irregulations")
        analyzeControlFlowIrregulations()
        println(" - Analyzing function calls")
        analyzeFunctionCalls()
        println(" - Calculating the bin score for each block")
        calculateEachBlockBin()
        println(" - Filtering blocks")
        binScoreBlocks.foreach(block => {
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

        writeMapFile()

        ignoredStatements
    }

    private def writeMapFile(): Unit = {
        val pw = new PrintWriter(new File(dir + "map.csv"))
        var string = ""

        for ((k, v) <- binScoreBlocks) {
            var ifBin = 0
            var switchBin = 0
            var loopsBin = 0
            var callBin = 0
            var flowBin = 0

            if (ifBinBlocks.contains(k)) {
                ifBin = ifBinBlocks(k)
            }
            if (switchBinBlocks.contains(k)) {
                switchBin = switchBinBlocks(k)
            }
            if (loopsBinBlocks.contains(k)) {
                loopsBin = loopsBinBlocks(k)
            }
            if (callBinBlocks.contains(k)) {
                callBin = callBinBlocks(k)
            }
            if (flowBinBlocks.contains(k)) {
                flowBin = flowBinBlocks(k)
            }

            val id = k.split("_").last
            string = string + id + "," + k.substring(0, k.length - id.length - 1) + "," + v.toString + "," + ifBin.toString + "," + switchBin.toString + "," + loopsBin.toString + "," + callBin.toString + "," + flowBin.toString + "\n"
        }

        pw.write(string)
        pw.close()
    }

    private def granularity(obj: Any, currentBlock: String = null, currentFunction: String = null): Unit = {
        obj match {
            case x: IfStatement =>
                var block = currentBlock
                val ifBranches = x.elifs.size + 2

                if (statementToBlock.containsKey(x)) {
                    block = statementToBlock.get(x)

                    if (!binScoreBlocks.contains(block)) {
                        binScoreBlocks += (block -> 0)
                    }

                    if (ifStatementsBlocks.contains(block)) {
                        var set = ifStatementsBlocks(block)
                        set += ifBranches

                        ifStatementsBlocks -= block
                        ifStatementsBlocks += (block -> set)
                    } else {
                        ifStatementsBlocks += (block -> Set(ifBranches))
                    }
                } else {
                    if (ifStatementsFunctions.contains(currentFunction)) {
                        var set = ifStatementsFunctions(currentFunction)
                        set += ifBranches

                        ifStatementsFunctions -= currentFunction
                        ifStatementsFunctions += (currentFunction -> set)
                    } else {
                        ifStatementsFunctions += (currentFunction -> Set(ifBranches))
                    }
                }

                if (x.productArity > 0) {
                    for (y <- x.productIterator.toList) {
                        granularity(y, block, currentFunction)
                    }
                }
            case SwitchStatement(expr: Expr, One(CompoundStatement(list))) =>
                var block = currentBlock
                var amountCases = 0
                var insideCase: Boolean = false

                // Count amount of case statements and default statement
                for (elem <- list) {
                    elem.entry match {
                        case _: CaseStatement | _: DefaultStatement =>
                            if (!insideCase) {
                                amountCases += 1
                            }
                        case _: BreakStatement =>
                            insideCase = false
                        case _ =>
                    }
                }

                if (statementToBlock.containsKey(obj)) {
                    block = statementToBlock.get(obj)

                    if (!binScoreBlocks.contains(block)) {
                        binScoreBlocks += (block -> 0)
                    }

                    if (switchStatementsBlocks.contains(block)) {
                        var set = switchStatementsBlocks(block)
                        set += amountCases

                        switchStatementsBlocks -= block
                        switchStatementsBlocks += (block -> set)
                    } else {
                        switchStatementsBlocks += (block -> Set(amountCases))
                    }
                } else {
                    if (switchStatementsFunctions.contains(currentFunction)) {
                        var set = switchStatementsFunctions(currentFunction)
                        set += amountCases

                        switchStatementsFunctions -= currentFunction
                        switchStatementsFunctions += (currentFunction -> set)
                    } else {
                        switchStatementsFunctions += (currentFunction -> Set(amountCases))
                    }
                }

                granularity(expr, block, currentFunction)
                granularity(list, block, currentFunction)

            case x: ForStatement =>
                var block: String = currentBlock

                if (statementToBlock.containsKey(x)) {
                    block = statementToBlock.get(x)

                    if (!binScoreBlocks.contains(block)) {
                        binScoreBlocks += (block -> 0)
                    }

                    if (loopsBlocks.contains(block)) {
                        val count = loopsBlocks(block)

                        loopsBlocks -= block
                        loopsBlocks += (block -> (count+1))
                    } else {
                        loopsBlocks += (block -> 1)
                    }
                } else {
                    if (loopsFunctions.contains(currentFunction)) {
                        val count = loopsFunctions(currentFunction)

                        loopsFunctions -= currentFunction
                        loopsFunctions += (currentFunction -> (count+1))
                    } else {
                        loopsFunctions += (currentFunction -> 1)
                    }
                }

                if (x.productArity > 0) {
                    for (y <- x.productIterator.toList) {
                        granularity(y, block, currentFunction)
                    }
                }

            case x: WhileStatement =>
                var block: String = currentBlock

                if (statementToBlock.containsKey(x)) {
                    block = statementToBlock.get(x)

                    if (!binScoreBlocks.contains(block)) {
                        binScoreBlocks += (block -> 0)
                    }

                    if (loopsBlocks.contains(block)) {
                        val count = loopsBlocks(block)

                        loopsBlocks -= block
                        loopsBlocks += (block -> (count+1))
                    } else {
                        loopsBlocks += (block -> 1)
                    }
                } else {
                    if (loopsFunctions.contains(currentFunction)) {
                        val count = loopsFunctions(currentFunction)

                        loopsFunctions -= currentFunction
                        loopsFunctions += (currentFunction -> (count+1))
                    } else {
                        loopsFunctions += (currentFunction -> 1)
                    }
                }

                if (x.productArity > 0) {
                    for (y <- x.productIterator.toList) {
                        granularity(y, block, currentFunction)
                    }
                }

            case x: DoStatement =>
                var block: String = currentBlock

                if (statementToBlock.containsKey(x)) {
                    block = statementToBlock.get(x)

                    if (!binScoreBlocks.contains(block)) {
                        binScoreBlocks += (block -> 0)
                    }

                    if (loopsBlocks.contains(block)) {
                        val count = loopsBlocks(block)

                        loopsBlocks -= block
                        loopsBlocks += (block -> (count+1))
                    } else {
                        loopsBlocks += (block -> 1)
                    }
                } else {
                    if (loopsFunctions.contains(currentFunction)) {
                        val count = loopsFunctions(currentFunction)

                        loopsFunctions -= currentFunction
                        loopsFunctions += (currentFunction -> (count+1))
                    } else {
                        loopsFunctions += (currentFunction -> 1)
                    }
                }

                if (x.productArity > 0) {
                    for (y <- x.productIterator.toList) {
                        granularity(y, block, currentFunction)
                    }
                }

            case ContinueStatement | BreakStatement =>
                if (statementToBlock.containsKey(obj)) {
                    val block = statementToBlock.get(obj)

                    if (!binScoreBlocks.contains(block)) {
                        binScoreBlocks += (block -> 0)
                    }

                    if (flowIrregulationsBlocks.contains(block)) {
                        val count = flowIrregulationsBlocks(block)

                        flowIrregulationsBlocks -= block
                        flowIrregulationsBlocks += (block -> (count+1))
                    } else {
                        flowIrregulationsBlocks += (block -> 1)
                    }
                } else {
                    if (flowIrregulationsFunctions.contains(currentFunction)) {
                        val count = flowIrregulationsFunctions(currentFunction)

                        flowIrregulationsFunctions -= currentFunction
                        flowIrregulationsFunctions += (currentFunction -> (count+1))
                    } else {
                        flowIrregulationsFunctions += (currentFunction -> 1)
                    }
                }
            case x: GotoStatement =>
                var block: String = currentBlock

                if (statementToBlock.containsKey(x)) {
                    block = statementToBlock.get(x)

                    if (!binScoreBlocks.contains(block)) {
                        binScoreBlocks += (block -> 0)
                    }

                    if (flowIrregulationsBlocks.contains(block)) {
                        val count = flowIrregulationsBlocks(block)

                        flowIrregulationsBlocks -= block
                        flowIrregulationsBlocks += (block -> (count+1))
                    } else {
                        flowIrregulationsBlocks += (block -> 1)
                    }
                } else {
                    if (flowIrregulationsFunctions.contains(currentFunction)) {
                        val count = flowIrregulationsFunctions(currentFunction)

                        flowIrregulationsFunctions -= currentFunction
                        flowIrregulationsFunctions += (currentFunction -> (count+1))
                    } else {
                        flowIrregulationsFunctions += (currentFunction -> 1)
                    }
                }

                if (x.productArity > 0) {
                    for (y <- x.productIterator.toList) {
                        granularity(y, block, currentFunction)
                    }
                }

            case x: Statement =>
                var block = currentBlock

                if (statementToBlock.containsKey(x)) {
                    block = statementToBlock.get(x)

                    if (!binScoreBlocks.contains(block)) {
                        binScoreBlocks += (block -> 0)
                    }
                }

                if (x.productArity > 0) {
                    for (y <- x.productIterator.toList) {
                        granularity(y, block, currentFunction)
                    }
                }

            case x: AST =>
                var functionDef = currentFunction

                obj match {
                    case funcDef: FunctionDef => // Function definition
                        functionDef = funcDef.getName
                        functionDefs = functionDefs + functionDef
                    case PostfixExpr(p: Id, s: FunctionCall) => // Function call
                        val funcName: String = p.name

                        if (currentBlock != null) {
                            // Add function call to general map
                            val tuple = new FuncCall(funcName, currentBlock, blockToExpr(currentBlock), 1.0)
                            if (globalFunctionCalls.contains(currentFunction)) {
                                val list = globalFunctionCalls(currentFunction)

                                globalFunctionCalls -= currentFunction
                                globalFunctionCalls += (currentFunction -> (list ::: List(tuple)))
                            } else {
                                globalFunctionCalls += (currentFunction -> List(tuple))
                            }

                            // Update function calls in blocks
                            if (funcCallsBlocks.contains(currentBlock)) {
                                var set = funcCallsBlocks(currentBlock)
                                set += tuple

                                funcCallsBlocks -= currentBlock
                                funcCallsBlocks += (currentBlock -> set)
                            } else {
                                funcCallsBlocks += (currentBlock -> Set(tuple))
                            }
                        } else {
                            // Add function call to general map
                            val tuple = new FuncCall(funcName, "True", FeatureExprFactory.True, 1.0)
                            if (globalFunctionCalls.contains(currentFunction)) {
                                val list = globalFunctionCalls(currentFunction)

                                globalFunctionCalls -= currentFunction
                                globalFunctionCalls += (currentFunction -> (list ::: List(tuple)))
                            } else {
                                globalFunctionCalls += (currentFunction -> List(tuple))
                            }

                            // Update function calls in functions
                            if (funcCallsFunctions.contains(currentFunction)) {
                                var set = funcCallsFunctions(currentFunction)
                                set += tuple

                                funcCallsFunctions -= currentFunction
                                funcCallsFunctions += (currentFunction -> set)
                            } else {
                                funcCallsFunctions += (currentFunction -> Set(tuple))
                            }
                        }

                    case _ =>
                }

                if (x.productArity > 0) {
                    for (y <- x.productIterator.toList) {
                        granularity(y, currentBlock, functionDef)
                    }
                }
            case x: Opt[_] =>
                granularity(x.entry, currentBlock, currentFunction)
            case x: List[_] =>
                for (elem <- x) {
                    granularity(elem, currentBlock, currentFunction)
                }
            case Some(x) =>
                granularity(x, currentBlock, currentFunction)
            case x: One[_] =>
                granularity(x.value, currentBlock, currentFunction)
            case x: Choice[_] =>
                granularity(x.thenBranch, currentBlock, currentFunction)
                granularity(x.elseBranch, currentBlock, currentFunction)
            case None =>
            case o =>
        }
    }

    private def analyzeIfStatements(): Unit = {
        // Analyze blocks
        for (block <- blockToExpr.keySet) {
            var amountBranches: Double = 0.0

            if (ifStatementsBlocks.contains(block)) {
                for (v <- ifStatementsBlocks(block)) {
                    if (v <= 2) {
                        amountBranches += v/4
                    } else {
                        amountBranches += v/2
                    }
                }
            }

            if (blockCapsuling.contains(block)) {
                for (subBlock <- blockCapsuling(block).filter(b => ifStatementsBlocks.contains(b))) {
                    for (v <- ifStatementsBlocks(subBlock)) {
                        if (v <= 2) {
                            amountBranches += 0.5 * v/4
                        } else {
                            amountBranches += 0.5 * v/2
                        }
                    }
                }
            }


            var score = 11 - Math.pow(1.25, amountBranches)

            if (score < 1) {
                score = 1.0
            }

            ifBinBlocks += (block -> Math.round(score).toInt)
        }

        // Analyze functions
        for (func <- functionDefs) {
            var amountBranches: Double = 0.0

            if (ifStatementsFunctions.contains(func)) {
                for (v <- ifStatementsFunctions(func)) {
                    if (v <= 2) {
                        amountBranches += v/4
                    } else {
                        amountBranches += v/2
                    }
                }
            }

            if (functionBlocks.contains(func)) {
                for (subBlock <- functionBlocks(func).filter(b => ifStatementsBlocks.contains(b))) {
                    for (v <- ifStatementsBlocks(subBlock)) {
                        if (v <= 2) {
                            amountBranches += 0.5 * v/4
                        } else {
                            amountBranches += 0.5 * v/2
                        }
                    }
                }
            }

            var score = 11 - Math.pow(1.25, amountBranches)

            if (score < 1) {
                score = 1.0
            }

            ifBinFunctions += (func -> Math.round(score).toInt)
        }
    }

    private def analyzeSwitchStatements(): Unit = {
        // Analyze blocks
        for (block <- blockToExpr.keySet) {
            var amountCases: Double = 0.0

            if (switchStatementsBlocks.contains(block)) {
                for (v <- switchStatementsBlocks(block)) {
                    amountCases += v
                }
            }

            if (blockCapsuling.contains(block)) {
                for (subBlock <- blockCapsuling(block).filter(b => switchStatementsBlocks.contains(b))) {
                    for (v <- switchStatementsBlocks(subBlock)) {
                        amountCases += 0.5 * v
                    }
                }
            }

            var score = 11 - Math.pow(1.25, amountCases)

            if (score < 1) {
                score = 1.0
            }

            switchBinBlocks += (block -> Math.round(score).toInt)
        }

        // Analyze functions
        for (func <- functionDefs) {
            var amountCases: Double = 0.0

            if (switchStatementsFunctions.contains(func)) {
                for (v <- switchStatementsFunctions(func)) {
                    amountCases += v
                }
            }

            if (functionBlocks.contains(func)) {
                for (subBlock <- functionBlocks(func).filter(b => switchStatementsBlocks.contains(b))) {
                    for (v <- switchStatementsBlocks(subBlock)) {
                        amountCases += 0.5 * v
                    }
                }
            }

            var score = 11 - Math.pow(1.25, amountCases)

            if (score < 1) {
                score = 1.0
            }

            switchBinFunctions += (func -> Math.round(score).toInt)
        }
    }

    private def analyzeLoops(): Unit = {
        // Analyze blocks
        for (block <- blockToExpr.keySet) {
            var score: Double = 0.0

            if (loopsBlocks.contains(block)) {
                score += loopsBlocks(block)
            }

            if (blockCapsuling.contains(block)) {
                for (subBlock <- blockCapsuling(block).filter(b => loopsBlocks.contains(b))) {
                    score += 0.5*loopsBlocks(subBlock)
                }
            }

            score = Math.pow(1.2, score)

            if (score > 10) {
                score = 10.0
            }

            loopsBinBlocks += (block -> Math.round(score).toInt)
        }

        // Analyze functions
        for (func <- functionDefs) {
            var score: Double = 0.0

            if (loopsFunctions.contains(func)) {
                score += loopsFunctions(func)
            }

            if (functionBlocks.contains(func)) {
                for (subBlock <- functionBlocks(func).filter(b => loopsBlocks.contains(b))) {
                    score += 0.5*loopsBlocks(subBlock)
                }
            }

            score = Math.pow(1.25, score)

            if (score > 10) {
                score = 10.0
            }

            loopsBinFunctions += (func -> Math.round(score).toInt)
        }
    }

    private def analyzeControlFlowIrregulations(): Unit = {
        // Analyze blocks
        for (block <- blockToExpr.keySet) {
            var score: Double = 0.0

            if (flowIrregulationsBlocks.contains(block)) {
                score += flowIrregulationsBlocks(block)
            }

            if (blockCapsuling.contains(block)) {
                for (subBlock <- blockCapsuling(block).filter(b => flowIrregulationsBlocks.contains(b))) {
                    score += 0.5*flowIrregulationsBlocks(subBlock)
                }
            }

            score = 11 - Math.pow(1.15, score)

            if (score < 1) {
                score = 1.0
            }

            flowBinBlocks += (block -> Math.round(score).toInt)
        }

        // Analyze functions
        for (func <- functionDefs) {
            var score: Double = 0.0

            if (flowIrregulationsFunctions.contains(func)) {
                score += flowIrregulationsFunctions(func)
            }

            if (functionBlocks.contains(func)) {
                for (subBlock <- functionBlocks(func).filter(b => flowIrregulationsBlocks.contains(b))) {
                    score += 0.5*flowIrregulationsBlocks(subBlock)
                }
            }

            score = 11 - Math.pow(1.15, score)

            if (score < 1) {
                score = 1.0
            }

            flowIrregulationsFunctions += (func -> Math.round(score).toInt)
        }
    }

    private def analyzeFunctionCalls(): Unit = {
        val maxValue = 10*(IF_WEIGHT + SWITCH_WEIGHT + LOOP_WEIGHT + CONTROL_FLOW_WEIGHT + FUNCTION_CALL_WEIGHT)

        // Analyze single functions and calculate their bin score
        for (func <- functionDefs) {
            var sum: Double = 0

            if (ifBinFunctions.contains(func)) {
                sum += IF_WEIGHT * ifBinFunctions(func)
            }

            if (switchBinFunctions.contains(func)) {
                sum += SWITCH_WEIGHT * switchBinFunctions(func)
            }

            if (loopsBinFunctions.contains(func)) {
                sum += LOOP_WEIGHT * loopsBinFunctions(func)
            }

            if (flowBinFunctions.contains(func)) {
                sum += CONTROL_FLOW_WEIGHT * flowBinFunctions(func)
            }

            // Counting all called functions. Calls within blocks add 0.5 to the score.
            var callScore: Double = 0.0

            if (funcCallsFunctions.contains(func)) {
                callScore = funcCallsFunctions(func).size
            }

            if (functionBlocks.contains(func)) {
                for (block <- functionBlocks(func).filter(b => funcCallsBlocks.contains(b))) {
                    for (call <- funcCallsBlocks(block)) {
                        callScore += 0.5
                    }
                }
            }

            callScore = Math.pow(1.5, callScore)

            if (callScore > 10) {
                callScore = 10
            } else if (callScore < 1) {
                callScore = 1
            }

            if (binScoreFunctions.contains(func)) {
                binScoreFunctions -= func
            }
            binScoreFunctions += (func -> Math.round(((sum + FUNCTION_CALL_WEIGHT * callScore)/maxValue)*10).toInt)
        }

        // Analyze blocks and their functions calls
        for (block <- blockToExpr.keySet) {
            var score = 0.0

            // Get all called functions
            var calledFunctions: Set[String] = Set.empty[String]
            var nextFunctions: Set[String] = Set.empty[String]

            if (funcCallsBlocks.contains(block)) {
                nextFunctions = funcCallsBlocks(block).map(call => call.functionName)
            }

            while (nextFunctions.nonEmpty && score <= 10) {
                var functions: Set[String] = Set.empty[String]

                for (func <- nextFunctions.diff(calledFunctions)) {
                    calledFunctions += func

                    if (recSets.exists(rec => rec.contains(func))) {
                        val recSet: Set[String] = recSets.filter(r => r.contains(func)).head

                        calledFunctions = calledFunctions.union(recSet)

                        for (f <- recSet) {
                            score += 1.25*binScoreFunctions(func)
                            functions = functions.union(globalFunctionCalls(f).map(f => f.functionName).toSet.diff(recSet))
                        }
                    } else {
                        if (binScoreFunctions.contains(func)) {
                            score += binScoreFunctions(func)
                        } else {
                            score += 0.5
                        }

                        if (globalFunctionCalls.contains(func)) {
                            functions = functions.union(globalFunctionCalls(func).map(f => f.functionName).toSet)
                        }
                    }
                }

                nextFunctions = functions
            }

            if (score > 10) {
                score = 10.0
            } else if (score < 1) {
                score = 1.0
            }

            callBinBlocks += (block -> Math.round(score).toInt)
        }
    }

    private def calculateEachBlockBin(): Unit = {
        val maxValue = 10*(IF_WEIGHT + SWITCH_WEIGHT + LOOP_WEIGHT + CONTROL_FLOW_WEIGHT + FUNCTION_CALL_WEIGHT)

        for (block <- blockToExpr.keySet) {
            var sum: Double = 0

            if (ifBinBlocks.contains(block)) {
                sum += IF_WEIGHT * ifBinBlocks(block)
            }

            if (switchBinBlocks.contains(block)) {
                sum += SWITCH_WEIGHT * switchBinBlocks(block)
            }

            if (loopsBinBlocks.contains(block)) {
                sum += LOOP_WEIGHT * loopsBinBlocks(block)
            }

            if (flowBinBlocks.contains(block)) {
                sum += CONTROL_FLOW_WEIGHT * flowBinBlocks(block)
            }

            if (callBinBlocks.contains(block)) {
                sum += FUNCTION_CALL_WEIGHT * callBinBlocks(block)
            }

            if (binScoreBlocks.contains(block)) {
                binScoreBlocks -= block
            }

            // Calculate the final bin score depending on the factors
            binScoreBlocks += (block -> ((sum/maxValue)*10).toInt)
        }
    }
}

trait IfdefToIfGranularityPerformanceFiltering extends IfdefToIfGranularityInterface with IOUtilities {

    private var blockPerformances: Map[String, Double] = Map.empty[String, Double]

    override def calculateGranularity(ast: TranslationUnit, fm: FeatureModel, outputDir: String, threshold: Double = 2.0): IdentityHashMap[Any, Boolean] = {
        val ignoredStatements: IdentityHashMap[Any, Boolean] = new IdentityHashMap[Any, Boolean]

        readPerformanceFile()

        println(" - Calculating block mapping")
        calculateBlockMapping(ast)
        println(" - Filtering blocks")
        for ((block, performance) <- blockPerformances) {
            if (blockToStatements.contains(block) && performance < threshold) {
                val statements = blockToStatements(block)

                statements.keySet().toArray.foreach({
                    case i@IfStatement(_, One(CompoundStatement(list)), _, _) =>
                        ignoredStatements.put(i, performance < threshold)

                        if (list.size == 1) {
                            ignoredStatements.put(list.head.entry, performance < threshold)
                        }
                    case s: Statement =>
                        ignoredStatements.put(s, performance < threshold)
                })
            }
        }

        ignoredStatements
    }

    private def readPerformanceFile(): Unit = {
        if (Files.exists(Paths.get("./block_performances.txt"))) {
            for (c <- Source.fromFile("block_performances.txt").getLines()) {
                val configParts = c.split(",")

                if (configParts.size == 2) {
                    blockPerformances += (configParts(0) -> configParts(1).toDouble)
                }
            }
        }

    }
}

abstract class IfdefToIfGranularity extends IfdefToIfGranularityInterface {

}
