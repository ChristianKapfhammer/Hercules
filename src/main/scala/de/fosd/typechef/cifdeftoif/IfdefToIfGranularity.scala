package de.fosd.typechef.cifdeftoif

import java.util
import java.util.IdentityHashMap

import de.fosd.typechef.conditional.{Choice, One, Opt}
import de.fosd.typechef.featureexpr._
import de.fosd.typechef.parser.c._

trait IfdefToIfGranularityInterface {

    protected var featureModel: FeatureModel = _

    def calculateGranularity(ast: TranslationUnit, fm: FeatureModel, threshold: Int): Map[FeatureExpr, List[Int]]
}

trait IfdefToIfGranularityExecCode extends IfdefToIfGranularityInterface with IOUtilities {

    class FuncCall(var functionName: String, var condition: FeatureExpr, var weight: Int) {}

    private val DEFAULT_FUNCTION_WEIGHT = 5

    private val FOR_WEIGHT = 1
    private val WHILE_WEIGHT = 1
    private val DO_WEIGHT = 1
    private val RECURSIVE_WEIGHT = 1

    private var functionDefs: Set[String] = Set.empty[String]
    private var functionLoC: Map[String, Int] = Map.empty[String, Int]
    private var functionBlocks: Map[String, Set[String]] = Map.empty[String, Set[String]]
    // in which function is the call? -> (what function is called?, which condition?, which weight?)
    private var globalFunctionCalls: Map[String, List[FuncCall]] = Map.empty[String, List[FuncCall]]
    private val exprToBlock: IdentityHashMap[FeatureExpr, String] = new IdentityHashMap[FeatureExpr, String]()
    private var blockToExprs: Map[String, IdentityHashMap[FeatureExpr, FeatureExpr]] = Map.empty[String, IdentityHashMap[FeatureExpr, FeatureExpr]]
    private var blockCapsuling: Map[String, Set[String]] = Map.empty[String, Set[String]]
    private var blockLoC: Map[String, Int] = Map.empty[String, Int]
    private var blockNumbering: Map[String, List[Int]] = Map.empty[String, List[Int]]
    private var featureCounter: Map[FeatureExpr, Int] = Map.empty[FeatureExpr, Int]

    override def calculateGranularity(ast: TranslationUnit, fm: FeatureModel, threshold: Int = 2): Map[FeatureExpr, List[Int]] = {
        var ignoredBlocks: Map[FeatureExpr, List[Int]] = Map.empty[FeatureExpr, List[Int]]

        featureModel = fm

        // Order is important, blockMapping -> generalGranularity -> blocks -> functions -> function calls
        calculateBlockMapping(ast)
        granularity(ast)
        calculateBlockLoCs()
        calculateFunctionLoCs()
        careFunctionCalls()

        blockLoC.foreach(block => {
            if (block._2 < threshold) {
                val ft = blockToExprs(block._1).keySet().toArray()(0).asInstanceOf[FeatureExpr]

                if (ignoredBlocks.contains(ft)) {
                    val list = ignoredBlocks(ft)
                    ignoredBlocks -= ft
                    ignoredBlocks += (ft -> (list ::: blockNumbering(block._1)))
                } else {
                    ignoredBlocks += (ft  -> blockNumbering(block._1))
                }
            }
        })

        ignoredBlocks
    }

    // Global for block mapping calculation
    var currentBlockMapping: Map[FeatureExpr, String] = Map.empty[FeatureExpr, String]

    private def calculateBlockMapping(obj: Any, currentBlocks: Set[FeatureExpr] = Set.empty[FeatureExpr], currentFunction: String = null): Unit = {
        obj match {
            case x: AST =>

                var function = currentFunction

                obj match {
                    case funcDef: FunctionDef =>
                        function = funcDef.getName
                    case o =>
                }

                if (x.productArity > 0) {
                    for (y <- x.productIterator.toList) {
                        calculateBlockMapping(y, currentBlocks, function)
                    }
                }
            case x: Opt[_] =>
                if (currentFunction != null) {
                    updateBlockMapping(x.condition)

                    if (x.condition != FeatureExprFactory.True) {
                        val block = currentBlockMapping(x.condition)

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

                        calculateBlockMapping(x.entry, currentBlocks + x.condition, currentFunction)
                    } else {
                        calculateBlockMapping(x.entry, currentBlocks, currentFunction)
                    }
                }
            case One(x) =>
                calculateBlockMapping(x, currentBlocks, currentFunction)
            case x: Choice[_] =>
                updateBlockMapping(x.condition)
                calculateBlockMapping(x.thenBranch, currentBlocks + x.condition, currentFunction)

                updateBlockMapping(x.condition.not())
                calculateBlockMapping(x.elseBranch, currentBlocks + x.condition.not(), currentFunction)
            case x: List[_] =>
                for (elem <- x) {
                    calculateBlockMapping(elem, currentBlocks, currentFunction)
                }
            case Some(x) =>
                calculateBlockMapping(x, currentBlocks, currentFunction)
            case None =>
            case o =>
        }
    }

    private def createBlockName(expr: FeatureExpr): String = {
        val blockName = expr.toString() + "_"
        var id = 0

        while(blockToExprs.contains(blockName + id)) {
            id += 1
        }

        blockName + id
    }

    private def updateBlockMapping(currentExpr: FeatureExpr): Unit = {
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
                currentBlockMapping += (currentExpr -> createBlockName(currentExpr))
            }

            val currBlock = currentBlockMapping(currentExpr)

            exprToBlock.put(currentExpr, currBlock)

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

            // Update block numbering and feature counter
            if (keysToRemove.nonEmpty || !blockToExprs.contains(currBlock)) {
                var ftCounter = 0

                if (featureCounter.contains(currentExpr)) {
                    ftCounter = featureCounter(currentExpr)

                    featureCounter -= currentExpr
                }

                featureCounter += (currentExpr -> (ftCounter + 1))

                if (blockNumbering.contains(currBlock)) {
                    val list = blockNumbering(currBlock)

                    blockNumbering -= currBlock
                    blockNumbering += (currBlock -> (list ::: List(ftCounter)))
                } else {
                    blockNumbering += (currBlock -> List(ftCounter))
                }
            }

            // Update block mapping
            if (blockToExprs.contains(currBlock)) {
                val map = blockToExprs(currBlock)
                map.put(currentExpr, null)

                blockToExprs -= currBlock
                blockToExprs += (currBlock -> map)
            } else {
                val map = new IdentityHashMap[FeatureExpr, FeatureExpr]()
                map.put(currentExpr, null)

                blockToExprs += (currBlock -> map)
            }
        }
    }

    private def granularity(obj: Any, currentBlocks: Set[FeatureExpr] = Set.empty[FeatureExpr], currentFunction: String = null, weight: Int = 1): Unit = {
        obj match {
            case x: ForStatement =>
                if (x.productArity > 0) {
                    for (y <- x.productIterator.toList) {
                        granularity(y, currentBlocks, currentFunction, FOR_WEIGHT)
                    }
                }
            case x: WhileStatement =>
                if (x.productArity > 0) {
                    for (y <- x.productIterator.toList) {
                        granularity(y, currentBlocks, currentFunction, WHILE_WEIGHT)
                    }
                }
            case x: DoStatement =>
                if (x.productArity > 0) {
                    for (y <- x.productIterator.toList) {
                        granularity(y, currentBlocks, currentFunction, DO_WEIGHT)
                    }
                }

            case x: AST =>

                var functionDef = currentFunction

                obj match {
                    case funcDef: FunctionDef =>
                        functionDef = funcDef.getName
                        functionDefs = functionDefs + functionDef
                    case funcCall: PostfixExpr =>
                        (funcCall.p, funcCall.s) match {
                            case t: (Id, FunctionCall) =>
                                for (block <- currentBlocks.filter(p => p != FeatureExprFactory.True)) {
                                    val tuple = new FuncCall(t._1.name, block, weight)
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
                    case _: Declaration | _: FunctionCall | _: ArrayAccess | _: SizeOfExprT | _: SizeOfExprU
                         | _: CastExpr | _: PointerDerefExpr | _: PointerCreationExpr | _: UnaryOpExpr | _: NAryExpr
                         | _: ConditionalExpr | _: AssignExpr | _: ExprStatement | _: GotoStatement
                         | _: ContinueStatement | _: BreakStatement | _: ReturnStatement =>
                        increaseCounters(currentBlocks, currentFunction, weight)
                    case _ =>
                }

                if (x.productArity > 0) {
                    for (y <- x.productIterator.toList) {
                        granularity(y, currentBlocks, functionDef, weight)
                    }
                }
            case x: Opt[_] =>
                granularity(x.entry, currentBlocks + x.condition, currentFunction, weight)
            case x: List[_] =>
                for (elem <- x) {
                    granularity(elem, currentBlocks, currentFunction, weight)
                }
            case Some(x) =>
                granularity(x, currentBlocks, currentFunction, weight)
            case x: One[_] =>
                granularity(x.value, currentBlocks, currentFunction, weight)
            case x: Choice[_] =>
                granularity(x.thenBranch, currentBlocks + x.condition, currentFunction, weight)
                granularity(x.elseBranch, currentBlocks + x.condition.not(), currentFunction, weight)
            case None =>
            case o =>
        }
    }

    private def increaseCounters(currentBlocks: Set[FeatureExpr], currentFunction: String, weight: Int): Unit = {
        // Update loc of blocks
        for (key <- currentBlocks) {
            if (key != FeatureExprFactory.True && currentFunction != null) {
                val block = exprToBlock.get(key)

                if (blockLoC.contains(block)) {
                    val w = blockLoC(block)

                    blockLoC -= block
                    blockLoC += (block -> (w + weight))
                } else {
                    blockLoC += (block -> weight)
                }
            }
        }

        // Update loc of functions (True only)
        if (currentFunction != null) {
            if (currentBlocks.size == 1 && currentBlocks.head == FeatureExprFactory.True) {
                if (functionLoC.contains(currentFunction)) {
                    val loc = functionLoC(currentFunction)

                    functionLoC -= currentFunction
                    functionLoC += (currentFunction -> (loc + weight))
                } else {
                    functionLoC = functionLoC + (currentFunction -> weight)
                }
            }
        }
    }

    private def calculateBlockLoCs(): Unit = {
        var blockLoCChange: Map[String, Int] = Map.empty[String, Int]

        blockLoC.foreach(block => {
            var sum = blockLoC(block._1)
            var count = 1

            if (blockCapsuling.contains(block._1)) {
                for (subBlock <- blockCapsuling(block._1)) {
                    sum += blockLoC(subBlock)
                    count += 1
                }
            }

            blockLoCChange += (block._1 -> sum/count)
        })

        blockLoC = blockLoCChange
    }

    private def calculateFunctionLoCs(): Unit = {
        for (func <- functionDefs) {
            var sum = 0
            var count = 1 // Starting at 1 because of the function's default loc

            if (functionLoC.contains(func)) {
                sum += functionLoC(func)
            }

            if (functionBlocks.contains(func)) {
                for (block <- functionBlocks(func)) {
                    sum += blockLoC(block)
                    count += 1
                }
            }

            if (functionLoC.contains(func)) {
                functionLoC -= func
            }

            functionLoC += (func -> (sum/count))
        }

        // Setting weights for functions which are not defined in this AST
        for (calls <- globalFunctionCalls.values) {
            for (c <- calls) {
                if (!functionLoC.contains(c.functionName)) {
                    functionLoC += (c.functionName -> DEFAULT_FUNCTION_WEIGHT)
                }
            }
        }
    }

    private def getRecSet(call: FuncCall): Option[(Set[String], FeatureExpr)] = {
        var visitedFunctions: Map[String, Boolean] = Map.empty[String, Boolean]
        var nextFunctionCalls: Set[FuncCall] = Set.empty[FuncCall]
        var recCondition = FeatureExprFactory.True

        nextFunctionCalls += call

        while (nextFunctionCalls.nonEmpty) {
            var functionCalls: Set[FuncCall] = Set.empty[FuncCall]

            for (func <- nextFunctionCalls) {
                if (recCondition.and(func.condition).isSatisfiable(featureModel)) {
                    recCondition = recCondition.and(func.condition)

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

        val recSet = visitedFunctions.filter(p => p._2).keySet

        if (recSet.isEmpty) {
            None
        } else {
            Some((recSet, recCondition))
        }
    }

    private def careFunctionCalls(): Unit = {

        var functionRecSets: Set[Set[String]] = Set.empty[Set[String]]

        for ((funcLocation, funcCalls) <- globalFunctionCalls) {
            for (call <- funcCalls) {
                getRecSet(call) match {
                    case Some(x) =>
                        functionRecSets += x._1
                    case None =>
                }
            }
        }

        // Calculate the general value for each function in a recursion set
        var recValues: Map[String, List[Int]] = Map.empty[String, List[Int]]

        for (recSet <- functionRecSets) {
            var value: Int = 0

            for (func <- recSet) {
                value += functionLoC(func)
            }

            for (func <- recSet) {
                if (recValues.contains(func)) {
                    val list = recValues(func)

                    recValues -= func
                    recValues += (func -> (list ::: List(value)))
                } else {
                    recValues += (func -> List(value))
                }
            }
        }

        var recSetValue: Map[String, Int] = Map.empty[String, Int]

        for (entry <- recValues) {
            var value: Int = 0

            for (v <- entry._2) {
                value += v
            }

            recSetValue += (entry._1 -> (value/entry._2.length))
        }

        // Calculate the accumulated costs of a function call
        def getCallValue(call: FuncCall, cond: FeatureExpr): Int = {
            if (recSetValue.contains(call.functionName)) {
                RECURSIVE_WEIGHT * recSetValue(call.functionName)
            } else {
                if (call.condition.and(cond).isSatisfiable(featureModel)) {
                    var sum = functionLoC(call.functionName)

                    if (globalFunctionCalls.contains(call.functionName)) {
                        for (furtherCall <- globalFunctionCalls(call.functionName)) {
                            sum += getCallValue(furtherCall, cond.and(call.condition))
                        }
                    }

                    sum
                } else {
                    0
                }
            }
        }

        // Add function call costs to the corresponding blocks
        for (value <- globalFunctionCalls.values) {
            for (call <- value) {
                if (call.condition != FeatureExprFactory.True) {
                    val block = exprToBlock.get(call.condition)

                    if (blockLoC.contains(block)) {
                        val w = blockLoC(block)

                        blockLoC -= block
                        blockLoC += (block -> (w + getCallValue(call, FeatureExprFactory.True)))
                    } else {
                        blockLoC += (block -> getCallValue(call, FeatureExprFactory.True))
                    }
                }
            }
        }
    }

}

class IfdefToIfGranularity extends IfdefToIfGranularityInterface with IfdefToIfGranularityExecCode {

}