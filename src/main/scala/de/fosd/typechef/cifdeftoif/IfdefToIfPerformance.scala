package de.fosd.typechef.cifdeftoif

import java.util
import java.util.IdentityHashMap

import de.fosd.typechef.conditional.{Choice, Conditional, One, Opt}
import de.fosd.typechef.featureexpr.{FeatureExpr, FeatureExprFactory}
import de.fosd.typechef.parser.c._
import org.apache.logging.log4j.LogManager
import org.kiama.rewriting.Rewriter._

import scala.collection.JavaConversions._

trait IfdefToIfPerformanceInterface {

    def insertPerfFunctCalls(cmpstmt: CompoundStatement, context: FeatureExpr): CompoundStatement = {
        cmpstmt
    }

    def insertPerfMainFunctCalls(cmpstmt: CompoundStatement): CompoundStatement = {
        cmpstmt
    }

    def removePerformanceBeforeFunction(stmts: List[Opt[Statement]]): List[Opt[Statement]] = {
        stmts
    }

    def removePerformanceAfterFunction(stmts: List[Opt[Statement]]): (List[Opt[Statement]], Int) = {
        (stmts, 0)
    }

    def combinePerformancePair(firstStmts: CompoundStatement, secondStmts: CompoundStatement): CompoundStatement = {
        CompoundStatement(firstStmts.innerStatements ++ secondStmts.innerStatements)
    }

    def printPerformanceCounter(path: String) = {
        // Nothing
    }

    def insertPerformanceCounter(suffix: PostfixSuffix): PostfixSuffix = {
        suffix
    }

    def insertPerformanceCounter(cmpStmt: CompoundStatement): CompoundStatement = {
        cmpStmt
    }

    def updatePerformancePrependString(prependString: String, createIncludeDirective: (String) => String, path: String, fileName: String): String = {
        ""
    }

    def fixBreakAndContinues[T <: Product](t: T, ifdefDepth: Int = 0, forDoWhileDepth: Int = 0, switchIfdefDepth: Int = 0, lastStmtWasSwitch: Boolean = false): T = {
        t
    }

    def correctPerformanceFeaturePrefix(newPrefix: String) = {
        // Nothing
    }

    def setIgnoredStatements(statements: IdentityHashMap[Any, Boolean]) = {
        // Nothing
    }

    def setStatementMapping(statements: IdentityHashMap[Any, String]) = {
        // Nothing
    }

    def updateIgnoredStatements(old: Any, updated: Any) = {
        // Nothing
    }
}

trait IfdefToIfPerformance extends IfdefToIfPerformanceInterface with IOUtilities {
    private lazy val logger2 = LogManager.getLogger(this.getClass.getName)
    val trueF3 = FeatureExprFactory.True
    val functionBeforeName = "id2iperf_time_before"
    val functionBeforeCounterName = "id2iperf_time_before_counter"
    val functionAfterName = "id2iperf_time_after"
    val functionStartName = "id2iperf_time_start"
    val functionEndName = "id2iperf_time_end"
    val returnMacroName = "id2iperf_return"
    private val featureStructInitializedName2 = "id2i"
    private val performanceIncludeFileName = "perf_measuring.c"
    private val noIncludeFileName = "noincludes.c"
    private val includeFileName = "includes.c"
    private val performanceCmpStmtContextMap: java.util.LinkedHashMap[CompoundStatement, String] = new java.util.LinkedHashMap()
    private val returnMacro = "#define id2iperf_return(expr, stmts) __typeof__(expr) ____RetTmp = expr; stmts; return ____RetTmp;\n"
    private var featurePrefix2 = "f_"
    private var performanceCounter = 0
    private var insertPerformanceCounter = true
    private var ignoredStatements: IdentityHashMap[Any, Boolean] = new IdentityHashMap[Any, Boolean]()
    private var statementMapping: IdentityHashMap[Any, String] = new IdentityHashMap[Any, String]()

    override def setIgnoredStatements(statements: IdentityHashMap[Any, Boolean]): Unit = {
        ignoredStatements = statements
    }

    override def setStatementMapping(statements: IdentityHashMap[Any, String]): Unit = {
        statementMapping = statements
    }

    override def updateIgnoredStatements(old: Any, updated: Any): Unit = {
        (old, updated) match {
            case o@(One(o1), One(o2)) =>
                updateIgnoredStatements(o1, o2)
            case c@(CompoundStatement(c1), CompoundStatement(c2)) =>
                updateIgnoredStatements(c1, c2)
            case o@(Opt(_, o1), Opt(_, o2)) =>
                updateIgnoredStatements(o1, o2)
            case s@(Some(s1), Some(s2)) =>
                updateIgnoredStatements(s1, s2)
            case _ =>
        }

        old match {
            case x: AST =>
                updated match {
                    case y: AST =>
                        if (x.productArity > 0 && y.productArity > 0
                            && x.productIterator.toList.size == y.productIterator.toList.size) {
                            val l1 = x.productIterator.toList
                            val l2 = y.productIterator.toList
                            for (i <- x.productIterator.toList.indices) {
                                updateIgnoredStatements(l1.get(i), l2.get(i))
                            }
                        }
                    case _ =>
                }
            case x: List[_] =>
                updated match {
                    case y: List[_] =>
                        if (x.size == y.size) {
                            for (i <- x.indices) {
                                updateIgnoredStatements(x.get(i), y.get(i))
                            }
                        }
                    case _ =>
                }
            case _ =>
        }

        if (statementMapping.containsKey(old) && !statementMapping.containsKey(updated)) {
            statementMapping.put(updated, statementMapping.get(old))
        }

        if (ignoredStatements.containsKey(old) && !ignoredStatements.containsKey(updated)) {
            //ignoredStatements.remove(old)
            ignoredStatements.put(updated, false)
        }
    }

    private def isStatementLegal(s: Statement): Boolean = {
        !ignoredStatements.containsKey(s)
        /*val stmtMap = getASTElements(s, new IdentityHashMap[Any, Any]())

        ignoredStatements.keySet().toArray.foreach(stmt => {
            val ignoredMap = getASTElements(stmt, new IdentityHashMap[Any, Any]())

            stmtMap.keySet().toArray.foreach(prt => {
                if (ignoredMap.containsKey(prt)) {
                    return false
                }
            })
        })

        true*/

        /*s match {
            case ExprStatement(AssignExpr(p: PostfixExpr, _, _)) =>
                !ignoredStatements.containsKey(p) || !ignoredStatements.get(p)
            case ExprStatement(AssignExpr(_, _, p: PostfixExpr)) =>
                !ignoredStatements.containsKey(p) || !ignoredStatements.get(p)
            case ExprStatement(CastExpr(_, e)) =>
                !ignoredStatements.containsKey(e) || !ignoredStatements.get(e)
            case _ =>
                !ignoredStatements.containsKey(s) || !ignoredStatements.get(s)
        }*/
    }

    override def correctPerformanceFeaturePrefix(newPrefix: String): Unit = {
        featurePrefix2 = newPrefix
    }

    override def fixBreakAndContinues[T <: Product](t: T, ifdefDepth: Int = 0, forDoWhileIfdefDepth: Int = 0, switchIfdefDepth: Int = 0, lastStmtWasSwitch: Boolean = false): T = {
        val transformation = alltd(rule[Product] {
            case Opt(ft, i@IfStatement(cond, _, _, _)) =>
                if (isIfdeftoifCondition2(cond)) {
                    Opt(ft, fixBreakAndContinues(i, ifdefDepth + 1, forDoWhileIfdefDepth, switchIfdefDepth, lastStmtWasSwitch))
                } else {
                    Opt(ft, fixBreakAndContinues(i, ifdefDepth, forDoWhileIfdefDepth, switchIfdefDepth, lastStmtWasSwitch))
                }
            case Opt(ft, i@ElifStatement(cond, _)) =>
                if (isIfdeftoifCondition2(cond)) {
                    Opt(ft, fixBreakAndContinues(i, ifdefDepth + 1, forDoWhileIfdefDepth, switchIfdefDepth, lastStmtWasSwitch))
                } else {
                    Opt(ft, fixBreakAndContinues(i, ifdefDepth, forDoWhileIfdefDepth, switchIfdefDepth, lastStmtWasSwitch))
                }
            case Opt(ft, s: ForStatement) =>
                Opt(ft, fixBreakAndContinues(s, ifdefDepth, ifdefDepth, switchIfdefDepth, false))
            case Opt(ft, s: DoStatement) =>
                Opt(ft, fixBreakAndContinues(s, ifdefDepth, ifdefDepth, switchIfdefDepth, false))
            case Opt(ft, s: WhileStatement) =>
                Opt(ft, fixBreakAndContinues(s, ifdefDepth, ifdefDepth, switchIfdefDepth, false))
            case Opt(ft, s: SwitchStatement) =>
                Opt(ft, fixBreakAndContinues(s, ifdefDepth, forDoWhileIfdefDepth, ifdefDepth, true))
            case Opt(ft, f: FunctionDef) =>
                Opt(ft, fixBreakAndContinues(fixLabelAndGotos(f), ifdefDepth, forDoWhileIfdefDepth, ifdefDepth, lastStmtWasSwitch))
            case CompoundStatement(innerStmts) =>
                CompoundStatement(innerStmts.flatMap {
                    case o@Opt(ft, ReturnStatement(None)) if ifdefDepth > 0 =>
                        if (isStatementLegal(o.entry)) {
                            var result: List[Opt[Statement]] = List()
                            val afterStmt = Opt(trueF3, ExprStatement(PostfixExpr(Id(functionAfterName), FunctionCall(ExprList(List(Opt(trueF3, Constant("0"))))))))
                            for (counter <- 0 until ifdefDepth) {
                                result = afterStmt :: result
                            }
                            result ++ List(Opt(ft, ReturnStatement(None)))
                        } else {
                            List(o)
                        }
                    case o@Opt(ft, ReturnStatement(Some(expr))) if ifdefDepth > 0 =>
                        if (isStatementLegal(o.entry)) {
                            var result: List[Opt[Statement]] = List()
                            val afterStmt = Opt(trueF3, ExprStatement(PostfixExpr(Id(functionAfterName), FunctionCall(ExprList(List(Opt(trueF3, Constant("0"))))))))
                            val returnMacroCall = Opt(ft, ExprStatement(PostfixExpr(Id(returnMacroName), FunctionCall(ExprList(List(Opt(trueF3, expr), Opt(trueF3, Id(functionAfterName + "(" + "0" + ")"))))))))
                            for (counter <- 1 until ifdefDepth) {
                                result = afterStmt :: result
                            }
                            result ++ List(returnMacroCall)
                        } else {
                            List(o)
                        }
                    case o@Opt(ft, ExprStatement(PostfixExpr(Id(name), _))) if name.equals(returnMacroName) && ifdefDepth > 0 =>
                        if (isStatementLegal(o.entry)) {
                            var result: List[Opt[Statement]] = List()
                            val afterStmt = Opt(trueF3, ExprStatement(PostfixExpr(Id(functionAfterName), FunctionCall(ExprList(List(Opt(trueF3, Constant("0"))))))))
                            for (counter <- 1 until ifdefDepth - forDoWhileIfdefDepth) {
                                result = afterStmt :: result
                            }
                            result ++ List(o)
                        } else {
                            List(o)
                        }
                    case Opt(ft, cs: ContinueStatement) if ifdefDepth > 0 =>
                        if (isStatementLegal(cs)) {
                            var result: List[Opt[Statement]] = List()
                            val afterStmt = Opt(trueF3, ExprStatement(PostfixExpr(Id(functionAfterName), FunctionCall(ExprList(List(Opt(trueF3, Constant("0"))))))))
                            for (counter <- 0 until ifdefDepth - forDoWhileIfdefDepth) {
                                result = afterStmt :: result
                            }
                            result ++ List(Opt(ft, ContinueStatement()))
                        } else {
                            List(Opt(ft, ContinueStatement()))
                        }

                    case Opt(ft, bt: BreakStatement) if ifdefDepth > 0 =>
                        if (isStatementLegal(bt)) {
                            var result: List[Opt[Statement]] = List()
                            val afterStmt = Opt(trueF3, ExprStatement(PostfixExpr(Id(functionAfterName), FunctionCall(ExprList(List(Opt(trueF3, Constant("0"))))))))
                            var limit = 0
                            if (lastStmtWasSwitch) {
                                limit = switchIfdefDepth
                            } else {
                                limit = forDoWhileIfdefDepth
                            }
                            for (counter <- 0 until ifdefDepth - limit) {
                                result = afterStmt :: result
                            }
                            result ++ List(Opt(ft, BreakStatement()))
                        } else {
                            List(Opt(ft, BreakStatement()))
                        }
                    case k =>
                        List(fixBreakAndContinues(k, ifdefDepth, forDoWhileIfdefDepth, switchIfdefDepth, lastStmtWasSwitch))
                })
        })
        transformation(t).getOrElse(t).asInstanceOf[T]
    }

    override def updatePerformancePrependString(prependString: String, createIncludeDirective: (String) => String, path: String, fileName: String): String = {
        var result = returnMacro
        if (fileName.startsWith("sqlite")) {
            result += createIncludeDirective(path ++ noIncludeFileName)
        } else {
            result += createIncludeDirective(path ++ includeFileName)
        }
        result += createIncludeDirective(path ++ performanceIncludeFileName)
        result
    }

    override def printPerformanceCounter(path: String) = {
        var resultString = ""
        if (insertPerformanceCounter) {
            //println("Number of performance measuring nodes: " + performanceCounter)
            resultString += "Number of performance measuring nodes: " + performanceCounter.toString() + "\n"
            var currentIndex = 0
            performanceCmpStmtContextMap.foreach(x => {
                //println("Node " + currentIndex.toString + ":\t" + x._2 + " -> " + x._1)
                resultString += "Node " + currentIndex.toString + ":\t" + x._2 + " -> " + x._1 + "\n"
                currentIndex += 1
            })
        }
        writeToFile(path ++ "_nodes.txt", resultString)
    }

    override def insertPerformanceCounter(suffix: PostfixSuffix): PostfixSuffix = {
        if (insertPerformanceCounter) {
            suffix match {
                case FunctionCall(ExprList(List(opt1@Opt(_, StringLit(_))))) =>
                    performanceCounter += 1
                    return FunctionCall(ExprList(List(opt1, Opt(trueF3, Constant(performanceCounter.toString)))))
                case _ =>
            }
        }
        suffix
    }

    override def insertPerformanceCounter(cmpStmt: CompoundStatement): CompoundStatement = {
        if (insertPerformanceCounter) {
            cmpStmt.innerStatements.head match {
                case Opt(ft, ExprStatement(PostfixExpr(Id(name), FunctionCall(ExprList(List(opt1@Opt(_, StringLit(_)))))))) if name.equals(functionBeforeName) || name.equals(functionBeforeCounterName) =>
                    val result = CompoundStatement(Opt(ft, ExprStatement(PostfixExpr(Id(name), FunctionCall(ExprList(List(opt1, Opt(trueF3, Constant(performanceCounter.toString)))))))) :: cmpStmt.innerStatements.tail)
                    performanceCmpStmtContextMap.put(result, getContext(cmpStmt))
                    performanceCounter += 1
                    return result
                case _ =>
            }
            return cmpStmt
        } else {
            return cmpStmt
        }
    }

    private def getContext(cmpStmt: CompoundStatement, throwErrors: Boolean = true): String = {
        if (!cmpStmt.innerStatements.isEmpty) {
            cmpStmt.innerStatements.head match {
                case Opt(ft, ExprStatement(PostfixExpr(Id(name), FunctionCall(ExprList(entries))))) if name.equals(functionBeforeName) || name.equals(functionBeforeCounterName) =>
                    entries match {
                        case Opt(_, StringLit(List(Opt(_, stringLiteral)))) :: xs =>
                            return stringLiteral.replaceFirst("\"(.*?)\"", "$1")
                        case _ =>
                            if (throwErrors) {
                                logger2.error("Could not find context for statement: " + CompoundStatement)
                            }
                            return ""
                    }
                case _ =>
                    if (throwErrors) {
                        logger2.error("Could not find context for statement: " + CompoundStatement)
                    }
                    return ""
            }
        }
        if (throwErrors) {
            logger2.error("Could not find context for statement: " + CompoundStatement)
        }
        return ""
    }

    override def insertPerfFunctCalls(cmpstmt: CompoundStatement, context: FeatureExpr): CompoundStatement = {
        if (context == trueF3 || cmpstmt.innerStatements.isEmpty) {
            // Don't insert anything
            return cmpstmt
        }

        var result: CompoundStatement = cmpstmt
        val numberOfStatements = getNumberOfStatements(cmpstmt)
        var functionName = functionBeforeName
        if (insertPerformanceCounter) {
            functionName = functionBeforeCounterName
        }

        val last = cmpstmt.innerStatements.last
        var contextString = contextToReadableString(context)

        last match {
            case Opt(ft, ReturnStatement(_)) =>
                contextString = contextString + "_" + statementMapping.get(last.entry)
            case Opt(ft, ExprStatement(PostfixExpr(Id(name), _))) if name.equals(returnMacroName) =>
                contextString = contextString + "_" + statementMapping.get(last.entry)
            case k =>
                contextString = contextString + "_" + statementMapping.get(cmpstmt.innerStatements.head.entry)
        }

        if (contextString.endsWith("null")) {
            contextString = contextString.substring(0, contextString.length-5)
        }

        val beforeStmt = ExprStatement(PostfixExpr(Id(functionName), FunctionCall(ExprList(List(Opt(trueF3, StringLit(List(Opt(trueF3, "\"" ++ contextString ++ "\"")))))))))
        val afterStmt = ExprStatement(PostfixExpr(Id(functionAfterName), FunctionCall(ExprList(List(Opt(trueF3, Constant(numberOfStatements.toString)))))))

        def alterStatementHelper[T <: Product](t: T, continueExitsContext: Boolean = true): T = {
            val transformation = alltd(rule[Product] {
                case i@IfStatement(cond, One(CompoundStatement(List(Opt(ft, ContinueStatement())))), List(), None) =>
                    //IfStatement(cond, One(CompoundStatement(List(Opt(trueF3, afterStmt), Opt(ft, ContinueStatement())))), List(), None)

                    if (continueExitsContext) {
                        IfStatement(cond, One(CompoundStatement(List(Opt(trueF3, afterStmt), Opt(ft, ContinueStatement())))), List(), None)
                    } else {
                        i
                    }
                case Opt(ft, s: ForStatement) =>
                    Opt(ft, alterStatementHelper(s, false))
                case Opt(ft, s: DoStatement) =>
                    Opt(ft, alterStatementHelper(s, false))
                case Opt(ft, s: WhileStatement) =>
                    Opt(ft, alterStatementHelper(s, false))
                case CompoundStatement(innerStmts) =>
                    CompoundStatement(innerStmts.flatMap {
                        case Opt(ft, ReturnStatement(None)) =>
                            List(Opt(ft, ExprStatement(PostfixExpr(Id(functionAfterName), FunctionCall(ExprList(List(Opt(trueF3, Constant(numberOfStatements.toString)))))))), Opt(ft, ReturnStatement(None)))
                        case Opt(ft, ReturnStatement(Some(expr))) =>
                            List(Opt(ft, ExprStatement(PostfixExpr(Id(returnMacroName), FunctionCall(ExprList(List(Opt(trueF3, expr), Opt(trueF3, Id(functionAfterName + "(" + numberOfStatements.toString + ")")))))))))
                        case k =>
                            List(alterStatementHelper(k, continueExitsContext))
                    })
            })
            transformation(t).getOrElse(t).asInstanceOf[T]
        }
        val r = manytd(rule[Statement] {
            case i@IfStatement(cond, One(CompoundStatement(List(Opt(ft, ContinueStatement())))), List(), None) =>
                if (isStatementLegal(i)) {
                    IfStatement(cond, One(CompoundStatement(List(Opt(trueF3, afterStmt), Opt(ft, ContinueStatement())))), List(), None)
                } else {
                    i
                }
            case CompoundStatement(innerStmts) =>
                CompoundStatement(innerStmts.flatMap {
                    case o@Opt(ft, ReturnStatement(None)) =>
                        if (isStatementLegal(o.entry)) {
                            List(Opt(ft, ExprStatement(PostfixExpr(Id(functionAfterName), FunctionCall(ExprList(List(Opt(trueF3, Constant(numberOfStatements.toString)))))))), Opt(ft, ReturnStatement(None)))
                        } else {
                            List(Opt(ft, ReturnStatement(None)))
                        }
                        List(Opt(ft, ExprStatement(PostfixExpr(Id(functionAfterName), FunctionCall(ExprList(List(Opt(trueF3, Constant(numberOfStatements.toString)))))))), Opt(ft, ReturnStatement(None)))
                    case o@Opt(ft, ReturnStatement(Some(expr))) =>
                        if (isStatementLegal(o.entry)) {
                            List(Opt(ft, ExprStatement(PostfixExpr(Id(returnMacroName), FunctionCall(ExprList(List(Opt(trueF3, expr), Opt(trueF3, Id(functionAfterName + "(" + numberOfStatements.toString + ")")))))))))
                        } else {
                            List(Opt(ft, ReturnStatement(Some(expr))))
                        }
                    case k =>
                        List(k)
                })
        })
        last match {
            case Opt(ft, ReturnStatement(_)) =>
                if (isStatementLegal(last.entry)) {
                    result = CompoundStatement(List(Opt(trueF3, beforeStmt)) ++ r(cmpstmt).getOrElse(cmpstmt).asInstanceOf[CompoundStatement].innerStatements)
                } else {
                    result = cmpstmt
                }
            case Opt(ft, ExprStatement(PostfixExpr(Id(name), _))) if name.equals(returnMacroName) =>
                if (isStatementLegal(last.entry)) {
                    result = CompoundStatement(List(Opt(trueF3, beforeStmt)) ++ r(cmpstmt).getOrElse(cmpstmt).asInstanceOf[CompoundStatement].innerStatements)
                } else {
                    result = cmpstmt
                }
            case k =>
                val newCompound = cmpstmt
                if (isStatementLegal(cmpstmt.innerStatements.head.entry)) {
                    result = CompoundStatement(List(Opt(trueF3, beforeStmt)) ++ newCompound.innerStatements ++ List(Opt(trueF3, afterStmt)))
                } else {
                    result = newCompound
                }
        }
        print("")
        return result
        /*if (last.entry.isInstanceOf[ReturnStatement]) {
            val currentReturn = last.entry.asInstanceOf[ReturnStatement]
            if (currentReturn.expr.isDefined) {
                val fctCall = ExprStatement(PostfixExpr(Id(returnMacroName), FunctionCall(ExprList(List(Opt(trueF3, last.entry.asInstanceOf[ReturnStatement].expr.get), Opt(trueF3, Id(functionAfterName + "(" + numberOfStatements.toString + ")")))))))
                return CompoundStatement(List(Opt(trueF3, beforeStmt)) ++ cmpstmt.innerStatements.take(cmpstmt.innerStatements.size - 1) ++ List(Opt(trueF3, fctCall)))
            } else {
                //val fctCall = ExprStatement(PostfixExpr(Id(returnMacroName), FunctionCall(ExprList(List(Opt(trueF3, Constant("0")), Opt(trueF3, Id(functionAfterName + "(" + numberOfStatements.toString + ")")))))))
                //return CompoundStatement(List(Opt(trueF3, beforeStmt)) ++ cmpstmt.innerStatements.take(cmpstmt.innerStatements.size - 1) ++ List(Opt(trueF3, fctCall)))

                val afterStmt = ExprStatement(PostfixExpr(Id(functionAfterName), FunctionCall(ExprList(List(Opt(trueF3, Constant(numberOfStatements.toString)))))))
                return CompoundStatement(List(Opt(trueF3, beforeStmt)) ++ cmpstmt.innerStatements.take(cmpstmt.innerStatements.size - 1) ++ List(Opt(trueF3, afterStmt)) ++ List(last))
            }
        } else {
            val afterStmt = ExprStatement(PostfixExpr(Id(functionAfterName), FunctionCall(ExprList(List(Opt(trueF3, Constant(numberOfStatements.toString)))))))
            return CompoundStatement(List(Opt(trueF3, beforeStmt)) ++ cmpstmt.innerStatements ++ List(Opt(trueF3, afterStmt)))
        }*/
    }

    override def insertPerfMainFunctCalls(cmpstmt: CompoundStatement): CompoundStatement = {
        if (cmpstmt.innerStatements.isEmpty) {
            // Don't insert anything
            return cmpstmt
        }
        var last = cmpstmt.innerStatements.last
        val r = manytd(rule[Statement] {
            case compStmt@CompoundStatement(innerStmts) =>
                val result = CompoundStatement(innerStmts.flatMap {
                    case Opt(ft, ReturnStatement(None)) =>
                        List(Opt(ft, ExprStatement(PostfixExpr(Id(functionEndName), FunctionCall(ExprList(List()))))), Opt(ft, ReturnStatement(None)))
                    case Opt(ft, ReturnStatement(Some(expr))) =>
                        List(Opt(ft, ExprStatement(PostfixExpr(Id(returnMacroName), FunctionCall(ExprList(List(Opt(trueF3, expr), Opt(trueF3, Id(functionEndName + "()")))))))))
                    case k =>
                        List(k)
                })
                updateIgnoredStatements(compStmt, result)
                result
        })
        val newCmpStmt = r(cmpstmt).getOrElse(cmpstmt).asInstanceOf[CompoundStatement]
        last = newCmpStmt.innerStatements.last
        val startStmt = ExprStatement(PostfixExpr(Id(functionStartName), FunctionCall(ExprList(List()))))
        var result: CompoundStatement = CompoundStatement(List())
        last match {
            case Opt(ft, ReturnStatement(None)) =>
                val endStmt = ExprStatement(PostfixExpr(Id(functionEndName), FunctionCall(ExprList(List()))))
                result = CompoundStatement(List(Opt(trueF3, startStmt)) ++ newCmpStmt.innerStatements.take(newCmpStmt.innerStatements.size - 1) ++ List(Opt(trueF3, endStmt)) ++ List(last))
            case Opt(ft, ReturnStatement(Some(_))) =>
                val fctCall = ExprStatement(PostfixExpr(Id(returnMacroName), FunctionCall(ExprList(List(Opt(trueF3, last.entry.asInstanceOf[ReturnStatement].expr.get), Opt(trueF3, Id(functionEndName + "()")))))))
                result = CompoundStatement(List(Opt(trueF3, startStmt)) ++ newCmpStmt.innerStatements.take(newCmpStmt.innerStatements.size - 1) ++ List(Opt(trueF3, fctCall)))
            case Opt(ft, ExprStatement(PostfixExpr(Id(name), _))) if name.equals(returnMacroName) =>
                result = CompoundStatement(List(Opt(trueF3, startStmt)) ++ newCmpStmt.innerStatements)
            case k =>
                val endStmt = ExprStatement(PostfixExpr(Id(functionEndName), FunctionCall(ExprList(List()))))
                result = CompoundStatement(List(Opt(trueF3, startStmt)) ++ newCmpStmt.innerStatements ++ List(Opt(trueF3, endStmt)))
        }
        return result
    }

    override def combinePerformancePair(firstStmts: CompoundStatement, secondStmts: CompoundStatement): CompoundStatement = {
        val tmpTuple = removePerformanceAfterFunction(firstStmts.innerStatements)
        val result = CompoundStatement(tmpTuple._1 ++ updatePerformanceAfterFunction(removePerformanceBeforeFunction(secondStmts.innerStatements), tmpTuple._2))
        return result
    }

    override def removePerformanceBeforeFunction(stmts: List[Opt[Statement]]): List[Opt[Statement]] = {
        val first = stmts.head
        first match {
            case Opt(trueF3, ExprStatement(PostfixExpr(Id(name), fc: FunctionCall))) if name.equals(functionBeforeName) || name.equals(functionBeforeCounterName) =>
                return stmts.drop(1)
            case _ =>
                return stmts
        }
        return stmts
    }

    override def removePerformanceAfterFunction(stmts: List[Opt[Statement]]): (List[Opt[Statement]], Int) = {
        val last = stmts.last
        last match {
            case Opt(_, ExprStatement(PostfixExpr(Id(name), FunctionCall(ExprList(List(Opt(_, Constant(numberOfStatements)))))))) if name.equals(functionAfterName) =>
                return (stmts.take(stmts.size - 1), numberOfStatements.toInt)
            case _ =>
                return (stmts, 0)
        }
        return (stmts, 0)
    }

    private def updatePerformanceAfterFunction(stmts: List[Opt[Statement]], numberOfStmtsToAdd: Int): List[Opt[Statement]] = {
        val last = stmts.last
        last match {
            case Opt(f1, ExprStatement(PostfixExpr(Id(name), FunctionCall(ExprList(List(Opt(f2, Constant(numberOfStatements)))))))) if name.equals(functionAfterName) =>
                return stmts.updated(stmts.size - 1, Opt(f1, ExprStatement(PostfixExpr(Id(functionAfterName), FunctionCall(ExprList(List(Opt(f2, Constant((numberOfStatements.toInt + numberOfStmtsToAdd).toString())))))))))
            case _ =>
                return stmts
        }
        return stmts
    }

    private def fixLabelAndGotos[T <: Product](t: T): T = {
        val labelContextMap: java.util.HashMap[String, List[String]] = new java.util.HashMap()
        def getLabelContext[T <: Product](currentT: T, ifdefs: List[String] = List()): T = {
            val labelContext = alltd(rule[Product] {
                case cs: CompoundStatement =>
                    val context = getContext(cs, false)
                    if (context == "") {
                        CompoundStatement(getLabelContext(cs.innerStatements, ifdefs))
                    } else {
                        CompoundStatement(getLabelContext(cs.innerStatements, context :: ifdefs))
                    }
                case o@Opt(ft, LabelStatement(id: Id, _)) =>
                    labelContextMap.put(id.name, ifdefs)
                    o

            })
            labelContext(currentT).getOrElse(currentT).asInstanceOf[T]
        }
        getLabelContext(t)

        def fixLabelAndGotosHelper[T <: Product](currentT: T, currentIfdefs: List[String] = List()): T = {
            val transformation = alltd(rule[Product] {
                case cs: CompoundStatement =>
                    val context = getContext(cs, false)
                    if (context == "") {
                        CompoundStatement(fixLabelAndGotosHelper(cs.innerStatements, currentIfdefs))
                    } else {
                        CompoundStatement(fixLabelAndGotosHelper(cs.innerStatements, context :: currentIfdefs))
                    }
                case l: List[_] =>
                    l.flatMap(x => x match {
                        case o@Opt(ft, GotoStatement(id: Id)) if (currentIfdefs.size > 0 && labelContextMap.containsKey(id.name)) =>
                            val listDiff = listDifference(labelContextMap.get(id.name), currentIfdefs)
                            /*if (!listDiff._1.isEmpty) {
                                println("Goto: " + id.name + " <-> " + currentIfdefs + "\nDiff: " + listDifference(labelContextMap.get(id.name), currentIfdefs))
                            }*/
                            var resultList: List[Opt[Statement]] = List()
                            val afterStmt = Opt(trueF3, ExprStatement(PostfixExpr(Id(functionAfterName), FunctionCall(ExprList(List(Opt(trueF3, Constant("0"))))))))
                            for (toBuild <- listDiff._2) {
                                resultList = afterStmt :: resultList
                            }
                            resultList ++ List(o)
                        case k: Opt[_] =>
                            val result = fixLabelAndGotosHelper(k, currentIfdefs)
                            updateIgnoredStatements(k.entry, result.entry)
                            List(result)
                        case _ =>
                            List()
                    })
            })
            transformation(currentT).getOrElse(currentT).asInstanceOf[T]
        }
        fixLabelAndGotosHelper(t)
    }

    private def listDifference(label: List[String], goto: List[String]): (List[String], List[String]) = {
        label match {
            case Nil =>
                return (List(), goto)
            case x :: Nil =>
                goto match {
                    case Nil =>
                        return (label, List())
                    case y :: Nil =>
                        if (x == y) {
                            return (List(), List())
                        } else {
                            return (label, goto)
                        }
                    case y :: ys =>
                        if (x == y) {
                            return (List(), ys)
                        }
                }
            case x :: xs =>
                goto match {
                    case Nil =>
                        return (label, List())
                    case y :: Nil =>
                        if (x == y) {
                            return (xs, List())
                        } else {
                            return (label, goto)
                        }
                    case y :: ys =>
                        if (y == x) {
                            return listDifference(xs, ys)
                        } else {
                            return (label, goto)
                        }
                }
        }
        (label, goto)
    }

    private def contextToReadableString(context: FeatureExpr): String = {
        val regexPattern = "(defined|definedEx)\\(([a-zA-Z_0-9]+)\\)".r
        return regexPattern replaceAllIn(context.toTextExpr, "$2")
    }

    /**
      * Checks if given Conditional[Expr] is a condition generated from the ifdeftoif transformation process (see
      * function toCExpr).
      */
    private def isIfdeftoifCondition2(cExpr: Conditional[Expr]): Boolean = {
        var result = false
        cExpr match {
            case One(expr@NAryExpr(PostfixExpr(Id(name), PointerPostfixSuffix(".", i: Id)), _)) =>
                if (name.equals(featureStructInitializedName2))
                    result = true
            case One(expr@PostfixExpr(Id(name), PointerPostfixSuffix(".", i: Id))) =>
                if (name.equals(featureStructInitializedName2))
                    result = true
            case One(expr@UnaryOpExpr("!", NAryExpr(PostfixExpr(Id(name), PointerPostfixSuffix(".", i: Id)), _))) =>
                if (name.equals(featureStructInitializedName2))
                    result = true
            case One(expr@UnaryOpExpr("!", PostfixExpr(Id(name), PointerPostfixSuffix(".", i: Id)))) =>
                if (name.equals(featureStructInitializedName2))
                    result = true
            case One(expr@NAryExpr(exprs, others)) =>
                result = isIfdeftoifCondition2(exprs)
            case One(id: Id) =>
                result = id.name.startsWith(featurePrefix2)
            case One(UnaryOpExpr("!", id: Id)) =>
                result = id.name.startsWith(featurePrefix2)
            case _ =>
        }
        return result
    }

    /**
      * Checks if given Conditional[Expr] is a condition generated from the ifdeftoif transformation process (see
      * function toCExpr).
      */
    private def isIfdeftoifCondition2(cExpr: Expr): Boolean = {
        cExpr match {
            case NAryExpr(expr, others) =>
                return isIfdeftoifCondition2(expr)
            case id: Id =>
                return id.name.startsWith(featurePrefix2)
            case UnaryOpExpr("!", id: Id) =>
                return id.name.startsWith(featurePrefix2)
            case _ =>
                return false
        }
    }

    private def getNumberOfStatements(stmt: Statement): Int = {
        stmt match {
            case CompoundStatement(innerStmts) =>
                return innerStmts.filter(x => x.entry.isInstanceOf[CompoundStatement]).map(y => getNumberOfStatements(y.entry)).sum + innerStmts.filter(x => !x.entry.isInstanceOf[CompoundStatement]).map(x => getNumberOfStatements(x.entry)).sum
            case IfStatement(cond, thens, elifs, elses) =>
                if (isIfdeftoifCondition2(cond)) {
                    return 0
                } else {
                    // TODO statement counting inside ifs?
                    return 1
                }
            case s: Statement =>
                return 1
        }
    }
}