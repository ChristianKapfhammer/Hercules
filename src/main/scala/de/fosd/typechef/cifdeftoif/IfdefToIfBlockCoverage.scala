package de.fosd.typechef.cifdeftoif

import java.io.{File, PrintWriter}

import de.fosd.typechef.conditional.{Choice, Conditional, One, Opt}
import de.fosd.typechef.featureexpr.{FeatureExpr, FeatureExprFactory, FeatureModel}
import de.fosd.typechef.featureexpr.bdd.BDDFeatureModel
import de.fosd.typechef.featureexpr.sat.SATFeatureModel
import de.fosd.typechef.parser.c.{AST, TranslationUnit}

import scala.io.Source

trait IfdefToIfBlockCoverageInterface {

    protected var featureModel: FeatureModel = _

    def blockCoverage(ast: TranslationUnit, fm: FeatureModel, filename: String): Unit
    def blockCoverageTest(ast: TranslationUnit, fm: FeatureModel, filename: String): Unit
}

class IfdefToIfBlockCoverage extends IfdefToIfBlockCoverageInterface with IOUtilities {

    override def blockCoverage(ast: TranslationUnit, fm: FeatureModel, dirname: String): Unit = {

        featureModel = fm

        var finalConfs: List[FeatureExpr] = List.empty[FeatureExpr]

        coverageCases(ast).foreach(exp => {
            if(exp.isSatisfiable(fm)) {
                exp.getSatisfiableAssignment(fm, exp.collectDistinctFeatureObjects, true) match {
                    case Some(x) =>
                        finalConfs :::= List(FeatureExprFactory.createFeatureExprFast(x._1.toSet, x._2.toSet))
                    case None =>
                }
            }
        })

        finalConfs = finalConfs.map(completeConfiguration)

        println("Calculated " + finalConfs.size + " configurations")

        val directory = new File(dirname)

        if (!directory.exists()) {
            directory.mkdir()
        }

        writeConfigFile(dirname, finalConfs)

        val hDirectory = new File(dirname + "/hFiles")

        if (!hDirectory.exists()) {
            hDirectory.mkdir()
        }

        writeHFiles(dirname, finalConfs)
    }

    override def blockCoverageTest(ast: TranslationUnit, fm: FeatureModel, filename: String): Unit = {
        featureModel = fm

        val configs = readConfigFile(filename)
        var codeBlocks = getCodeBlocks(ast)
        var unusedBlocks = List.empty[FeatureExpr]
        var usedBlocks = List.empty[FeatureExpr]

        codeBlocks = codeBlocks - FeatureExprFactory.True
        codeBlocks = codeBlocks - FeatureExprFactory.False

        for (block <- codeBlocks) {
            var satisfiable = false
            var i = 0

            while (i < configs.size && !satisfiable) {
                satisfiable = block.and(configs(i)).isSatisfiable(featureModel)
                i = i + 1
            }

            if (satisfiable) {
                usedBlocks :::= List(block)
            } else {
                unusedBlocks :::= List(block)
            }
        }

        println("Valid code blocks found: " + codeBlocks.size)
        println("Fulfilled code bocks: " + usedBlocks.size)
        println("Unused code blocks: " + unusedBlocks.size)

    }

    private def writeConfigFile(dirname: String, configs: List[FeatureExpr]): Unit = {
        val pw = new PrintWriter(new File(dirname + "/bcConfigs.txt"))

        for (conf <- configs) {
            val features = conf.collectDistinctFeatures.toArray
            var string = conf.toString()

            if (string.head == '(') {
                string = string.substring(1, string.length-1)
            }

            val configParts = string.split("&")
            string = ""

            for (i <- 0 until configParts.length) {
                var ft = features(i).toString

                if (configParts(i).head == '!') {
                    ft = "!" + ft
                }

                if (string.length == 0) {
                    string = ft
                } else {
                    string = string + "&" + ft
                }
            }

            pw.write(string + "\n")
        }

        pw.close()
    }

    private def writeHFiles(dirname: String, configs: List[FeatureExpr]): Unit = {
        for (counter <- configs.indices) {
            val pw = new PrintWriter(new File(dirname + "/hFiles/config_" + (counter+1) + ".h"))

            val features = configs(counter).collectDistinctFeatures.toArray
            var string = configs(counter).toString()

            if (string.head == '(') {
                string = string.substring(1, string.length-1)
            }

            val configParts = string.split("&")
            string = ""

            // Add feature definitions into file
            for (i <- 0 until configParts.length) {
                if (configParts(i).head != '!') {
                    string = string + "#define " + features(i).toString + "\n"
                }
            }

            // Write beginning and end of file
            string = "#ifndef POLARSSL_CONFIG_H\n#define POLARSSL_CONFIG_H\n\n" + string + "#endif"

            pw.write(string)
            pw.close()
        }
    }

    private def readConfigFile(filename: String): List[FeatureExpr] = {
        var configs = List.empty[FeatureExpr]

        for (c <- Source.fromFile(filename).getLines()) {
            var config: FeatureExpr = FeatureExprFactory.True

            for (confPart <- c.split("&")) {
                var feature: FeatureExpr = FeatureExprFactory.createDefinedExternal(if (confPart.head == '!') confPart.tail else confPart)

                if (confPart.head == '!') {
                    feature = feature.not()
                }

                config = if (config == FeatureExprFactory.True) feature else config.and(feature)
            }

            configs :::= List(config)
        }

        println("Loaded " + configs.size + " configurations")

        configs
    }

    private def completeConfiguration(fexpr : FeatureExpr): FeatureExpr = {
        var baseFeatures: FeatureExpr = null

        for (feature <- getVars(featureModel).keys) {
            val createdFeature = FeatureExprFactory.createDefinedExternal(feature)
            val featureMandatory = createdFeature.and(fexpr).equivalentTo(fexpr, featureModel)

            if (featureMandatory && !fexpr.collectDistinctFeatures.contains(feature)) {
                if (baseFeatures == null) {
                    baseFeatures = createdFeature
                } else {
                    baseFeatures = baseFeatures.and(createdFeature)
                }
            }
        }

        var result:FeatureExpr = null

        if (baseFeatures == null)
            result = fexpr
        else
            result = baseFeatures.and(fexpr)

        result
    }

    private def getVars(fm: FeatureModel) =
        if (fm.isInstanceOf[BDDFeatureModel]) fm.asInstanceOf[BDDFeatureModel].variables
        else fm.asInstanceOf[SATFeatureModel].variables

    private def generateConfiguration(o: Opt[_]): List[FeatureExpr] = {

        var configurations: List[FeatureExpr] = List.empty[FeatureExpr]

        if (o.condition != FeatureExprFactory.False) {
            if (o.condition != FeatureExprFactory.True) {
                configurations = List(o.condition)
            }

            configurations = mergeConfigurations(configurations, coverageCases(o.entry))
        }

        configurations
    }

    private def generateConfiguration(c: Conditional[_]): List[FeatureExpr] = {

        c match {
            case one: One[_] =>
                coverageCases(one.value)
            case choice: Choice[_] =>
                var configurations: List[FeatureExpr] = List.empty[FeatureExpr]

                if (choice.condition == FeatureExprFactory.False) {
                    configurations = generateConfiguration(choice.elseBranch)
                } else if (choice.condition == FeatureExprFactory.True) {
                    configurations = generateConfiguration(choice.thenBranch)
                } else {
                    // Then-Branch with choice.condition
                    val thenConfigurations = generateConfiguration(choice.thenBranch)
                        .map(fe => choice.condition.and(fe)).filter(fe => fe.isSatisfiable(featureModel))
                    // Else-Branch with !choice.condition
                    val elseConfigurations = generateConfiguration(choice.elseBranch)
                        .map(fe => choice.condition.not().and(fe)).filter(fe => fe.isSatisfiable(featureModel))

                    configurations :::= (if (thenConfigurations.isEmpty) List(choice.condition) else thenConfigurations)
                    configurations :::= (if (elseConfigurations.isEmpty) List(choice.condition.not()) else elseConfigurations)
                }

                configurations
        }
    }

    private def coverageCases(obj: Any): List[FeatureExpr] = {
        var newConfigurations: List[FeatureExpr] = List.empty[FeatureExpr]

        obj match {
            case x: AST =>
                if (x.productArity > 0) {
                    for (y <- x.productIterator.toList) {
                        newConfigurations = mergeConfigurations(newConfigurations, coverageCases(y))
                    }
                }
            case x: Opt[_] =>
                newConfigurations = generateConfiguration(x)
            case One(x) =>
                newConfigurations = coverageCases(x)
            case x: Choice[_] =>
                newConfigurations = generateConfiguration(x)
            case x: List[_] =>
                for (elem <- x) {
                    newConfigurations = mergeConfigurations(newConfigurations, coverageCases(elem))
                }
            case Some(x) =>
                newConfigurations = coverageCases(x)
            case None =>
            case o =>
        }

        newConfigurations
    }

    private def getCodeBlocks(obj: Any): Set[FeatureExpr] = {
        var codeBlocks: Set[FeatureExpr] = Set()

        obj match {
            case x: Opt[_] =>
                codeBlocks += x.condition
                codeBlocks = codeBlocks ++ getCodeBlocks(x.entry)
            case x: Choice[_] =>
                codeBlocks += x.condition
                codeBlocks = codeBlocks ++ getCodeBlocks(x.thenBranch).map(fe => x.condition.and(fe))
                codeBlocks += x.condition.not()
                codeBlocks = codeBlocks ++ getCodeBlocks(x.elseBranch).map(fe => x.condition.and(fe))
            case x: List[_] =>
                for (elem <- x) {
                    codeBlocks = codeBlocks ++ getCodeBlocks(elem)
                }
            case x: AST =>
                if (x.productArity > 0) {
                    for (y <- x.productIterator.toList) {
                        codeBlocks = codeBlocks ++ getCodeBlocks(y)
                    }
                }
            case Some(x) =>
                codeBlocks = getCodeBlocks(x)
            case None => // Nothing should happen here
            case One(x) =>
                codeBlocks = getCodeBlocks(x)
            case o => // Nothing should happen here
        }

        codeBlocks
    }

    private def mergeConfigurations(origin: List[FeatureExpr], extension: List[FeatureExpr]): List[FeatureExpr] = {
        var unusedConfigurations: Set[FeatureExpr] = Set.empty[FeatureExpr]
        var mergedConfigurations: List[FeatureExpr] = List.empty[FeatureExpr]

        if (origin == Nil || origin.isEmpty) {
            return extension
        }

        if (extension == Nil || extension.isEmpty) {
            return origin
        }

        origin.foreach(oriConf => {
            unusedConfigurations += oriConf
        })

        extension.foreach(extConf => {
            unusedConfigurations += extConf
        })

        origin.foreach(oriConf => {
            extension.foreach(extConf => {
                // TODO: Simplify expression
                val mergedConf: FeatureExpr = oriConf.and(extConf)

                if (mergedConf.isSatisfiable() && oriConf != extConf) {
                    mergedConfigurations :::= List(mergedConf)

                    unusedConfigurations -= oriConf
                    unusedConfigurations -= extConf
                }
            })
        })

        unusedConfigurations.foreach(conf =>
            mergedConfigurations :::= List(conf)
        )

        mergedConfigurations
    }

}
