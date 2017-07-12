package de.fosd.typechef.cifdeftoif

import java.util

import de.fosd.typechef.options.Options.OptionGroup
import de.fosd.typechef.options.{FrontendOptionsWithConfigFiles, OptionException, Options}
import gnu.getopt.{Getopt, LongOpt}

class IfdefToIfOptions extends FrontendOptionsWithConfigFiles {
    private final val F_IFDEFTOIF: Char = Options.genOptionId
    private final val F_IFDEFTOIFSTATISTICS: Char = Options.genOptionId
    private final val F_IFDEFTOIFNOCHECK: Char = Options.genOptionId
    private final val F_BLOCKCOVERAGE: Char = Options.genOptionId()
    private final val F_BLOCKCOVERAGETEST: Char = Options.genOptionId()
    private final val F_GRANULAREXECCODE: Char = Options.genOptionId()
    private final val F_GRANULARBINSCORE: Char = Options.genOptionId()
    private final val F_GRANULARPERFFILTER: Char = Options.genOptionId()
    private final val F_SIMPLE_SWITCH_TRANSFORMATION: Char = Options.genOptionId
    private final val F_FEATURECONFIG: Char = Options.genOptionId
    private final val F_DECLUSE: Char = Options.genOptionId
    private final val F_PERFORMANCE: Char = Options.genOptionId
    private final val F_EXTERNOPTIONS: Char = Options.genOptionId
    private final val F_MD: Char = Options.genOptionId // dependency output option of gcc

    var performance: Boolean = false
    var ifdeftoifstatistics: Boolean = false
    var ifdeftoifnocheck: Boolean = false
    var blockCoverage: Boolean = false
    var blockCoverageTest: Boolean = false
    var granularExecCode: Boolean = false
    var granularBinScore: Boolean = false
    var granularPerfFilter: Boolean = false
    var simple_switch_transformation: Boolean = false
    var externoptions: Boolean = true
    var featureConfig: Boolean = false

    private var featureConfigFile: String = ""
    private var md: String = ""
    private var bcPath: String = ""
    private var gt: Double = 0.0

    def getFeatureConfigFilename: String = featureConfigFile

    def getMDoption: String = md

    def getBCFilename: String = bcPath

    def getGToption: Double = gt

    protected override def getOptionGroups() = {
        val groups = new util.ArrayList[OptionGroup](super.getOptionGroups())

        groups.add(
            new Options.OptionGroup("#ifdef to if options", 1,
                new Options.Option("ifdeftoif", LongOpt.NO_ARGUMENT, F_IFDEFTOIF, "file",
                    "Make #ifdef to if transformation."),
                new Options.Option("ifdeftoifstatistics", LongOpt.NO_ARGUMENT, F_IFDEFTOIFSTATISTICS, "file",
                    "Save statistics for #ifdef to if transformation."),
                new Options.Option("ifdeftoifnocheck", LongOpt.NO_ARGUMENT, F_IFDEFTOIFNOCHECK, "file",
                    "Do not typecheck the result of #ifdef to if transformation."),
                new Options.Option("simpleSwitch", LongOpt.NO_ARGUMENT, F_SIMPLE_SWITCH_TRANSFORMATION, "file",
                    "Does not generate duplicate switch statements for variability which occurs in child elements of the switch statement. This can lead to syntactical misbehavior of the program."),
                new Options.Option("featureConfig", LongOpt.REQUIRED_ARGUMENT, F_FEATURECONFIG, null,
                    "Save file for load-time feature configuration at given filename."),
                new Options.Option("decluse", LongOpt.NO_ARGUMENT, F_DECLUSE, null,
                    "Test the declaration use map."),
                new Options.Option("performance", LongOpt.NO_ARGUMENT, F_PERFORMANCE, null,
                    "Adds functions and function calls into the code for performance measurements of features."),
                new Options.Option("blockcoverage", LongOpt.REQUIRED_ARGUMENT, F_BLOCKCOVERAGE, null,
                    "Calculate all configurations for block coverage."),
                new Options.Option("blockcoveragetest", LongOpt.REQUIRED_ARGUMENT, F_BLOCKCOVERAGETEST, "file",
                    "Calculate all configurations for block coverage."),
                new Options.Option("granularexeccode", LongOpt.REQUIRED_ARGUMENT, F_GRANULAREXECCODE, "threshold",
                    "Calculates the lines of code of each code block."),
                new Options.Option("granularbinscore", LongOpt.REQUIRED_ARGUMENT, F_GRANULARBINSCORE, "threshold",
                    "Calculates the bin score each code block."),
                new Options.Option("granularperffilter", LongOpt.REQUIRED_ARGUMENT, F_GRANULARPERFFILTER, "threshold",
                    "Filters te block with extern performance data."),
                new Options.Option("externoptions", LongOpt.NO_ARGUMENT, F_EXTERNOPTIONS, null,
                    "Ifdeftoif transformation feature variables are exported into an external optionstruct.h file instead of adding them to the beginning of the transformed file."),
                new Options.Option("MD", LongOpt.REQUIRED_ARGUMENT, F_MD, "file",
                    "Export dependency list.")
            ))

        groups
    }

    protected override def interpretOption(c: Int, g: Getopt): Boolean = {
        if (c == F_IFDEFTOIFSTATISTICS) {
            parse = true
            typecheck = true
            ifdeftoif = true
            ifdeftoifstatistics = true
        } else if (c == F_IFDEFTOIF) {
            parse = true
            typecheck = true
            ifdeftoif = true
            externoptions = true
        } else if (c == F_FEATURECONFIG) {
            checkFileExists(g.getOptarg)
            featureConfigFile = g.getOptarg
            featureConfig = true
        } else if (c == F_IFDEFTOIFNOCHECK) {
            parse = true
            typecheck = true
            ifdeftoif = true
            ifdeftoifnocheck = true
        } else if (c == F_DECLUSE) {
            parse = true
            typecheck = true
            decluse = true
        } else if (c == F_PERFORMANCE) {
            parse = true
            typecheck = true
            ifdeftoif = true
            // disabled typechecking ifdeftoif result because of macro insertions and including <stdio.h> which can't be parsed by TypeChef
            ifdeftoifnocheck = true
            performance = true
        } else if (c == F_BLOCKCOVERAGE) {
            if (!g.getOptarg.endsWith("/")) {
                bcPath = g.getOptarg + "/"
            }
            bcPath += "bcConfigs"
            parse = true
            typecheck = true
            ifdeftoif = true
            ifdeftoifnocheck = true
            blockCoverage = true
        } else if (c == F_BLOCKCOVERAGETEST) {
            checkFileExists(g.getOptarg)
            bcPath = g.getOptarg
            parse = true
            typecheck = true
            ifdeftoif = true
            ifdeftoifnocheck = true
            blockCoverageTest = true
        } else if (c == F_GRANULAREXECCODE) {
            try {
                gt = g.getOptarg.toDouble
            } catch {
                case e: Exception => throw new OptionException("Cannot transform " + g.getOptarg + " into number")
            }

            parse = true
            typecheck = true
            ifdeftoif = true
            ifdeftoifnocheck = true
            performance = true
            granularExecCode = true
        } else if (c == F_GRANULARBINSCORE) {
            try {
                gt = g.getOptarg.toDouble
            } catch {
                case e: Exception => throw new OptionException("Cannot transform " + g.getOptarg + " into number")
            }

            parse = true
            typecheck = true
            ifdeftoif = true
            ifdeftoifnocheck = true
            performance = true
            granularBinScore = true
        } else if (c == F_GRANULARPERFFILTER) {
            try {
                gt = g.getOptarg.toDouble
            } catch {
                case e: Exception => throw new OptionException("Cannot transform " + g.getOptarg + " into number")
            }

            parse = true
            typecheck = true
            ifdeftoif = true
            ifdeftoifnocheck = true
            performance = true
            granularPerfFilter = true
        } else if (c == F_EXTERNOPTIONS) {
            parse = true
            typecheck = true
            ifdeftoif = true
            externoptions = true
        } else if (c == F_MD) {
            md = g.getOptarg
        } else if (c == F_SIMPLE_SWITCH_TRANSFORMATION) {
            simple_switch_transformation = true
        } else {
            return super.interpretOption(c, g)
        }

        true
    }

}
