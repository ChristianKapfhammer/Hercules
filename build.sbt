name := "Hercules"

version := "1.0"

organization := "de.fosd.typechef"

scalaVersion := "2.11.7"

libraryDependencies += "de.fosd.typechef" % "frontend_2.11" % "0.4.1"

libraryDependencies += "de.fosd.typechef" % "sampling_2.11" % "0.4.1"

libraryDependencies += "com.novocode" % "junit-interface" % "0.10" % "test"

libraryDependencies += "junit" % "junit" % "4.11"

libraryDependencies += "org.apache.logging.log4j" % "log4j-api" % "2.0-beta4"

libraryDependencies += "org.apache.logging.log4j" % "log4j-core" % "2.0-beta4"

javacOptions ++= Seq("-Xlint:unchecked")

javacOptions ++= Seq("-source", "1.6", "-target", "1.6")

scalacOptions += "-target:jvm-1.6"

scalacOptions ++= Seq("-deprecation",
    "-unchecked",
    "-optimise",
    "-Yinline-warnings",
    "-feature",
    "-language:postfixOps",
    "-language:reflectiveCalls",
    "-language:implicitConversions")

resolvers += "SonaType" at "http://oss.sonatype.org/content/repositories/snapshots/"

mainClass in Runtime := Some("de.fosd.typechef.cifdeftoif.IfdeftoifFrontend")

//generate ifdeftoif.sh file with full classpath
TaskKey[File]("mkrun") <<= (baseDirectory, fullClasspath in Runtime, mainClass in Runtime) map {
    (base, cp, main) =>
        val template = """#!/bin/sh
java -ea -Xmx6G -Xss512M -classpath "%s" %s --ifdeftoif "$@"
                       """
        val mainStr = main getOrElse error("No main class specified")
        val contents = template.format(cp.files.absString, mainStr)
        val out = base / "ifdeftoif.sh"
        IO.write(out, contents)
        out.setExecutable(true)
        out
}

