package de.fosd.typechef.cifdeftoif

import java.io.PrintWriter

trait IOUtilities {
    // http://stackoverflow.com/questions/4604237/how-to-write-to-a-file-in-scala

    import java.io.FileWriter

    def using[A <: {def close()}, B](param: A)(f: A => B): B =
        try {
            f(param)
        } finally {
            param.close()
        }

    def writeToFile(fileName: String, data: String) {
        using(new FileWriter(fileName)) {
            fileWriter => fileWriter.write(data)
        }
    }

    def appendToFile(fileName: String, textData: String) {
        using(new FileWriter(fileName, true)) {
            fileWriter => using(new PrintWriter(fileWriter)) {
                printWriter => printWriter.print(textData)
            }
        }
    }
}