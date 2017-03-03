#!/bin/sh

cd "$(dirname "$0")"

java -Xmx32768M -Xss20M -jar sbt-launch.jar compile copy-resources mkrun
