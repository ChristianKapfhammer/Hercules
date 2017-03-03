#!/bin/sh

cd "$(dirname "$0")"

java -Xmx65536M -Xss20M -jar sbt-launch.jar compile copy-resources mkrun
