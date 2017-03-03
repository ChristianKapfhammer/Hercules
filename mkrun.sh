#!/bin/sh

cd "$(dirname "$0")"

java -Xmx16384M -Xss40M -jar sbt-launch.jar compile copy-resources mkrun
