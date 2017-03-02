#!/bin/sh

cd "$(dirname "$0")"

java -Xmx4096M -Xss10M -jar sbt-launch.jar compile copy-resources mkrun
