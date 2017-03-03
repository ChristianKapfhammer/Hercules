#!/bin/sh

cd "$(dirname "$0")"

java -Xmx8192M -Xss10M -jar sbt-launch.jar compile copy-resources mkrun
