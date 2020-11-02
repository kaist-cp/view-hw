#!/bin/bash

filename="artifact.zip"

included="src"
included+=" lib"
included+=" Makefile"
included+=" build.sh"
included+=" README.md"

excluded="*.vio"
excluded+=" *.vos"
excluded+=" *.coq"
excluded+=" *.conf"
excluded+=" *.git"
excluded+=" *.d"

zip -r ${filename} ${included} -x ${excluded}