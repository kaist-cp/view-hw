#!/usr/bin/env bash

# This script makes artifact.zip that contains proof dir and model checker dir

# 1. Making a temporary directory
tmpdir="artifact_tmp"
mkdir ${tmpdir}
cd ${tmpdir}


# 2. Making proof directory
coqdir="proof"

coqin="../src"
coqin+=" ../lib"
coqin+=" ../Makefile"
coqin+=" ../build.sh"
coqin+=" ../README.md"

coqex="*.vio"
coqex+=" *.vos"
coqex+=" *.coq"
coqex+=" *.conf"
coqex+=" *.git"
coqex+=" *.d"

zip -FSr ${coqdir}.zip ${coqin} -x ${coqex}
unzip ${coqdir}.zip -d ${coqdir}


# 3. Making model checker directory
# TODO: assuming the model checker dir is at ../


# 4. Making artifact.zip file
filename="artifact.zip"
zip -r ${filename} ${coqdir}
mv ${filename} ../


# 5. Removing the temporary directory
cd ..
rm -rf ${tmpdir}
