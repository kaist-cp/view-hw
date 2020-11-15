#!/usr/bin/env bash

# This script makes artifact.zip that contains:
# - README.md
# - proof dir
# - model checker dir

# 1. Making a temporary directory
tmpdir="artifact_tmp"
set -e
mkdir ${tmpdir}
set +e
cd ${tmpdir}


# 2. Making proof directory
coqrepo="promising-hw"
coqdir="proof"

git clone git@github.com:kaist-cp/${coqrepo}.git
cd ${coqrepo}

git submodule init
git submodule update

coqin="src"
coqin+=" lib"
coqin+=" Makefile"
coqin+=" build.sh"
coqin+=" status.sh"

zip -FSr ${coqdir}.zip ${coqin}
unzip ${coqdir}.zip -d ../${coqdir} # making output directory

cd ..


# 3. Making model checker directory
# TODO: assuming the model checker dir is at ../


# 4. Making artifact.zip file
filename="artifact.zip"
zip -r ${filename} ${coqdir} ../README.md
mv ${filename} ../


# 5. Removing the temporary directory
cd ..
rm -rf ${tmpdir}
