#!/usr/bin/env bash

# This script makes artifact.zip that contains:
# - README.md
# - proof dir
# - model checker dir

# Making a temporary directory
tmpdir="artifact_tmp"
set -e
mkdir ${tmpdir}
set +e
cd ${tmpdir}


# Making proof directory
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


# Making model checker directory
rmemrepo="rmem-persistency"
rmemdir="model-checker"

git clone git@github.com:kaist-cp/${rmemrepo}.git ${rmemdir}

rm -rf ${rmemdir}/.git* # anonymizing

# Importing model-checked examples
paperrepo="persistent-mem-paper"
git clone git@github.com:kaist-cp/${paperrepo}.git

rm -rf ${paperrepo}/experiment/queue # not mentioned in the paper
mv ${paperrepo}/experiment ${rmemdir}/parmv8-view-examples


# Making artifact.zip file
filename="artifact.zip"
# TODO: add supplementary_text.pdf
zip -r ${filename} ../README.md ${coqdir} ${rmemdir}
mv ${filename} ../


# Removing the temporary directory
cd ..
rm -rf ${tmpdir}
