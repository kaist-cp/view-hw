#!/usr/bin/env bash

# This script makes artifact.zip that contains:
# - README.md
# - proof dir
# - model checker dir

artifactname="pldi2021-paper21-artifact"

# Making a temporary directory
tmpdir="artifact_tmp"
set -e
mkdir ${tmpdir}
set +e
cd ${tmpdir}
mkdir ${artifactname}


# Making proof directory
coqrepo="promising-hw"
coqdir="proof"
mkdir ${artifactname}/${coqdir}

git clone git@github.com:kaist-cp/${coqrepo}.git
cd ${coqrepo}

git submodule init
git submodule update

coqin="src"
coqin+=" lib"
coqin+=" Makefile"
coqin+=" build.sh"
coqin+=" status.sh"

for f in ${coqin}
do
    mv $f ../${artifactname}/${coqdir}
done

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
rm -rf ${paperrepo}/experiment/scripts # not used
mv ${paperrepo}/experiment ${rmemdir}/parmv8-view-examples

mv ${rmemdir} ${artifactname}


# Adding README.md
cp ../README.md ${artifactname}


# Making artifact.zip file
filename="${artifactname}.zip"

zip -r ${filename} ${artifactname}
mv ${filename} ../


# Removing the temporary directory
cd ..
rm -rf ${tmpdir}
