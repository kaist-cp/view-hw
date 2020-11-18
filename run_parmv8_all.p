#!/usr/bin/env bash

# This script runs the model checker for all PARMv8-view examples

basedir="$(dirname "$0")"

exdir="${basedir}/parmv8-view-examples"
run="${basedir}/rmem -model promising -model promise_first -model promising_parallel_thread_state_search -model promising_parallel_without_follow_trace -priority_reduction false -interactive false -hash_prune false -pp_hex true -shared_memory"

echo -e "Checking all PARMv8-view examples..."

for f in $(ls ${exdir})
do
    title="\"${f}\" example"
    title_len=$(echo ${title} | wc -m)
    snd_dash_len=80
    fst_dash_len=$((${snd_dash_len}-${title_len}+1))

    echo -e "\n\n"
    printf "${title}"; printf -- '-%.0s' $(seq ${fst_dash_len}); echo ""
    ${run} ${exdir}/${f}/shared_memory.txt ${exdir}/${f}/${f}.litmus
    printf -- '-%.0s' $(seq ${snd_dash_len}); echo ""
done
