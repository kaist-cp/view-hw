# Revamping Hardware Persistency Models (View-based and Axiomatic Persistency Models for Intel-x86 and ARMv8)

This supplementary material provides mechanized proofs and a model checker mentioned in the paper.

## Installation

We assume you are on **Ubuntu 20.04**.

### Common requirement

```
apt install -y build-essential rsync opam
opam init
opam switch create 4.10.0  # or later. If your system OCaml version is >= 4.10.0, you can use it.
```

## Mechanized proofs

### Build

- Requirement: [Coq 8.12.0](https://coq.inria.fr/download).

        cd proof
        opam install coq.8.12.0

- `make -j`: quickly build without checking the proofs.

- `./build.sh`: build with checking all the proofs.  It will incrementally copy the development to
  `.build` sub-directory, and then build there.

- `./status.sh`: check if there is any `admit` in the proofs. (It will print a single result, which is tactic in the library used for development and has nothing to do with the proofs.)

- Interactive Theorem Proving: use [ProofGeneral](https://proofgeneral.github.io/) or
  [CoqIDE](https://coq.inria.fr/download).  Note that `make` creates `_CoqProject`, which is then
  used by ProofGeneral and CoqIDE. To use it:
    + ProofGeneral: use a recent version.
    + CoqIDE: configure it to use `_CoqProject`: `Edit` > `Preferences` > `Project`: change
      `ignored` to `appended to arguments`.

### Our results

Our proofs are based on [a prior work](https://github.com/snu-sf/promising-arm) for ARMv8-view, originally named "Promising-ARMv8". The prior work contains:

- the proof of the equivalence between ARMv8-view and ARMv8-axiom
- some proofs about certification

We extend the existing proofs for ARMv8 to persistency. In addition, we newly define Px86-view/Px86-axiom and prove the theorems of it mentioned in the paper.

#### Model

- `lib`(open source) and `src/lib` contain libraries not necessarily related to
  relaxed-memory concurrency and persistency.

- `src/lib/Lang.v`: Definition of assembly-like language and its interpretation for both x86 and ARMv8 (corresponding to Figure 13)

- `src/promising/TsoPromising.v`: Definition of Px86-view and Px86-prom (corresponding to Figure 11 and 12)

- `src/axiomatic/TsoAxiomatic.v`: Definition of Px86-axiom (corresponding to Figure 7)

- `src/promising/Promising.v`: Definition of PARMv8-view without
  certification (corresponding to Figure 14, 15 and 16)

- `src/axiomatic/Axiomatic.v`: Definition of PARMv8-axiom (corresponding to Figure 9)

- `src/lcertify`: Thread-local certification

#### Results

- Theorem 5.3: Equivalence between Px86-view and Px86-axiom
  + Theorem `axiomatic_to_promising` in `src/equiv/TsoAtoP.v`:
    Px86-axiom refines Px86-prom.
  + Theorem `promising_to_axiomatic` in `src/equiv/TsoPFtoA.v`:
    Px86-prom refines Px86-axiom.
    * `TsoPFtoA1.v`: construction of axiomatic execution from promising execution
    * `TsoPFtoA2.v`, `TsoPFtoA3.v`: definitions and lemmas for main proof
    * `TsoPFtoA4*.v`: proof for validity of constructed axiomatic execution
      * `TsoPFtoA4SL.v`: simulation between promising and axiomatic execution
      * `TsoPFtoA4OBR.v`, `TsoPFtoA4OBW.v`, `TsoPFtoA4FR.v`, `TsoPFtoA4FOB.v`, `TsoPFtoA4FP.v`: proof for "external" axiom
  + Lemma 5.1: Equivalence between Px86-prom and Px86-view
    * The paper says that after the x86-prom and x86-view have been proven to be equivalent (Theorem 5.2)
      and then extended to persistency, the proof in Coq was done right away.
    * Theorem `promising_to_view` in `src/equiv/TsoPFtoV.v`:
      Px86-prom refines Px86-view.
    * Theorem `view_to_promising` in `src/equiv/TsoVtoP.v`:
      Px86-view refines Px86-prom.

- Theorem 6.2: Equivalence between PARMv8-view and PARMv8-axiom
  + Theorem `axiomatic_to_promising` in `src/equiv/AtoP.v`:
    PARMv8-axiom refines PARMv8-view without certification.
  + Theorem `promising_to_axiomatic` in `src/equiv/PFtoA.v`:
    PARMv8-view without certification refines PARMv8-axiom.
    * `PFtoA1.v`: construction of axiomatic execution from promising execution
    * `PFtoA2.v`, `PFtoA3.v`: definitions and lemmas for main proof
    * `PFtoA4*.v`: proof for validity of constructed axiomatic execution
      * `PFtoA4SL.v`: simulation between promising and axiomatic execution
      * `PFtoA4OBR.v`, `PFtoA4OBW.v`, `PFtoA4FR.v`, `PFtoA4FOB.v`, `PFtoA4FP.v`: proof for "external" axiom
      * `PFtoA4Atomic.v`: proof for "atomic" axiom
  + Theorem `certified_exec_equivalent` in `src/lcertify/CertifyComplete.v`:
    PARMv8-view and PARMv8-view without certification are equivalent.

### Results of prior work

Theories included in the code but not directly related to what we did are:
- Theorem `certified_deadlock_free` in `src/lcertify/CertifyProgressRiscV.v`:
    Promising-RISC-V is deadlock-free.
- Theorem `certified_promise_correct` in `src/lcertify/FindCertify.v`:
    `find_and_certify` is correct.
    + Theorem `certified_promise_sound` in `src/lcertify/FindCertify.v`:
        Assume the thread configuration `<T, M>` is certified, and promising
        `p` leads to `<T', M'>`. Then `<T'. M'>` is certified if `p` is in
        `find_and_certify <T, M>`.
    + Theorem `certified_promise_complete` in `src/lcertify/FindCertify.v`:
        Assume the thread configuration `<T, M>` is certified, and promising
        `p` leads to `<T', M'>`. Then `p` is in `find_and_certify <T, M>` if
        `<T', M'>` is certified.

## Model Checker

This model checker is based on [rmem](https://github.com/rems-project/rmem), executable concurrency models for ARMv8, RISC-V, Power, and x86. In particular, this model checker basically uses the Promising model for ARMv8 and RISC-V by Pulte et al.

### Our extension

We extends the original checker to the PARMv8 model checker by supporting:

- ARMv8 instruction for persistency (i.e., DC CVAP)
- persistency views of PARMv8-view (i.e., VpReady, VpAsync, VpCommit)
- enumeration of states of when crash occurs at arbitrary point

### Build

```
cd model-checker
sudo apt install findutils libgmp-dev m4 perl pkg-config zlib1g-dev
opam repository add rems https://github.com/rems-project/opam-repository.git#opam2
opam install --deps-only .
ulimit -s unlimited
make -j MODE=opt ISA=AArch64
```

If it doesn't work, please read `model-checker/README.md` for more details.

### Run an example

We use our model checker to verify several representative persistent synchronization examples, including *all* examples presented in the paper (modulo architectural differences) and the "Atomic Persists" example in [Raad et al. (Example 3)](http://plv.mpi-sws.org/pog/paper.pdf) for modeling persistent transaction. All of these examples are in `parmv8-view-examples`.

To run one of examples:

```
./run.p [litmus file]
```

A Litmus file and the corresponding `shared_memory.txt` must be in the same directory.

For example, the following command is to enumerate every states that the **(COMMIT WEAK)** example can be reachable in case of either normal termination or an unexpected crash:

```
./run.p parmv8-view-examples/commit_weak/commit_weak.litmus
```

Then the output is printed out like below:

```
Test commit_weak Allowed
Shared-memory=0x0000000000001000 (data)/8; 0x0000000000001100 (commit)/8;
Memory-writes=
States 3
1     *>data=0x0; commit=0x0;  via "0"
1     :>data=0x2a; commit=0x0;  via "1;0"
2     :>data=0x2a; commit=0x1;  via "1;1;0"
NVM States 4
4     :>data=0x0; commit=0x0;
2     :>data=0x0; commit=0x1;
3     :>data=0x2a; commit=0x0;
2     :>data=0x2a; commit=0x1;
Deadlock states 1  via "2;0"
Unhandled exceptions 0
Ok
Condition exists (data=0x0 /\ commit=0x0)
Hash=98aca2103a7db7335c83aa17e3f47b8c
Observation commit_weak Sometimes 1 2 with deadlocks
Runtime: 0.034074 sec
```

`NVM States` in the middle is a list of all the reachable states of NVM when a program crashes while running or when the program ends. In this case, we can conclude that the desired invariant *"commit=1 ⇒ data=42"* doesn't hold because the state `data=0x0; commit=0x1;` denoting *"data=0 ∧ commit=1"* is on the list.

On the other hand, the output from the command `./run.p parmv8-view-examples/commit1/commit1.litmus` to check the **(COMMIT1)** example is like below:

```
Test commit1 Allowed
Shared-memory=0x0000000000001000 (data)/8; 0x0000000000001100 (commit)/8;
Memory-writes=
States 3
1     *>data=0x0; commit=0x0;  via "0"
1     :>data=0x2a; commit=0x0;  via "1;0"
1     :>data=0x2a; commit=0x1;  via "1;1;0;0"
NVM States 3
2     :>data=0x0; commit=0x0;
2     :>data=0x2a; commit=0x0;
1     :>data=0x2a; commit=0x1;
Unhandled exceptions 0
Ok
Condition exists (data=0x0 /\ commit=0x0)
Hash=d126aef71c01c0b3308c22bd06292d09
Observation commit1 Sometimes 1 2
Runtime: 0.033494 sec
```

We can conclude the invariant *"commit=1 ⇒ data=42"* holds in this case because there is no NVM state other than *data=42(0x2a)* when *commit=1*.

### Run all examples

You can run all PARMv8-view examples in `parmv8-view-examples` by executing this script:

```
./run_parmv8_all.p
```
