# Revamping Hardware Persistency Models

View-based and Axiomatic Persistency Models for Intel-x86 and ARMv8

## Build

- Requirement: [Coq 8.12.0](https://coq.inria.fr/download), Make, Rsync.

        apt install -y build-essential rsync opam
        opam init
        opam install coq.8.12.0

- `make`: quickly build without checking the proofs.

- `./build.sh`: build with checking all the proofs.  It will incrementally copy the development to
  `.build` sub-directory, and then build there.

- `./status.sh`: check if there is any `admit` in the proofs. (It will print a single result, which is tactic in the library used for development and has nothing to do with the proofs.)

- Interactive Theorem Proving: use [ProofGeneral](https://proofgeneral.github.io/) or
  [CoqIDE](https://coq.inria.fr/download).  Note that `make` creates `_CoqProject`, which is then
  used by ProofGeneral and CoqIDE. To use it:
    + ProofGeneral: use a recent version.
    + CoqIDE: configure it to use `_CoqProject`: `Edit` > `Preferences` > `Project`: change
      `ignored` to `appended to arguments`.

## Results of the existing work

- Our proofs are based on [the existing work](https://github.com/snu-sf/promising-arm) for ARMv8-view, originally named "Promising-ARMv8".

- Theories included in the code but not directly related to what we did are:
  + Theorem `certified_deadlock_free` in `src/lcertify/CertifyProgressRiscV.v`:
    Promising-RISC-V is deadlock-free.
  + Theorem `certified_promise_correct` in `src/lcertify/FindCertify.v`:
    `find_and_certify` is correct.
    * Theorem `certified_promise_sound` in `src/lcertify/FindCertify.v`:
      Assume the thread configuration `<T, M>` is certified, and promising
      `p` leads to `<T', M'>`. Then `<T'. M'>` is certified if `p` is in
      `find_and_certify <T, M>`.
    * Theorem `certified_promise_complete` in `src/lcertify/FindCertify.v`:
      Assume the thread configuration `<T, M>` is certified, and promising
      `p` leads to `<T', M'>`. Then `p` is in `find_and_certify <T, M>` if
      `<T', M'>` is certified.

## Our results

### Model

- `lib` and `src/lib` contains libraries not necessarily related to
  relaxed-memory concurrency and persistency.

- `src/lib/Lang.v`: Definition of assembly-like language and its interpretation for both x86 and ARMv8 (corresponding to the rules on Figure TODO)

- `src/promising/TsoPromising.v`: Definition of Px86-view and Px86-prom (corresponding to the rules on Figure TODO)

- `src/axiomatic/TsoAxiomatic.v`: Definition of Px86-axiom (corresponding to the rules on Figure TODO)

- `src/promising/Promising.v`: Definition of PARMv8-view without
  certification (corresponding to the rules on Figure TODO)

- `src/axiomatic/Axiomatic.v`: Definition of PARMv8-axiom (corresponding to the rules on Figure TODO)

- `src/lcertify`: Thread-local certification

### Results

- Theorem TODO: Equivalence between Px86-prom and Px86-axiom
  + Theorem `axiomatic_to_promising` in `src/equiv/TsoAtoP.v`:
    Px86-axiom refines Px86-prom.
  + Theorem `promising_to_axiomatic` in `src/equiv/TsoPFtoA.v`:
    Px86-prom refines Px86-axiom.
    * `TsoPFtoA1.v`: construction of axiomatic execution from promising execution
    * `TsoPFtoA2.v`, `TsoPFtoA3.v`: definitions and lemmas for main proof
    * `TsoPFtoA4*.v`: proof for validity of constructed axiomatic execution
      * `TsoPFtoA4SL.v`: simulation between promising and axiomatic execution
      * `TsoPFtoA4OBR.v`, `TsoPFtoA4OBW.v`, `TsoPFtoA4FR.v`, `TsoPFtoA4FOB.v`, `TsoPFtoA4FP.v`: proof for "external" axiom
  + Lemma TODO: Equivalence between Px86-prom and Px86-view
    * The paper says that after the x86-prom and x86-view have been proven to be equivalent
      and then extended to persistency, the proof in Coq was done right away.
    * Theorem `promising_to_view` in `src/equiv/TsoPFtoV.v`:
      Px86-prom refines Px86-view.
    * Theorem `view_to_promising` in `src/equiv/TsoVtoP.v`:
      Px86-view refines Px86-prom.

- Theorem TODO: Equivalence between PARMv8-view and PARMv8-axiom
  + Theorem `axiomatic_to_promising` in `src/equiv/AtoP.v`:
    PARMv8-axiom refines PARMv8-view without certification.
  + Theorem `promising_to_axiomatic` in `src/equiv/PFtoA.v`:
    PARMv8-view without certification refines PARMv8-axiom.
    * `PFtoA1.v`: construction of axiomatic execution from promising execution
    * `PFtoA2.v`, `PFtoA3.v`: definitions and lemmas for main proof
    * `PFtoA4*.v`: proof for validity of constructed axiomatic execution
      * `PFtoA4SL.v`: simulation between promising and axiomatic execution
      * `PFtoA4OBR.v`, `PFtoA4OBW.v`, `PFtoA4FR.v`: proof for "external" axiom
      * `PFtoA4Atomic.v`: proof for "atomic" axiom
  + Equivalence between PARMv8-view and PARMv8-view without certification
    + Theorem `certified_exec_equivalent` in `src/lcertify/CertifyComplete.v`:
      PARMv8-view and PARMv8-view without certification are equivalent.
