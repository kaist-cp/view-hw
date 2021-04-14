<!---
This file was generated from `meta.yml`, please do not edit manually.
Follow the instructions on https://github.com/coq-community/templates to regenerate.
--->

# View-based semantics for hardware

[![CI][docker-action-shield]][docker-action-link]

[docker-action-shield]: https://github.com/kaist-cp/view-hw/workflows/Docker%20CI/badge.svg?branch=master
[docker-action-link]: https://github.com/kaist-cp/view-hw/actions?query=workflow:"Docker%20CI"


Related publications:

- Christopher Pulte, Jean Pichon-Pharabod, Jeehoon Kang, Sung-Hwan Lee, Chung-Kil Hur.  Promising-ARM/RISC-V: a simpler and faster operational concurrency model.  PLDI 2019.

  This repository is a fork of [this paper's artifact](https://github.com/snu-sf/promising-arm).

- Kyeongmin Cho, Sung-Hwan Lee, Azalea Raad, and Jeehoon Kang.  Revamping Hardware Persistency Models: View-Based and Axiomatic Persistency Models for Intel-x86 and Armv8.  PLDI 2021 (conditionally accepted).


## Installation

We assume you use **Ubuntu 20.04** and **Coq 8.13.1 or later**.


### Requirements

- [opam](https://opam.ocaml.org/)
  ```
  sudo apt install -y build-essential rsync opam
  opam init
  opam switch create 4.10.0  # or later. If your system OCaml version is >= 4.10.0, you can use it.
  eval $(opam env)
  opam update
  ```

- [Coq 8.13.1](https://coq.inria.fr/)
  ```
  opam install coq.8.13.1
  ```


### Build

- `make -j`: quickly build without checking the proofs.

- `./build.sh`: build with checking all the proofs.  It will incrementally copy the development to `.build` sub-directory, and then build there.

- `./status.sh`: check if there is any `admit` in the proofs. (It will print a single result, which is tactic in the library used for development and has nothing to do with the proofs.)

- Interactive Theorem Proving: use [ProofGeneral](https://proofgeneral.github.io/) or
  [CoqIDE](https://coq.inria.fr/download).  Note that `make` creates `_CoqProject`, which is then
  used by ProofGeneral and CoqIDE. To use it:
    + ProofGeneral: use a recent version.
    + CoqIDE: configure it to use `_CoqProject`: `Edit` > `Preferences` > `Project`: change
      `ignored` to `appended to arguments`.


### Our results

Our proofs are based on [a prior work](https://github.com/snu-sf/promising-arm) for Armv8-view, originally named "Promising-ARMv8". The prior work contains:

- the proof of the equivalence between Armv8-view and Armv8-axiom
- some proofs about certification

We extend the existing proofs for Armv8 to persistency. In addition, we newly define Px86-view/Px86-axiom and prove the theorems of it mentioned in the paper.


#### Model

- `lib`(open source) and `src/lib` contain libraries not necessarily related to relaxed-memory concurrency and persistency.

- `src/lib/Lang.v`: Definition of assembly-like language and its interpretation for both x86 and Armv8 (corresponding to Figure 13)

- `src/promising/TsoPromising.v`: Definition of Px86-view and Px86-prom (corresponding to Figure 11 and 12)

- `src/axiomatic/TsoAxiomatic.v`: Definition of Px86-axiom (corresponding to Figure 7)

- `src/promising/Promising.v`: Definition of PArmv8-view without
  certification (corresponding to Figure 14, 15 and 16)

- `src/axiomatic/Axiomatic.v`: Definition of PArmv8-axiom (corresponding to Figure 9)

- `src/lcertify`: Thread-local certification

#### Results

- Background definitions

    + A **behavior** is either (1) post-crash image of memory or (2) non-crash terminal image of memory.
      This is the simplest possible definition of behaviors for NVM; we may refine the concept by incorporating I/O or other kinds of externally visible interactions.
      We believe it is straightforward to incorporate such interactions in the definition of behaviors as future work.
    + The **behaviors** of a program is (1) the set of **post-crash memories** and (2) the set of **non-crash terminal memories** resulting from an execution of the program.
    + A behavior is **allowed** in a program iff the behavior---either post-crash or non-crash terminal image---is in the corresponding set of memories of the program's behaviors.
    + A model, say X, **refines** another model, say Y, iff the set of behaviors according to X, is a subset of that according to Y.
    + A model, say X, is **equivalent** to another model, say Y, iff the set of behaviors according to X coincides with that according to Y.

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

- Theorem 6.2: Equivalence between PArmv8-view and PArmv8-axiom
  + Theorem `axiomatic_to_promising` in `src/equiv/AtoP.v`:
    PArmv8-axiom refines PArmv8-view without certification.
  + Theorem `promising_to_axiomatic` in `src/equiv/PFtoA.v`:
    PArmv8-view without certification refines PArmv8-axiom.
    * `PFtoA1.v`: construction of axiomatic execution from promising execution
    * `PFtoA2.v`, `PFtoA3.v`: definitions and lemmas for main proof
    * `PFtoA4*.v`: proof for validity of constructed axiomatic execution
    * `PFtoA4SL.v`: simulation between promising and axiomatic execution
    * `PFtoA4OBR.v`, `PFtoA4OBW.v`, `PFtoA4FR.v`, `PFtoA4FOB.v`, `PFtoA4FP.v`: proof for "external" axiom
    * `PFtoA4Atomic.v`: proof for "atomic" axiom
  + Theorem `certified_exec_equivalent` in `src/lcertify/CertifyComplete.v`:
    PArmv8-view and PArmv8-view without certification are equivalent.

### Results of prior work

Theorems included in the code but not directly related to what we did are:
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
