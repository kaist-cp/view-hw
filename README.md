# Promising-ARM/RISC-V

This is the supplementary material for POPL 2019 submission #23: "Promising-ARM/RISC-V: a simpler and faster operational memory model for ARMv8 and RISC-V"

## Build

- Requirement: [Coq 8.8](https://coq.inria.fr/download), Make, Rsync.

- Initialization

        cd promising-arm
        git submodule init
        git submodule update

- `make`: quickly build without checking the proofs.

- `./build.sh`: build with checking all the proofs.  It will incrementally copy the development to `.build` sub-directory, and then build there.

- Interactive Theorem Proving: use [ProofGeneral](https://proofgeneral.github.io/) or [CoqIDE](https://coq.inria.fr/download).
  Note that `make` creates `_CoqProject`, which is then used by ProofGeneral and CoqIDE. To use it:
    + ProofGeneral: use a recent version.
    + CoqIDE: configure it to use `_CoqProject`: `Edit` > `Preferences` > `Project`: change `ignored` to `appended to arguments`.

## References

### Model

- `lib` and `src/lib` contains libraries not necessarily related to relaxed-memory concurrency.

- `src/lib/Lang.v`: Definition of assembly-like language and its interpretation

- `src/promising/Promising.v`: Definition of Global-Promising-ARM/RISC-V (Definition 7.1)

- `src/axiomatic/Axiomatic.v`: Definition of ARMv8-Axiomatic (Section 7)

- `src/lcertify`: Thread-local certification of Promising-ARM/RISC-V (Section 3.5, formalisation work in progress)

- `src/certify`: Certification with ARMv8 store exclusives (Section 6, formalisation work in progress)

### Results

- Theorem `promising_to_promising_pf` in `src/promising/PtoPF.v`:
  The optimisation for exhaustive exploration is sound (Section 5.1),
  or equivalently, Global-Promising-ARM/RISC-V refines Optimised Global-Promising-ARM/RISC-V.

- Theorem `promising_pf_to_axiomatic` in `src/axiomatic/PFtoA.v`:
  Optimised Global-Promising-ARM/RISC-V refines ARMv8-Axiomatic (Theorem 7.3).

    + `PFtoA1.v`: construction of axiomatic execution from promising execution
    + `PFtoA2.v`, `PFtoA3.v`: definitions and lemmas for main proof
    + `PFtoA4*.v`: proof for validity of constructed axiomatic execution
        * `PFtoA4SL.v`: simulation between promising and axiomatic execution
        * `PFtoA4OBR.v`, `PFtoA4OBW.v`, `PFtoA4FR.v`: proof for "external" axiom
        * `PFtoA4Atomic.v`: proof for "atomic" axiom

- Theorem `axiomatic_to_promising` in `src/axiomatic/AtoP.v`:
  ARMv8-Axiomatic refines Global-Promising-ARM/RISC-V (Theorem 7.3).
