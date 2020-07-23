Require Import Relations.
Require Import EquivDec.
Require Import Equality.
Require Import List.
Require Import Bool.
Require Import Lia.
Require Import NArith.
Require Import PArith.
Require Import ZArith.
Require Import FMapPositive.
Require Import FSetPositive.
Require Import sflib.

Require Import PromisingArch.lib.Basic.
Require Import PromisingArch.lib.Order.
Require Import PromisingArch.lib.Time.
Require Import PromisingArch.lib.Lang.
Require Import PromisingArch.promising.CommonPromising.
Require Import PromisingArch.promising.TsoPromising.
Require Import PromisingArch.promising.TsoView.

Set Implicit Arguments.


Inductive sim_state (vstate:State.t (A:=unit)) (pstate:State.t (A:=unit)): Prop :=
| sim_state_intro
    (STMTS: vstate.(State.stmts) = pstate.(State.stmts))
    (RMAP: vstate.(State.rmap) = pstate.(State.rmap))
.
Hint Constructors sim_state.

Inductive sim_local (vlocal:TsoView.Local.t) (plocal:TsoPromising.Local.t): Prop :=
| sim_local_intro
    (COH: vlocal.(TsoView.Local.coh) = plocal.(TsoPromising.Local.coh))
    (VRN: vlocal.(TsoView.Local.vrn) = plocal.(TsoPromising.Local.vrn))
.
Hint Constructors sim_local.

Inductive sim_machine (vm:TsoView.Machine.t) (pm:TsoPromising.Machine.t): Prop :=
| sim_machine_intro
    (TPOOL: IdMap.Forall2
              (fun _ vsl psl =>
                <<STATE: sim_state (fst vsl) (fst psl)>> /\
                <<LOCAL: sim_local (snd vsl) (snd psl)>>)
              vm.(TsoView.Machine.tpool) pm.(TsoPromising.Machine.tpool))
    (MEM: vm.(TsoView.Machine.mem) = pm.(TsoPromising.Machine.mem))
.
Hint Constructors sim_machine.

Lemma sim_machine_step
      vm1 vm2 pm1
      (WF: TsoView.Machine.wf vm1)
      (STEP: TsoView.Machine.step TsoView.ExecUnit.step vm1 vm2)
      (SIM: sim_machine vm1 pm1)
      (NOPROMISE: TsoPromising.Machine.no_promise pm1):
  exists pm2,
    <<STEP: rtc (TsoPromising.Machine.step TsoPromising.ExecUnit.step) pm1 pm2>> /\
    <<SIM: sim_machine vm2 pm2>> /\
    <<NOPROMISE: TsoPromising.Machine.no_promise pm2>>.
Proof.
  inv SIM. inv STEP. generalize (TPOOL tid). intro TP. inv TP; rewrite FIND in *; ss.
  inv H0. destruct st1 as [stmts1 rmap1].
  destruct b as [[pstmts1 prmap1] plc1].
  symmetry in H. des; ss.
  inv STATE. ss. subst. rename LOCAL into SIM_LOCAL.
  inv STEP0. inv STEP. inv STATE; inv LOCAL; inv EVENT; ss; subst.
  - (* skip *)
    eexists (TsoPromising.Machine.mk _ _). esplits.
    + econs; eauto. econs; ss; eauto.
      econs 1. econs. econs; econs; ss.
    + econs; ss; cycle 1.
      { rewrite <- MEM. rewrite MEM0. ss. }
      ii. rewrite TPOOL0. repeat rewrite IdMap.add_spec. repeat condtac; ss.
      econs. splits; ss.
    + inv NOPROMISE. econs; ss. i.
      rewrite IdMap.add_spec in *. destruct (tid0 == tid).
      * apply PROMISES in H. inv FIND0. ss.
      * eapply PROMISES. eauto.
  - (* assign *)
    eexists (TsoPromising.Machine.mk _ _). esplits.
    + econs; eauto. econs; ss; eauto.
      econs 1. econs. econs; econs; ss.
    + econs; ss; cycle 1.
      { rewrite <- MEM. rewrite MEM0. ss. }
      ii. rewrite TPOOL0. repeat rewrite IdMap.add_spec. repeat condtac; ss.
      econs. splits; ss.
    + inv NOPROMISE. econs; ss. i.
      rewrite IdMap.add_spec in *. destruct (tid0 == tid).
      * apply PROMISES in H. inv FIND0. ss.
      * eapply PROMISES. eauto.
  - (* read *)
    inv SIM_LOCAL. inv STEP. rewrite COH, VRN, MEM in *.
    eexists (TsoPromising.Machine.mk _ _). esplits.
    + econs; eauto. econs; ss; eauto.
      econs 1. econs. econs; ss.
      { econs; ss. }
      econs 2; ss. econs; try exact LATEST; eauto.
    + econs; ss.
      ii. rewrite TPOOL0. repeat rewrite IdMap.add_spec. repeat condtac; ss.
      econs. splits; ss.
    + inv NOPROMISE. econs; ss. i.
      rewrite IdMap.add_spec in *. destruct (tid0 == tid).
      * apply PROMISES in H. inv FIND0. ss.
      * eapply PROMISES. eauto.
  - (* write *)
    inv SIM_LOCAL. inv STEP. rewrite COH, VRN, MEM in *.

    assert (PROMISE: exists plc2 mem,
                      TsoPromising.Local.promise
                        (ValA.val (sem_expr prmap1 eloc))
                        (ValA.val (sem_expr prmap1 eval))
                        ts tid plc1 (TsoPromising.Machine.mem pm1) plc2 mem).
    { esplits. econs; eauto. }
    des.

    assert (FULFILL: exists plc3,
                      TsoPromising.Local.fulfill
                        (sem_expr prmap1 eloc)
                        (sem_expr prmap1 eval)
                        (ValA.mk _ 0 bot) ts tid plc2 mem plc3).
    { inv WF. apply WF0 in FIND. inv FIND.
      inv LOCAL. inv COHMAX. inv COHMAX0; ss. rewrite COH in *.
      inv PROMISE. rewrite MEM0 in MEM2. inv MEM2.
      generalize MEM0. intro X. inv X.
      esplits. econs; eauto.
      - econs; eauto; ss.
        + econs; ss.
        + inv MEM0. rewrite MEM in *.
          specialize (COH0 mloc). lia.
      - eapply Memory.append_spec; eauto. ss.
      - ss. rewrite Promises.set_o. condtac; [|congr]. ss.
    }
    des.

    eexists (TsoPromising.Machine.mk _ _). esplits.
    + econs 2.
      { (* 1. promise *)
        econs; ss; eauto.
        - econs 2. instantiate (1 := TsoPromising.Machine.mk _ mem). econs; eauto; ss.
        - ss.
      }
      econs 2; eauto.
      (* 2. fulfill *)
      econs; ss; cycle 1.
      * econs. econs. econs; ss.
        { econs 4; ss. }
        econs 3; eauto.
      * rewrite IdMap.add_spec. condtac; ss. congr.
    + econs; ss; cycle 1.
      { inv PROMISE. rewrite MEM0 in MEM2. inv MEM2. ss. }
      ii. rewrite TPOOL0. repeat rewrite IdMap.add_spec. repeat condtac; ss.
      econs. splits; ss.
      inv PROMISE. inv FULFILL. econs; ss.
    + inv NOPROMISE. econs; ss. i.
      rewrite IdMap.add_spec in *. destruct (tid0 == tid).
      * apply PROMISES in H. inv FIND0. inv PROMISE. inv FULFILL. ss.
        rewrite H. funext. i.
        unfold Promises.unset, Promises.set. destruct (Promises.id_of_time ts); ss.
        funtac.
      * rewrite IdMap.add_spec in *. destruct (tid0 == tid); ss. eapply PROMISES. eauto.
  - (* rmw *)
    inv SIM_LOCAL. inv STEP. rewrite COH, VRN, MEM in *.

    assert (PROMISE: exists plc2 mem,
                      TsoPromising.Local.promise
                        (ValA.val (sem_expr prmap1 eloc))
                        (ValA.val vnew)
                        ts tid plc1 (TsoPromising.Machine.mem pm1) plc2 mem).
    { esplits. econs; eauto. }
    des.

    assert (PRMW: exists plc3,
                   TsoPromising.Local.rmw
                     (sem_expr prmap1 eloc)
                     vold vnew old_ts ts tid plc2 mem plc3).
    { inv WF. apply WF0 in FIND. inv FIND.
      inv LOCAL. inv COHMAX. inv COHMAX0; ss. rewrite COH in *.
      inv PROMISE. rewrite MEM0 in MEM2. inv MEM2. inv MEM0.
      esplits. econs; eauto.
      - exploit Memory.read_spec; eauto. lia.
      - rewrite <- H2 in *. ss.
      - eapply Memory.read_mon. ss.
      - econs; eauto; ss.
        + econs; ss.
        + rewrite MEM in *.
          specialize (COH1 mloc). lia.
      - eapply Memory.append_spec; eauto. ss.
      - ss. rewrite Promises.set_o. condtac; [|congr]. ss.
    }
    des.

    eexists (TsoPromising.Machine.mk _ _). esplits.
    + econs 2.
      { (* 1. promise *)
        econs; ss; eauto.
        - econs 2. instantiate (1 := TsoPromising.Machine.mk _ mem). econs; eauto; ss.
        - ss.
      }
      econs 2; eauto.
      (* 2. rmw *)
      econs; ss; cycle 1.
      * econs. econs. econs; ss.
        { econs 5; eauto. }
        econs 4; eauto.
      * rewrite IdMap.add_spec. condtac; ss. congr.
    + econs; ss; cycle 1.
      { inv PROMISE. rewrite MEM0 in MEM2. inv MEM2. ss. }
      ii. rewrite TPOOL0. repeat rewrite IdMap.add_spec. repeat condtac; ss.
      econs. splits; ss.
      inv PROMISE. inv PRMW. econs; ss.
    + inv NOPROMISE. econs; ss. i.
      rewrite IdMap.add_spec in *. destruct (tid0 == tid).
      * apply PROMISES in H. inv FIND0. inv PROMISE. inv PRMW. ss.
        rewrite H. funext. i.
        unfold Promises.unset, Promises.set. destruct (Promises.id_of_time ts); ss.
        funtac.
      * rewrite IdMap.add_spec in *. destruct (tid0 == tid); ss. eapply PROMISES. eauto.
  - (* rmw_failure *)
    inv SIM_LOCAL. inv STEP. rewrite COH, VRN, MEM in *.
    eexists (TsoPromising.Machine.mk _ _). esplits.
    + econs; eauto. econs; ss; eauto.
      econs 1. econs. econs; ss.
      { inversion RMW. inv H0. econs 6; ss. }
      econs 5; ss. econs; try exact LATEST; eauto.
    + econs; ss.
      ii. rewrite TPOOL0. repeat rewrite IdMap.add_spec. repeat condtac; ss.
      econs. splits; ss.
    + inv NOPROMISE. econs; ss. i.
      rewrite IdMap.add_spec in *. destruct (tid0 == tid).
      * apply PROMISES in H. inv FIND0. ss.
      * eapply PROMISES. eauto.
  - (* dmb *)
    inv SIM_LOCAL. inv STEP. rewrite COH, VRN, MEM in *.
    eexists (TsoPromising.Machine.mk _ _). esplits.
    + econs; eauto. econs; ss; eauto.
      econs 1. econs. econs; ss.
      { econs; ss. }
      econs 6; ss. econs; eauto.
      inv COHMAX. rewrite COH in *. econs; eauto.
    + econs; ss.
      ii. rewrite TPOOL0. repeat rewrite IdMap.add_spec. repeat condtac; ss.
      econs. splits; ss.
    + inv NOPROMISE. econs; ss. i.
      rewrite IdMap.add_spec in *. destruct (tid0 == tid).
      * apply PROMISES in H. inv FIND0. ss.
      * eapply PROMISES. eauto.
  - (* dowhile *)
    eexists (TsoPromising.Machine.mk _ _). esplits.
    + econs; eauto. econs; ss; eauto.
      econs 1; ss. econs. econs; ss; econs; ss.
    + econs; ss; cycle 1.
      { rewrite <- MEM. rewrite MEM0. ss. }
      ii. rewrite TPOOL0. repeat rewrite IdMap.add_spec. repeat condtac; ss.
      econs. splits; ss.
    + inv NOPROMISE. econs; ss. i.
      rewrite IdMap.add_spec in *. destruct (tid0 == tid).
      * apply PROMISES in H. inv FIND0. ss.
      * eapply PROMISES. eauto.

  Grab Existential Variables.
  auto. (* vold when rmw_failure *)
Qed.

Lemma sim_machine_rtc_step
      vm1 vm2 pm1
      (WF: TsoView.Machine.wf vm1)
      (STEP: rtc (TsoView.Machine.step ExecUnit.step) vm1 vm2)
      (SIM: sim_machine vm1 pm1)
      (NOPROMISE: TsoPromising.Machine.no_promise pm1):
  exists pm2,
    <<STEP: rtc (TsoPromising.Machine.step TsoPromising.ExecUnit.step) pm1 pm2>> /\
    <<SIM: sim_machine vm2 pm2>> /\
    <<NOPROMISE: TsoPromising.Machine.no_promise pm2>>.
Proof.
  revert WF SIM NOPROMISE. revert pm1. induction STEP; eauto. i.
  exploit sim_machine_step; eauto. i. des.
  exploit Machine.step_step_wf; eauto. intro WF0.
  exploit IHSTEP; try exact SIM0; ss. i. des.
  esplits; [etrans; eauto | exact SIM1 |]; eauto.
Qed.

Theorem promising_to_promising_pf
        p vm
        (EXEC: TsoView.Machine.exec p vm):
  exists pm,
    <<STEP: TsoPromising.Machine.exec p pm>> /\
    <<SIM: sim_machine vm pm>>.
Proof.
  inv EXEC.
  generalize (Machine.init_wf p). intro WF.
  generalize (Machine.init_no_promise p). intro NOPROMISE.
  exploit sim_machine_rtc_step; eauto; cycle 1.
  { i. des. esplits; eauto. }
  econs; ss. ii. repeat rewrite IdMap.map_spec.
  destruct (IdMap.find id p); ss. econs; ss.
Qed.
