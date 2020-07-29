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

Set Implicit Arguments.


Lemma sim_machine_step
      vm1 vm2 pm1
      (WF: Machine.wf vm1)
      (VNOPROMISE: Machine.no_promise vm1)
      (STEP: Machine.step ExecUnit.view_step vm1 vm2)
      (SIM: Machine.equiv vm1 pm1)
      (NOPROMISE: Machine.no_promise pm1):
  exists pm2,
    <<STEP: rtc (Machine.step ExecUnit.step) pm1 pm2>> /\
    <<SIM: Machine.equiv vm2 pm2>> /\
    <<NOPROMISE: Machine.no_promise pm2>>.
Proof.
  inv SIM. inv STEP. rewrite MEM in *.
  generalize (TPOOL tid). intro TPEQ. rewrite TPEQ in *.
  inv STEP0. inv STEP. inv STATE; inv LOCAL; inv EVENT; ss; subst.
  - (* skip *)
    eexists (Machine.mk _ _). esplits.
    + econs; eauto. econs; ss; eauto.
      econs 1. econs. econs; econs; ss.
    + econs; ss.
      ii. rewrite TPOOL0. repeat rewrite IdMap.add_spec. repeat condtac; ss.
    + inv NOPROMISE. econs; ss. i.
      rewrite IdMap.add_spec in *. destruct (tid0 == tid); [inv FIND0|]; eapply PROMISES; eauto.
  - (* assign *)
    eexists (Machine.mk _ _). esplits.
    + econs; eauto. econs; ss; eauto.
      econs 1. econs. econs; econs; ss.
    + econs; ss.
      ii. rewrite TPOOL0. repeat rewrite IdMap.add_spec. repeat condtac; ss.
    + inv NOPROMISE. econs; ss. i.
      rewrite IdMap.add_spec in *. destruct (tid0 == tid); [inv FIND0|]; eapply PROMISES; eauto.
  - (* read *)
    inv STEP.
    eexists (Machine.mk _ _). esplits.
    + econs; eauto. econs; ss; eauto.
      econs 1. econs. econs; ss.
      { econs; ss. }
      econs 2; ss. econs; try exact LATEST; eauto.
    + econs; ss.
      ii. rewrite TPOOL0. repeat rewrite IdMap.add_spec. repeat condtac; ss.
    + inv NOPROMISE. econs; ss. i.
      rewrite IdMap.add_spec in *. destruct (tid0 == tid).
      * inv FIND0. apply PROMISES in FIND. ss.
      * eapply PROMISES. eauto.
  - (* write *)
    remember lc2. guardH Heqt.
    rewrite <- TPEQ in FIND. generalize FIND. intro NPROM.
    inv VNOPROMISE. eapply PROMISES in NPROM. clear PROMISES.
    inv STEP.

    assert (PROMISE: exists lcmid mem,
                      Local.promise
                        (ValA.val (sem_expr rmap eloc))
                        (ValA.val (sem_expr rmap eval))
                        ts tid lc1 (Machine.mem pm1) lcmid mem).
    { esplits. econs; eauto. }
    des.

    assert (FULFILL: Local.fulfill
                       (sem_expr rmap eloc)
                       (sem_expr rmap eval)
                       (ValA.mk _ 0 bot) ts tid lcmid mem lc2).
    { generalize FIND. intro PWF.
      inv WF. apply WF0 in PWF. inv PWF.
      inv LOCAL. inv COHMAX. inv COHMAX0; ss. rewrite COH in *.
      inv PROMISE. rewrite MEM0 in MEM2. inv MEM2.
      generalize MEM0. intro X. inv X.
      esplits. econs; eauto; ss.
      - econs; eauto; ss.
        + econs; ss.
        + inv MEM0. rewrite MEM in *.
          specialize (COH mloc). lia.
      - eapply Memory.append_spec; eauto. ss.
      - rewrite Promises.set_o. condtac; [|congr]. ss.
      - unguardH Heqt. subst.
        rewrite NPROM. rewrite Promises.unset_set_bot. ss.
    }
    des.

    eexists (Machine.mk _ _). esplits.
    + econs 2.
      { (* 1. promise *)
        rewrite TPEQ in FIND. econs; ss; eauto.
        - econs 2. instantiate (1 := Machine.mk _ mem). econs; eauto; ss.
        - ss.
      }
      econs 2; eauto.
      (* 2. fulfill *)
      econs; ss; cycle 1.
      * econs. econs. econs; ss.
        { econs 4; ss. }
        econs 3; eauto.
      * rewrite IdMap.add_spec. condtac; ss. congr.
    + rewrite <- Heqt. econs; ss; cycle 1.
      { inv PROMISE. rewrite MEM0 in MEM2. inv MEM2. ss. }
      ii. rewrite TPOOL0. repeat rewrite IdMap.add_spec. repeat condtac; ss.
    + inv NOPROMISE. econs; ss. i.
      rewrite IdMap.add_spec in *. destruct (tid0 == tid).
      * inv FIND0. inv PROMISE. inv FULFILL. ss.
        rewrite NPROM. rewrite Promises.unset_set_bot. ss.
      * rewrite IdMap.add_spec in *. destruct (tid0 == tid); ss. eapply PROMISES. eauto.
  - (* rmw *)
    remember lc2. guardH Heqt.
    rewrite <- TPEQ in FIND. generalize FIND. intro NPROM.
    inv VNOPROMISE. eapply PROMISES in NPROM. clear PROMISES.
    inv STEP.

    assert (PROMISE: exists lcmid mem,
                      Local.promise
                        (ValA.val (sem_expr rmap eloc))
                        (ValA.val vnew)
                        ts tid lc1 (Machine.mem pm1) lcmid mem).
    { esplits. econs; eauto. }
    des.

    assert (PRMW: Local.rmw (sem_expr rmap eloc) vold vnew old_ts ts tid lcmid mem lc2).
    { generalize FIND. intro PWF.
      inv WF. apply WF0 in PWF. inv PWF.
      inv LOCAL. inv COHMAX. inv COHMAX0; ss. rewrite COH0 in *.
      inv PROMISE. rewrite MEM0 in MEM2. inv MEM2. inv MEM0.
      esplits. econs; eauto.
      - exploit Memory.read_spec; eauto. lia.
      - rewrite <- H1 in *. ss.
      - eapply Memory.read_mon. ss.
      - econs; eauto; ss.
        + econs; ss.
        + rewrite MEM in *.
          specialize (COH0 mloc). lia.
      - eapply Memory.append_spec; eauto. ss.
      - ss. rewrite Promises.set_o. condtac; [|congr]. ss.
      - unguardH Heqt. subst.
        rewrite NPROM. rewrite Promises.unset_set_bot. ss.
    }
    des.

    eexists (Machine.mk _ _). esplits.
    + econs 2.
      { (* 1. promise *)
        rewrite TPEQ in FIND. econs; ss; eauto.
        - econs 2. instantiate (1 := Machine.mk _ mem). econs; eauto; ss.
        - ss.
      }
      econs 2; eauto.
      (* 2. rmw *)
      econs; ss; cycle 1.
      * econs. econs. econs; ss.
        { econs 5; eauto. }
        econs 4; eauto.
      * rewrite IdMap.add_spec. condtac; ss. congr.
    + rewrite <- Heqt. econs; ss; cycle 1.
      { inv PROMISE. rewrite MEM0 in MEM2. inv MEM2. ss. }
      ii. rewrite TPOOL0. repeat rewrite IdMap.add_spec. repeat condtac; ss.
    + inv NOPROMISE. econs; ss. i.
      rewrite IdMap.add_spec in *. destruct (tid0 == tid).
      * inv FIND0. inv PROMISE. inv PRMW. ss.
        rewrite NPROM. rewrite Promises.unset_set_bot. ss.
      * rewrite IdMap.add_spec in *. destruct (tid0 == tid); ss. eapply PROMISES. eauto.
  - (* rmw_failure *)
    inv STEP.
    eexists (Machine.mk _ _). esplits.
    + econs; eauto. econs; ss; eauto.
      econs 1. econs. econs; ss.
      { inversion RMW. inv H0. econs 6; ss. }
      econs 5; ss. econs; try exact LATEST; eauto.
    + econs; ss.
      ii. rewrite TPOOL0. repeat rewrite IdMap.add_spec. repeat condtac; ss.
    + inv NOPROMISE. econs; ss. i.
      rewrite IdMap.add_spec in *. destruct (tid0 == tid).
      * inv FIND0. apply PROMISES in FIND. ss.
      * eapply PROMISES. eauto.
  - (* dmb *)
    inv STEP.
    eexists (Machine.mk _ _). esplits.
    + econs; eauto. econs; ss; eauto.
      econs 1. econs. econs; ss.
      { econs; ss. }
      econs 6; ss. econs; try exact LATEST; eauto.
    + econs; ss.
      ii. rewrite TPOOL0. repeat rewrite IdMap.add_spec. repeat condtac; ss.
    + inv NOPROMISE. econs; ss. i.
      rewrite IdMap.add_spec in *. destruct (tid0 == tid).
      * inv FIND0. apply PROMISES in FIND. ss.
      * eapply PROMISES. eauto.
  - (* dowhile *)
    eexists (Machine.mk _ _). esplits.
    + econs; eauto. econs; ss; eauto.
      econs 1; ss. econs. econs; ss; econs; ss.
    + econs; ss.
      ii. rewrite TPOOL0. repeat rewrite IdMap.add_spec. repeat condtac; ss.
    + inv NOPROMISE. econs; ss. i.
      rewrite IdMap.add_spec in *. destruct (tid0 == tid); [inv FIND0|]; eapply PROMISES; eauto.

  Grab Existential Variables.
  auto. (* vold when rmw_failure *)
Qed.

Lemma sim_machine_rtc_step
      vm1 vm2 pm1
      (WF: Machine.wf vm1)
      (VNOPROMISE: Machine.no_promise vm1)
      (STEP: rtc (Machine.step ExecUnit.view_step) vm1 vm2)
      (SIM: Machine.equiv vm1 pm1)
      (NOPROMISE: Machine.no_promise pm1):
  exists pm2,
    <<STEP: rtc (Machine.step ExecUnit.step) pm1 pm2>> /\
    <<SIM: Machine.equiv vm2 pm2>> /\
    <<NOPROMISE: Machine.no_promise pm2>>.
Proof.
  revert WF SIM NOPROMISE. revert pm1. induction STEP; eauto. i.
  exploit sim_machine_step; eauto. i. des.
  exploit Machine.step_view_step_wf; eauto. intro WF0.
  exploit IHSTEP; try exact SIM0; ss.
  { eapply Machine.step_view_step_no_promise; eauto. }
  i. des.
  esplits; [etrans; eauto | exact SIM1 |]; eauto.
Qed.

Theorem view_to_promising
        p vm
        (EXEC: Machine.view_exec p vm):
  exists pm,
    <<STEP: Machine.exec p pm>> /\
    <<SIM: Machine.equiv vm pm>>.
Proof.
  inv EXEC.
  generalize (Machine.init_wf p). intro WF.
  generalize (Machine.init_no_promise p). intro NOPROMISE.
  exploit sim_machine_rtc_step; eauto; ss. i. des.
  esplits; eauto.
Qed.
