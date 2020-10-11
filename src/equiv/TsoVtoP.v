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
      m1 m2
      (WF: Machine.wf m1)
      (NOPROMISE: Machine.no_promise m1)
      (STEP: Machine.step ExecUnit.view_step m1 m2):
  rtc (Machine.step ExecUnit.step) m1 m2.
Proof.
  inv STEP. inv STEP0. inv STEP. inv STATE; inv LOCAL; inv EVENT; ss; subst.
  - (* skip *)
    econs; eauto. econs; ss; eauto.
    econs 1. econs. econs; try econs; ss.
  - (* assign *)
    econs; eauto. econs; ss; eauto.
    econs 1. econs. econs; try econs; ss.
  - (* read *)
    inv STEP.
    econs; eauto. econs; ss; eauto.
    econs 1. econs. econs; ss.
    { econs; ss. }
    econs 2; ss. econs; try exact LATEST; eauto.
  - (* write *)
    remember lc2. guardH Heqt.
    generalize FIND. intro NPROM. inv NOPROMISE. eapply PROMISES in NPROM. clear PROMISES.
    inv STEP.

    assert (PROMISE: exists lcmid,
                      Local.promise
                        (ValA.val (sem_expr rmap eloc))
                        (ValA.val (sem_expr rmap eval))
                        ts tid lc1 (Machine.mem m1) lcmid (Machine.mem m2)).
    { esplits. econs; eauto. }
    des.

    assert (FULFILL: Local.fulfill
                       (sem_expr rmap eloc)
                       (sem_expr rmap eval)
                       (ValA.mk _ 0 bot) ts tid lcmid (Machine.mem m2) lc2).
    { generalize FIND. intro PWF.
      inv WF. apply WF0 in PWF. inv PWF.
      inv LOCAL. inv COHMAX. inv COHMAX0; ss. rewrite COH in *.
      inv PROMISE. inv MEM2.
      esplits. econs; eauto; ss.
      - econs; eauto; ss.
        specialize (COH x). lia.
      - eapply Memory.append_spec; eauto. ss.
      - rewrite Promises.set_o. condtac; [|congr]. ss.
      - unguardH Heqt. subst.
        rewrite NPROM. rewrite Promises.unset_set_bot. ss.
    }
    des.

    econs 2.
    { (* 1. promise *)
      instantiate (1 := Machine.mk _ (Machine.mem m2)).
      econs; ss; eauto. econs 2. econs; eauto; ss.
    }
    econs 2; eauto.
    (* 2. fulfill *)
    econs; ss; cycle 1.
    + econs. econs. econs; ss.
      { econs 4; ss. }
      econs 3; eauto.
    + rewrite IdMap.add_add.
      rewrite Heqt in TPOOL. rewrite TPOOL. ss.
    + rewrite IdMap.add_spec. condtac; ss. congr.
  - (* rmw *)
    remember lc2. guardH Heqt.
    generalize FIND. intro NPROM. inv NOPROMISE. eapply PROMISES in NPROM. clear PROMISES.
    inv STEP.

    assert (PROMISE: exists lcmid,
                      Local.promise
                        (ValA.val (sem_expr rmap eloc))
                        (ValA.val vnew)
                        ts tid lc1 (Machine.mem m1) lcmid (Machine.mem m2)).
    { esplits. econs; eauto. }
    des.

    assert (PRMW: Local.rmw (sem_expr rmap eloc) vold vnew old_ts ts tid lcmid (Machine.mem m2) lc2).
    { generalize FIND. intro PWF.
      inv WF. apply WF0 in PWF. inv PWF.
      inv LOCAL. inv COHMAX. inv COHMAX0; ss. rewrite COH0 in *.
      inv PROMISE. inv MEM.
      esplits. econs; eauto.
      - exploit Memory.read_spec; eauto. lia.
      - rewrite <- H1 in *. ss.
      - eapply Memory.read_mon. ss.
      - econs; eauto; ss.
        specialize (COH0 x). lia.
      - eapply Memory.append_spec; eauto. ss.
      - ss. rewrite Promises.set_o. condtac; [|congr]. ss.
      - unguardH Heqt. subst.
        rewrite NPROM. rewrite Promises.unset_set_bot. ss.
    }
    des.

    econs 2.
    { (* 1. promise *)
      instantiate (1 := Machine.mk _ (Machine.mem m2)).
      econs; ss; eauto. econs 2. econs; eauto; ss.
    }
    econs 2; eauto.
    (* 2. rmw *)
    econs; ss; cycle 1.
    + econs. econs. econs; ss.
      { econs 5; eauto. }
      econs 4; eauto.
    + rewrite IdMap.add_add.
      rewrite Heqt in TPOOL. rewrite TPOOL. ss.
    + rewrite IdMap.add_spec. condtac; ss. congr.
  - (* rmw_failure *)
    inv STEP.
    econs; eauto. econs; ss; eauto.
    econs 1. econs. econs; ss.
    { inversion RMW. inv H0. econs 6; ss. }
    econs 5; ss. econs; try exact LATEST; eauto.
  - (* mfence *)
    inv STEP.
    econs; eauto. econs; ss; eauto.
    econs 1. econs. econs; ss.
    { econs; ss. }
    econs 6; ss. econs; try exact LATEST; eauto.
  - (* sfence *)
    inv STEP.
    econs; eauto. econs; ss; eauto.
    econs 1. econs. econs; ss.
    { econs; ss. }
    econs 7; ss. econs; try exact LATEST; eauto.
  - (* dowhile *)
    econs; eauto. econs; ss; eauto.
    econs 1; ss. econs. econs; ss; econs; ss.
  - (* flushopt *)
    inv STEP.
    econs; eauto. econs; ss; eauto.
    econs 1; ss. econs. econs; ss; [econs | econs 9]; ss. econs; ss.
    inv COHMAX_CL. econs; ss.
  - (* flush *)
    inv STEP.
    econs; eauto. econs; ss; eauto.
    econs 1; ss. econs. econs; ss; [econs | econs 8]; ss. econs; eauto; ss.
Qed.

Lemma sim_machine_rtc_step
      m1 m2
      (WF: Machine.wf m1)
      (NOPROMISE: Machine.no_promise m1)
      (STEP: rtc (Machine.step ExecUnit.view_step) m1 m2):
  rtc (Machine.step ExecUnit.step) m1 m2.
Proof.
  revert WF NOPROMISE. induction STEP; eauto. i.
  exploit sim_machine_step; eauto. i. des.
  exploit Machine.step_view_step_wf; eauto. intro WF0.
  exploit IHSTEP; eauto.
  { eapply Machine.step_view_step_no_promise; eauto. }
  etrans; eauto.
Qed.

Theorem view_to_promising
        p m
        (EXEC: Machine.view_exec p m):
  Machine.exec p m.
Proof.
  inv EXEC.
  generalize (Machine.init_wf p). intro WF.
  generalize (Machine.init_no_promise p). intro NOPROMISE.
  exploit sim_machine_rtc_step; eauto. i. des. subst.
  exploit Machine.rtc_step_view_step_no_promise; eauto.
Qed.
