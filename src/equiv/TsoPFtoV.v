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
Require Import HahnRelationsBasic.

Require Import PromisingArch.lib.Basic.
Require Import PromisingArch.lib.Order.
Require Import PromisingArch.lib.Time.
Require Import PromisingArch.lib.Lang.
Require Import PromisingArch.promising.CommonPromising.
Require Import PromisingArch.promising.TsoPromising.

Set Implicit Arguments.

(* TODO: move *)
Require Import ClassicalChoice.

(* TODO: move *)
Inductive opt_rel3 A B C (rel: A -> B -> C -> Prop): forall (a:option A) (b:option B) (c:option C), Prop :=
| opt_rel3_None:
    opt_rel3 rel None None None
| opt_rel3_Some
    a b c
    (REL: rel a b c):
    opt_rel3 rel (Some a) (Some b) (Some c)
.
Hint Constructors opt_rel3.

Inductive sim_memory (n: nat) (mem_pf mem_v: Memory.t): Prop :=
| sim_memory_intro
    mem_post
    (MEMORY: mem_pf = mem_v ++ mem_post)
    (LENGTH: List.length mem_v = n)
.
Hint Constructors sim_memory.

Inductive sim_local (n: nat) (lc_pf lc_v: Local.t): Prop :=
| sim_local_intro
    (COH: lc_pf.(Local.coh) = lc_v.(Local.coh))
    (VRN: lc_pf.(Local.vrn) = lc_v.(Local.vrn))
    (LPER: lc_pf.(Local.lper) = lc_v.(Local.lper))
    (PER: lc_pf.(Local.per) = lc_v.(Local.per))
    (PROMISES_PF: forall ts (PROMISE: Promises.lookup ts lc_pf.(Local.promises) = true), ts > n)
    (PROMISES_V: lc_v.(Local.promises) = fun _ => false)
.
Hint Constructors sim_local.

Inductive sim_sl (n: nat) (sl_pf sl_v: State.t (A:=unit) * Local.t): Prop :=
| sim_sl_intro
    (STATE: fst sl_pf = fst sl_v)
    (LOCAL: sim_local n (snd sl_pf) (snd sl_v))
.
Hint Constructors sim_sl.

Inductive sim (n: nat) (m_pf m_v: Machine.t): Prop :=
| sim_intro
    (TPOOL: forall tid, opt_rel (sim_sl n)
                           (IdMap.find tid m_pf.(Machine.tpool))
                           (IdMap.find tid m_v.(Machine.tpool)))
    (MEMORY: sim_memory n m_pf.(Machine.mem) m_v.(Machine.mem))
.
Hint Constructors sim.

Definition promises_le (tid: Id.t) (promises: Promises.t) (mem: Memory.t): Prop :=
  forall ts (LOOKUP: Promises.lookup ts promises = true),
  exists loc val, Memory.get_msg ts mem = Some (Msg.mk loc val tid).

Inductive promises_wf (n: nat) (m: Machine.t): Prop :=
| promises_wf_intro
    (SOUND: forall tid st lc
              (FIND: IdMap.find tid m.(Machine.tpool) = Some (st, lc)),
        <<LE: promises_le tid lc.(Local.promises) m.(Machine.mem)>>)
    (COMPLETE: forall ts loc val tid
           (GT: n < ts)
           (GET: Memory.get_msg ts m.(Machine.mem) = Some (Msg.mk loc val tid)),
        exists st lc,
          (<<FIND: IdMap.find tid m.(Machine.tpool) = Some (st, lc)>>) /\
          (<<IN: Promises.lookup ts lc.(Local.promises) = true>>))
.
Hint Constructors promises_wf.



Lemma sim_memory_latest
      n mem_pf mem_v loc from to
      (SIM: sim_memory n mem_pf mem_v)
      (TO: to <= n)
      (LATEST: Memory.latest loc from to mem_pf):
  Memory.latest loc from to mem_v.
Proof.
  inv SIM. ii. exploit LATEST; eauto.
  rewrite nth_error_app1; ss. nia.
Qed.

Lemma sim_memory_read
      n mem_pf mem_v loc ts val
      (SIM: sim_memory n mem_pf mem_v)
      (TS: ts <= n)
      (READ: Memory.read loc ts mem_pf = val):
  Memory.read loc ts mem_v = val.
Proof.
  inv SIM. unfold Memory.read in *.
  destruct ts; ss.
  des_ifs; rewrite nth_error_app1 in *; try nia; congr.
Qed.

Lemma sim_memory_exclusive
      n mem_pf mem_v tid loc val from
      (SIM: sim_memory n mem_pf mem_v)
      (LENGTH: length mem_pf > n)
      (FROM: from < n + 1)
      (EXCLUSIVE: Memory.exclusive tid loc from (n + 1) mem_pf):
  Memory.exclusive tid loc from (n + 1) (mem_v ++ [Msg.mk loc val tid]).
Proof.
  inv SIM. ii. des.
  exploit EXCLUSIVE; eauto.
  destruct (classic (ts = length mem_v)).
  { subst. rewrite nth_error_app2 in MSG; try nia.
    rewrite Nat.sub_diag in MSG. ss. inv MSG. rewrite <- H1 in *. ss. }
  rewrite nth_error_app1 in *; try nia. ss.
Qed.

Lemma next_fulfill_exists
      n m1 m
      (EXEC1: Machine.state_exec m1 m)
      (PROMISES1: promises_wf n m1):
  exists tid st1 lc1 st2 lc2,
    (<<FIND: IdMap.find tid m1.(Machine.tpool) = Some (st1, lc1)>>) /\
    (<<STEPS: rtc (ExecUnit.state_step tid)
                  (ExecUnit.mk st1 lc1 m1.(Machine.mem))
                  (ExecUnit.mk st2 lc2 m1.(Machine.mem))>>) /\
    (exists st3 lc3 ord vloc vval res m2,
        (<<STEP_ST: State.step (Event.write false ord vloc vval res) st2 st3>>) /\
        (<<STEP_LC: Local.fulfill vloc vval res (n + 1) tid lc2 m1.(Machine.mem) lc3>>) /\
        (<<MACHINE2: m2 = Machine.mk (IdMap.add tid (st3, lc3) m1.(Machine.tpool)) m1.(Machine.mem)>>) /\
        (<<EXEC2: Machine.state_exec m2 m>>) /\
        (<<PROMISES2: promises_wf (n + 1) m2>>)) \/
    (exists st3 lc3 ordr ordw vloc vold vnew old_ts m2,
        (<<STEP_ST: State.step (Event.rmw ordr ordw vloc vold vnew) st2 st3>>) /\
        (<<STEP_LC: Local.rmw vloc vold vnew old_ts (n + 1) tid lc2 m1.(Machine.mem) lc3>>) /\
        (<<MACHINE2: m2 = Machine.mk (IdMap.add tid (st3, lc3) m1.(Machine.tpool)) m1.(Machine.mem)>>) /\
        (<<EXEC2: Machine.state_exec m2 m>>) /\
        (<<PROMISES2: promises_wf (n + 1) m2>>)).
Proof.
Admitted.

Lemma sim_step
      n
      e tid lc1_pf lc2_pf mem_pf
      lc1_v mem_v
      (LOCAL1: sim_local n lc1_pf lc1_v)
      (MEMORY: sim_memory n mem_pf mem_v)
      (WF1_PF: Local.wf tid mem_pf lc1_pf)
      (WF1_V: Local.wf tid mem_v lc1_v)
      (STEP_PF: Local.step e tid mem_pf lc1_pf lc2_pf):
  (exists lc2_v,
      (<<STEP_V: Local.view_step e tid mem_v mem_v lc1_v lc2_v>>) /\
      (<<LOCAL2: sim_local n lc2_pf lc2_v>>) /\
      (<<PROMISES_PF: lc2_pf.(Local.promises) = lc1_pf.(Local.promises)>>)) \/
  (exists loc,
      <<COH: (lc2_pf.(Local.coh) loc).(View.ts) > n>>).
Proof.
  destruct lc1_pf as [coh_pf vrn_pf lper_pf per_pf promises_pf].
  destruct lc1_v as [coh_v vrn_v lper_v per_v promises_v].
  dup LOCAL1. inv LOCAL0. ss. subst.
  inv STEP_PF.
  - (* internal *)
    left. esplits; eauto. econs 1; ss.
  - (* read *)
    destruct (classic (ts <= n)).
    + inv STEP. ss. left. esplits.
      * econs 2; eauto. econs; s; eauto.
        { eapply sim_memory_latest; eauto.
          inv WF1_V. inv MEMORY; ss. }
        { eapply sim_memory_read; eauto. }
      * eauto.
      * ss.
    + inv STEP. ss. right. exists vloc.(ValA.val).
      rewrite fun_add_spec_eq. ss.
      unfold Local.read_view. condtac; s.
      { rewrite <- e in *.
        eapply le_gt_trans; [eapply join_l|]. nia. }
      eapply le_gt_trans; [eapply join_r|]. nia.
  - (* fulfill - promises_wf required *)
    inv STEP. ss. exploit PROMISES_PF; eauto. i.
    right. exists vloc.(ValA.val).
    rewrite fun_add_spec_eq. ss.
  - (* rmw - promises_wf required *)
    inv STEP. ss. exploit PROMISES_PF; eauto. i.
    right. exists vloc.(ValA.val).
    rewrite fun_add_spec_eq. ss.
  - (* rmw failure *)
    destruct (classic (old_ts <= n)).
    + inv STEP. ss. left. esplits.
      * econs 5; eauto. econs; s; eauto.
        { eapply sim_memory_latest; eauto.
          inv WF1_V. inv MEMORY. ss. }
        { eapply sim_memory_read; eauto. }
      * eauto.
      * ss.
    + inv STEP. ss. right. exists vloc.(ValA.val).
      rewrite fun_add_spec_eq. ss.
      unfold Local.read_view. condtac; s.
      { rewrite <- e in *.
        eapply le_gt_trans; [eapply join_l|]. nia. }
      eapply le_gt_trans; [eapply join_r|]. nia.
  - (* dmb *)
    left. inv STEP. inv COHMAX. ss. esplits.
    + econs 6; eauto. econs; eauto. econs. ss.
    + eauto.
    + ss.
  - (* flush *)
    left. inv STEP. ss. esplits.
    + econs 7; eauto. econs; eauto.
    + eauto.
    + ss.
  - (* flushopt *)
    left. inv STEP. ss. esplits.
    + econs 8; eauto. econs; eauto.
    + eauto.
    + ss.
Qed.

Lemma sim_fulfill
      n tid
      vloc vval res lc1_pf mem_pf lc2_pf
      lc1_v mem1_v
      (LOCAL1: sim_local n lc1_pf lc1_v)
      (MEMORY1: sim_memory n mem_pf mem1_v)
      (WF1_PF: Local.wf tid mem_pf lc1_pf)
      (WF1_V: Local.wf tid mem1_v lc1_v)
      (STEP_PF: Local.fulfill vloc vval res (n + 1) tid lc1_pf mem_pf lc2_pf):
  exists lc2_v mem2_v,
    (<<STEP_V: Local.write vloc vval res (n + 1) tid lc1_v mem1_v lc2_v mem2_v>>) /\
    (<<LOCAL2: sim_local (n + 1) lc2_pf lc2_v>>) /\
    (<<MEMORY2: sim_memory (n + 1) mem_pf mem2_v>>) /\
    (<<PROMISES_PF: lc2_pf.(Local.promises) = Promises.unset (n + 1) lc1_pf.(Local.promises)>>).
Proof.
  destruct lc1_pf as [coh_pf vrn_pf lper_pf per_pf promises_pf].
  destruct lc1_v as [coh_v vrn_v lper_v per_v promises_v].
  inv LOCAL1. inv MEMORY1. inv STEP_PF. ss. subst.
  esplits.
  - econs; eauto.
    unfold Memory.append. rewrite Nat.add_1_r. refl.
  - econs; eauto; s. i.
    revert PROMISE0. rewrite Promises.unset_o. condtac; ss. i.
    exploit PROMISES_PF; eauto. i.
    destruct (classic (ts = length mem1_v + 1)); try nia. congr.
  - revert MSG. unfold Memory.get_msg. rewrite Nat.add_1_r. ss.
    rewrite nth_error_app2; try nia.
    rewrite Nat.sub_diag.
    destruct mem_post; ss. i. inv MSG.
    econs.
    + rewrite <- app_assoc. ss.
    + rewrite app_length. s. rewrite Nat.add_1_r. ss.
  - ss.
Qed.

Lemma sim_rmw
      n tid
      vloc vold vnew old_ts lc1_pf mem_pf lc2_pf
      lc1_v mem1_v
      (LOCAL1: sim_local n lc1_pf lc1_v)
      (MEMORY1: sim_memory n mem_pf mem1_v)
      (WF1_PF: Local.wf tid mem_pf lc1_pf)
      (WF1_V: Local.wf tid mem1_v lc1_v)
      (STEP_PF: Local.rmw vloc vold vnew old_ts (n + 1) tid lc1_pf mem_pf lc2_pf):
  exists lc2_v mem2_v,
    (<<STEP_V: Local.vrmw vloc vold vnew old_ts (n + 1) tid lc1_v mem1_v lc2_v mem2_v>>) /\
    (<<LOCAL2: sim_local (n + 1) lc2_pf lc2_v>>) /\
    (<<MEMORY2: sim_memory (n + 1) mem_pf mem2_v>>) /\
    (<<PROMISES_PF: lc2_pf.(Local.promises) = Promises.unset (n + 1) lc1_pf.(Local.promises)>>).
Proof.
  destruct lc1_pf as [coh_pf vrn_pf lper_pf per_pf promises_pf].
  destruct lc1_v as [coh_v vrn_v lper_v per_v promises_v].
  inv LOCAL1. dup MEMORY1. inv MEMORY0. inv STEP_PF. ss. subst.
  esplits.
  - econs.
    + ss.
    + ss.
    + instantiate (1 := mem1_v ++ [Msg.mk vloc.(ValA.val) vnew.(ValA.val) tid]).
      eapply sim_memory_exclusive; eauto.
      rewrite app_length.
      destruct mem_post; s; try nia.
      rewrite Nat.add_1_r, app_nil_r in MSG.
      unfold Memory.get_msg in *. ss.
      exploit nth_error_some; eauto. i. nia.
    + eapply sim_memory_read; eauto. nia.
    + ss.
    + ss.
    + ss.
    + unfold Memory.append. rewrite Nat.add_1_r. refl.
    + ss.
  - econs; eauto; s. i.
    revert PROMISE0. rewrite Promises.unset_o. condtac; ss. i.
    exploit PROMISES_PF; eauto. i.
    destruct (classic (ts = length mem1_v + 1)); try nia. congr.
  - revert MSG. unfold Memory.get_msg. rewrite Nat.add_1_r. ss.
    rewrite nth_error_app2; try nia.
    rewrite Nat.sub_diag.
    destruct mem_post; ss. i. inv MSG.
    econs.
    + rewrite <- app_assoc. ss.
    + rewrite app_length. s. rewrite Nat.add_1_r. ss.
  - ss.
Qed.

(* TODO: move *)

Lemma rtc_state_step_incr
      tid eu1 eu2
      (STEP: rtc (ExecUnit.state_step tid) eu1 eu2):
  ExecUnit.le eu1 eu2.
Proof.
  induction STEP; try refl.
  exploit ExecUnit.state_step_incr; eauto. i.
  etrans; eauto.
Qed.

Lemma sim_next_fulfill
      n tid
      mem_pf mem1_v
      st1 lc1_pf st2 lc2_pf st3 lc3_pf ord vloc vval res
      lc1_v
      (MEMORY1: sim_memory n mem_pf mem1_v)
      (LOCAL1: sim_local n lc1_pf lc1_v)
      (WF1_PF: Local.wf tid mem_pf lc1_pf)
      (WF1_V: Local.wf tid mem1_v lc1_v)
      (STEPS: rtc (ExecUnit.state_step tid)
                  (ExecUnit.mk st1 lc1_pf mem_pf)
                  (ExecUnit.mk st2 lc2_pf mem_pf))
      (STEP_ST: State.step (Event.write false ord vloc vval res) st2 st3)
      (STEP_LC: Local.fulfill vloc vval res (n + 1) tid lc2_pf mem_pf lc3_pf):
  exists lc2_v lc3_v mem3_v,
    (<<STEPS_V: rtc (ExecUnit.view_step tid)
                    (ExecUnit.mk st1 lc1_v mem1_v)
                    (ExecUnit.mk st2 lc2_v mem1_v)>>) /\
    (<<STEP_V: ExecUnit.view_step tid (ExecUnit.mk st2 lc2_v mem1_v) (ExecUnit.mk st3 lc3_v mem3_v)>>) /\
    (<<LOCAL3: sim_local (n + 1) lc3_pf lc3_v>>) /\
    (<<MEMORY3: sim_memory (n + 1) mem_pf mem3_v>>) /\
    (<<PROMISES2_PF: lc2_pf.(Local.promises) = lc1_pf.(Local.promises)>>) /\
    (<<PROMISES3_PF: lc3_pf.(Local.promises) = Promises.unset (n + 1) lc1_pf.(Local.promises)>>).
Proof.
  revert n mem1_v st3 lc3_pf ord vloc vval res lc1_v MEMORY1 LOCAL1 WF1_PF WF1_V STEP_ST STEP_LC.
  dependent induction STEPS; i.
  { exploit sim_fulfill; eauto. i. des.
    esplits; eauto.
    econs. econs; eauto. econs 3; eauto. }
  inv H. inv STEP.
  exploit sim_step; eauto. i. des.
  - destruct y. ss. subst.
    exploit Local.step_wf; try exact LOCAL; eauto. i.
    exploit Local.view_step_wf; try exact STEP_V; eauto. i.
    exploit IHSTEPS; eauto. i. des.
    esplits.
    + econs 2; eauto. econs. econs; eauto.
    + eauto.
    + ss.
    + ss.
    + congr.
    + congr.
  - exfalso.
    exploit rtc_state_step_incr; try exact STEPS. i.
    inv STEP_LC. inv WRITABLE. inv COHMAX. inv x0. inv LC. ss.
    specialize (COH0 loc). specialize (COHMAX0 loc).
    rewrite COHMAX0 in COH0.
    exploit le_lt_trans; [exact COH0|exact EXT|]. i. nia.
Qed.
      
Lemma sim_next_rmw
      n tid
      mem_pf mem1_v
      st1 lc1_pf st2 lc2_pf st3 lc3_pf ordr ordw vloc vold vnew old_ts
      lc1_v
      (MEMORY1: sim_memory n mem_pf mem1_v)
      (LOCAL1: sim_local n lc1_pf lc1_v)
      (WF1_PF: Local.wf tid mem_pf lc1_pf)
      (WF1_V: Local.wf tid mem1_v lc1_v)
      (STEPS: rtc (ExecUnit.state_step tid)
                  (ExecUnit.mk st1 lc1_pf mem_pf)
                  (ExecUnit.mk st2 lc2_pf mem_pf))
      (STEP_ST: State.step (Event.rmw ordr ordw vloc vold vnew) st2 st3)
      (STEP_LC: Local.rmw vloc vold vnew old_ts (n + 1) tid lc2_pf mem_pf lc3_pf):
  exists lc2_v lc3_v mem3_v,
    (<<STEPS_V: rtc (ExecUnit.view_step tid)
                    (ExecUnit.mk st1 lc1_v mem1_v)
                    (ExecUnit.mk st2 lc2_v mem1_v)>>) /\
    (<<STEP_V: ExecUnit.view_step tid (ExecUnit.mk st2 lc2_v mem1_v) (ExecUnit.mk st3 lc3_v mem3_v)>>) /\
    (<<LOCAL3: sim_local (n + 1) lc3_pf lc3_v>>) /\
    (<<MEMORY3: sim_memory (n + 1) mem_pf mem3_v>>) /\
    (<<PROMISES2_PF: lc2_pf.(Local.promises) = lc1_pf.(Local.promises)>>) /\
    (<<PROMISES3_PF: lc3_pf.(Local.promises) = Promises.unset (n + 1) lc1_pf.(Local.promises)>>).
Proof.
  revert n mem1_v st3 lc3_pf ordr ordw vloc vold vnew lc1_v MEMORY1 LOCAL1 WF1_PF WF1_V STEP_ST STEP_LC.
  dependent induction STEPS; i.
  { exploit sim_rmw; eauto. i. des.
    esplits; eauto.
    econs. econs; eauto. econs 4; eauto. }
  inv H. inv STEP.
  exploit sim_step; eauto. i. des.
  - destruct y. ss. subst.
    exploit Local.step_wf; try exact LOCAL; eauto. i.
    exploit Local.view_step_wf; try exact STEP_V; eauto. i.
    exploit IHSTEPS; eauto. i. des.
    esplits.
    + econs 2; eauto. econs. econs; eauto.
    + eauto.
    + ss.
    + ss.
    + congr.
    + congr.
  - exfalso.
    exploit rtc_state_step_incr; try exact STEPS. i.
    inv STEP_LC. inv WRITABLE. inv COHMAX. inv x0. inv LC. ss.
    specialize (COH1 loc). specialize (COHMAX0 loc).
    rewrite COHMAX0 in COH1.
    exploit le_lt_trans; [exact COH1|exact EXT|]. i. nia.
Qed.


Theorem promising_pf_to_view
        p pm
        (EXEC: Machine.pf_exec p pm):
  exists vm,
    <<STEP: Machine.view_exec p vm>> /\
    <<SIM: Machine.equiv pm vm>>.
Proof.
Admitted.
