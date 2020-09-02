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


(* simulation relations *)

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
    (VPN: lc_pf.(Local.vpn) = lc_v.(Local.vpn))
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

Lemma sim_local_last
      tid lc_pf lc_v mem_pf
      (SIM: sim_local (length mem_pf) lc_pf lc_v)
      (WF: Local.wf tid mem_pf lc_pf):
  lc_pf = lc_v.
Proof.
  destruct lc_pf, lc_v.
  inv SIM. inv WF. ss. subst. f_equal.
  apply Promises.ext. i.
  destruct (Promises.lookup i promises) eqn:GET.
  - exploit PROMISES; eauto. i.
    exploit PROMISES_PF; eauto. i. nia.
  - unfold Promises.lookup, bot, fun_bot. condtac; ss.
Qed.

Lemma sim_memory_last
      mem_pf mem_v
      (SIM: sim_memory (length mem_pf) mem_pf mem_v):
  mem_pf = mem_v.
Proof.
  inv SIM. destruct mem_post.
  - rewrite app_nil_r. ss.
  - rewrite app_length in *. ss. nia.
Qed.

Lemma sim_last
      m_pf m_v
      (SIM: sim (length m_pf.(Machine.mem)) m_pf m_v)
      (WF: Machine.wf m_pf):
  Machine.equiv m_pf m_v.
Proof.
  inv SIM. exploit sim_memory_last; eauto. i.
  econs; ss.
  ii. specialize (TPOOL y). inv TPOOL; ss.
  destruct a, b. symmetry in H0, H. inv REL. ss. subst.
  inv WF. exploit WF0; try eapply H0. i. inv x.
  exploit sim_local_last; eauto. s. i. subst. ss.
Qed.

Lemma sim_local_refl
      n lc
      (PROMISES: lc.(Local.promises) = bot):
  sim_local n lc lc.
Proof.
  econs; i; try refl.
  - rewrite PROMISES in *.
    unfold Promises.lookup, bot, fun_bot in *. des_ifs.
  - rewrite PROMISES in *. ss.
Qed.

Lemma sim_memory_refl mem:
  sim_memory (length mem) mem mem.
Proof.
  econs; ss.
  rewrite app_nil_r. ss.
Qed.


Lemma init_sim p:
  (<<SIM: sim 0 (Machine.init p) (Machine.init p)>>) /\
  (<<PROMISES_WF: promises_wf 0 (Machine.init p)>>).
Proof.
  split; unnw.
  - unfold Machine.init. econs; ss.
    + i. rewrite IdMap.map_spec.
      destruct (IdMap.find tid p); ss. econs. econs; ss. econs; ss. i.
      unfold Promises.lookup, bot, fun_bot in *. des_ifs.
    + econs; ss.
  - econs; ii.
    + revert FIND. unfold Machine.init. s. rewrite IdMap.map_spec.
      destruct (IdMap.find tid p); ss. i. inv FIND.
      unfold Promises.lookup, bot, fun_bot in *. des_ifs.
    + ss. unfold Memory.get_msg in *. des_ifs. destruct t; ss.
Qed.

Lemma promise_step_sim
      n m1_pf m2_pf m_v
      (SIM1: sim n m1_pf m_v)
      (STEP: Machine.step ExecUnit.promise_step m1_pf m2_pf):
  sim n m2_pf m_v.
Proof.
  inv SIM1. inv STEP. inv STEP0. ss. subst. inv LOCAL.
  econs; i.
  - rewrite TPOOL0. rewrite IdMap.add_spec. condtac; ss.
    rewrite e in *. specialize (TPOOL tid). rewrite FIND in *. inv TPOOL.
    destruct b as [st lc]. inv REL. ss. econs. econs; ss.
    inv LOCAL. econs; ss. i. revert PROMISE.
    rewrite Promises.set_o. condtac; ss; eauto. i.
    rewrite e0 in *. unfold Memory.append in *. inv MEM2.
    inv MEMORY. rewrite MEMORY0. rewrite app_length. nia.
  - inv MEMORY. unfold Memory.append in *. inv MEM2. econs; ss.
    rewrite MEMORY0. rewrite <- app_assoc. refl.
Qed.

Lemma promise_step_promises_wf
      n m1 m2
      (WF1: promises_wf n m1)
      (STEP: Machine.step ExecUnit.promise_step m1 m2):
  promises_wf n m2.
Proof.
  inv WF1. inv STEP. inv STEP0. ss. subst. inv LOCAL.
  econs; ii.
  - revert FIND0. rewrite TPOOL. rewrite IdMap.add_spec. condtac; ss.
    + rewrite e in *. i. inv FIND0. ss.
      revert LOOKUP. rewrite Promises.set_o. condtac; ss.
      * i. rewrite e0 in *. inv MEM2.
        unfold Memory.get_msg. ss.
        rewrite nth_error_last. esplits; eauto.
      * i. inv MEM2. exploit SOUND; eauto. i. des.
        unfold Memory.get_msg in *. destruct ts0; ss.
        rewrite nth_error_app1; eauto.
        exploit nth_error_some; eauto.
    + i. exploit SOUND; eauto. i. des. inv MEM2.
      unfold Memory.get_msg in *. destruct ts0; ss.
      rewrite nth_error_app1; eauto.
      exploit nth_error_some; eauto.
  - inv MEM2. rewrite <- H1 in *.
    unfold Memory.get_msg in *. destruct ts0; ss.
    destruct (classic (ts0 = length m1.(Machine.mem))).
    + rewrite H in *. rewrite nth_error_last in GET. inv GET.
      rewrite TPOOL. rewrite IdMap.gss. esplits; eauto. s.
      rewrite Promises.set_o. condtac; ss. congr.
    + exploit nth_error_some; eauto. rewrite app_length. s. i.
      rewrite nth_error_app1 in GET by nia.
      exploit COMPLETE; eauto. i. des.
      rewrite TPOOL. rewrite IdMap.add_spec. condtac; ss; eauto.
      rewrite e in *. rewrite FIND in *. inv FIND0.
      esplits; eauto. s.
      rewrite Promises.set_o. condtac; eauto.
Qed.

Lemma rtc_promise_step_sim
      n m1_pf m2_pf m_v
      (SIM1: sim n m1_pf m_v)
      (WF1: promises_wf n m1_pf)
      (STEP: rtc (Machine.step ExecUnit.promise_step) m1_pf m2_pf):
  (<<SIM2: sim n m2_pf m_v>>) /\
  (<<PROMISES_WF2: promises_wf n m2_pf>>).
Proof.
  dependent induction STEP; eauto using promise_step_sim, promise_step_promises_wf.
Qed.


(* next fulfillment *)

Definition is_writing (e: Event.t (A:=unit)): bool :=
  match e with
  | Event.write _ _ _ _ _
  | Event.rmw _ _ _ _ _  => true
  | _ => false
  end.

Lemma non_fulfillable
      tid st1 lc1 st lc mem ts loc
      (STEPS: rtc (ExecUnit.state_step tid)
                  (ExecUnit.mk st1 lc1 mem)
                  (ExecUnit.mk st lc mem))
      (PROMISE: Promises.lookup ts lc1.(Local.promises) = true)
      (PROMISES_BOT: lc.(Local.promises) = bot)
      (COH: ts <= (lc1.(Local.coh) loc).(View.ts)):
  False.
Proof.
  revert PROMISE COH. dependent induction STEPS; i.
  { rewrite PROMISES_BOT in *.
    unfold Promises.lookup, bot, fun_bot in *. des_ifs. }
  exploit ExecUnit.state_step_incr; eauto. i.
  destruct y. inv H. inv STEP. ss. subst.
  apply (IHSTEPS state local st lc mem); eauto.
  - inv LOCAL; try inv STEP; ss.
    + rewrite Promises.unset_o. condtac; ss. rewrite e in *.
      inv WRITABLE. inv COHMAX.
      exploit le_lt_trans; [eapply (COHMAX0 loc)|eapply EXT|]. i. nia.
    + rewrite Promises.unset_o. condtac; ss. rewrite e in *.
      inv WRITABLE. inv COHMAX.
      exploit le_lt_trans; [eapply (COHMAX0 loc)|eapply EXT|]. i. nia.
  - inv x0. inv LC. ss. etrans; eauto. apply COH0.
Qed.

Lemma next_fulfill_exists_eu
      tid st1 lc1 st lc mem ts
      (STEPS: rtc (ExecUnit.state_step tid)
                  (ExecUnit.mk st1 lc1 mem)
                  (ExecUnit.mk st lc mem))
      (PROMISE: Promises.lookup ts lc1.(Local.promises) = true)
      (PROMISES_TS: forall ts' (GET: Promises.lookup ts' lc1.(Local.promises) = true), ts' >= ts)
      (BOT: lc.(Local.promises) = bot):
  exists st2 lc2,
    (<<STEPS: rtc (ExecUnit.state_step tid)
                  (ExecUnit.mk st1 lc1 mem)
                  (ExecUnit.mk st2 lc2 mem)>>) /\
    ((exists st3 lc3 ord vloc vval res,
         (<<STEP_ST: State.step (Event.write false ord vloc vval res) st2 st3>>) /\
         (<<STEP_LC: Local.fulfill vloc vval res ts tid lc2 mem lc3>>) /\
         (<<PROMISES: lc3.(Local.promises) = Promises.unset ts lc1.(Local.promises)>>) /\
         (<<STEPS_POST: rtc (ExecUnit.state_step tid)
                            (ExecUnit.mk st3 lc3 mem)
                            (ExecUnit.mk st lc mem)>>)) \/
     (exists st3 lc3 ordr ordw vloc vold vnew old_ts,
         (<<STEP_ST: State.step (Event.rmw ordr ordw vloc vold vnew) st2 st3>>) /\
         (<<STEP_LC: Local.rmw vloc vold vnew old_ts ts tid lc2 mem lc3>>) /\
         (<<PROMISES: lc3.(Local.promises) = Promises.unset ts lc1.(Local.promises)>>) /\
         (<<STEPS_POST: rtc (ExecUnit.state_step tid)
                            (ExecUnit.mk st3 lc3 mem)
                            (ExecUnit.mk st lc mem)>>))).
Proof.
  dependent induction STEPS; i.
  { rewrite BOT in *.
    unfold Promises.lookup, bot, fun_bot in *.
    des_ifs. }
  destruct y. dup H. inv H0. inv STEP. ss. subst.
  destruct (is_writing e) eqn:EVENT; cycle 1.
  { assert (local.(Local.promises) = lc1.(Local.promises)).
    { destruct e; ss; try (inv LOCAL; ss); inv STEP; ss. }
    exploit (IHSTEPS state local st lc mem); eauto; try congr.
    { destruct e; ss; try (inv LOCAL; ss); inv STEP; ss. }
    i. des.
    - esplits.
      + econs 2; eauto.
      + left. esplits; eauto. congr.
    - esplits.
      + econs 2; eauto.
      + right. esplits; eauto. congr.
  }

  destruct e; ss.
  - inv LOCAL; ss. inv EVENT0.
    destruct (classic (ts0 = ts)).
    { subst. esplits; try refl. left. esplits; eauto. inv STEP. ss. }
    exfalso. eapply (@non_fulfillable _ _ _ _ _ _ ts vloc0.(ValA.val)); eauto.
    + inv STEP. s. rewrite Promises.unset_o. condtac; ss. congr.
    + inv STEP. s. rewrite fun_add_spec_eq. ss.
      exploit PROMISES_TS; try exact PROMISE0. i. ss.
  - inv LOCAL; ss. inv EVENT0.
    destruct (classic (ts0 = ts)).
    { subst. esplits; try refl. right. esplits; eauto. inv STEP. ss. }
    exfalso. eapply (@non_fulfillable _ _ _ _ _ _ ts vloc0.(ValA.val)); eauto.
    + inv STEP. s. rewrite Promises.unset_o. condtac; ss. congr.
    + inv STEP. s. rewrite fun_add_spec_eq. ss.
      exploit PROMISES_TS; try exact PROMISE0. i. ss.
Qed.

Lemma next_fulfill_exists
      n m1 m m1_v
      (SIM: sim n m1 m1_v)
      (EXEC1: Machine.state_exec m1 m)
      (N: n < length m1.(Machine.mem))
      (PROMISES1: promises_wf n m1)
      (PROMISES_BOT: Machine.no_promise m):
  exists tid st1 lc1 st2 lc2,
    (<<FIND: IdMap.find tid m1.(Machine.tpool) = Some (st1, lc1)>>) /\
    (<<STEPS: rtc (ExecUnit.state_step tid)
                  (ExecUnit.mk st1 lc1 m1.(Machine.mem))
                  (ExecUnit.mk st2 lc2 m1.(Machine.mem))>>) /\
    __guard__ (
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
            (<<PROMISES2: promises_wf (n + 1) m2>>))).
Proof.
  unguard.
  destruct m1 as [tpool1 mem]. dup EXEC1. inv EXEC0. ss.
  destruct (Memory.get_msg (n + 1) mem) as [[]|] eqn:GET; cycle 1.
  { unfold Memory.get_msg in *. rewrite Nat.add_1_r in *. ss.
    exploit nth_error_None. i. des.
    exploit x0; eauto. i. nia. }
  dup PROMISES1. inv PROMISES0.
  exploit COMPLETE; try exact GET; try nia. s. i. des.
  specialize (TPOOL tid). inv TPOOL; try congr.
  rewrite FIND in *. inv H0.
  destruct b as [st_end lc_end]. ss.
  exploit next_fulfill_exists_eu; eauto.
  { inv SIM. specialize (TPOOL tid). inv TPOOL; try congr.
    rewrite FIND in *. inv H1. inv REL0. inv LOCAL. ss.
    i. exploit PROMISES_PF; eauto. i. nia. }
  { inv PROMISES_BOT. eauto. }
  i. des.
  - esplits; eauto. left. esplits; eauto.
    + econs; ss. ii.
      rewrite IdMap.add_spec. condtac; ss.
      * rewrite <- e in *. rewrite <- H. econs. ss.
      * inv EXEC1. ss.
    + inv PROMISES1. econs; s; i; unnw.
      * revert FIND0. rewrite IdMap.add_spec. condtac; eauto.
        i. inv FIND0. rewrite e in *. rewrite PROMISES. ii.
        revert LOOKUP. rewrite Promises.unset_o. condtac; ss. i.
        eapply SOUND0; eauto.
      * exploit COMPLETE0; try exact GET0; try by nia. i. des.
        rewrite IdMap.add_spec. condtac; ss; eauto.
        rewrite e, FIND in *. inv x. esplits; eauto.
        rewrite PROMISES. rewrite Promises.unset_o. condtac; ss.
        rewrite e0 in *. nia.
  - esplits; eauto. right. esplits; eauto.
    + econs; ss. ii.
      rewrite IdMap.add_spec. condtac; ss.
      * rewrite <- e in *. rewrite <- H. econs. ss.
      * inv EXEC1. ss.
    + inv PROMISES1. econs; s; i; unnw.
      * revert FIND0. rewrite IdMap.add_spec. condtac; eauto.
        i. inv FIND0. rewrite e in *. rewrite PROMISES. ii.
        revert LOOKUP. rewrite Promises.unset_o. condtac; ss. i.
        eapply SOUND0; eauto.
      * exploit COMPLETE0; try exact GET0; try by nia. i. des.
        rewrite IdMap.add_spec. condtac; ss; eauto.
        rewrite e, FIND in *. inv x. esplits; eauto.
        rewrite PROMISES. rewrite Promises.unset_o. condtac; ss.
        rewrite e0 in *. nia.
Qed.


(* simulating eu steps *)

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
  - (* fulfill *)
    inv STEP. ss. exploit PROMISES_PF; eauto. i.
    right. exists vloc.(ValA.val).
    rewrite fun_add_spec_eq. ss.
  - (* rmw *)
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
  - (* mfence *)
    left. inv STEP. inv COHMAX. ss. esplits.
    + econs 6; eauto. econs; eauto. econs. ss.
    + eauto.
    + ss.
  - (* sfence *)
    left. inv STEP. inv COHMAX. ss. esplits.
    + econs 7; eauto. econs; eauto. econs. ss.
    + eauto.
    + ss.
  - (* flush *)
    left. inv STEP. inv COHMAX. ss. esplits.
    + econs 8; eauto. econs; eauto. econs. ss.
    + eauto.
    + ss.
  - (* flushopt *)
    left. inv STEP. ss. esplits.
    + econs 9; eauto. econs; eauto.
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
    exploit ExecUnit.rtc_state_step_incr; try exact STEPS. i.
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
    exploit ExecUnit.rtc_state_step_incr; try exact STEPS. i.
    inv STEP_LC. inv WRITABLE. inv COHMAX. inv x0. inv LC. ss.
    specialize (COH1 loc). specialize (COHMAX0 loc).
    rewrite COHMAX0 in COH1.
    exploit le_lt_trans; [exact COH1|exact EXT|]. i. nia.
Qed.

Lemma sim_step_last
      e tid lc1_pf lc2_pf mem_pf
      lc1_v mem_v
      (LOCAL1: sim_local (length mem_pf) lc1_pf lc1_v)
      (MEMORY: sim_memory (length mem_pf) mem_pf mem_v)
      (WF1_PF: Local.wf tid mem_pf lc1_pf)
      (WF1_V: Local.wf tid mem_v lc1_v)
      (STEP_PF: Local.step e tid mem_pf lc1_pf lc2_pf):
  (<<STEP_V: Local.view_step e tid mem_v mem_v lc1_v lc2_pf>>) /\
  (<<LOCAL2: sim_local (length mem_pf) lc2_pf lc2_pf>>) /\
  (<<PROMISES: lc2_pf.(Local.promises) = bot>>).
Proof.
  exploit sim_local_last; eauto. i. subst.
  exploit sim_memory_last; eauto. i. subst.
  destruct lc1_v. dup LOCAL1. inv LOCAL0. ss. subst.
  inv STEP_PF.
  - (* internal *)
    esplits; eauto. econs 1; ss.
  - (* read *)
    esplits.
    + econs 2; eauto.
    + eapply sim_local_refl; eauto. inv STEP. ss.
    + inv STEP. ss.
  - (* fulfill *)
    inv STEP. ss. unfold Promises.lookup, bot, fun_bot in *. des_ifs.
  - (* rmw *)
    inv STEP. ss. unfold Promises.lookup, bot, fun_bot in *. des_ifs.
  - (* rmw failure *)
    esplits.
    + econs 5; eauto.
    + eapply sim_local_refl; eauto. inv STEP. ss.
    + inv STEP. ss.
  - (* mfence *)
    esplits.
    + econs 6; eauto.
    + eapply sim_local_refl; eauto. inv STEP. ss.
    + inv STEP. ss.
  - (* sfence *)
    esplits.
    + econs 7; eauto.
    + eapply sim_local_refl; eauto. inv STEP. ss.
    + inv STEP. ss.
  - (* flush *)
    esplits.
    + econs 8; eauto.
    + eapply sim_local_refl; eauto. inv STEP. ss.
    + inv STEP. ss.
  - (* flushopt *)
    esplits.
    + econs 9; eauto.
    + eapply sim_local_refl; eauto. inv STEP. ss.
    + inv STEP. ss.
Qed.

Lemma sim_rtc_step_last
      tid st1 lc1_pf st2 lc2_pf mem_pf
      lc1_v mem_v
      (LOCAL1: sim_local (length mem_pf) lc1_pf lc1_v)
      (MEMORY: sim_memory (length mem_pf) mem_pf mem_v)
      (WF1_PF: Local.wf tid mem_pf lc1_pf)
      (WF1_V: Local.wf tid mem_v lc1_v)
      (STEPS: rtc (ExecUnit.state_step tid)
                  (ExecUnit.mk st1 lc1_pf mem_pf)
                  (ExecUnit.mk st2 lc2_pf mem_pf)):
  (<<STEPS_V: rtc (ExecUnit.view_step tid)
                  (ExecUnit.mk st1 lc1_v mem_v)
                  (ExecUnit.mk st2 lc2_pf mem_v)>>) /\
  (<<LOCAL2: sim_local (length mem_pf) lc2_pf lc2_pf>>) /\
  (<<PROMISES: lc2_pf.(Local.promises) = bot>>).
Proof.
  exploit sim_local_last; eauto. i. subst.
  exploit sim_memory_last; eauto. i. subst.
  revert LOCAL1 MEMORY WF1_PF WF1_V.
  dependent induction STEPS; i.
  { splits; eauto. inv LOCAL1. ss. }
  inv H. inv STEP. ss.
  exploit sim_step_last; try exact LOCAL; eauto. i. des.
  destruct y. ss. subst.
  exploit Local.step_wf; try exact LOCAL; eauto. i.
  exploit (IHSTEPS state st2 lc2_pf local mem_v); eauto. i. des.
  splits; eauto. econs 2; eauto. econs. econs; eauto.
Qed.

Lemma sim_rtc_machine_step_last
      m1_pf m2_pf m1_v
      (SIM1: sim (length m1_pf.(Machine.mem)) m1_pf m1_v)
      (EXEC_PF: Machine.state_exec m1_pf m2_pf)
      (WF1_PF: Machine.wf m1_pf)
      (WF1_V: Machine.wf m1_v):
  exists m2_v,
    (<<STEPS_V: rtc (Machine.step ExecUnit.view_step) m1_v m2_v>>) /\
    (<<SIM2: sim (length m1_pf.(Machine.mem)) m2_pf m2_v>>).
Proof.
  inv EXEC_PF.
  assert (IN: forall tid sl1_pf
                (FIND1: IdMap.find tid m1_pf.(Machine.tpool) = Some sl1_pf),
             exists sl2_pf,
               IdMap.find tid m2_pf.(Machine.tpool) = Some sl2_pf /\
               rtc (ExecUnit.state_step tid)
                   (ExecUnit.mk (fst sl1_pf) (snd sl1_pf) m1_pf.(Machine.mem))
                   (ExecUnit.mk (fst sl2_pf) (snd sl2_pf) m1_pf.(Machine.mem))).
  { i. specialize (TPOOL tid). rewrite FIND1 in TPOOL. inv TPOOL. esplits; ss. }
  assert (OUT: forall tid
                 (FIND1: IdMap.find tid m1_pf.(Machine.tpool) = None),
             IdMap.find tid m1_pf.(Machine.tpool) = IdMap.find tid m2_pf.(Machine.tpool)).
  { i. specialize (TPOOL tid). rewrite FIND1 in TPOOL. inv TPOOL. ss. }
  assert (P: forall tid sl1_pf
               (FIND1: IdMap.find tid m1_pf.(Machine.tpool) = Some sl1_pf),
             IdMap.find tid m1_pf.(Machine.tpool) = Some sl1_pf).
  { ss. }
  clear TPOOL.
  setoid_rewrite IdMap.elements_spec in IN at 1.
  setoid_rewrite IdMap.elements_spec in OUT at 1.
  setoid_rewrite IdMap.elements_spec in P at 1.
  generalize (IdMap.elements_3w m1_pf.(Machine.tpool)). intro NODUP. revert NODUP.
  revert IN OUT P. generalize (IdMap.elements (m1_pf.(Machine.tpool))). intro ps.
  revert m1_pf m1_v SIM1 WF1_PF WF1_V MEM. induction ps; ss; i.
  { esplits; try refl.
    inv SIM1. econs.
    - i. specialize (TPOOL tid). rewrite <- OUT; ss.
    - rewrite <- MEM. ss.
  }

  destruct a as [tid [st1_pf lc1_pf]].
  exploit (P tid); eauto.
  { condtac; ss. revert X. condtac; ss. congr. }
  intro FIND_PF.
  exploit (IN tid); eauto.
  { condtac; ss. revert X. condtac; ss. congr. }
  i. des.
  dup SIM1. inv SIM0. specialize (TPOOL tid).
  rewrite FIND_PF in TPOOL. inv TPOOL.
  destruct b as [st1_v lc1_v]. inv REL. ss. subst.
  dup WF1_PF. inv WF1_PF0. exploit WF; eauto. i.
  dup WF1_V. inv WF1_V0. exploit WF0; eauto. i.
  clear WF WF0.
  exploit sim_rtc_step_last; try exact LOCAL; eauto; try apply x; try apply x2. i. des.
  exploit Machine.rtc_eu_step_step; try eapply x1; eauto. i.
  exploit Machine.rtc_eu_step_step; try eapply STEPS_V; eauto. i.
  inv NODUP.
  assert (TID: forall tid' sl
                 (FIND: SetoidList.findA (fun id': IdMap.key => if equiv_dec tid id' then true else false) ps = Some sl),
             tid' <> tid).
  { ii. subst. apply H2. revert FIND. clear. induction ps; ss.
    destruct a. destruct (equiv_dec tid k); ss.
    - inv e. i. inv FIND. left. ss.
    - i. right. apply IHps. ss.
  }
  inv SIM1.
  exploit (IHps (Machine.mk (IdMap.add tid (fst sl2_pf, snd sl2_pf) m1_pf.(Machine.tpool)) m1_pf.(Machine.mem))
                (Machine.mk (IdMap.add tid (fst sl2_pf, snd sl2_pf) m1_v.(Machine.tpool)) m1_v.(Machine.mem))); ss.
  - econs; ss. i.
    repeat rewrite IdMap.add_spec. condtac; ss; eauto.
  - eapply Machine.rtc_step_state_step_wf; eauto.
  - eapply Machine.rtc_step_view_step_wf; eauto.
  - i. eapply IN. condtac; ss. revert X. condtac; ss.
    rewrite e in *. exfalso. eapply TID; eauto.
  - i. rewrite IdMap.add_spec. condtac.
    + inversion e. subst. rewrite x0. destruct sl2_pf. ss.
    + eapply OUT. destruct (equiv_dec tid0 tid); ss.
  - i. rewrite IdMap.add_spec. condtac.
    + inversion e. subst. exfalso. eapply TID; eauto.
    + eapply P. destruct (equiv_dec tid0 tid); ss.
  - i. des. esplits; [|eauto]. etrans; eauto.
Qed.


Theorem promising_pf_to_view
        p m_pf
        (EXEC_PF: Machine.pf_exec p m_pf):
  exists m_v,
    <<EXEC_V: Machine.view_exec p m_v>> /\
    <<EQUIV: Machine.equiv m_pf m_v>>.
Proof.
  cut (exists m2_pf m2_v,
          (<<EXEC_PF: Machine.state_exec m2_pf m_pf>>) /\
          (<<STEPS_V: rtc (Machine.step ExecUnit.view_step) (Machine.init p) m2_v>>) /\
          (<<SIM2: sim (length m_pf.(Machine.mem)) m2_pf m2_v>>) /\
          (<<WF2_PF: Machine.wf m2_pf>>) /\
          (<<WF2_V: Machine.wf m2_v>>)).
  { i. des.
    exploit sim_rtc_machine_step_last; try exact SIM2; eauto.
    { inv EXEC_PF0. rewrite MEM. ss. }
    i. des.
    esplits.
    - econs. etrans; eauto.
    - exploit Machine.state_exec_wf; eauto. i.
      eapply sim_last; eauto.
      inv EXEC_PF0. rewrite MEM in *. ss.
  }

  inv EXEC_PF. specialize (init_sim p). i. des.
  specialize (Machine.init_wf p). intro WF_V.
  exploit rtc_promise_step_sim; eauto. i. des.
  exploit Machine.rtc_step_promise_step_wf; eauto. intro WF_PF.
  remember (Machine.init p) as m1_v.
  clear p Heqm1_v STEP1 SIM PROMISES_WF.

  remember (length m_pf.(Machine.mem) - 0) as n.
  replace 0 with (length m_pf.(Machine.mem) - n) in SIM2, PROMISES_WF2 by nia.
  clear Heqn.
  rename STEP2 into EXEC_PF, SIM2 into SIM, PROMISES_WF2 into PROMISES_WF.
  revert m1 m1_v EXEC_PF SIM PROMISES_WF WF_PF WF_V.
  induction n; i.
  { replace (length m_pf.(Machine.mem) - 0) with (length m_pf.(Machine.mem)) in * by nia.
    esplits; eauto. }

  destruct (classic (length (Machine.mem m_pf) > n)); cycle 1.
  { eapply IHn; eauto.
    - replace (length (Machine.mem m_pf) - n) with 0 in * by nia.
      replace (length (Machine.mem m_pf) - S n) with 0 in * by nia.
      ss.
    - replace (length (Machine.mem m_pf) - n) with 0 in * by nia.
      replace (length (Machine.mem m_pf) - S n) with 0 in * by nia.
      ss.
  }

  exploit next_fulfill_exists; try exact EXEC_PF; eauto.
  { inv EXEC_PF. rewrite MEM. nia. }
  i. des.
  dup SIM. inv SIM0.
  specialize (TPOOL tid). rewrite FIND in *. inv TPOOL. inv REL.
  symmetry in H2. destruct b as [st1_v lc1_v]. ss. subst.
  dup WF_PF. inv WF_PF0. exploit WF; eauto. i.
  dup WF_V. inv WF_V0. exploit WF0; eauto. i.
  clear WF WF0. unguard. des.
  - exploit sim_next_fulfill; try exact LOCAL; eauto; try apply x; try apply x1. i. des.
    exploit Machine.rtc_eu_step_step; [exact FIND|refl|..]; i.
    { etrans; [eauto|]. econs 2; [|refl].
      econs. econs; [eauto|econs 3; eauto|]; ss. }
    exploit Machine.rtc_eu_step_step; [eapply H2|refl|..]; i.
    { etrans; [eauto|]. econs 2; eauto. }
    exploit Machine.rtc_step_state_step_wf; try exact x2; eauto. i.
    exploit Machine.rtc_step_view_step_wf; try exact x3; eauto. i.
    exploit (IHn (Machine.mk (IdMap.add tid (st3, lc3) m1.(Machine.tpool)) m1.(Machine.mem))
                 (Machine.mk (IdMap.add tid (st3, lc3_v) m1_v.(Machine.tpool)) mem3_v)); eauto.
    { inv EXEC2. econs; ss. }
    { replace (length (Machine.mem m_pf) - S n + 1) with (length (Machine.mem m_pf) - n) in * by nia.
      econs; ss; i.
      repeat rewrite IdMap.add_spec. condtac; ss.
      { inversion e. subst. econs. econs; ss. }
      inv SIM. specialize (TPOOL tid0). inv TPOOL; ss.
      destruct a as [st_pf lc_pf], b as [st_v lc_v].
      inv REL. ss. subst. econs. econs; ss.
      inv LOCAL0. econs; ss. i.
      exploit PROMISES_PF; eauto. i.
      destruct (classic (ts = length m_pf.(Machine.mem) - n)); try by nia. subst.
      exfalso.
      inv STEP_LC. inv PROMISES_WF. rewrite PROMISES2_PF in *.
      exploit SOUND; try exact FIND; eauto. i. des.
      symmetry in H1.
      exploit SOUND; try eapply H1; eauto. i. des.
      congr.
    }
    { inv PROMISES_WF. econs; s; i; unnw.
      - revert FIND0. rewrite IdMap.add_spec. condtac; ss; eauto.
        ii. inv FIND0. inversion e. subst.
        revert LOOKUP. rewrite PROMISES3_PF.
        rewrite Promises.unset_o. condtac; ss. i.
        exploit SOUND; eauto.
      - exploit COMPLETE; try exact GET; try by nia. i. des.
        rewrite IdMap.add_spec. condtac; ss; eauto.
        inversion e. subst. esplits; eauto.
        rewrite PROMISES3_PF. rewrite Promises.unset_o. condtac; ss; try congr.
        inversion e0. subst. nia.
    }
    i. des.
    esplits; try exact SIM2; eauto. etrans; eauto.
  - exploit sim_next_rmw; try exact LOCAL; eauto; try apply x; try apply x1. i. des.
    exploit Machine.rtc_eu_step_step; [exact FIND|refl|..]; i.
    { etrans; [eauto|]. econs 2; [|refl].
      econs. econs; [eauto|econs 4; eauto|]; ss. }
    exploit Machine.rtc_eu_step_step; [eapply H2|refl|..]; i.
    { etrans; [eauto|]. econs 2; eauto. }
    exploit Machine.rtc_step_state_step_wf; try exact x2; eauto. i.
    exploit Machine.rtc_step_view_step_wf; try exact x3; eauto. i.
    exploit (IHn (Machine.mk (IdMap.add tid (st3, lc3) m1.(Machine.tpool)) m1.(Machine.mem))
                 (Machine.mk (IdMap.add tid (st3, lc3_v) m1_v.(Machine.tpool)) mem3_v)); eauto.
    { inv EXEC2. econs; ss. }
    { replace (length (Machine.mem m_pf) - S n + 1) with (length (Machine.mem m_pf) - n) in * by nia.
      econs; ss; i.
      repeat rewrite IdMap.add_spec. condtac; ss.
      { inversion e. subst. econs. econs; ss. }
      inv SIM. specialize (TPOOL tid0). inv TPOOL; ss.
      destruct a as [st_pf lc_pf], b as [st_v lc_v].
      inv REL. ss. subst. econs. econs; ss.
      inv LOCAL0. econs; ss. i.
      exploit PROMISES_PF; eauto. i.
      destruct (classic (ts = length m_pf.(Machine.mem) - n)); try by nia. subst.
      exfalso.
      inv STEP_LC. inv PROMISES_WF. rewrite PROMISES2_PF in *.
      exploit SOUND; try exact FIND; eauto. i. des.
      symmetry in H1.
      exploit SOUND; try eapply H1; eauto. i. des.
      congr.
    }
    { inv PROMISES_WF. econs; s; i; unnw.
      - revert FIND0. rewrite IdMap.add_spec. condtac; ss; eauto.
        ii. inv FIND0. inversion e. subst.
        revert LOOKUP. rewrite PROMISES3_PF.
        rewrite Promises.unset_o. condtac; ss. i.
        exploit SOUND; eauto.
      - exploit COMPLETE; try exact GET; try by nia. i. des.
        rewrite IdMap.add_spec. condtac; ss; eauto.
        inversion e. subst. esplits; eauto.
        rewrite PROMISES3_PF. rewrite Promises.unset_o. condtac; ss; try congr.
        inversion e0. subst. nia.
    }
    i. des.
    esplits; try exact SIM2; eauto. etrans; eauto.
Qed.
