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

Set Implicit Arguments.


Module Local.
Section Local.
  Inductive t := mk {
    coh: Loc.t -> View.t (A:=unit);
    vrn: View.t (A:=unit);
    lper: Loc.t -> View.t (A:=unit);
    per: Loc.t -> View.t (A:=unit);
    promises: Promises.t;
  }.
  Hint Constructors t.

  Definition read_view (coh:View.t (A:=unit)) (tsx:Time.t): View.t (A:=unit) :=
    if coh.(View.ts) == tsx
    then View.mk bot bot
    else View.mk tsx bot.

  Definition init: t := mk bot bot bot bot bot.

  Definition init_with_promises (promises: Promises.t): Local.t :=
    mk bot bot bot bot promises.

  Inductive promise (loc:Loc.t) (val:Val.t) (ts:Time.t) (tid:Id.t) (lc1:t) (mem1:Memory.t) (lc2:t) (mem2:Memory.t): Prop :=
  | promise_intro
      (LC2: lc2 =
            mk
              lc1.(coh)
              lc1.(vrn)
              lc1.(lper)
              lc1.(per)
              (Promises.set ts lc1.(promises)))
      (MEM2: Memory.append (Msg.mk loc val tid) mem1 = (ts, mem2))
  .
  Hint Constructors promise.

  Inductive read (vloc res:ValA.t (A:=unit)) (ts:Time.t) (lc1:t) (mem1: Memory.t) (lc2:t): Prop :=
  | read_intro
      loc val
      view_pre view_msg view_post
      (LOC: loc = vloc.(ValA.val))
      (VIEW_PRE: view_pre = lc1.(vrn))
      (COH: (lc1.(coh) loc).(View.ts) <= ts)
      (LATEST: Memory.latest loc ts view_pre.(View.ts) mem1)
      (MSG: Memory.read loc ts mem1 = Some val)
      (VIEW_MSG: view_msg = read_view (lc1.(coh) loc) ts)
      (VIEW_POST: view_post = view_msg)
      (RES: res = ValA.mk _ val bot)
      (LC2: lc2 =
            mk
              (fun_add loc (join (lc1.(coh) loc) view_post) lc1.(coh))
              (join lc1.(vrn) view_post)
              lc1.(lper)
              lc1.(per)
              lc1.(promises))
  .
  Hint Constructors read.

  Inductive cohmax (mloc:Loc.t) (lc1:t): Prop :=
  | cohmax_intro
      (COHMAX: forall loc, (lc1.(coh) loc).(View.ts) <= (lc1.(coh) mloc).(View.ts))
  .
  Hint Constructors cohmax.

  Inductive writable (vloc vval:ValA.t (A:=unit)) (tid:Id.t) (lc1:t) (mem1: Memory.t) (ts:Time.t): Prop :=
  | writable_intro
      loc mloc
      view_pre
      (LOC: loc = vloc.(ValA.val))
      (COHMAX: cohmax mloc lc1)
      (VIEW_PRE: view_pre = lc1.(coh) mloc)
      (EXT: lt view_pre.(View.ts) ts)
  .
  Hint Constructors writable.

  Inductive fulfill (vloc vval res:ValA.t (A:=unit)) (ts:Time.t) (tid:Id.t) (lc1:t) (mem1: Memory.t) (lc2:t): Prop :=
  | fulfill_intro
      loc val
      (LOC: loc = vloc.(ValA.val))
      (VAL: val = vval.(ValA.val))
      (WRITABLE: writable vloc vval tid lc1 mem1 ts)
      (MSG: Memory.get_msg ts mem1 = Some (Msg.mk loc val tid))
      (PROMISE: Promises.lookup ts lc1.(promises))
      (RES: res = ValA.mk _ 0 bot)
      (LC2: lc2 =
            mk
              (fun_add loc (View.mk ts bot) lc1.(coh))
              lc1.(vrn)
              lc1.(lper)
              lc1.(per)
              (Promises.unset ts lc1.(promises)))
  .
  Hint Constructors fulfill.

  Inductive rmw (vloc vold vnew:ValA.t (A:=unit)) (old_ts:Time.t) (ts:Time.t) (tid:Id.t) (lc1:t) (mem1:Memory.t) (lc2:t): Prop :=
  | rmw_intro
      loc old new
      (LOC: loc = vloc.(ValA.val))
      (COH: (lc1.(coh) loc).(View.ts) <= old_ts)
      (OLD_RANGE: lt old_ts ts)
      (EX: Memory.exclusive tid loc old_ts ts mem1)
      (OLD_MSG: Memory.read loc old_ts mem1 = Some old)
      (OLD: vold.(ValA.val) = old)
      (NEW: new = vnew.(ValA.val))
      (WRITABLE: writable vloc vnew tid lc1 mem1 ts)
      (MSG: Memory.get_msg ts mem1 = Some (Msg.mk loc new tid))
      (PROMISE: Promises.lookup ts lc1.(promises))
      (LC2: lc2 =
            mk
              (fun_add loc (View.mk ts bot) lc1.(coh))
              (join lc1.(vrn) (View.mk ts bot))
              lc1.(lper)
              (fun_join lc1.(per) lc1.(lper))
              (Promises.unset ts lc1.(promises)))
  .
  Hint Constructors rmw.

  Inductive rmw_failure (vloc vold res:ValA.t (A:=unit)) (old_ts:Time.t) (lc1:t) (mem1:Memory.t) (lc2:t): Prop :=
  | rmw_failure_intro
      loc old
      view_pre view_old view_post
      (LOC: loc = vloc.(ValA.val))
      (VIEW_PRE: view_pre = lc1.(vrn))
      (COH: (lc1.(coh) loc).(View.ts) <= old_ts)
      (LATEST: Memory.latest loc old_ts view_pre.(View.ts) mem1)
      (OLD_MSG: Memory.read loc old_ts mem1 = Some old)
      (VIEW_OLD: view_old = read_view (lc1.(coh) loc) old_ts)
      (VIEW_POST: view_post = view_old)
      (RES: res = ValA.mk _ old bot)
      (LC2: lc2 =
            mk
              (fun_add loc (join (lc1.(coh) loc) view_post) lc1.(coh))
              (join lc1.(vrn) view_post)
              lc1.(lper)
              lc1.(per)
              lc1.(promises))
  .
  Hint Constructors rmw_failure.

  Inductive dmb (rr rw wr ww:bool) (lc1 lc2:t): Prop :=
  | dmb_intro
      mloc
      (COHMAX: cohmax mloc lc1)
      (LC2: lc2 =
            mk
              lc1.(coh)
              (joins [lc1.(vrn); ifc wr (lc1.(coh) mloc)])
              lc1.(lper)
              (if (orb wr ww)
               then fun_join lc1.(per) lc1.(lper)
               else lc1.(per))
              lc1.(promises))
  .
  Hint Constructors dmb.

  Inductive write (vloc vval res:ValA.t (A:=unit)) (ts:Time.t) (tid:Id.t) (lc1:t) (mem1: Memory.t) (lc2:t) (mem2: Memory.t): Prop :=
  | write_intro
      loc val
      view_post
      (LOC: loc = vloc.(ValA.val))
      (VAL: val = vval.(ValA.val))
      (VIEW_POST: view_post = View.mk ts bot)
      (RES: res = ValA.mk _ 0 bot)
      (MEM: Memory.append (Msg.mk loc val tid) mem1 = (ts, mem2))
      (LC2: lc2 =
            mk
              (fun_add loc view_post lc1.(coh))
              lc1.(vrn)
              lc1.(lper)
              lc1.(per)
              lc1.(promises))
  .
  Hint Constructors write.

  Inductive vrmw (vloc vold vnew:ValA.t (A:=unit)) (old_ts:Time.t) (ts:Time.t) (tid:Id.t) (lc1:t) (mem1:Memory.t) (lc2:t) (mem2: Memory.t): Prop :=
  | vrmw_intro
      loc old new
      view_post
      (LOC: loc = vloc.(ValA.val))
      (COH: (lc1.(coh) loc).(View.ts) <= old_ts)
      (EX: Memory.exclusive tid loc old_ts ts mem2)
      (OLD_MSG: Memory.read loc old_ts mem1 = Some old)
      (OLD: old = vold.(ValA.val))
      (NEW: new = vnew.(ValA.val))
      (VIEW_POST: view_post = View.mk ts bot)
      (MEM: Memory.append (Msg.mk loc new tid) mem1 = (ts, mem2))
      (LC2: lc2 =
            mk
              (fun_add loc view_post lc1.(coh))
              (join lc1.(vrn) view_post)
              lc1.(lper)
              (fun_join lc1.(per) lc1.(lper))
              lc1.(promises))
  .
  Hint Constructors rmw.

  (* TODO: + same cacheline *)
  Inductive flush (vloc:ValA.t (A:=unit)) (lc1:t) (lc2:t): Prop :=
  | flush_intro
      loc view_post
      (LOC: loc = vloc.(ValA.val))
      (VIEW_POST: view_post = join (lc1.(coh) loc) lc1.(vrn))
      (LC2: lc2 =
            mk
              lc1.(coh)
              lc1.(vrn)
              (lc1.(lper))
              (fun_add loc (join (lc1.(per) loc) view_post) lc1.(per))
              lc1.(promises))
  .
  Hint Constructors flush.

  (* TODO: + same cacheline *)
  Inductive flushopt (vloc:ValA.t (A:=unit)) (lc1:t) (lc2:t): Prop :=
  | flushopt_intro
      loc view_post
      (LOC: loc = vloc.(ValA.val))
      (VIEW_POST: view_post = join (lc1.(coh) loc) lc1.(vrn))
      (LC2: lc2 =
            mk
              lc1.(coh)
              lc1.(vrn)
              (fun_add loc (join (lc1.(lper) loc) view_post) lc1.(lper))
              lc1.(per)
              lc1.(promises))
  .
  Hint Constructors flush.

  Inductive step (event:Event.t (A:=unit)) (tid:Id.t) (mem:Memory.t) (lc1 lc2:t): Prop :=
  | step_internal
      (EVENT: event = Event.internal)
      (LC: lc2 = lc1)
  | step_read
      vloc res ts ord
      (EVENT: event = Event.read false false ord vloc res)
      (STEP: read vloc res ts lc1 mem lc2)
  | step_fulfill
      vloc vval res ts ord
      (EVENT: event = Event.write false ord vloc vval res)
      (STEP: fulfill vloc vval res ts tid lc1 mem lc2)
  | step_rmw
      vloc vold vnew old_ts ts ordr ordw
      (EVENT: event = Event.rmw ordr ordw vloc vold vnew)
      (STEP: rmw vloc vold vnew old_ts ts tid lc1 mem lc2)
  | step_rmw_failure
      vloc vold old_ts ord res
      (EVENT: event = Event.read false true ord vloc res)
      (STEP: rmw_failure vloc vold res old_ts lc1 mem lc2)
  | step_dmb
      rr rw wr ww
      (EVENT: event = Event.barrier (Barrier.dmb rr rw wr ww))
      (STEP: dmb rr rw wr ww lc1 lc2)
  | step_flush
      vloc
      (EVENT: event = Event.flush vloc)
      (STEP: flush vloc lc1 lc2)
  | step_flushopt
      vloc
      (EVENT: event = Event.flushopt vloc)
      (STEP: flushopt vloc lc1 lc2)
  .
  Hint Constructors step.

  Inductive view_step (event:Event.t (A:=unit)) (tid:Id.t) (mem1 mem2:Memory.t) (lc1 lc2:t): Prop :=
  | view_step_internal
      (EVENT: event = Event.internal)
      (LC: lc2 = lc1)
      (MEM: mem2 = mem1)
  | view_step_read
      vloc res ts ord
      (EVENT: event = Event.read false false ord vloc res)
      (STEP: read vloc res ts lc1 mem1 lc2)
      (MEM: mem2 = mem1)
  | view_step_write
      vloc vval res ts ord
      (EVENT: event = Event.write false ord vloc vval res)
      (STEP: write vloc vval res ts tid lc1 mem1 lc2 mem2)
  | view_step_rmw
      vloc vold vnew old_ts ts ordr ordw
      (EVENT: event = Event.rmw ordr ordw vloc vold vnew)
      (STEP: vrmw vloc vold vnew old_ts ts tid lc1 mem1 lc2 mem2)
  | view_step_rmw_failure
      vloc vold old_ts ord res
      (EVENT: event = Event.read false true ord vloc res)
      (STEP: rmw_failure vloc vold res old_ts lc1 mem1 lc2)
      (MEM: mem2 = mem1)
  | view_step_dmb
      rr rw wr ww
      (EVENT: event = Event.barrier (Barrier.dmb rr rw wr ww))
      (STEP: dmb rr rw wr ww lc1 lc2)
      (MEM: mem2 = mem1)
  | view_step_flush
      vloc
      (EVENT: event = Event.flush vloc)
      (STEP: flush vloc lc1 lc2)
      (MEM: mem2 = mem1)
  | view_step_flushopt
      vloc
      (EVENT: event = Event.flushopt vloc)
      (STEP: flushopt vloc lc1 lc2)
      (MEM: mem2 = mem1)
  .
  Hint Constructors view_step.

  Inductive wf_fwdbank (loc:Loc.t) (mem:Memory.t) (coh: Time.t): Prop :=
  | wf_fwdbank_intro
      (VAL: exists val, Memory.read loc coh mem = Some val)
  .

  Inductive wf_cohmax (lc:t): Prop :=
  | wf_cohmax_intro
      mloc
      (COHMAX: cohmax mloc lc)
      (VRN: lc.(vrn).(View.ts) <= (lc.(coh) mloc).(View.ts))
  .

  Inductive wf (tid:Id.t) (mem:Memory.t) (lc:t): Prop :=
  | wf_intro
      (COH: forall loc, (lc.(coh) loc).(View.ts) <= List.length mem)
      (VRN: lc.(vrn).(View.ts) <= List.length mem)
      (LPER: forall loc, (lc.(lper) loc).(View.ts) <= List.length mem)
      (PER: forall loc, (lc.(per) loc).(View.ts) <= List.length mem)
      (FWDBANK: forall loc, wf_fwdbank loc mem (lc.(coh) loc).(View.ts))
      (PROMISES: forall ts (IN: Promises.lookup ts lc.(promises)), ts <= List.length mem)
      (PROMISES: forall ts msg
                   (MSG: Memory.get_msg ts mem = Some msg)
                   (TID: msg.(Msg.tid) = tid)
                   (TS: (lc.(coh) msg.(Msg.loc)).(View.ts) < ts),
          Promises.lookup ts lc.(promises))
      (COHMAX: wf_cohmax lc)
      (NFWD: forall ts msg
                (MSG: Memory.get_msg ts mem = Some msg)
                (TID: msg.(Msg.tid) <> tid)
                (TS: (lc.(coh) msg.(Msg.loc)).(View.ts) = ts),
          ts <= lc.(vrn).(View.ts))
  .
  Hint Constructors wf.

  Lemma init_wf tid: wf tid Memory.empty init.
  Proof.
    econs; ss; i; try by apply bot_spec.
    - econs; ss. eexists. ss.
    - destruct ts; ss.
    - destruct ts; ss. destruct ts; ss.
    - exists Loc.default; ss.
    - rewrite TS. ss.
  Qed.

  Lemma fwd_read_view_le
        tid mem lc loc ts
        (WF: wf tid mem lc):
    (read_view (lc.(coh) loc) ts).(View.ts) <= ts.
  Proof.
    inv WF. destruct (FWDBANK loc). des.
    unfold read_view. condtac; ss.
    apply bot_spec.
  Qed.

  Lemma wf_fwdbank_mon
        loc mem1 mem2 ts
        (FWDBANK: wf_fwdbank loc mem1 ts):
    wf_fwdbank loc (mem1 ++ mem2) ts.
  Proof.
    inv FWDBANK. des.
    econs. eexists. apply Memory.read_mon. eauto.
  Qed.

  Lemma read_spec
        tid mem vloc res ts lc1 lc2
        (WF: Local.wf tid mem lc1)
        (READ: Local.read vloc res ts lc1 mem lc2):
    <<LATEST: Memory.latest vloc.(ValA.val) ts lc2.(Local.vrn).(View.ts) mem>> /\
    <<COH: ts = (lc2.(Local.coh) vloc.(ValA.val)).(View.ts)>>.
  Proof.
    inv READ. ss. rewrite fun_add_spec. condtac; [|congr]. splits.
    - repeat apply Memory.latest_join; auto.
      apply Memory.ge_latest. eapply fwd_read_view_le; eauto.
    - unfold join. ss. apply le_antisym.
      + unfold read_view. des_ifs; ss; [| apply join_r].
        inv e0. apply join_l.
      + viewtac. eapply fwd_read_view_le; eauto.
  Qed.

  Lemma rmw_failure_spec
        tid mem vloc vold res old_ts lc1 lc2
        (WF: Local.wf tid mem lc1)
        (READ: Local.rmw_failure vloc vold res old_ts lc1 mem lc2):
    <<LATEST: Memory.latest vloc.(ValA.val) old_ts lc2.(Local.vrn).(View.ts) mem>> /\
    <<COH: old_ts = (lc2.(Local.coh) vloc.(ValA.val)).(View.ts)>>.
  Proof.
    inv READ. ss. rewrite fun_add_spec. condtac; [|congr]. splits.
    - repeat apply Memory.latest_join; auto.
      apply Memory.ge_latest. eapply fwd_read_view_le; eauto.
    - unfold join. ss. apply le_antisym.
      + unfold read_view. des_ifs; ss; [| apply join_r].
        inv e0. apply join_l.
      + viewtac. eapply fwd_read_view_le; eauto.
  Qed.

  Lemma rmw_spec
        tid mem vloc vold vnew old_ts ts lc1 lc2
        (WF: Local.wf tid mem lc1)
        (RMW: Local.rmw vloc vold vnew old_ts ts tid lc1 mem lc2):
    <<COH: ts = Memory.latest_ts vloc.(ValA.val) (lc2.(Local.coh) vloc.(ValA.val)).(View.ts) mem>>.
  Proof.
    inv RMW. ss. rewrite fun_add_spec. condtac; [|congr]. splits.
    - apply le_antisym; ss.
      + eapply Memory.latest_ts_read_le; eauto.
        eapply Memory.get_msg_read. eauto.
      + apply Memory.latest_latest_ts.
        apply Memory.ge_latest. ss.
  Qed.

  Lemma interference_wf
        tid (lc:t) mem mem_interference
        (INTERFERENCE: Forall (fun msg => msg.(Msg.tid) <> tid) mem_interference)
        (WF: wf tid mem lc):
    wf tid (mem ++ mem_interference) lc.
  Proof.
    inv WF. econs; i; ss.
    all: try rewrite app_length.
    all: try lia.
    - rewrite COH. lia.
    - rewrite LPER. lia.
    - rewrite PER. lia.
    - destruct (FWDBANK loc). des. econs; esplits; eauto.
      apply Memory.read_mon. eauto.
    - exploit PROMISES; eauto. lia.
    - apply Memory.get_msg_app_inv in MSG. des.
      + eapply PROMISES0; eauto.
      + apply nth_error_In in MSG0. eapply Forall_forall in INTERFERENCE; eauto.
        subst. destruct (nequiv_dec (Msg.tid msg) (Msg.tid msg)); ss. congr.
    - apply Memory.get_msg_app_inv in MSG. des.
      + eapply NFWD; eauto.
      + subst. specialize (COH (Msg.loc msg)). lia.
  Qed.

  Lemma wf_promises_above
        tid mem (lc:t) ts
        (WF: wf tid mem lc)
        (ABOVE: length mem < ts):
    Promises.lookup ts lc.(promises) = false.
  Proof.
    destruct (Promises.lookup ts (Local.promises lc)) eqn:X; ss.
    inv WF. exploit PROMISES; eauto. clear -ABOVE. lia.
  Qed.

  Inductive le (lhs rhs:t): Prop :=
  | le_intro
      (COH: forall loc, Order.le (lhs.(coh) loc).(View.ts) (rhs.(coh) loc).(View.ts))
      (VRN: Order.le lhs.(vrn).(View.ts) rhs.(vrn).(View.ts))
      (LPER: forall loc, Order.le (lhs.(lper) loc).(View.ts) (rhs.(lper) loc).(View.ts))
      (PER: forall loc, Order.le (lhs.(per) loc).(View.ts) (rhs.(per) loc).(View.ts))
  .

  Global Program Instance le_partial_order: PreOrder le.
  Next Obligation. econs; refl. Qed.
  Next Obligation. ii. inv H. inv H0. econs; etrans; eauto. Qed.

  Lemma writable_lt_coh_ts
        vloc vval tid lc mem ts
        (WRITABLE: writable vloc vval tid lc mem ts):
    lt (lc.(coh) vloc.(ValA.val)).(View.ts) ts.
  Proof.
    inv WRITABLE. inv COHMAX. specialize (COHMAX0 (ValA.val vloc)).
    unfold Order.le in *. lia.
  Qed.

  Lemma promise_incr
        loc val ts tid lc1 mem1 lc2 mem2
        (LC: promise loc val ts tid lc1 mem1 lc2 mem2):
    le lc1 lc2.
  Proof.
    inv LC. econs; ss; try refl; try apply join_l.
  Qed.

  Lemma read_incr
        vloc res ts lc1 mem1 lc2
        (LC: read vloc res ts lc1 mem1 lc2):
    le lc1 lc2.
  Proof.
    inv LC. econs; ss; try refl; try apply join_l.
    i. rewrite fun_add_spec. condtac; try refl.
    clear X. inv e. s. apply join_l.
  Qed.

  Lemma fulfill_incr
        vloc vval res ts tid lc1 mem1 lc2
        (LC: fulfill vloc vval res ts tid lc1 mem1 lc2):
    le lc1 lc2.
  Proof.
    inv LC. econs; ss; try refl; try apply join_l.
    i. rewrite fun_add_spec. condtac; try refl.
    clear X. inv e. s.
    unfold Order.le. exploit writable_lt_coh_ts; eauto. lia.
  Qed.

  Lemma rmw_incr
        vloc vold vnew old_ts ts tid lc1 mem lc2
        (LC: rmw vloc vold vnew old_ts ts tid lc1 mem lc2):
    le lc1 lc2.
  Proof.
    inv LC. econs; ss; try refl; try apply join_l.
    - i. funtac. inversion e.
      unfold Order.le. exploit writable_lt_coh_ts; eauto. lia.
    - i. apply join_l.
  Qed.

  Lemma rmw_failure_incr
        vloc vold res ts lc1 mem1 lc2
        (LC: rmw_failure vloc vold res ts lc1 mem1 lc2):
    le lc1 lc2.
  Proof.
    inv LC. econs; ss; try refl; try apply join_l.
    i. rewrite fun_add_spec. condtac; try refl.
    clear X. inv e. s. apply join_l.
  Qed.

  Lemma dmb_incr
        rr rw wr ww lc1 lc2
        (LC: dmb rr rw wr ww lc1 lc2):
    le lc1 lc2.
  Proof.
    inv LC. econs; ss; try refl; try apply join_l.
    i. condtac; ss. apply join_l.
  Qed.

  Lemma flush_incr
        vloc lc1 lc2
        (LC: flush vloc lc1 lc2):
    le lc1 lc2.
  Proof.
    inv LC. econs; ss; try refl.
    i. funtac. inversion e. apply join_l.
  Qed.

  Lemma flushopt_incr
        vloc lc1 lc2
        (LC: flushopt vloc lc1 lc2):
    le lc1 lc2.
  Proof.
    inv LC. econs; ss; try refl.
    i. funtac. inversion e. apply join_l.
  Qed.

  Lemma step_incr
        e tid mem lc1 lc2
        (LC: step e tid mem lc1 lc2):
    le lc1 lc2.
  Proof.
    inv LC; try refl.
    - eapply read_incr. eauto.
    - eapply fulfill_incr. eauto.
    - eapply rmw_incr. eauto.
    - eapply rmw_failure_incr. eauto.
    - eapply dmb_incr. eauto.
    - eapply flush_incr. eauto.
    - eapply flushopt_incr. eauto.
  Qed.

  Lemma high_ts_spec
        tid mem lc ts
        (WF: wf tid mem lc)
        (GT: forall loc, (lc.(coh) loc).(View.ts) < ts):
      <<NOFWD: forall loc, read_view (lc.(coh) loc) ts = View.mk ts bot >> /\
      <<JOINS: forall loc, ts = join (lc.(coh) loc).(View.ts)
                                     (read_view (lc.(coh) loc) ts).(View.ts)>>.
  Proof.
    assert (NOFWD: forall loc, read_view (lc.(coh) loc) ts = View.mk ts bot).
    { i. unfold read_view. condtac; ss.
      inversion e. inv H. inv WF.
      specialize (FWDBANK loc). inv FWDBANK.
      assert (COHLE: Memory.latest_ts loc (View.ts (coh lc loc)) mem <= View.ts (coh lc loc)).
      { eapply Memory.latest_ts_spec. }
      specialize (GT loc).
      lia.
    }
    splits; ss. i. apply le_antisym.
    { repeat rewrite <- join_r. rewrite NOFWD. ss. }
    inv WF. inv COHMAX. viewtac.
    - specialize (GT loc). lia.
    - rewrite NOFWD. ss.
  Qed.

  Lemma step_wf
        tid e mem lc1 lc2
        (STEP: step e tid mem lc1 lc2)
        (WF: wf tid mem lc1):
    wf tid mem lc2.
  Proof.
    assert (FWDVIEW: forall loc ts,
               (View.ts (coh lc1 loc)) <= ts ->
               ts <= length mem ->
               View.ts (read_view (coh lc1 loc) ts) <= length mem).
    { i. rewrite fwd_read_view_le; eauto. }
    inversion WF. inv STEP; ss; inv STEP0.
    - exploit FWDVIEW; eauto.
      { eapply Memory.read_wf. eauto. }
      i. econs; viewtac.
      + i. rewrite fun_add_spec. condtac; viewtac.
      + i. exploit FWDBANK; eauto. intro Y. inv Y. des.
        econs; eauto. rewrite fun_add_spec. condtac; ss; eauto.
        inversion e. subst.
        unfold read_view. condtac; ss.
        * eexists val0. rewrite bot_join; [|apply Time.order]. ss.
        * eexists val. rewrite le_join; [|apply Time.order|]; eauto.
      + i. eapply PROMISES0; eauto. eapply Time.le_lt_trans; [|by eauto].
        rewrite fun_add_spec. condtac; ss. inversion e. rewrite H0. apply join_l.
      + inv COHMAX. inv COHMAX0. destruct (lt_eq_lt_dec ts (View.ts (coh lc1 mloc))).
        { econs; ss. instantiate (1 := mloc).
          - econs; ss.
            i. repeat rewrite fun_add_spec. repeat condtac; ss.
            + viewtac. unfold read_view.
              condtac; [apply bot_spec | inv s; ss; lia].
            + inversion e. subst.
            specialize (COHMAX loc). rewrite <- join_l. ss.
          - rewrite fun_add_spec. condtac; ss.
            + inversion e. subst.
              unfold join. unfold Time.join. lia.
            + viewtac. unfold read_view.
              condtac; [apply bot_spec | inv s; ss; lia].
        }
        { exploit high_ts_spec; eauto.
          { i. eapply le_lt_trans; try exact l; eauto. }
          i. des.
          econs; ss. instantiate (1 := (ValA.val vloc)).
          - econs; ss.
            i. repeat rewrite fun_add_spec. repeat condtac; ss; cycle 2.
            { exfalso. apply c0. ss. }
            { exfalso. apply c. ss. }
            exploit high_ts_spec; eauto.
            { i. eapply le_lt_trans; try exact l; eauto. }
            i. des.
            rewrite NOFWD. repeat rewrite <- join_r. ss.
            specialize (COHMAX loc). lia.
          - rewrite fun_add_spec. condtac; ss.
            + rewrite NOFWD. ss. viewtac; rewrite <- join_r; lia.
            + exfalso. apply c. ss.
        }
      + i. revert TS. rewrite fun_add_spec. condtac; ss; cycle 1.
        { i. rewrite <- join_l. eapply NFWD; eauto. }
        unfold read_view. condtac; ss.
        * rewrite bot_join; [|apply Time.order]. rewrite (bot_join (View.ts (vrn lc1))).
          intro TS. rewrite <- TS in *.
          eapply NFWD; eauto. inversion e. ss.
        * i. rewrite <- TS. viewtac; rewrite <- join_r; ss.
    - inversion WRITABLE.
      econs; viewtac; rewrite <- ? TS0, <- ? TS1.
      + i. rewrite fun_add_spec. condtac; viewtac.
      + i. rewrite ? fun_add_spec. condtac; viewtac.
        inversion e. subst.
        econs; viewtac.
        revert MSG. unfold Memory.read, Memory.get_msg.
        destruct ts; ss. i. rewrite MSG. ss. eexists. des_ifs.
      + i. revert IN. rewrite Promises.unset_o. condtac; ss. eauto.
      + i. rewrite Promises.unset_o. rewrite fun_add_spec in TS. condtac.
        { inversion e. subst. rewrite MSG in MSG0. destruct msg. inv MSG0. ss.
          revert TS. condtac; ss; intuition.
        }
        { eapply PROMISES0; eauto. revert TS. condtac; ss. i.
          inversion e. rewrite H0.
          exploit writable_lt_coh_ts; eauto. lia.
        }
      + inv COHMAX. inv COHMAX0. inv COHMAX1. econs; ss. instantiate (1 := ValA.val vloc).
        * econs; ss.
          i. repeat rewrite fun_add_spec. repeat condtac; ss; cycle 2.
          { exfalso. apply c0. ss. }
          { exfalso. apply c. ss. }
          specialize (COHMAX loc). lia.
        * rewrite fun_add_spec. condtac; ss; cycle 1.
          { exfalso. apply c. ss. }
          specialize (COHMAX mloc0). lia.
      + i. eapply NFWD; eauto.
        rewrite fun_add_spec in TS. eqvtac.
        rewrite MSG in MSG0. inv MSG0. ss.
    - inversion WRITABLE.
      econs; viewtac; rewrite <- ? TS0, <- ? TS1.
      + i. rewrite fun_add_spec. condtac; viewtac.
      + i. viewtac.
      + i. rewrite ? fun_add_spec. condtac; viewtac.
        inversion e. subst.
        econs; viewtac.
        revert MSG. unfold Memory.read, Memory.get_msg.
        destruct ts; ss. i. rewrite MSG. ss. eexists. des_ifs.
      + i. revert IN. rewrite Promises.unset_o. condtac; ss. eauto.
      + i. rewrite Promises.unset_o. rewrite fun_add_spec in TS. condtac.
        { inversion e. subst. rewrite MSG in MSG0. destruct msg. inv MSG0. ss.
        revert TS. condtac; ss; intuition.
        }
        { eapply PROMISES0; eauto. revert TS. condtac; ss. i.
          inversion e. rewrite H0.
          exploit writable_lt_coh_ts; eauto. lia.
        }
      + inv COHMAX. inv COHMAX0. inv COHMAX1. econs; ss. instantiate (1 := ValA.val vloc).
        * econs; ss.
          i. repeat rewrite fun_add_spec. repeat condtac; ss; cycle 2.
          { exfalso. apply c0. ss. }
          { exfalso. apply c. ss. }
          specialize (COHMAX loc). lia.
        * rewrite fun_add_spec. condtac; ss; cycle 1.
          { exfalso. apply c. ss. }
          viewtac. specialize (COHMAX mloc0). lia.
      + i. rewrite <- join_l. eapply NFWD; eauto.
        rewrite fun_add_spec in TS. eqvtac.
        rewrite MSG in MSG0. inv MSG0. ss.
    - exploit FWDVIEW; eauto.
      { eapply Memory.read_wf. eauto. }
      i. econs; viewtac.
      + i. rewrite fun_add_spec. condtac; viewtac.
      + i. exploit FWDBANK; eauto. intro Y. inv Y. des.
        econs; eauto. rewrite fun_add_spec. condtac; ss; eauto.
        inversion e. subst.
        unfold read_view. condtac; ss.
        * eexists val. rewrite bot_join; [|apply Time.order]. ss.
        * eexists old. rewrite le_join; [|apply Time.order|]; eauto.
      + i. eapply PROMISES0; eauto. eapply Time.le_lt_trans; [|by eauto].
        rewrite fun_add_spec. condtac; ss. inversion e. rewrite H0. apply join_l.
      + inv COHMAX. inv COHMAX0. destruct (lt_eq_lt_dec old_ts (View.ts (coh lc1 mloc))).
        { econs; ss. instantiate (1 := mloc).
          - econs; ss.
            i. repeat rewrite fun_add_spec. repeat condtac; ss.
            + viewtac. unfold read_view.
              condtac; [apply bot_spec | inv s; ss; lia].
            + inversion e. subst.
            specialize (COHMAX loc). rewrite <- join_l. ss.
          - rewrite fun_add_spec. condtac; ss.
            + inversion e. subst.
              unfold join. unfold Time.join. lia.
            + viewtac. unfold read_view.
              condtac; [apply bot_spec | inv s; ss; lia].
        }
        { exploit high_ts_spec; eauto.
          { i. eapply le_lt_trans; try exact l; eauto. }
          i. des.
          econs; ss. instantiate (1 := (ValA.val vloc)).
          - econs; ss.
            i. repeat rewrite fun_add_spec. repeat condtac; ss; cycle 2.
            { exfalso. apply c0. ss. }
            { exfalso. apply c. ss. }
            rewrite NOFWD. repeat rewrite <- join_r. ss.
            specialize (COHMAX loc). lia.
          - rewrite fun_add_spec. condtac; ss.
            + rewrite NOFWD. ss. viewtac; rewrite <- join_r; lia.
            + exfalso. apply c. ss.
        }
      + i. revert TS. rewrite fun_add_spec. condtac; ss; cycle 1.
        { i. rewrite <- join_l. eapply NFWD; eauto. }
        unfold read_view. condtac; ss.
        * rewrite bot_join; [|apply Time.order]. rewrite (bot_join (View.ts (vrn lc1))).
          intro TS. rewrite <- TS in *.
          eapply NFWD; eauto. inversion e. ss.
        * i. rewrite <- TS. viewtac; rewrite <- join_r; ss.
    - econs; viewtac.
      + i. condtac; ss. viewtac.
      + inv COHMAX0. econs; [econs|]; ss.
        viewtac. inv COHMAX. specialize (COHMAX1 mloc0). lia.
      + i. rewrite <- join_l. eapply NFWD; eauto.
    - econs; viewtac.
      + i. funtac. viewtac.
      + inv COHMAX. inv COHMAX0. econs; [econs|]; ss.
    - econs; viewtac.
      + i. funtac. viewtac.
      + inv COHMAX. inv COHMAX0. econs; [econs|]; ss.
  Qed.

  Lemma view_step_wf
        tid e mem1 mem2 lc1 lc2
        (STEP: view_step e tid mem1 mem2 lc1 lc2)
        (WF: wf tid mem1 lc1):
    wf tid mem2 lc2.
  Proof.
    assert (FWDVIEW: forall loc ts,
               (View.ts (coh lc1 loc)) <= ts ->
               ts <= length mem1 ->
               View.ts (read_view (coh lc1 loc) ts) <= length mem1).
    { i. rewrite fwd_read_view_le; eauto. }
    inversion WF. inv STEP; ss; inv STEP0.
    - exploit FWDVIEW; eauto.
      { eapply Memory.read_wf. eauto. }
      i. econs; viewtac.
      + i. rewrite fun_add_spec. condtac; viewtac.
      + i. exploit FWDBANK; eauto. intro Y. inv Y. des.
        econs; eauto. rewrite fun_add_spec. condtac; ss; eauto.
        inversion e. subst.
        unfold read_view. condtac; ss.
        * eexists val0. rewrite bot_join; [|apply Time.order]. ss.
        * eexists val. rewrite le_join; [|apply Time.order|]; eauto.
      + i. eapply PROMISES0; eauto. eapply Time.le_lt_trans; [|by eauto].
        rewrite fun_add_spec. condtac; ss. inversion e. rewrite H0. apply join_l.
      + inv COHMAX. inv COHMAX0. destruct (lt_eq_lt_dec ts (View.ts (coh lc1 mloc))).
        { econs; ss. instantiate (1 := mloc).
          - econs; ss.
            i. repeat rewrite fun_add_spec. repeat condtac; ss.
            + viewtac. unfold read_view.
              condtac; [apply bot_spec | inv s; ss; lia].
            + inversion e. subst.
            specialize (COHMAX loc). rewrite <- join_l. ss.
          - rewrite fun_add_spec. condtac; ss.
            + inversion e. subst.
              unfold join. unfold Time.join. lia.
            + viewtac. unfold read_view.
              condtac; [apply bot_spec | inv s; ss; lia].
        }
        { exploit high_ts_spec; eauto.
          { i. eapply le_lt_trans; try exact l; eauto. }
          i. des.
          econs; ss. instantiate (1 := (ValA.val vloc)).
          - econs; ss.
            i. repeat rewrite fun_add_spec. repeat condtac; ss; cycle 2.
            { exfalso. apply c0. ss. }
            { exfalso. apply c. ss. }
            exploit high_ts_spec; eauto.
            { i. eapply le_lt_trans; try exact l; eauto. }
            i. des.
            rewrite NOFWD. repeat rewrite <- join_r. ss.
            specialize (COHMAX loc). lia.
          - rewrite fun_add_spec. condtac; ss.
            + rewrite NOFWD. ss. viewtac; rewrite <- join_r; lia.
            + exfalso. apply c. ss.
        }
      + i. revert TS. rewrite fun_add_spec. condtac; ss; cycle 1.
        { i. rewrite <- join_l. eapply NFWD; eauto. }
        unfold read_view. condtac; ss.
        * rewrite bot_join; [|apply Time.order]. rewrite (bot_join (View.ts (vrn lc1))).
          intro TS. rewrite <- TS in *.
          eapply NFWD; eauto. inversion e. ss.
        * i. rewrite <- TS. viewtac; rewrite <- join_r; ss.
    - inversion MEM. subst. econs; try rewrite app_length; viewtac; ss.
      all: try by lia.
      + i. funtac; try rewrite COH; lia.
      + i. rewrite LPER. lia.
      + i. rewrite PER. lia.
      + i. funtac; cycle 1.
        { apply wf_fwdbank_mon. specialize (FWDBANK loc). ss. }
        inversion e. subst. econs.
        exploit Memory.append_spec; eauto.
        unfold Memory.read, Memory.get_msg. destruct (S (length mem1)); ss. intro MSG. des.
        rewrite MSG. ss. eexists. des_ifs.
      + i. apply PROMISES in IN. lia.
      + i. inv MEM. eapply PROMISES0; eauto.
        * generalize MSG. intro X.
          eapply Memory.get_msg_snoc_inv in X. des; ss.
          revert TS. funtac.
          { i. lia. }
          exfalso. apply c. inv X0. ss.
        * revert TS. funtac. i.
          etrans; try exact TS; eauto. eapply le_lt_trans; [rewrite COH; eauto | lia].
      + unfold Memory.append in MEM. inv MEM.
        econs; ss. instantiate (1 := ValA.val vloc).
        * econs. i. funtac.
        * funtac.
      + i. inv MEM.
        eapply Memory.get_msg_snoc_inv in MSG. revert MSG. funtac.
        * i. des; [lia |]. inv MSG0. ss.
        * i. des; [eapply NFWD; eauto |]. inv MSG0. ss.
    - inversion MEM. subst. econs; try rewrite app_length; viewtac; ss.
      all: try by lia.
      + i. funtac; try rewrite COH; lia.
      + i. rewrite LPER. lia.
      + i. viewtac; [rewrite PER|rewrite LPER]; lia.
      + i. funtac; cycle 1.
        { apply wf_fwdbank_mon. specialize (FWDBANK loc). ss. }
        inversion e. subst. econs.
        exploit Memory.append_spec; eauto.
        unfold Memory.read, Memory.get_msg. destruct (S (length mem1)); ss. intro MSG. des.
        rewrite MSG. ss. eexists. des_ifs.
      + i. apply PROMISES in IN. lia.
      + i. inv MEM. eapply PROMISES0; eauto.
        * generalize MSG. intro X.
          eapply Memory.get_msg_snoc_inv in X. des; ss.
          revert TS. funtac.
          { i. lia. }
          exfalso. apply c. inv X0. ss.
        * revert TS. funtac. i.
          etrans; try exact TS; eauto. eapply le_lt_trans; [rewrite COH; eauto | lia].
      + unfold Memory.append in MEM. inv MEM.
        econs; ss. instantiate (1 := ValA.val vloc).
        * econs. i. funtac.
        * funtac. viewtac.
      + i. inv MEM.
        eapply Memory.get_msg_snoc_inv in MSG. revert MSG. funtac.
        * i. des; [lia |]. inv MSG0. ss.
        * i. rewrite <- join_l. des; [eapply NFWD; eauto |]. inv MSG0. ss.
    - exploit FWDVIEW; eauto.
      { eapply Memory.read_wf. eauto. }
      i. econs; viewtac.
      + i. rewrite fun_add_spec. condtac; viewtac.
      + i. exploit FWDBANK; eauto. intro Y. inv Y. des.
        econs; eauto. rewrite fun_add_spec. condtac; ss; eauto.
        inversion e. subst.
        unfold read_view. condtac; ss.
        * eexists val. rewrite bot_join; [|apply Time.order]. ss.
        * eexists old. rewrite le_join; [|apply Time.order|]; eauto.
      + i. eapply PROMISES0; eauto. eapply Time.le_lt_trans; [|by eauto].
        rewrite fun_add_spec. condtac; ss. inversion e. rewrite H0. apply join_l.
      + inv COHMAX. inv COHMAX0. destruct (lt_eq_lt_dec old_ts (View.ts (coh lc1 mloc))).
        { econs; ss. instantiate (1 := mloc).
          - econs; ss.
            i. repeat rewrite fun_add_spec. repeat condtac; ss.
            + viewtac. unfold read_view.
              condtac; [apply bot_spec | inv s; ss; lia].
            + inversion e. subst.
            specialize (COHMAX loc). rewrite <- join_l. ss.
          - rewrite fun_add_spec. condtac; ss.
            + inversion e. subst.
              unfold join. unfold Time.join. lia.
            + viewtac. unfold read_view.
              condtac; [apply bot_spec | inv s; ss; lia].
        }
        { exploit high_ts_spec; eauto.
          { i. eapply le_lt_trans; try exact l; eauto. }
          i. des.
          econs; ss. instantiate (1 := (ValA.val vloc)).
          - econs; ss.
            i. repeat rewrite fun_add_spec. repeat condtac; ss; cycle 2.
            { exfalso. apply c0. ss. }
            { exfalso. apply c. ss. }
            rewrite NOFWD. repeat rewrite <- join_r. ss.
            specialize (COHMAX loc). lia.
          - rewrite fun_add_spec. condtac; ss.
            + rewrite NOFWD. ss. viewtac; rewrite <- join_r; lia.
            + exfalso. apply c. ss.
        }
      + i. revert TS. rewrite fun_add_spec. condtac; ss; cycle 1.
        { i. rewrite <- join_l. eapply NFWD; eauto. }
        unfold read_view. condtac; ss.
        * rewrite bot_join; [|apply Time.order]. rewrite (bot_join (View.ts (vrn lc1))).
          intro TS. rewrite <- TS in *.
          eapply NFWD; eauto. inversion e. ss.
        * i. rewrite <- TS. viewtac; rewrite <- join_r; ss.
    - econs; viewtac.
      + i. condtac; ss. viewtac.
      + inv COHMAX0. econs; [econs|]; ss.
        viewtac. inv COHMAX. specialize (COHMAX1 mloc0). lia.
      + i. rewrite <- join_l. eapply NFWD; eauto.
    - econs; viewtac.
      + i. funtac. viewtac.
      + inv COHMAX. inv COHMAX0. econs; [econs|]; ss.
    - econs; viewtac.
      + i. funtac. viewtac.
      + inv COHMAX. inv COHMAX0. econs; [econs|]; ss.
  Qed.
End Local.
End Local.

Module ExecUnit.
Section ExecUnit.
  Inductive t := mk {
    state: State.t (A:=unit);
    local: Local.t;
    mem: Memory.t;
  }.
  Hint Constructors t.

  Inductive state_step0 (tid:Id.t) (e1 e2:Event.t (A:=unit)) (eu1 eu2:t): Prop :=
  | state_step0_intro
      (STATE: State.step e1 eu1.(state) eu2.(state))
      (LOCAL: Local.step e2 tid eu1.(mem) eu1.(local) eu2.(local))
      (MEM: eu2.(mem) = eu1.(mem))
  .
  Hint Constructors state_step0.

  Inductive state_step (tid:Id.t) (eu1 eu2:t): Prop :=
  | state_step_intro
      e
      (STEP: state_step0 tid e e eu1 eu2)
  .
  Hint Constructors state_step.

  Inductive promise_step (tid:Id.t) (eu1 eu2:t): Prop :=
  | promise_step_intro
      loc val ts
      (STATE: eu1.(state) = eu2.(state))
      (LOCAL: Local.promise loc val ts tid eu1.(local) eu1.(mem) eu2.(local) eu2.(mem))
  .
  Hint Constructors promise_step.

  Inductive step (tid:Id.t) (eu1 eu2:t): Prop :=
  | step_state (STEP: state_step tid eu1 eu2)
  | step_promise (STEP: promise_step tid eu1 eu2)
  .
  Hint Constructors step.

  Inductive view_step0 (tid:Id.t) (e1 e2:Event.t (A:=unit)) (eu1 eu2:t): Prop :=
  | view_step0_intro
      (STATE: State.step e1 eu1.(state) eu2.(state))
      (LOCAL: Local.view_step e2 tid eu1.(mem) eu2.(mem) eu1.(local) eu2.(local))
  .
  Hint Constructors view_step0.

  Inductive view_step (tid:Id.t) (eu1 eu2:t): Prop :=
  | view_step_intro
      e
      (STEP: view_step0 tid e e eu1 eu2)
  .
  Hint Constructors view_step.

  Inductive wf (tid:Id.t) (eu:t): Prop :=
  | wf_intro
      (LOCAL: Local.wf tid eu.(mem) eu.(local))
  .
  Hint Constructors wf.

  Lemma state_step0_wf tid e eu1 eu2
        (STEP: state_step0 tid e e eu1 eu2)
        (WF: wf tid eu1):
    wf tid eu2.
  Proof.
    inv WF. inv STEP. econs; ss.
    rewrite MEM. eapply Local.step_wf; eauto.
  Qed.

  Lemma state_step_wf tid eu1 eu2
        (STEP: state_step tid eu1 eu2)
        (WF: wf tid eu1):
    wf tid eu2.
  Proof.
    inv STEP. eapply state_step0_wf; eauto.
  Qed.

  Lemma rtc_state_step_wf tid eu1 eu2
        (STEP: rtc (state_step tid) eu1 eu2)
        (WF: wf tid eu1):
    wf tid eu2.
  Proof.
    revert WF. induction STEP; ss. i. apply IHSTEP.
    eapply state_step_wf; eauto.
  Qed.

  Lemma promise_step_wf tid eu1 eu2
        (STEP: promise_step tid eu1 eu2)
        (WF: wf tid eu1):
    wf tid eu2.
  Proof.
    destruct eu1 as [state1 local1 mem1].
    destruct eu2 as [state2 local2 mem2].
    inv WF. inv STEP. ss. subst.
    inv LOCAL. inv LOCAL0. inv MEM2. econs; ss.
    econs; eauto.
    all: try rewrite List.app_length; s; try lia.
    - i. rewrite COH. lia.
    - i. rewrite LPER. lia.
    - i. rewrite PER. lia.
    - i. destruct (FWDBANK loc0). des. econs; esplits; ss.
      apply Memory.read_mon; eauto.
    - i. revert IN. rewrite Promises.set_o. condtac.
      + inversion e. i. inv IN. lia.
      + i. exploit PROMISES; eauto. lia.
    - i. rewrite Promises.set_o. apply Memory.get_msg_snoc_inv in MSG. des.
      + destruct ts; ss. condtac; ss.
        eapply PROMISES0; eauto.
      + subst. condtac; ss. congr.
    - inv COHMAX. inv COHMAX0. econs; [econs|]; ss.
    - i. apply Memory.get_msg_snoc_inv in MSG. des.
      + eapply NFWD; eauto.
      + rewrite <- MSG0 in TID. ss.
  Qed.

  Lemma step_wf tid eu1 eu2
        (STEP: step tid eu1 eu2)
        (WF: wf tid eu1):
    wf tid eu2.
  Proof.
    inv STEP.
    - eapply state_step_wf; eauto.
    - eapply promise_step_wf; eauto.
  Qed.

  Lemma view_step0_wf tid e eu1 eu2
        (STEP: view_step0 tid e e eu1 eu2)
        (WF: wf tid eu1):
    wf tid eu2.
  Proof.
    inv WF. inv STEP. econs; ss.
    eapply Local.view_step_wf; eauto.
  Qed.

  Lemma view_step_wf tid eu1 eu2
        (STEP: view_step tid eu1 eu2)
        (WF: wf tid eu1):
    wf tid eu2.
  Proof.
    inv STEP. eapply view_step0_wf; eauto.
  Qed.

  Lemma rtc_view_step_wf tid eu1 eu2
        (STEP: rtc (view_step tid) eu1 eu2)
        (WF: wf tid eu1):
    wf tid eu2.
  Proof.
    revert WF. induction STEP; ss. i. apply IHSTEP.
    eapply view_step_wf; eauto.
  Qed.

  Inductive le (eu1 eu2:t): Prop :=
  | le_intro
      mem'
      (LC: Local.le eu1.(local) eu2.(local))
      (MEM: eu2.(mem) = eu1.(mem) ++ mem')
  .

  Global Program Instance le_partial_order: PreOrder le.
  Next Obligation.
    econs.
    - refl.
    - rewrite app_nil_r. ss.
  Qed.
  Next Obligation.
    ii. inv H. inv H0. econs; etrans; eauto.
    rewrite MEM, app_assoc. eauto.
  Qed.

  Lemma state_step_incr tid eu1 eu2
        (STEP: state_step tid eu1 eu2):
    le eu1 eu2.
  Proof.
    inv STEP. inv STEP0. econs.
    - eapply Local.step_incr. eauto.
    - rewrite MEM, app_nil_r. ss.
  Qed.

  Lemma promise_step_incr tid eu1 eu2
        (STEP: promise_step tid eu1 eu2):
    le eu1 eu2.
  Proof.
    inv STEP. econs.
    - eapply Local.promise_incr. eauto.
    - inv LOCAL. inv MEM2. ss.
  Qed.

  Lemma step_incr tid eu1 eu2
        (STEP: step tid eu1 eu2):
    le eu1 eu2.
  Proof.
    inv STEP.
    - eapply state_step_incr. eauto.
    - eapply promise_step_incr. eauto.
  Qed.

  Lemma state_step_promise_remained tid eu1 eu2 ts loc val
        (WF: wf tid eu1)
        (STEP: state_step tid eu1 eu2)
        (LE: ts <= (eu1.(ExecUnit.local).(Local.coh) loc).(View.ts))
        (MSG: Memory.get_msg ts eu1.(ExecUnit.mem) = Some (Msg.mk loc val tid))
        (PROMISE: Promises.lookup ts eu1.(ExecUnit.local).(Local.promises)):
    Promises.lookup ts eu2.(ExecUnit.local).(Local.promises).
  Proof.
    inv STEP. inv STEP0. inv LOCAL.
    - rewrite LC. ss.
    - inv STEP. rewrite LC2. ss.
    - inv STEP. rewrite LC2. ss.
      destruct (ts == ts0).
      + inv e. rewrite MSG in MSG0. inv MSG0.
        exploit Local.writable_lt_coh_ts; eauto. lia.
      + exploit Promises.unset_o. intro UNSET.
        rewrite UNSET. eqvtac.
    - inv STEP. rewrite LC2. ss.
      destruct (ts == ts0).
      + inv e. rewrite MSG in MSG0. inv MSG0.
        exploit Local.writable_lt_coh_ts; eauto. lia.
      + exploit Promises.unset_o. intro UNSET.
        rewrite UNSET. eqvtac.
    - inv STEP. rewrite LC2. ss.
    - inv STEP. rewrite LC2. ss.
    - inv STEP. rewrite LC2. ss.
    - inv STEP. rewrite LC2. ss.
  Qed.

  Lemma rtc_state_step_promise_remained tid eu1 eu2 ts loc val
        (WF: Local.wf tid eu1.(ExecUnit.mem) eu1.(ExecUnit.local))
        (STEP: rtc (state_step tid) eu1 eu2)
        (LE: ts <= (eu1.(ExecUnit.local).(Local.coh) loc).(View.ts))
        (MSG: Memory.get_msg ts eu1.(ExecUnit.mem) = Some (Msg.mk loc val tid))
        (PROMISE: Promises.lookup ts eu1.(ExecUnit.local).(Local.promises)):
    Promises.lookup ts eu2.(ExecUnit.local).(Local.promises).
  Proof.
    induction STEP; ss. eapply IHSTEP.
    - eapply state_step_wf; eauto.
    - inv H. inv STEP0. inv LOCAL.
      + rewrite LC. ss.
      + inv STEP0. rewrite LC2. ss. rewrite fun_add_spec. condtac; ss.
        inversion e. subst. etrans; eauto. apply join_l.
      + inv STEP0. rewrite LC2. ss. rewrite fun_add_spec. condtac; ss.
        inversion e. subst. exploit Local.writable_lt_coh_ts; eauto. lia.
      + inv STEP0. rewrite LC2. ss. rewrite fun_add_spec. condtac; ss.
        inversion e. subst. exploit Local.writable_lt_coh_ts; eauto. lia.
      + inv STEP0. rewrite LC2. ss. rewrite fun_add_spec. condtac; ss.
        inversion e. subst. etrans; eauto. apply join_l.
      + inv STEP0. rewrite LC2. ss.
      + inv STEP0. rewrite LC2. ss.
      + inv STEP0. rewrite LC2. ss.
    - inv H. inv STEP0. rewrite MEM. ss.
    - exploit state_step_promise_remained; eauto.
  Qed.

  Lemma rtc_state_step_mem
        tid eu1 eu2
        (STEP: rtc (ExecUnit.state_step tid) eu1 eu2):
    eu1.(ExecUnit.mem) = eu2.(ExecUnit.mem).
  Proof.
    induction STEP; ss.
    inv H. inv STEP0. rewrite <- MEM. ss.
  Qed.

  Lemma no_promise_rmw_spec
        eu1 eu2 eu_last
        vloc vold vnew old_ts ts tid
        (WF: Local.wf tid eu1.(ExecUnit.mem) eu1.(ExecUnit.local))
        (MEM: eu1.(ExecUnit.mem) = eu2.(ExecUnit.mem))
        (RMW_STEP: Local.rmw vloc vold vnew old_ts ts tid eu1.(ExecUnit.local) eu1.(ExecUnit.mem) eu2.(ExecUnit.local))
        (RTC_STEP: rtc (ExecUnit.state_step tid) eu2 eu_last)
        (NOPROMISE: eu_last.(ExecUnit.local).(Local.promises) = bot):
      old_ts = Memory.latest_ts (ValA.val vloc) (Init.Nat.pred ts) (eu1.(ExecUnit.mem)).
  Proof.
    generalize RMW_STEP. intro RMW. inv RMW.
    eapply le_antisym; ss.
    { eapply Memory.latest_ts_read_le; eauto. lia. }
    eapply Memory.latest_latest_ts. ii.
    unfold Memory.exclusive in EX. unfold Memory.no_msgs in EX. exploit EX; eauto.
    { etrans; eauto. lia. }
    split; ss. destruct msg as [ts' val' tidtmp]. destruct (tidtmp == tid); ss. inv e.
    unfold Memory.latest in COH. unfold Memory.no_msgs in COH.
    destruct (lt_eq_lt_dec (S ts0) (View.ts (Local.coh (ExecUnit.local eu1) (ValA.val vloc)))). inv s; try lia.
    inversion WF.
    exploit PROMISES0; [| | instantiate (1 := S ts0)|]; eauto. intro PROMISE_TS.
    assert (PROMISE_TS0: Promises.lookup (S ts0) (Local.promises (ExecUnit.local eu2))).
    { rewrite LC2. ss. exploit Promises.unset_o. intro UNSET. rewrite UNSET. condtac; ss. inversion e. lia. }
    exploit ExecUnit.rtc_state_step_promise_remained; try exact PROMISE_TS0; eauto.
    { rewrite <- MEM. eapply Local.step_wf; eauto. econs 4; eauto. }
    { instantiate (1 := ValA.val vloc). rewrite LC2. ss.
      rewrite fun_add_spec. condtac; cycle 1.
      { exfalso. apply c. ss. }
      etrans; eauto. ss. lia.
    }
    { rewrite <- MEM. unfold Memory.get_msg. ss. rewrite MSG0. ss. }
    unfold Promises.lookup. ss. rewrite NOPROMISE. ss.
    Grab Existential Variables.
    all: auto.
  Qed.
End ExecUnit.
End ExecUnit.

Module Machine.
  Inductive t := mk {
    tpool: IdMap.t (State.t (A:=unit) * Local.t);
    mem: Memory.t;
  }.
  Hint Constructors t.

  Definition init (p:program): t :=
    mk
      (IdMap.map (fun stmts => (State.init stmts, Local.init)) p)
      Memory.empty.

  Inductive is_terminal (m:t): Prop :=
  | is_terminal_intro
      (TERMINAL:
         forall tid st lc
           (FIND: IdMap.find tid m.(tpool) = Some (st, lc)),
           State.is_terminal st /\ lc.(Local.promises) = bot)
  .
  Hint Constructors is_terminal.

  Inductive no_promise (m:t): Prop :=
  | no_promise_intro
      (PROMISES:
         forall tid st lc
           (FIND: IdMap.find tid m.(tpool) = Some (st, lc)),
           lc.(Local.promises) = bot)
  .
  Hint Constructors no_promise.

  Lemma is_terminal_no_promise
        m
        (TERMINAL: is_terminal m):
    no_promise m.
  Proof.
    econs. i. eapply TERMINAL. eauto.
  Qed.

  Inductive step (eustep: forall (tid:Id.t) (eu1 eu2:ExecUnit.t), Prop) (m1 m2:t): Prop :=
  | step_intro
      tid st1 lc1 st2 lc2
      (FIND: IdMap.find tid m1.(tpool) = Some (st1, lc1))
      (STEP: eustep tid (ExecUnit.mk st1 lc1 m1.(mem)) (ExecUnit.mk st2 lc2 m2.(mem)))
      (TPOOL: m2.(tpool) = IdMap.add tid (st2, lc2) m1.(tpool))
  .
  Hint Constructors step.

  Lemma rtc_eu_step_step
        eustep tid m st1 lc1 mem1 st2 lc2 mem2
        (FIND: IdMap.find tid m.(tpool) = Some (st1, lc1))
        (MEM: m.(mem) = mem1)
        (EX: rtc (eustep tid)
                 (ExecUnit.mk st1 lc1 mem1)
                 (ExecUnit.mk st2 lc2 mem2)):
    rtc (step eustep)
        m
        (mk
           (IdMap.add tid (st2, lc2) m.(tpool))
           mem2).
  Proof.
    revert m FIND MEM.
    depind EX.
    { i. subst. destruct m. s. rewrite PositiveMapAdditionalFacts.gsident; ss. refl. }
    destruct y. i. subst. econs.
    - instantiate (1 := mk _ _). econs; ss; eauto.
    - exploit IHEX; eauto.
      + instantiate (1 := mk _ _). s.
        rewrite IdMap.add_spec. condtac; eauto. exfalso. apply c. ss.
      + ss.
      + s. rewrite (IdMap.add_add tid (st2, lc2)). eauto.
  Qed.

  Inductive wf (m:t): Prop :=
  | wf_intro
      (WF: forall tid st lc
             (FIND: IdMap.find tid m.(tpool) = Some (st, lc)),
          ExecUnit.wf tid (ExecUnit.mk st lc m.(mem)))
  .
  Hint Constructors wf.

  Lemma init_wf p:
    wf (init p).
  Proof.
    econs. i. ss.
    rewrite IdMap.map_spec in FIND. destruct (IdMap.find tid p); inv FIND.
    econs; ss. apply Local.init_wf.
  Qed.

  Lemma init_no_promise p:
    no_promise (init p).
  Proof.
    econs. s. i.
    revert FIND. rewrite IdMap.map_spec. destruct (IdMap.find tid p); ss. i. inv FIND.
    ss.
  Qed.

  Lemma step_state_step_wf
        m1 m2
        (STEP: step ExecUnit.state_step m1 m2)
        (WF: wf m1):
    wf m2.
  Proof.
    destruct m1 as [tpool1 mem1].
    destruct m2 as [tpool2 mem2].
    inv STEP. inv STEP0. inv WF. econs. ss. subst.
    i. revert FIND0. rewrite IdMap.add_spec. condtac.
    - inversion e0. i. inv FIND0.
      eapply ExecUnit.state_step_wf; eauto. econs; eauto.
    - inv STEP. ss. i. subst. exploit WF0; eauto.
  Qed.

  Lemma step_promise_step_wf
        m1 m2
        (STEP: step ExecUnit.promise_step m1 m2)
        (WF: wf m1):
    wf m2.
  Proof.
    destruct m1 as [tpool1 mem1].
    destruct m2 as [tpool2 mem2].
    inv STEP. inv STEP0. inv LOCAL. inv MEM2. inv WF. econs. ss. subst.
    i. revert FIND0. rewrite IdMap.add_spec. condtac.
    - inversion e. i. inv FIND0.
      eapply ExecUnit.promise_step_wf; eauto. econs; eauto. econs; eauto.
      + econs; eauto.
      + refl.
    - i. exploit WF0; eauto. i. inv x. ss. econs; ss.
      inv LOCAL. econs; eauto.
      all: try rewrite List.app_length; s; try lia.
      + i. rewrite COH. lia.
      + i. rewrite LPER. lia.
      + i. rewrite PER. lia.
      + i. destruct (FWDBANK loc0). des. econs; esplits; ss.
        apply Memory.read_mon; eauto.
      + i. exploit PROMISES; eauto. lia.
      + i. apply Memory.get_msg_snoc_inv in MSG. des.
        { eapply PROMISES0; eauto. }
        { subst. ss. congr. }
      + i. apply Memory.get_msg_snoc_inv in MSG. des.
        * eapply NFWD; eauto.
        * rewrite MSG in TS. specialize (COH (Msg.loc msg)). lia.
  Qed.

  Lemma rtc_step_promise_step_wf
        m1 m2
        (STEP: rtc (step ExecUnit.promise_step) m1 m2)
        (WF: wf m1):
    wf m2.
  Proof.
    revert WF. induction STEP; ss. i. apply IHSTEP.
    eapply step_promise_step_wf; eauto.
  Qed.

  Lemma step_step_wf
        m1 m2
        (STEP: step ExecUnit.step m1 m2)
        (WF: wf m1):
    wf m2.
  Proof.
    inv STEP. inv STEP0.
    - eapply step_state_step_wf; eauto.
    - eapply step_promise_step_wf; eauto.
  Qed.

  Lemma rtc_step_step_wf
        m1 m2
        (STEP: rtc (step ExecUnit.step) m1 m2)
        (WF: wf m1):
    wf m2.
  Proof.
    revert WF. induction STEP; ss. i. apply IHSTEP.
    eapply step_step_wf; eauto.
  Qed.

  Lemma step_view_step_wf
        m1 m2
        (STEP: step ExecUnit.view_step m1 m2)
        (WF: wf m1):
    wf m2.
  Proof.
    destruct m1 as [tpool1 mem1].
    destruct m2 as [tpool2 mem2].
    inv STEP. inv STEP0. inv WF. econs. ss. subst.
    i. revert FIND0. rewrite IdMap.add_spec. condtac.
    - inversion e0. i. inv FIND0.
      eapply ExecUnit.view_step_wf; eauto. econs; eauto.
    - i. inv STEP. exploit WF0; eauto. i. inv x. ss. econs; ss.
      inv LOCAL0. inv LOCAL; ss.
      + inv STEP. inv MEM. econs; ss.
        * i. rewrite COH. rewrite app_length. lia.
        * rewrite app_length. lia.
        * i. rewrite LPER. rewrite app_length. lia.
        * i. rewrite PER. rewrite app_length. lia.
        * i. apply Local.wf_fwdbank_mon. ss.
        * i. exploit PROMISES; eauto. rewrite List.app_length. lia.
        * i. apply Memory.get_msg_snoc_inv in MSG. des.
          { eapply PROMISES0; eauto. }
          { subst. ss. congr. }
        * i. apply Memory.get_msg_snoc_inv in MSG. des.
          { eapply NFWD; eauto. }
          { rewrite MSG in TS. specialize (COH (Msg.loc msg)). lia. }
      + inv STEP. inv MEM. econs; ss.
        * i. rewrite COH. rewrite app_length. lia.
        * rewrite app_length. lia.
        * i. rewrite LPER. rewrite app_length. lia.
        * i. rewrite PER. rewrite app_length. lia.
        * i. apply Local.wf_fwdbank_mon. ss.
        * i. exploit PROMISES; eauto. rewrite List.app_length. lia.
        * i. apply Memory.get_msg_snoc_inv in MSG. des.
          { eapply PROMISES0; eauto. }
          { subst. ss. congr. }
        * i. apply Memory.get_msg_snoc_inv in MSG. des.
          { eapply NFWD; eauto. }
          { rewrite MSG in TS. specialize (COH (Msg.loc msg)). lia. }
  Qed.

  Lemma rtc_step_view_step_wf
        m1 m2
        (STEP: rtc (step ExecUnit.view_step) m1 m2)
        (WF: wf m1):
    wf m2.
  Proof.
    revert WF. induction STEP; ss. i. apply IHSTEP.
    eapply step_view_step_wf; eauto.
  Qed.

  Lemma step_view_step_no_promise
        m1 m2
        (STEP: step ExecUnit.view_step m1 m2)
        (NOPROMISE: no_promise m1):
    no_promise m2.
  Proof.
    inv NOPROMISE. inv STEP.
    generalize FIND. intro NPROM. apply PROMISES in NPROM.
    econs. i.
    revert FIND0. rewrite TPOOL. rewrite IdMap.add_spec. condtac; [| apply PROMISES]. i. inv FIND0.
    inv STEP0. inv STEP. inv LOCAL; try inv STEP; ss; subst; ss.
  Qed.

  Lemma step_mon
        (eustep1 eustep2: _ -> _ -> _ -> Prop)
        (EUSTEP: forall tid m1 m2, eustep1 tid m1 m2 -> eustep2 tid m1 m2):
    forall m1 m2, step eustep1 m1 m2 -> step eustep2 m1 m2.
  Proof.
    i. inv H. econs; eauto.
  Qed.

  Lemma rtc_step_mon
        (eustep1 eustep2: _ -> _ -> _ -> Prop)
        (EUSTEP: forall tid m1 m2, eustep1 tid m1 m2 -> eustep2 tid m1 m2):
    forall m1 m2, rtc (step eustep1) m1 m2 -> rtc (step eustep2) m1 m2.
  Proof.
    i. induction H; eauto. econs; eauto. eapply step_mon; eauto.
  Qed.

  Inductive exec (p:program) (m:t): Prop :=
  | exec_intro
      (STEP: rtc (step ExecUnit.step) (init p) m)
      (NOPROMISE: no_promise m)
  .
  Hint Constructors exec.

  Inductive state_exec (m1 m2:t): Prop :=
  | state_exec_intro
      (TPOOL: IdMap.Forall2
                (fun tid sl1 sl2 =>
                   rtc (ExecUnit.state_step tid)
                       (ExecUnit.mk (fst sl1) (snd sl1) m1.(mem))
                       (ExecUnit.mk (fst sl2) (snd sl2) m1.(mem)))
                m1.(tpool) m2.(tpool))
      (MEM: m1.(mem) = m2.(mem))
  .

  Inductive pf_exec (p:program) (m:t): Prop :=
  | pf_exec_intro
      m1
      (STEP1: rtc (step ExecUnit.promise_step) (init p) m1)
      (STEP2: state_exec m1 m)
      (NOPROMISE: no_promise m)
  .
  Hint Constructors pf_exec.

  Inductive view_exec (p:program) (m:t): Prop :=
  | view_exec_intro
      (STEP: rtc (step ExecUnit.view_step) (init p) m)
  .
  Hint Constructors view_exec.

  Inductive equiv (m1 m2:t): Prop :=
  | equiv_intro
      (TPOOL: IdMap.Equal m1.(tpool) m2.(tpool))
      (MEM: m1.(mem) = m2.(mem))
  .

  Lemma state_exec_wf
        m1 m2
        (STEP: state_exec m1 m2)
        (WF: wf m1):
    wf m2.
  Proof.
    econs. i.
    inv STEP. inv WF.
    specialize (TPOOL tid). inv TPOOL.
    { rewrite FIND in H. ss. }
    rewrite <- H in FIND. inv FIND.
    destruct a as [st_a lc_a]. symmetry in H0. eapply WF0 in H0.
    eapply ExecUnit.rtc_state_step_wf in H0; eauto.
    rewrite <- MEM. ss.
  Qed.

  Lemma equiv_no_promise
        m1 m2
        (EQUIV: equiv m1 m2)
        (NOPROMISE: no_promise m1):
    no_promise m2.
  Proof.
    inv EQUIV. inv NOPROMISE. econs. i.
    specialize (TPOOL tid). rewrite FIND in TPOOL.
    eapply PROMISES. eauto.
  Qed.

  Lemma unlift_step_state_step
        m1 m2 tid st1 lc1
        (STEPS: rtc (step ExecUnit.state_step) m1 m2)
        (TPOOL: IdMap.find tid m1.(tpool) = Some (st1, lc1)):
    exists st2 lc2,
      <<TPOOL: IdMap.find tid m2.(tpool) = Some (st2, lc2)>> /\
      <<STEPS: rtc (ExecUnit.state_step tid)
                   (ExecUnit.mk st1 lc1 m1.(mem))
                   (ExecUnit.mk st2 lc2 m2.(mem))>>.
  Proof.
    revert st1 lc1 TPOOL. induction STEPS; eauto. i.
    destruct x as [tpool1 mem1].
    destruct y as [tpool2 mem2].
    destruct z as [tpool3 mem3].
    inv H. ss.
    assert (mem2 = mem1).
    { inv STEP. inv STEP0. ss. }
    subst. exploit IHSTEPS.
    { rewrite IdMap.add_spec, TPOOL.
      instantiate (1 := if equiv_dec tid tid0 then lc2 else lc1).
      instantiate (1 := if equiv_dec tid tid0 then st2 else st1).
      condtac; ss.
    }
    i. des.
    esplits; eauto. rewrite <- STEPS0. condtac; eauto.
    inversion e. subst. rewrite TPOOL in FIND. inv FIND. econs; eauto.
  Qed.

  Lemma step_get_msg_tpool
        p m ts msg
        (STEPS: rtc (step ExecUnit.step) (init p) m)
        (MSG: Memory.get_msg ts m.(mem) = Some msg):
    exists sl, IdMap.find msg.(Msg.tid) m.(tpool) = Some sl.
  Proof.
    apply clos_rt_rt1n_iff in STEPS.
    apply clos_rt_rtn1_iff in STEPS.
    revert ts msg MSG. induction STEPS; ss.
    { destruct ts; ss. destruct ts; ss. }
    destruct y as [tpool1 mem1].
    destruct z as [tpool2 mem2].
    ss. inv H. ss. i. inv STEP.
    - rewrite IdMap.add_spec. condtac; eauto.
      inv STEP0. inv STEP. ss. subst. eauto.
    - rewrite IdMap.add_spec. condtac; eauto.
      inv STEP0. ss. subst. inv LOCAL. inv MEM2.
      apply Memory.get_msg_snoc_inv in MSG. des; eauto. subst.
      ss. congr.
  Qed.

  Definition init_with_promises (p:program) (mem:Memory.t): Machine.t :=
    Machine.mk
      (IdMap.mapi (fun tid stmts =>
                     (State.init stmts,
                      Local.init_with_promises (Promises.promises_from_mem tid mem)))
                  p)
      mem.

  Lemma pf_init_with_promises
        p promises
        (MEM: forall msg (MSG: List.In msg promises), IdMap.find msg.(Msg.tid) p <> None):
    exists m,
      <<STEP: rtc (Machine.step ExecUnit.promise_step) (Machine.init p) m>> /\
      <<TPOOL: IdMap.Equal m.(Machine.tpool) (init_with_promises p promises).(Machine.tpool)>> /\
      <<MEM: m.(Machine.mem) = promises>>.
  Proof.
    revert MEM. induction promises using List.rev_ind; i.
    { esplits; eauto. ii. s. rewrite IdMap.map_spec, IdMap.mapi_spec.
      destruct (IdMap.find y p); ss.
      unfold Local.init, Local.init_with_promises. repeat f_equal.
      rewrite Promises.promises_from_mem_nil. ss.
    }
    exploit IHpromises; eauto.
    { i. apply MEM. apply List.in_app_iff. intuition. }
    i. des. subst. destruct x.
    hexploit MEM.
    { apply List.in_app_iff. right. left. eauto. }
    match goal with
    | [|- context[(?f <> None) -> _]] => destruct f eqn:FIND
    end; ss.
    intro X. clear X.
    eexists (Machine.mk _ _). esplits.
    - etrans; [eauto|]. econs 2; [|refl].
      econs.
      + rewrite TPOOL, IdMap.mapi_spec, FIND. ss.
      + econs; ss.
      + ss.
    - s. ii. rewrite IdMap.add_spec. condtac; ss.
      + inversion e. subst. rewrite IdMap.mapi_spec, FIND. s.
        unfold Local.init_with_promises. repeat f_equal.
        rewrite Promises.promises_from_mem_snoc. condtac; ss.
      + rewrite TPOOL, ? IdMap.mapi_spec. destruct (IdMap.find y p); ss.
        unfold Local.init_with_promises. rewrite Promises.promises_from_mem_snoc. s.
        condtac; ss. congr.
    - ss.
  Qed.

  Lemma rtc_promise_step_spec
        p m
        (STEP: rtc (step ExecUnit.promise_step) (init p) m):
    IdMap.Equal m.(tpool) (init_with_promises p m.(mem)).(tpool).
  Proof.
    apply clos_rt_rt1n_iff in STEP.
    apply clos_rt_rtn1_iff in STEP.
    induction STEP.
    { s. ii. rewrite IdMap.map_spec, IdMap.mapi_spec.
      destruct (IdMap.find y p); ss. f_equal. f_equal.
      rewrite Promises.promises_from_mem_nil. ss.
    }
    destruct y as [tpool2 mem2].
    destruct z as [tpool3 mem3].
    ss. inv H. inv STEP0. inv LOCAL. ss. subst. inv MEM2.
    ii. generalize (IHSTEP y). rewrite IdMap.add_spec, ? IdMap.mapi_spec.
    rewrite Promises.promises_from_mem_snoc. s.
    repeat condtac; try congr.
    inversion e. subst. rewrite FIND. destruct (IdMap.find tid p); ss. i. inv H. ss.
  Qed.
End Machine.
