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

Module FwdItem.
Section FwdItem.
  Context `{A: Type, _: orderC A eq}.

  Inductive t := mk {
    ts: Time.t;
  }.
  Hint Constructors t.

  Definition init: t := mk bot.

  Definition read_view (fwd:t) (tsx:Time.t): View.t (A:=unit) :=
    if fwd.(ts) == tsx
    then View.mk bot bot
    else View.mk tsx bot.
End FwdItem.
End FwdItem.

Module Local.
Section Local.
  Inductive t := mk {
    coh: Loc.t -> View.t (A:=unit);
    vrn: View.t (A:=unit);
    vwn: View.t (A:=unit);
    vro: View.t (A:=unit);
    vwo: View.t (A:=unit);
    fwdbank: Loc.t -> (FwdItem.t);
    promises: Promises.t;
  }.
  Hint Constructors t.

  Definition init: t := mk bot bot bot bot bot (fun _ => FwdItem.init) bot.

  Definition init_with_promises (promises: Promises.t): Local.t :=
    mk bot bot bot bot bot (fun _ => FwdItem.init) promises.

  Inductive promise (loc:Loc.t) (val:Val.t) (ts:Time.t) (tid:Id.t) (lc1:t) (mem1:Memory.t) (lc2:t) (mem2:Memory.t): Prop :=
  | promise_intro
      (LC2: lc2 =
            mk
              lc1.(coh)
              lc1.(vrn)
              lc1.(vwn)
              lc1.(vro)
              lc1.(vwo)
              lc1.(fwdbank)
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
      (COH: Memory.latest loc ts (lc1.(coh) loc).(View.ts) mem1)
      (LATEST: Memory.latest loc ts view_pre.(View.ts) mem1)
      (MSG: Memory.read loc ts mem1 = Some val)
      (VIEW_MSG: view_msg = FwdItem.read_view (lc1.(fwdbank) loc) ts)
      (VIEW_POST: view_post = join view_pre view_msg)
      (RES: res = ValA.mk _ val bot)
      (LC2: lc2 =
            mk
              (fun_add loc (join (lc1.(coh) loc) view_post) lc1.(coh))
              (join lc1.(vrn) view_post)
              (join lc1.(vwn) view_post)
              (join lc1.(vro) view_post)
              lc1.(vwo)
              lc1.(fwdbank)
              lc1.(promises))
  .
  Hint Constructors read.

  Inductive writable (vloc vval:ValA.t (A:=unit)) (tid:Id.t) (lc1:t) (mem1: Memory.t) (ts:Time.t) (view_pre:View.t (A:=unit)): Prop :=
  | writable_intro
      loc val
      (LOC: loc = vloc.(ValA.val))
      (VAL: val = vval.(ValA.val))
      (VIEW_PRE: view_pre = lc1.(vwn))
      (COH: lt (lc1.(coh) loc).(View.ts) ts)
      (EXT: lt view_pre.(View.ts) ts)
  .
  Hint Constructors writable.

  Inductive fulfill (vloc vval res:ValA.t (A:=unit)) (ts:Time.t) (tid:Id.t) (view_pre:View.t (A:=unit)) (lc1:t) (mem1: Memory.t) (lc2:t): Prop :=
  | fulfill_intro
      loc val
      (LOC: loc = vloc.(ValA.val))
      (VAL: val = vval.(ValA.val))
      (WRITABLE: writable vloc vval tid lc1 mem1 ts view_pre)
      (MSG: Memory.get_msg ts mem1 = Some (Msg.mk loc val tid))
      (PROMISE: Promises.lookup ts lc1.(promises))
      (RES: res = ValA.mk _ 0 bot)
      (LC2: lc2 =
            mk
              (fun_add loc (View.mk ts bot) lc1.(coh))
              lc1.(vrn)
              (join lc1.(vwn) (View.mk ts bot))
              lc1.(vro)
              (join lc1.(vwo) (View.mk ts bot))
              (fun_add loc (FwdItem.mk ts) lc1.(fwdbank))
              (Promises.unset ts lc1.(promises)))
  .
  Hint Constructors fulfill.

  Inductive rmw (vloc vold vnew:ValA.t (A:=unit)) (ts:Time.t) (tid:Id.t) (view_pre:View.t (A:=unit)) (lc1:t) (mem1:Memory.t) (lc2:t): Prop :=
  | rmw_intro
      loc old new old_ts
      (LOC: loc = vloc.(ValA.val))
      (OLD_RANGE: old_ts < ts)
      (EX: Memory.exclusive tid loc old_ts ts mem1)
      (OLD_MSG: Memory.read loc old_ts mem1 = Some old)
      (OLD: vold.(ValA.val) = old)
      (NEW: new = vnew.(ValA.val))
      (WRITABLE: writable vloc vnew tid lc1 mem1 ts view_pre)
      (MSG: Memory.get_msg ts mem1 = Some (Msg.mk loc new tid))
      (PROMISE: Promises.lookup ts lc1.(promises))
      (LC: lc2 =
            mk
              (fun_add loc (View.mk ts bot) lc1.(coh))
              (join lc1.(vrn) (View.mk ts bot))
              (join lc1.(vwn) (View.mk ts bot))
              (join lc1.(vro) (View.mk ts bot)) (* vro is about what point this thread had seen while taking read step, not just msg view itself*)
              (join lc1.(vwo) (View.mk ts bot))
              (fun_add loc (FwdItem.mk ts) lc1.(fwdbank))
              (Promises.unset ts lc1.(promises)))
  .
  Hint Constructors rmw.

  Inductive rmw_failure (vloc vold res:ValA.t (A:=unit)) (old_ts:Time.t) (lc1:t) (mem1:Memory.t) (lc2:t): Prop :=
  | rmw_failure_intro
      loc old
      view_pre view_old view_post
      (LOC: loc = vloc.(ValA.val))
      (VIEW_PRE: view_pre = lc1.(vrn))
      (COH: Memory.latest loc old_ts (lc1.(coh) loc).(View.ts) mem1)
      (LATEST: Memory.latest loc old_ts view_pre.(View.ts) mem1)
      (OLD_MSG: Memory.read loc old_ts mem1 = Some old)
      (VIEW_OLD: view_old = FwdItem.read_view (lc1.(fwdbank) loc) old_ts)
      (VIEW_POST: view_post = join view_pre view_old)
      (RES: res = ValA.mk _ old bot)
      (LC: lc2 =
            mk
              (fun_add loc (join (lc1.(coh) loc) view_post) lc1.(coh))
              (join lc1.(vrn) view_post)
              (join lc1.(vwn) view_post)
              (join lc1.(vro) view_post)
              lc1.(vwo)
              lc1.(fwdbank)
              lc1.(promises))
  .
  Hint Constructors rmw_failure.

  Inductive dmb (rr rw wr ww:bool) (lc1 lc2:t): Prop :=
  | dmb_intro
      (LC2: lc2 =
            mk
              lc1.(coh)
              (joins [lc1.(vrn); ifc rr lc1.(vro); ifc wr lc1.(vwo)])
              (joins [lc1.(vwn); ifc rw lc1.(vro); ifc ww lc1.(vwo)])
              lc1.(vro)
              lc1.(vwo)
              lc1.(fwdbank)
              lc1.(promises))
  .
  Hint Constructors dmb.

  Inductive step (event:Event.t (A:=unit)) (tid:Id.t) (mem:Memory.t) (lc1 lc2:t): Prop :=
  | step_internal
      (EVENT: event = Event.internal)
      (LC: lc2 = lc1)
  | step_read
      vloc res ts
      (EVENT: event = Event.read false false OrdR.pln vloc res)
      (STEP: read vloc res ts lc1 mem lc2)
  | step_fulfill
      vloc vval res ts view_pre
      (EVENT: event = Event.write false OrdW.pln vloc vval res)
      (STEP: fulfill vloc vval res ts tid view_pre lc1 mem lc2)
  | step_rmw
      vloc vold vnew ts view_pre
      (EVENT: event = Event.rmw OrdR.pln OrdW.pln vloc vold vnew)
      (STEP: rmw vloc vold vnew ts tid view_pre lc1 mem lc2)
  | step_rmw_failure
      vloc vold old_ts res
      (EVENT: event = Event.read false true OrdR.pln vloc res)
      (STEP: rmw_failure vloc vold res old_ts lc1 mem lc2)
  | step_dmb
      rr rw wr ww
      (EVENT: event = Event.barrier (Barrier.dmb rr rw wr ww))
      (STEP: dmb rr rw wr ww lc1 lc2)
  .
  Hint Constructors step.

  Inductive wf_fwdbank (loc:Loc.t) (mem:Memory.t) (coh: Time.t) (fwd:FwdItem.t): Prop :=
  | wf_fwdbank_intro
      (TS: fwd.(FwdItem.ts) <= Memory.latest_ts loc coh mem)
      (VAL: exists val, Memory.read loc fwd.(FwdItem.ts) mem = Some val)
  .

  Inductive wf (tid:Id.t) (mem:Memory.t) (lc:t): Prop :=
  | wf_intro
      (COH: forall loc, (lc.(coh) loc).(View.ts) <= List.length mem)
      (VRN: lc.(vrn).(View.ts) <= List.length mem)
      (VWN: lc.(vwn).(View.ts) <= List.length mem)
      (VRO: lc.(vro).(View.ts) <= List.length mem)
      (VWO: lc.(vwo).(View.ts) <= List.length mem)
      (FWDBANK: forall loc, wf_fwdbank loc mem (lc.(coh) loc).(View.ts) (lc.(fwdbank) loc))
      (PROMISES: forall ts (IN: Promises.lookup ts lc.(promises)), ts <= List.length mem)
      (PROMISES: forall ts msg
                   (MSG: Memory.get_msg ts mem = Some msg)
                   (TID: msg.(Msg.tid) = tid)
                   (TS: (lc.(coh) msg.(Msg.loc)).(View.ts) < ts),
          Promises.lookup ts lc.(promises))
  .
  Hint Constructors wf.

  Lemma init_wf tid: wf tid Memory.empty init.
  Proof.
    econs; ss; i; try by apply bot_spec.
    - econs; ss. eexists. ss.
    - destruct ts; ss.
    - destruct ts; ss. destruct ts; ss.
  Qed.

  Lemma fwd_read_view_le
        tid mem lc loc ts
        (WF: wf tid mem lc)
        (COH: Memory.latest loc ts (lc.(coh) loc).(View.ts) mem):
    (FwdItem.read_view (lc.(fwdbank) loc) ts).(View.ts) <= ts.
  Proof.
    inv WF. destruct (FWDBANK loc). des.
    unfold FwdItem.read_view. condtac; ss.
    apply bot_spec.
  Qed.

  Lemma read_spec
        tid mem vloc res ts lc1 lc2
        (WF: Local.wf tid mem lc1)
        (READ: Local.read vloc res ts lc1 mem lc2):
    <<LATEST: Memory.latest vloc.(ValA.val) ts lc2.(Local.vrn).(View.ts) mem>> /\
    <<COH: ts = Memory.latest_ts vloc.(ValA.val) (lc2.(Local.coh) vloc.(ValA.val)).(View.ts) mem>> /\
    <<COH2: Memory.latest vloc.(ValA.val) ts (lc2.(Local.coh) vloc.(ValA.val)).(View.ts) mem>>.
  Proof.
    inv READ. ss. rewrite fun_add_spec. condtac; [|congr]. splits.
    - repeat apply Memory.latest_join; auto.
      apply Memory.ge_latest. eapply fwd_read_view_le; eauto.
    - unfold join. ss. apply le_antisym.
      + unfold FwdItem.read_view. des_ifs.
        * inv e0. inv WF. exploit FWDBANK. intro Y. inv Y.
          eapply Memory.latest_ts_read_le; eauto.
          rewrite TS, Memory.latest_latest_ts.
          { apply join_l. }
          { apply Memory.ge_latest. ss. }
        * eapply Memory.latest_ts_read_le; eauto.
          ss. repeat rewrite <- join_r. auto.
      + hexploit fwd_read_view_le; eauto. i.
        apply Memory.latest_latest_ts.
        apply Memory.latest_join; ss.
        apply Memory.latest_join; ss.
        apply Memory.ge_latest. etrans; eauto.
    - repeat apply Memory.latest_join; auto.
      apply Memory.ge_latest. eapply fwd_read_view_le; eauto.
  Qed.

  Lemma rmw_failure_spec
        tid mem vloc vold res old_ts lc1 lc2
        (WF: Local.wf tid mem lc1)
        (READ: Local.rmw_failure vloc vold res old_ts lc1 mem lc2):
    <<LATEST: Memory.latest vloc.(ValA.val) old_ts lc2.(Local.vrn).(View.ts) mem>> /\
    <<COH: old_ts = Memory.latest_ts vloc.(ValA.val) (lc2.(Local.coh) vloc.(ValA.val)).(View.ts) mem>> /\
    <<COH2: Memory.latest vloc.(ValA.val) old_ts (lc2.(Local.coh) vloc.(ValA.val)).(View.ts) mem>>.
  Proof.
    inv READ. ss. rewrite fun_add_spec. condtac; [|congr]. splits.
    - repeat apply Memory.latest_join; auto.
      apply Memory.ge_latest. eapply fwd_read_view_le; eauto.
    - unfold join. ss. apply le_antisym.
      + unfold FwdItem.read_view. des_ifs.
        * inv e0. inv WF. exploit FWDBANK. intro Y. inv Y.
          eapply Memory.latest_ts_read_le; eauto.
          rewrite TS, Memory.latest_latest_ts.
          { apply join_l. }
          { apply Memory.ge_latest. ss. }
        * eapply Memory.latest_ts_read_le; eauto.
          ss. repeat rewrite <- join_r. auto.
      + hexploit fwd_read_view_le; eauto. i.
        apply Memory.latest_latest_ts.
        apply Memory.latest_join; ss.
        apply Memory.latest_join; ss.
        apply Memory.ge_latest. etrans; eauto.
    - repeat apply Memory.latest_join; auto.
      apply Memory.ge_latest. eapply fwd_read_view_le; eauto.
  Qed.

  (* Lemma update_spec
        tid view_pre mem vloc vold vnew ts lc1 lc2
        (WF: Local.wf tid mem lc1)
        (RMW: Local.rmw vloc vold vnew ts tid view_pre lc1 mem lc2):
    <<COH: ts = Memory.latest_ts vloc.(ValA.val) (lc2.(Local.coh) vloc.(ValA.val)).(View.ts) mem>> /\
    <<OLD_TS:
      exists old_ts,
      <<PRED: old_ts = Memory.latest_ts vloc.(ValA.val) (pred ts) mem>> /\
      <<READ: Memory.read vloc.(ValA.val) old_ts mem = Some vold.(ValA.val)>>
    >>.
  Proof.
    inv RMW. ss. rewrite fun_add_spec. condtac; [|congr]. splits.
    - apply le_antisym; ss.
      + eapply Memory.latest_ts_read_le; eauto.
        eapply Memory.get_msg_read. eauto.
      + apply Memory.latest_latest_ts.
        apply Memory.ge_latest. ss.
    - eexists old_ts. split; ss.
      eapply le_antisym; ss.
      + eapply Memory.latest_ts_read_le; eauto. lia.
      + eapply Memory.latest_latest_ts. ss.
  Qed. *)

  Lemma interference_wf
        tid (lc:t) mem mem_interference
        (INTERFERENCE: Forall (fun msg => msg.(Msg.tid) <> tid) mem_interference)
        (WF: wf tid mem lc):
    wf tid (mem ++ mem_interference) lc.
  Proof.
    inv WF. econs; i.
    all: try rewrite app_length.
    all: try lia.
    - rewrite COH. lia.
    - destruct (FWDBANK loc). des. econs; esplits; eauto.
      + rewrite TS, Memory.latest_ts_append. ss.
      + apply Memory.read_mon. eauto.
    - exploit PROMISES; eauto. lia.
    - apply Memory.get_msg_app_inv in MSG. des.
      + eapply PROMISES0; eauto.
      + apply nth_error_In in MSG0. eapply Forall_forall in INTERFERENCE; eauto.
        subst. destruct (nequiv_dec (Msg.tid msg) (Msg.tid msg)); ss. congr.
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
      (VWN: Order.le lhs.(vwn).(View.ts) rhs.(vwn).(View.ts))
      (VRO: Order.le lhs.(vro).(View.ts) rhs.(vro).(View.ts))
      (VWO: Order.le lhs.(vwo).(View.ts) rhs.(vwo).(View.ts))
  .

  Global Program Instance le_partial_order: PreOrder le.
  Next Obligation. econs; refl. Qed.
  Next Obligation. ii. inv H. inv H0. econs; etrans; eauto. Qed.

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
        vloc vval res ts tid view_pre lc1 mem1 lc2
        (LC: fulfill vloc vval res ts tid view_pre lc1 mem1 lc2):
    le lc1 lc2.
  Proof.
    inv LC. econs; ss; try refl; try apply join_l.
    i. rewrite fun_add_spec. condtac; try refl.
    clear X. inv e. s.
    (* TODO: fulfill should update COH's taint, too. *)
    inv WRITABLE. unfold Order.le. clear -COH. lia.
  Qed.

  Lemma rmw_incr
        vloc vold vnew ts tid view_pre lc1 mem lc2
        (LC: rmw vloc vold vnew ts tid view_pre lc1 mem lc2):
    le lc1 lc2.
  Proof.
    inv LC. econs; ss; try refl; try apply join_l.
    i. rewrite fun_add_spec. condtac; try refl.
    clear X. inv e. s.
    inv WRITABLE. unfold Order.le. clear -COH. lia.
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
  Qed.
End Local.
End Local.

Ltac viewtac :=
  repeat
    (try match goal with
         | [|- join _ _ <= _] => apply join_spec
         | [|- bot <= _] => apply bot_spec
         | [|- ifc ?c _ <= _] => destruct c; s

         | [|- Time.join _ _ <= _] => apply join_spec
         | [|- Time.bot <= _] => apply bot_spec

         | [|- context[View.ts (join _ _)]] => rewrite View.ts_join
         | [|- context[View.ts bot]] => rewrite View.ts_bot
         | [|- context[View.ts (ifc _ _)]] => rewrite View.ts_ifc
         end;
     ss; eauto).

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

  Inductive wf (tid:Id.t) (eu:t): Prop :=
  | wf_intro
      (LOCAL: Local.wf tid eu.(mem) eu.(local))
  .
  Hint Constructors wf.

  Lemma read_wf
        ts loc val mem
        (READ: Memory.read loc ts mem = Some val):
    ts <= List.length mem.
  Proof.
    revert READ. unfold Memory.read. destruct ts; [lia|]. s.
    destruct (nth_error mem ts) eqn:NTH; ss. condtac; ss.
    i. eapply List.nth_error_Some. congr.
  Qed.

  Lemma get_msg_wf
        ts msg mem
        (READ: Memory.get_msg ts mem = Some msg):
    ts <= List.length mem.
  Proof.
    revert READ. unfold Memory.get_msg. destruct ts; [lia|]. s.
    destruct (nth_error mem ts) eqn:NTH; ss. i. inv READ.
    eapply List.nth_error_Some. congr.
  Qed.

  Lemma state_step0_wf tid e eu1 eu2
        (STEP: state_step0 tid e e eu1 eu2)
        (WF: wf tid eu1):
    wf tid eu2.
  Proof.
    destruct eu1 as [state1 local1 mem1].
    destruct eu2 as [state2 local2 mem2].
    inv WF. inv STEP. ss. subst.

    assert (FWDVIEW: forall loc ts,
               Memory.latest loc ts (View.ts (Local.coh local1 loc)) mem1 ->
               ts <= length mem1 ->
               View.ts (FwdItem.read_view (Local.fwdbank local1 loc) ts) <= length mem1).
    { i. rewrite Local.fwd_read_view_le; eauto. }
    generalize LOCAL. intro WF_LOCAL1.
    inversion STATE; inv LOCAL0; inv EVENT; inv LOCAL; ss.
    - inv STEP. ss.
      exploit FWDVIEW; eauto.
      { eapply read_wf. eauto. }
      i. econs; ss. econs; viewtac.
      + i. rewrite fun_add_spec. condtac; viewtac.
      + i. exploit FWDBANK; eauto. intro Y. inv Y. des.
        econs; eauto. rewrite TS, fun_add_spec. condtac; ss. inversion e. subst.
        apply Memory.latest_ts_mon. apply join_l.
      + i. eapply PROMISES0; eauto. eapply Time.le_lt_trans; [|by eauto].
        rewrite fun_add_spec. condtac; ss. inversion e. rewrite H0. apply join_l.
    - inv STEP. inv WRITABLE. econs; ss.
      econs; viewtac; rewrite <- ? TS0, <- ? TS1.
      + i. rewrite fun_add_spec. condtac; viewtac.
      + i. rewrite ? fun_add_spec. condtac; viewtac.
        inversion e. subst.
        econs; viewtac.
        { unfold Memory.get_msg in MSG. destruct ts; ss. rewrite MSG. condtac; ss. }
        { revert MSG. unfold Memory.read, Memory.get_msg.
          destruct ts; ss. i. rewrite MSG. ss. eexists. des_ifs.
        }
      + i. revert IN. rewrite Promises.unset_o. condtac; ss. eauto.
      + i. rewrite Promises.unset_o. rewrite fun_add_spec in TS. condtac.
        { inversion e. subst. rewrite MSG in MSG0. destruct msg. inv MSG0. ss.
          revert TS. condtac; ss; intuition.
        }
        { eapply PROMISES0; eauto. revert TS. condtac; ss. i.
          inversion e. rewrite H0. rewrite COH0. ss.
        }
    - inv STEP. inv WRITABLE. econs; ss.
      econs; viewtac; rewrite <- ? TS0, <- ? TS1.
      + i. rewrite fun_add_spec. condtac; viewtac.
      + i. rewrite ? fun_add_spec. condtac; viewtac.
        inversion e. subst.
        econs; viewtac.
        { unfold Memory.get_msg in MSG. destruct ts; ss. rewrite MSG. condtac; ss. }
        { revert MSG. unfold Memory.read, Memory.get_msg.
          destruct ts; ss. i. rewrite MSG. ss. eexists. des_ifs.
        }
      + i. revert IN. rewrite Promises.unset_o. condtac; ss. eauto.
      + i. rewrite Promises.unset_o. rewrite fun_add_spec in TS. condtac.
        { inversion e. subst. rewrite MSG in MSG0. destruct msg. inv MSG0. ss.
        revert TS. condtac; ss; intuition.
        }
        { eapply PROMISES0; eauto. revert TS. condtac; ss. i.
        inversion e. rewrite H0. rewrite COH0. ss.
        }
    - inv STEP. econs. ss.
      exploit FWDVIEW; eauto.
      { eapply read_wf. eauto. }
      i. econs; viewtac.
      + i. rewrite fun_add_spec. condtac; viewtac.
      + i. exploit FWDBANK; eauto. intro Y. inv Y. des.
        econs; eauto. rewrite TS, fun_add_spec. condtac; ss. inversion e. subst.
        apply Memory.latest_ts_mon. apply join_l.
      + i. eapply PROMISES0; eauto. eapply Time.le_lt_trans; [|by eauto].
        rewrite fun_add_spec. condtac; ss. inversion e. rewrite H0. apply join_l.
    - inv STEP. econs; ss. econs; viewtac.
  Qed.

  Lemma state_step_wf tid eu1 eu2
        (STEP: state_step tid eu1 eu2)
        (WF: wf tid eu1):
    wf tid eu2.
  Proof.
    inv STEP. eapply state_step0_wf; eauto.
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
    - i. destruct (FWDBANK loc0). des. econs; esplits; ss.
      + rewrite TS. apply Memory.latest_ts_append.
      + apply Memory.read_mon; eauto.
    - i. revert IN. rewrite Promises.set_o. condtac.
      + inversion e. i. inv IN. lia.
      + i. exploit PROMISES; eauto. lia.
    - i. rewrite Promises.set_o. apply Memory.get_msg_snoc_inv in MSG. des.
      + destruct ts; ss. condtac; ss.
        eapply PROMISES0; eauto.
      + subst. condtac; ss. congr.
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
      + i. destruct (FWDBANK loc0). des. econs; esplits; ss.
        { rewrite TS. apply Memory.latest_ts_append. }
        { apply Memory.read_mon; eauto. }
      + i. exploit PROMISES; eauto. lia.
      + i. apply Memory.get_msg_snoc_inv in MSG. des.
        { eapply PROMISES0; eauto. }
        { subst. ss. congr. }
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

  Inductive equiv (m1 m2:t): Prop :=
  | equiv_intro
      (TPOOL: IdMap.Equal m1.(tpool) m2.(tpool))
      (MEM: m1.(mem) = m2.(mem))
  .

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

  Definition promises_from_mem
             (tid:Id.t) (mem: Memory.t): Promises.t.
  Proof.
    induction mem using list_rev_rect.
    - exact bot.
    - destruct x.
      apply (if tid0 == tid
             then Promises.set (S (List.length (List.rev mem0))) IHmem
             else IHmem).
  Defined.

  Lemma promises_from_mem_nil tid:
    promises_from_mem tid Memory.empty = bot.
  Proof.
    unfold promises_from_mem, list_rev_rect, eq_rect. ss.
    match goal with
    | [|- context[match ?c with | eq_refl => _ end]] => destruct c
    end; ss.
  Qed.

  Lemma promises_from_mem_snoc tid mem msg:
    promises_from_mem tid (mem ++ [msg]) =
    if msg.(Msg.tid) == tid
    then Promises.set (S (List.length mem)) (promises_from_mem tid mem)
    else promises_from_mem tid mem.
  Proof.
    unfold promises_from_mem at 1, list_rev_rect, eq_rect.
    match goal with
    | [|- context[match ?c with | eq_refl => _ end]] => destruct c
    end; ss.
    rewrite List.rev_involutive, List.rev_app_distr. ss.
    destruct msg. s. condtac.
    - inversion e. subst. rewrite ? List.rev_length.
      f_equal.
      unfold promises_from_mem, list_rev_rect, eq_rect.
      match goal with
      | [|- context[match ?c with | eq_refl => _ end]] => destruct c
      end; ss.
    - unfold promises_from_mem, list_rev_rect, eq_rect.
      match goal with
      | [|- context[match ?c with | eq_refl => _ end]] => destruct c
      end; ss.
  Qed.

  Lemma promises_from_mem_inv
        ts tid mem
        (LOOKUP: Promises.lookup (S ts) (promises_from_mem tid mem)):
    exists loc val, List.nth_error mem ts = Some (Msg.mk loc val tid).
  Proof.
    revert LOOKUP. induction mem using List.rev_ind.
    { rewrite promises_from_mem_nil, Promises.lookup_bot. ss. }
    rewrite promises_from_mem_snoc. condtac.
    { rewrite Promises.set_o. condtac.
      - inversion e. inversion e0. subst.
        rewrite List.nth_error_app2; [|lia].
        rewrite Nat.sub_diag. ss.
        destruct x. esplits; eauto.
      - i. exploit IHmem; eauto.  i. des.
        rewrite List.nth_error_app1; eauto.
        apply List.nth_error_Some. congr.
    }
    i. exploit IHmem; eauto.  i. des.
    rewrite List.nth_error_app1; eauto.
    apply List.nth_error_Some. congr.
  Qed.

  Lemma promises_from_mem_lookup
        mem ts loc val tid
        (GET: List.nth_error mem ts = Some (Msg.mk loc val tid)):
    Promises.lookup (S ts) (promises_from_mem tid mem).
  Proof.
    revert GET. induction mem using List.rev_ind.
    { i. apply List.nth_error_In in GET. inv GET. }
    rewrite promises_from_mem_snoc. condtac.
    - rewrite Promises.set_o. condtac.
      + inversion e. inversion e0. subst.
        rewrite List.nth_error_app2; [|lia].
        rewrite Nat.sub_diag. ss.
      + i. apply IHmem.
        erewrite <- List.nth_error_app1; eauto.
        assert (H: ts < List.length (mem0 ++ [x])).
        { rewrite <- List.nth_error_Some. ii. congr. }
        rewrite List.app_length in H.
        rewrite Nat.add_1_r in H. inv H; try lia.
        exfalso. apply c. ss.
    - i. apply IHmem.
      destruct (Nat.eq_dec ts (List.length mem0)) eqn:Heq.
      + inv Heq. rewrite List.nth_error_app2 in GET; try lia.
        rewrite Nat.sub_diag in GET. ss. inv GET. ss.
        exfalso. apply c. ss.
      + rewrite List.nth_error_app1 in GET; auto.
        assert (H: ts < List.length (mem0 ++ [x])).
        { rewrite <- List.nth_error_Some. ii. congr. }
        rewrite List.app_length in H.
        rewrite Nat.add_1_r in H. inv H; try lia; congr.
  Qed.

  Lemma promises_from_mem_spec
        ts tid mem:
    Promises.lookup (S ts) (promises_from_mem tid mem) <->
    exists loc val, List.nth_error mem ts = Some (Msg.mk loc val tid).
  Proof.
    induction mem using List.rev_ind.
    { econs.
      - rewrite promises_from_mem_nil, Promises.lookup_bot. ss.
      - i. des. destruct ts; ss.
    }
    rewrite promises_from_mem_snoc. econs.
    - condtac.
      + inversion e. subst. rewrite Promises.set_o. condtac.
        * inversion e0. subst. i.
          rewrite List.nth_error_app2, Nat.sub_diag; [|lia]. ss.
          destruct x. ss. eauto.
        * intro Y. apply IHmem in Y. des.
          esplits; eauto. apply nth_error_app_mon. eauto.
      + intro Y. apply IHmem in Y. des.
        esplits; eauto. apply nth_error_app_mon. eauto.
    - i. des. apply nth_error_snoc_inv in H. des; ss.
      { condtac; eauto. rewrite Promises.set_o. condtac; eauto. }
      subst. condtac; ss; [|congr]. rewrite Promises.set_o. condtac; [|congr]. ss.
  Qed.

  Definition init_with_promises (p:program) (mem:Memory.t): Machine.t :=
    Machine.mk
      (IdMap.mapi (fun tid stmts =>
                     (State.init stmts,
                      Local.init_with_promises (promises_from_mem tid mem)))
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
      rewrite promises_from_mem_nil. ss.
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
        rewrite promises_from_mem_snoc. condtac; ss.
      + rewrite TPOOL, ? IdMap.mapi_spec. destruct (IdMap.find y p); ss.
        unfold Local.init_with_promises. rewrite promises_from_mem_snoc. s.
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
      rewrite promises_from_mem_nil. ss.
    }
    destruct y as [tpool2 mem2].
    destruct z as [tpool3 mem3].
    ss. inv H. inv STEP0. inv LOCAL. ss. subst. inv MEM2.
    ii. generalize (IHSTEP y). rewrite IdMap.add_spec, ? IdMap.mapi_spec.
    rewrite promises_from_mem_snoc. s.
    repeat condtac; try congr.
    inversion e. subst. rewrite FIND. destruct (IdMap.find tid p); ss. i. inv H. ss.
  Qed.
End Machine.
