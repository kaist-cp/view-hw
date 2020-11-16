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
    vpr: View.t (A:=unit);
    vpa: Loc.t -> View.t (A:=unit);
    vpc: Loc.t -> View.t (A:=unit);
    promises: Promises.t;
  }.
  Hint Constructors t.

  Definition read_view (coh:View.t (A:=unit)) (tsx:Time.t): View.t (A:=unit) :=
    if coh.(View.ts) == tsx
    then View.mk bot bot
    else View.mk tsx bot.

  Definition init: t := mk bot bot bot bot bot bot.

  Definition init_with_promises (promises: Promises.t): Local.t :=
    mk bot bot bot bot bot promises.

  Inductive promise (loc:Loc.t) (val:Val.t) (ts:Time.t) (tid:Id.t) (lc1:t) (mem1:Memory.t) (lc2:t) (mem2:Memory.t): Prop :=
  | promise_intro
      (LC2: lc2 =
            mk
              lc1.(coh)
              lc1.(vrn)
              lc1.(vpr)
              lc1.(vpa)
              lc1.(vpc)
              (Promises.set ts lc1.(promises)))
      (MEM2: Memory.append (Msg.mk loc val tid) mem1 = (ts, mem2))
  .
  Hint Constructors promise.

  Inductive read (vloc res:ValA.t (A:=unit)) (ts:Time.t) (lc1:t) (mem1: Memory.t) (lc2:t): Prop :=
  | read_intro
      loc val
      view_pre view_post
      (LOC: loc = vloc.(ValA.val))
      (VIEW_PRE: view_pre = lc1.(vrn))
      (COH: le (lc1.(coh) loc).(View.ts) ts)
      (LATEST: Memory.latest loc ts view_pre.(View.ts) mem1)
      (MSG: Memory.read loc ts mem1 = Some val)
      (VIEW_POST: view_post = read_view (lc1.(coh) loc) ts)
      (RES: res = ValA.mk _ val bot)
      (LC2: lc2 =
            mk
              (fun_add loc (View.mk ts bot) lc1.(coh))
              (join lc1.(vrn) view_post)
              (join lc1.(vpr) view_post)
              lc1.(vpa)
              lc1.(vpc)
              lc1.(promises))
  .
  Hint Constructors read.

  Inductive writable (vloc vval:ValA.t (A:=unit)) (tid:Id.t) (lc1:t) (mem1: Memory.t) (ts:Time.t): Prop :=
  | writable_intro
      loc cohmax
      (LOC: loc = vloc.(ValA.val))
      (COHMAX: fun_max lc1.(coh) cohmax)
      (EXT: lt cohmax.(View.ts) ts)
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
              lc1.(vpr)
              lc1.(vpa)
              lc1.(vpc)
              (Promises.unset ts lc1.(promises)))
  .
  Hint Constructors fulfill.

  Inductive rmw (vloc vold vnew:ValA.t (A:=unit)) (old_ts:Time.t) (ts:Time.t) (tid:Id.t) (lc1:t) (mem1:Memory.t) (lc2:t): Prop :=
  | rmw_intro
      loc old new view_post
      (LOC: loc = vloc.(ValA.val))
      (COH: le (lc1.(coh) loc).(View.ts) old_ts)
      (OLD_RANGE: lt old_ts ts)
      (EX: Memory.exclusive tid loc old_ts ts mem1)
      (OLD_MSG: Memory.read loc old_ts mem1 = Some old)
      (OLD: old = vold.(ValA.val))
      (NEW: new = vnew.(ValA.val))
      (WRITABLE: writable vloc vnew tid lc1 mem1 ts)
      (MSG: Memory.get_msg ts mem1 = Some (Msg.mk loc new tid))
      (PROMISE: Promises.lookup ts lc1.(promises))
      (VIEW_POST: view_post = View.mk ts bot)
      (LC2: lc2 =
            mk
              (fun_add loc (View.mk ts bot) lc1.(coh))
              (join lc1.(vrn) view_post)
              (join lc1.(vpr) view_post)
              lc1.(vpa)
              (fun_join lc1.(vpc) lc1.(vpa))
              (Promises.unset ts lc1.(promises)))
  .
  Hint Constructors rmw.

  Inductive rmw_failure (vloc vold res:ValA.t (A:=unit)) (old_ts:Time.t) (lc1:t) (mem1:Memory.t) (lc2:t): Prop :=
  | rmw_failure_intro
      loc old
      view_pre view_post
      (LOC: loc = vloc.(ValA.val))
      (VIEW_PRE: view_pre = lc1.(vrn))
      (COH: le (lc1.(coh) loc).(View.ts) old_ts)
      (LATEST: Memory.latest loc old_ts view_pre.(View.ts) mem1)
      (OLD_MSG: Memory.read loc old_ts mem1 = Some old)
      (OLD: old = vold.(ValA.val))
      (VIEW_POST: view_post = read_view (lc1.(coh) loc) old_ts)
      (RES: res = ValA.mk _ old bot)
      (LC2: lc2 =
            mk
              (fun_add loc (View.mk old_ts bot) lc1.(coh))
              (join lc1.(vrn) view_post)
              (join lc1.(vpr) view_post)
              lc1.(vpa)
              lc1.(vpc)
              lc1.(promises))
  .
  Hint Constructors rmw_failure.

  Inductive mfence (lc1 lc2:t): Prop :=
  | mfence_intro
      cohmax
      (COHMAX: fun_max lc1.(coh) cohmax)
      (LC2: lc2 =
            mk
              lc1.(coh)
              (join lc1.(vrn) cohmax)
              (join lc1.(vpr) cohmax)
              lc1.(vpa)
              (fun_join lc1.(vpc) lc1.(vpa))
              lc1.(promises))
  .
  Hint Constructors mfence.

  Inductive sfence (lc1 lc2:t): Prop :=
  | sfence_intro
      cohmax
      (COHMAX: fun_max lc1.(coh) cohmax)
      (LC2: lc2 =
            mk
              lc1.(coh)
              lc1.(vrn)
              (join lc1.(vpr) cohmax)
              lc1.(vpa)
              (fun_join lc1.(vpc) lc1.(vpa))
              lc1.(promises))
  .
  Hint Constructors sfence.

  Inductive write (vloc vval res:ValA.t (A:=unit)) (ts:Time.t) (tid:Id.t) (lc1:t) (mem1: Memory.t) (lc2:t) (mem2: Memory.t): Prop :=
  | write_intro
      loc val
      (LOC: loc = vloc.(ValA.val))
      (VAL: val = vval.(ValA.val))
      (RES: res = ValA.mk _ 0 bot)
      (MEM: Memory.append (Msg.mk loc val tid) mem1 = (ts, mem2))
      (LC2: lc2 =
            mk
              (fun_add loc (View.mk ts bot) lc1.(coh))
              lc1.(vrn)
              lc1.(vpr)
              lc1.(vpa)
              lc1.(vpc)
              lc1.(promises))
  .
  Hint Constructors write.

  Inductive vrmw (vloc vold vnew:ValA.t (A:=unit)) (old_ts:Time.t) (ts:Time.t) (tid:Id.t) (lc1:t) (mem1:Memory.t) (lc2:t) (mem2: Memory.t): Prop :=
  | vrmw_intro
      loc old new
      view_post
      (LOC: loc = vloc.(ValA.val))
      (NINTERVENING: Memory.latest loc old_ts (pred ts) mem1)
      (OLD_MSG: Memory.read loc old_ts mem1 = Some old)
      (OLD: old = vold.(ValA.val))
      (NEW: new = vnew.(ValA.val))
      (VIEW_POST: view_post = View.mk ts bot)
      (MEM: Memory.append (Msg.mk loc new tid) mem1 = (ts, mem2))
      (LC2: lc2 =
            mk
              (fun_add loc (View.mk ts bot) lc1.(coh))
              (join lc1.(vrn) view_post)
              (join lc1.(vpr) view_post)
              lc1.(vpa)
              (fun_join lc1.(vpc) lc1.(vpa))
              lc1.(promises))
  .
  Hint Constructors rmw.

  Inductive flush (vloc:ValA.t (A:=unit)) (lc1:t) (lc2:t): Prop :=
  | flush_intro
      loc cohmax view_post
      (LOC: loc = vloc.(ValA.val))
      (COHMAX: fun_max lc1.(coh) cohmax)
      (VIEW_POST: view_post = fun loc' => ifc (Loc.cl loc loc') cohmax)
      (LC2: lc2 =
            mk
              lc1.(coh)
              lc1.(vrn)
              lc1.(vpr)
              (fun_join lc1.(vpa) view_post)
              (fun_join lc1.(vpc) view_post)
              lc1.(promises))
  .
  Hint Constructors flush.

  Inductive flushopt (vloc:ValA.t (A:=unit)) (lc1:t) (lc2:t): Prop :=
  | flushopt_intro
      loc cohmax_cl view_post
      (LOC: loc = vloc.(ValA.val))
      (COHMAX_CL: fun_max (fun loc' => ifc (Loc.cl loc loc') (lc1.(coh) loc')) cohmax_cl)
      (VIEW_POST: view_post = fun loc' => ifc (Loc.cl loc loc') (join cohmax_cl lc1.(vpr)))
      (LC2: lc2 =
            mk
              lc1.(coh)
              lc1.(vrn)
              lc1.(vpr)
              (fun_join lc1.(vpa) view_post)
              lc1.(vpc)
              lc1.(promises))
  .
  Hint Constructors flushopt.

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
  | step_mfence
      b
      (EVENT: event = Event.barrier b)
      (BARRIER: Barrier.is_mfence b)
      (STEP: mfence lc1 lc2)
  | step_sfence
      b
      (EVENT: event = Event.barrier b)
      (BARRIER: Barrier.is_sfence b)
      (STEP: sfence lc1 lc2)
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
  | view_step_mfence
      b
      (EVENT: event = Event.barrier b)
      (BARRIER: Barrier.is_mfence b)
      (STEP: mfence lc1 lc2)
      (MEM: mem2 = mem1)
  | view_step_sfence
      b
      (EVENT: event = Event.barrier b)
      (BARRIER: Barrier.is_sfence b)
      (STEP: sfence lc1 lc2)
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
      cohmax
      (COHMAX: fun_max lc.(coh) cohmax)
      (VRN: lc.(vrn).(View.ts) <= cohmax.(View.ts))
      (VPR: lc.(vpr).(View.ts) <= cohmax.(View.ts))
      (VPA: forall loc, (lc.(vpa) loc).(View.ts) <= cohmax.(View.ts))
      (VPC: forall loc, (lc.(vpc) loc).(View.ts) <= cohmax.(View.ts))
  .

  Inductive wf (tid:Id.t) (mem:Memory.t) (lc:t): Prop :=
  | wf_intro
      (COH: forall loc, (lc.(coh) loc).(View.ts) <= List.length mem)
      (VRN: lc.(vrn).(View.ts) <= List.length mem)
      (VPR: lc.(vpr).(View.ts) <= List.length mem)
      (VPA: forall loc, (lc.(vpa) loc).(View.ts) <= List.length mem)
      (VPC: forall loc, (lc.(vpc) loc).(View.ts) <= List.length mem)
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
      (NINTERVENING: forall loc from to
                       (LATEST: Memory.latest loc from to mem),
          (lc.(coh) loc).(View.ts) <= from \/ to < (lc.(coh) loc).(View.ts))
      (VRNVPR: lc.(vrn).(View.ts) <= lc.(vpr).(View.ts))
      (VPACL: forall loc1 loc2 (CL: Loc.cl loc1 loc2), (lc.(vpa) loc1).(View.ts) = (lc.(vpa) loc2).(View.ts))
      (VPCCL: forall loc1 loc2 (CL: Loc.cl loc1 loc2), (lc.(vpc) loc1).(View.ts) = (lc.(vpc) loc2).(View.ts))
  .
  Hint Constructors wf.

  Lemma init_wf tid: wf tid Memory.empty init.
  Proof.
    econs; ss; i; try by apply bot_spec.
    - econs; ss. eexists. ss.
    - destruct ts; ss.
    - destruct ts; ss. destruct ts; ss.
    - econs; try i; try apply bot_spec.
      econs; ss. i. instantiate (1 := Loc.default). apply bot_spec.
    - rewrite TS. ss.
    - left. apply bot_spec.
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
    inv READ. ss. rewrite fun_add_spec. condtac; [|congr]. splits; ss.
    repeat apply Memory.latest_join; auto.
    apply Memory.ge_latest. eapply fwd_read_view_le; eauto.
  Qed.

  Lemma rmw_failure_spec
        tid mem vloc vold res old_ts lc1 lc2
        (WF: Local.wf tid mem lc1)
        (READ: Local.rmw_failure vloc vold res old_ts lc1 mem lc2):
    <<LATEST: Memory.latest vloc.(ValA.val) old_ts lc2.(Local.vrn).(View.ts) mem>> /\
    <<COH: old_ts = (lc2.(Local.coh) vloc.(ValA.val)).(View.ts)>>.
  Proof.
    inv READ. ss. rewrite fun_add_spec. condtac; [|congr]. splits; ss.
    repeat apply Memory.latest_join; auto.
    apply Memory.ge_latest. eapply fwd_read_view_le; eauto.
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
    inversion WF. econs; i; ss.
    all: try rewrite app_length.
    all: try lia.
    all: try apply WF; ss.
    - rewrite COH. lia.
    - rewrite VPA. lia.
    - rewrite VPC. lia.
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
    - eapply Memory.latest_app_inv. eauto.
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
      (VRN: Order.le lhs.(vpr).(View.ts) rhs.(vpr).(View.ts))
      (VPA: forall loc, Order.le (lhs.(vpa) loc).(View.ts) (rhs.(vpa) loc).(View.ts))
      (VPC: forall loc, Order.le (lhs.(vpc) loc).(View.ts) (rhs.(vpc) loc).(View.ts))
  .

  Global Program Instance le_partial_order: PreOrder le.
  Next Obligation. econs; refl. Qed.
  Next Obligation. ii. inv H. inv H0. econs; etrans; eauto. Qed.

  Lemma writable_lt_coh_ts
        vloc vval tid lc mem ts
        (WRITABLE: writable vloc vval tid lc mem ts):
    lt (lc.(coh) vloc.(ValA.val)).(View.ts) ts.
  Proof.
    inv WRITABLE. inv COHMAX. specialize (MAX (ValA.val vloc)).
    inv MAX. unfold Order.le in *. lia.
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
    inv LC. econs; ss; try refl; i; try apply join_l.
    rewrite fun_add_spec. condtac; try refl.
    clear X. inv e. ss.
  Qed.

  Lemma fulfill_incr
        vloc vval res ts tid lc1 mem1 lc2
        (LC: fulfill vloc vval res ts tid lc1 mem1 lc2):
    le lc1 lc2.
  Proof.
    inv LC. econs; ss; try refl; i; try apply join_l.
    rewrite fun_add_spec. condtac; try refl.
    clear X. inv e. s.
    unfold Order.le. exploit writable_lt_coh_ts; eauto. lia.
  Qed.

  Lemma rmw_incr
        vloc vold vnew old_ts ts tid lc1 mem lc2
        (LC: rmw vloc vold vnew old_ts ts tid lc1 mem lc2):
    le lc1 lc2.
  Proof.
    inv LC. econs; ss; try refl; i; try apply join_l.
    funtac. inversion e.
    unfold Order.le. exploit writable_lt_coh_ts; eauto. lia.
  Qed.

  Lemma rmw_failure_incr
        vloc vold res ts lc1 mem1 lc2
        (LC: rmw_failure vloc vold res ts lc1 mem1 lc2):
    le lc1 lc2.
  Proof.
    inv LC. econs; ss; try refl; i; try apply join_l.
    rewrite fun_add_spec. condtac; try refl.
    clear X. inv e. ss.
  Qed.

  Lemma mfence_incr
        lc1 lc2
        (LC: mfence lc1 lc2):
    le lc1 lc2.
  Proof.
    inv LC. econs; ss; try refl; i; try apply join_l.
  Qed.

  Lemma sfence_incr
        lc1 lc2
        (LC: sfence lc1 lc2):
    le lc1 lc2.
  Proof.
    inv LC. econs; ss; try refl; i; try apply join_l.
  Qed.

  Lemma flush_incr
        vloc lc1 lc2
        (LC: flush vloc lc1 lc2):
    le lc1 lc2.
  Proof.
    inv LC. econs; ss; try refl; i; try apply join_l.
  Qed.

  Lemma flushopt_incr
        vloc lc1 lc2
        (LC: flushopt vloc lc1 lc2):
    le lc1 lc2.
  Proof.
    inv LC. econs; ss; try refl; i; try apply join_l.
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
    - eapply mfence_incr. eauto.
    - eapply sfence_incr. eauto.
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

  Lemma high_ts_spec_cl
        tid mem lc ts loc0
        (WF: wf tid mem lc)
        (GT: forall loc (CL: Loc.cl loc loc0), (lc.(coh) loc).(View.ts) < ts):
      <<NOFWD: forall loc (CL: Loc.cl loc loc0), read_view (lc.(coh) loc) ts = View.mk ts bot >> /\
      <<JOINS: forall loc (CL: Loc.cl loc loc0),
                  ts = join (lc.(coh) loc).(View.ts)
                            (read_view (lc.(coh) loc) ts).(View.ts)>>.
  Proof.
    assert (NOFWD: forall loc (CL: Loc.cl loc loc0), read_view (lc.(coh) loc) ts = View.mk ts bot).
    { i. unfold read_view. condtac; ss.
      inversion e. inv H. inv WF.
      specialize (FWDBANK loc). inv FWDBANK.
      apply GT in CL. lia.
    }
    splits; ss. i. apply le_antisym.
    { repeat rewrite <- join_r. rewrite NOFWD; ss. }
    inv WF. inv COHMAX. viewtac.
    - apply GT in CL. lia.
    - rewrite NOFWD; ss.
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
      + i. rewrite fun_add_spec. condtac; viewtac. eapply Memory.read_spec; eauto.
      + i. exploit FWDBANK; eauto. intro Y. inv Y. des.
        econs; eauto. rewrite fun_add_spec. condtac; ss; eauto.
        inversion e. subst. eauto.
      + i. eapply PROMISES0; eauto. eapply Time.le_lt_trans; [|by eauto].
        rewrite fun_add_spec. condtac; ss. inversion e. rewrite H0. unfold Order.le in COH0. ss.
      + inv COHMAX. inv COHMAX0. rename x0 into mloc.
        destruct (lt_eq_lt_dec ts (View.ts (coh lc1 mloc))).
        { econs; ss.
          - econs; cycle 1.
            { i. funtac. econs; ss. unfold Order.le. inv s; lia. }
            funtac. inv s; ss.
            + inversion e. subst. unfold Order.le in *. lia.
            + destruct (coh lc1 mloc). s. destruct annot. ss.
          - viewtac. unfold read_view.
            condtac; [apply bot_spec | inv s; ss; lia].
          - viewtac. unfold read_view.
            condtac; [apply bot_spec | inv s; ss; lia].
        }
        { exploit high_ts_spec; eauto.
          { i. eapply le_lt_trans; try exact l. specialize (MAX loc). inv MAX. viewtac. }
          i. des.
          econs. instantiate (1 := (View.mk ts bot)).
          - econs; ss.
            { funtac. exfalso. apply c. ss. }
            i. funtac; econs; ss.
            unfold Order.le. etrans; [apply MAX|]. lia.
          - viewtac.
            { rewrite VRN0. lia. }
            unfold read_view. condtac; [apply bot_spec | ss].
          - viewtac.
            { rewrite VPR0. lia. }
            unfold read_view. condtac; [apply bot_spec | ss].
          - i. ss. rewrite VPA0. lia.
          - i. ss. rewrite VPC0. lia.
        }
      + i. revert TS. funtac; cycle 1.
        { i. rewrite <- join_l. eapply NFWD; eauto. }
        i. subst. unfold read_view. condtac; ss.
        * rewrite <- join_l. eapply NFWD; eauto. inversion e0. inversion e. ss.
        * viewtac; rewrite <- join_r; ss.
      + i. funtac. inversion e. subst.
        destruct (le_dec ts from); eauto. apply not_le in n.
        destruct (lt_dec to ts); eauto. apply not_lt in n0.
        unfold Memory.read in MSG. destruct ts; try lia. ss. des_ifs.
        exfalso. eapply LATEST0; eauto.
      + rewrite VRNVPR. apply join_l.
      + apply join_r.
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
      + inv COHMAX. inv COHMAX0. inv COHMAX1. econs.
        * econs; ss. instantiate (1 := ValA.val vloc).
          i. repeat rewrite fun_add_spec. repeat condtac; ss.
          { econs; ss. }
          { exfalso. apply c. ss. }
          { econs; ss. unfold Order.le. etrans; [apply MAX|]. lia. }
          { exfalso. apply c0. ss. }
        * funtac. specialize (MAX x0). inv MAX. unfold Order.le in TS. lia.
        * funtac. specialize (MAX x0). inv MAX. unfold Order.le in TS. lia.
        * i. ss. funtac. rewrite VPA0. specialize (MAX x0). inv MAX. unfold Order.le in TS. lia.
        * i. ss. funtac. rewrite VPC0. specialize (MAX x0). inv MAX. unfold Order.le in TS. lia.
      + i. eapply NFWD; eauto.
        rewrite fun_add_spec in TS. eqvtac.
        rewrite MSG in MSG0. inv MSG0. ss.
      + i. funtac. inversion e. subst.
        destruct (le_dec ts from); eauto. apply not_le in n.
        destruct (lt_dec to ts); eauto. apply not_lt in n0.
        unfold Memory.get_msg in MSG. destruct ts; try lia. ss.
        exfalso. eapply LATEST; eauto.
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
      + inv COHMAX. inv COHMAX0. inv COHMAX1. econs.
        * econs; ss. instantiate (1 := ValA.val vloc).
          i. repeat rewrite fun_add_spec. repeat condtac; ss.
          { econs; ss. }
          { exfalso. apply c. ss. }
          { econs; ss. unfold Order.le. etrans; [apply MAX|]. lia. }
          { exfalso. apply c0. ss. }
        * rewrite fun_add_spec. condtac; ss; cycle 1.
          { exfalso. apply c. ss. }
          viewtac. specialize (MAX x0). inv MAX. unfold Order.le in TS. lia.
        * rewrite fun_add_spec. condtac; ss; cycle 1.
          { exfalso. apply c. ss. }
          viewtac. specialize (MAX x0). inv MAX. unfold Order.le in TS. lia.
        * i. ss. funtac. rewrite VPA0. specialize (MAX x0). inv MAX. unfold Order.le in TS. lia.
        * i. ss. funtac. viewtac.
          { rewrite VPC0. specialize (MAX x0). inv MAX. unfold Order.le in TS. lia. }
          rewrite VPA0. specialize (MAX x0). inv MAX. unfold Order.le in TS. lia.
      + i. rewrite <- join_l. eapply NFWD; eauto.
        rewrite fun_add_spec in TS. eqvtac.
        rewrite MSG in MSG0. inv MSG0. ss.
      + i. funtac. inversion e. subst.
        destruct (le_dec ts from); eauto. apply not_le in n.
        destruct (lt_dec to ts); eauto. apply not_lt in n0.
        unfold Memory.get_msg in MSG. destruct ts; try lia. ss.
        exfalso. eapply LATEST; eauto.
      + rewrite VRNVPR. apply join_l.
      + apply join_r.
    - exploit FWDVIEW; eauto.
      { eapply Memory.read_wf. eauto. }
      i. econs; viewtac.
      + i. rewrite fun_add_spec. condtac; viewtac. eapply Memory.read_spec; eauto.
      + i. exploit FWDBANK; eauto. intro Y. inv Y. des.
        econs; eauto. rewrite fun_add_spec. condtac; ss; eauto.
        inversion e. subst. eauto.
      + i. eapply PROMISES0; eauto. eapply Time.le_lt_trans; [|by eauto].
        rewrite fun_add_spec. condtac; ss. inversion e. rewrite H0. unfold Order.le in COH0. ss.
      + inv COHMAX. inv COHMAX0. rename x0 into mloc.
        destruct (lt_eq_lt_dec old_ts (View.ts (coh lc1 mloc))).
        { econs; ss.
          - econs; cycle 1.
            { i. funtac. econs; ss. unfold Order.le. inv s; lia. }
            funtac. inv s; ss.
            + inversion e. subst. unfold Order.le in *. lia.
            + destruct (coh lc1 mloc). s. destruct annot. ss.
          - viewtac. unfold read_view.
            condtac; [apply bot_spec | inv s; ss; lia].
          - viewtac. unfold read_view.
            condtac; [apply bot_spec | inv s; ss; lia].
        }
        { exploit high_ts_spec; eauto.
          { i. eapply le_lt_trans; try exact l. specialize (MAX loc). inv MAX. viewtac. }
          i. des.
          econs. instantiate (1 := (View.mk old_ts bot)).
          - econs; ss.
            { funtac. exfalso. apply c. ss. }
            i. funtac; econs; ss.
            unfold Order.le. etrans; [apply MAX|]. lia.
          - viewtac.
            { rewrite VRN0. lia. }
            unfold read_view. condtac; [apply bot_spec | ss].
          - viewtac.
            { rewrite VPR0. lia. }
            unfold read_view. condtac; [apply bot_spec | ss].
          - i. ss. rewrite VPA0. lia.
          - i. ss. rewrite VPC0. lia.
        }
      + i. revert TS. funtac; cycle 1.
        { i. rewrite <- join_l. eapply NFWD; eauto. }
        i. subst. unfold read_view. condtac; ss.
        * rewrite <- join_l. eapply NFWD; eauto. inversion e0. inversion e. ss.
        * viewtac; rewrite <- join_r; ss.
      + i. funtac. inversion e. subst.
        destruct (le_dec old_ts from); eauto. apply not_le in n.
        destruct (lt_dec to old_ts); eauto. apply not_lt in n0.
        unfold Memory.read in OLD_MSG. destruct old_ts; try lia. ss. des_ifs.
        exfalso. eapply LATEST0; eauto.
      + rewrite VRNVPR. apply join_l.
      + apply join_r.
    - econs; viewtac.
      + inv COHMAX0. ss.
      + inv COHMAX0. ss.
      + i. viewtac.
      + inv COHMAX. inv COHMAX0. inv COHMAX1. econs; s; eauto.
        * viewtac. specialize (MAX0 x). inv MAX0. unfold Order.le in *. lia.
        * viewtac. specialize (MAX0 x). inv MAX0. unfold Order.le in *. lia.
        * i. viewtac.
      + i. rewrite <- join_l. eapply NFWD; eauto.
      + rewrite VRNVPR. apply join_l.
      + apply join_r.
    - econs; viewtac.
      + inv COHMAX0. ss.
      + i. viewtac.
      + inv COHMAX. inv COHMAX0. inv COHMAX1. econs; s; eauto.
        * viewtac. specialize (MAX0 x). inv MAX0. unfold Order.le in *. lia.
        * i. viewtac.
      + rewrite VRNVPR. apply join_l.
    - econs; viewtac.
      + i. viewtac. inv COHMAX0. ss.
      + i. viewtac. inv COHMAX0. ss.
      + inv COHMAX. inv COHMAX0. inv COHMAX1. econs; s; eauto.
        * i. viewtac.
          specialize (MAX0 x). inv MAX0. unfold Order.le in *. lia.
        * i. viewtac.
          specialize (MAX0 x). inv MAX0. unfold Order.le in *. lia.
      + i. rewrite VPACL at 1; eauto. viewtac. unfold ifc. repeat condtac; ss.
        * exploit Loc.cl_trans; eauto. rewrite X0. ss.
        * apply Loc.cl_sym in X0. exploit Loc.cl_trans; try exact CL; eauto.
          intro Z. apply Loc.cl_sym in Z. rewrite X in Z. ss.
      + i. rewrite VPCCL at 1; eauto. viewtac. unfold ifc. repeat condtac; ss.
        * exploit Loc.cl_trans; eauto. rewrite X0. ss.
        * apply Loc.cl_sym in X0. exploit Loc.cl_trans; try exact CL; eauto.
          intro Z. apply Loc.cl_sym in Z. rewrite X in Z. ss.
    - econs; viewtac.
      + i. viewtac. inv COHMAX_CL. unfold ifc. condtac; ss. apply bot_spec.
      + inv COHMAX. inv COHMAX0. econs; s; eauto. i. viewtac.
        inv COHMAX_CL. unfold ifc. condtac; [|apply bot_spec].
        specialize (MAX x0). inv MAX. unfold Order.le in *. ss.
      + i. rewrite VPACL at 1; eauto. unfold ifc. repeat condtac; ss.
        * exploit Loc.cl_trans; eauto. rewrite X0. ss.
        * apply Loc.cl_sym in X0. exploit Loc.cl_trans; try exact CL; eauto.
          intro Z. apply Loc.cl_sym in Z. rewrite X in Z. ss.
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
      + i. rewrite fun_add_spec. condtac; viewtac. eapply Memory.read_spec; eauto.
      + i. exploit FWDBANK; eauto. intro Y. inv Y. des.
        econs; eauto. rewrite fun_add_spec. condtac; ss; eauto.
        inversion e. subst. eauto.
      + i. eapply PROMISES0; eauto. eapply Time.le_lt_trans; [|by eauto].
        rewrite fun_add_spec. condtac; ss. inversion e. rewrite H0. unfold Order.le in COH0. ss.
      + inv COHMAX. inv COHMAX0. rename x0 into mloc.
        destruct (lt_eq_lt_dec ts (View.ts (coh lc1 mloc))).
        { econs; ss.
          - econs; cycle 1.
            { i. funtac. econs; ss. unfold Order.le. inv s; lia. }
            funtac. inv s; ss.
            + inversion e. subst. unfold Order.le in *. lia.
            + destruct (coh lc1 mloc). s. destruct annot. ss.
          - viewtac. unfold read_view.
            condtac; [apply bot_spec | inv s; ss; lia].
          - viewtac. unfold read_view.
            condtac; [apply bot_spec | inv s; ss; lia].
        }
        { exploit high_ts_spec; eauto.
          { i. eapply le_lt_trans; try exact l. specialize (MAX loc). inv MAX. viewtac. }
          i. des.
          econs. instantiate (1 := (View.mk ts bot)).
          - econs; ss.
            { funtac. exfalso. apply c. ss. }
            i. funtac; econs; ss.
            unfold Order.le. etrans; [apply MAX|]. lia.
          - viewtac.
            { rewrite VRN0. lia. }
            unfold read_view. condtac; [apply bot_spec | ss].
          - viewtac.
            { rewrite VPR0. lia. }
            unfold read_view. condtac; [apply bot_spec | ss].
          - i. ss. rewrite VPA0. lia.
          - i. ss. rewrite VPC0. lia.
        }
      + i. revert TS. funtac; cycle 1.
        { i. rewrite <- join_l. eapply NFWD; eauto. }
        i. subst. unfold read_view. condtac; ss.
        * rewrite <- join_l. eapply NFWD; eauto. inversion e0. inversion e. ss.
        * viewtac; rewrite <- join_r; ss.
      + i. funtac. inversion e. subst.
        destruct (le_dec ts from); eauto. apply not_le in n.
        destruct (lt_dec to ts); eauto. apply not_lt in n0.
        unfold Memory.read in MSG. destruct ts; try lia. ss. des_ifs.
        exfalso. eapply LATEST0; eauto.
      + rewrite VRNVPR. apply join_l.
      + apply join_r.
    - inversion MEM. subst. econs; try rewrite app_length; viewtac; ss.
      all: try by lia.
      + i. funtac; try rewrite COH; lia.
      + i. rewrite VPA. lia.
      + i. rewrite VPC. lia.
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
      + econs. instantiate (1 := (View.mk (S (length mem1)) bot)).
        all: viewtac.
        econs; ss.
        { funtac. exfalso. apply c. ss. }
        i. funtac; econs; ss.
        unfold Order.le. rewrite COH. lia.
      + i. inv MEM.
        eapply Memory.get_msg_snoc_inv in MSG. revert MSG. funtac.
        * i. des; [lia |]. inv MSG0. ss.
        * i. des; [eapply NFWD; eauto |]. inv MSG0. ss.
      + i. funtac; cycle 1.
        { apply NINTERVENING. eapply Memory.latest_app_inv. eauto. }
        inversion e. subst.
        destruct (le_dec (S (length mem1)) from); eauto. apply not_le in n.
        destruct (lt_dec to (S (length mem1))); eauto. apply not_lt in n0.
        exfalso. eapply LATEST; eauto; try rewrite nth_error_last; ss.
    - inversion MEM. subst. econs; try rewrite app_length; viewtac; ss.
      all: try by lia.
      + i. funtac; try rewrite COH; lia.
      + i. rewrite VPA. lia.
      + i. viewtac; [rewrite VPC|rewrite VPA]; lia.
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
      + econs. instantiate (1 := (View.mk (S (length mem1)) bot)).
        all: try i; viewtac.
        econs; ss.
        { funtac. exfalso. apply c. ss. }
        i. funtac; econs; ss.
        unfold Order.le. rewrite COH. lia.
      + i. inv MEM.
        eapply Memory.get_msg_snoc_inv in MSG. revert MSG. funtac.
        * i. des; [lia |]. inv MSG0. ss.
        * i. rewrite <- join_l. des; [eapply NFWD; eauto |]. inv MSG0. ss.
      + i. funtac; cycle 1.
        { apply NINTERVENING. eapply Memory.latest_app_inv. eauto. }
        inversion e. subst.
        destruct (le_dec (S (length mem1)) from); eauto. apply not_le in n.
        destruct (lt_dec to (S (length mem1))); eauto. apply not_lt in n0.
        exfalso. eapply LATEST; eauto; try rewrite nth_error_last; ss.
      + rewrite VRNVPR. apply join_l.
      + apply join_r.
    - exploit FWDVIEW; eauto.
      { eapply Memory.read_wf. eauto. }
      i. econs; viewtac.
      + i. rewrite fun_add_spec. condtac; viewtac. eapply Memory.read_spec; eauto.
      + i. exploit FWDBANK; eauto. intro Y. inv Y. des.
        econs; eauto. rewrite fun_add_spec. condtac; ss; eauto.
        inversion e. subst. eauto.
      + i. eapply PROMISES0; eauto. eapply Time.le_lt_trans; [|by eauto].
        rewrite fun_add_spec. condtac; ss. inversion e. rewrite H0. unfold Order.le in COH0. ss.
      + inv COHMAX. inv COHMAX0. rename x0 into mloc.
        destruct (lt_eq_lt_dec old_ts (View.ts (coh lc1 mloc))).
        { econs; ss.
          - econs; cycle 1.
            { i. funtac. econs; ss. unfold Order.le. inv s; lia. }
            funtac. inv s; ss.
            + inversion e. subst. unfold Order.le in *. lia.
            + destruct (coh lc1 mloc). s. destruct annot. ss.
          - viewtac. unfold read_view.
            condtac; [apply bot_spec | inv s; ss; lia].
          - viewtac. unfold read_view.
            condtac; [apply bot_spec | inv s; ss; lia].
        }
        { exploit high_ts_spec; eauto.
          { i. eapply le_lt_trans; try exact l. specialize (MAX loc). inv MAX. viewtac. }
          i. des.
          econs. instantiate (1 := (View.mk old_ts bot)).
          - econs; ss.
            { funtac. exfalso. apply c. ss. }
            i. funtac; econs; ss.
            unfold Order.le. etrans; [apply MAX|]. lia.
          - viewtac.
            { rewrite VRN0. lia. }
            unfold read_view. condtac; [apply bot_spec | ss].
          - viewtac.
            { rewrite VPR0. lia. }
            unfold read_view. condtac; [apply bot_spec | ss].
          - i. ss. rewrite VPA0. lia.
          - i. ss. rewrite VPC0. lia.
        }
      + i. revert TS. funtac; cycle 1.
        { i. rewrite <- join_l. eapply NFWD; eauto. }
        i. subst. unfold read_view. condtac; ss.
        * rewrite <- join_l. eapply NFWD; eauto. inversion e0. inversion e. ss.
        * viewtac; rewrite <- join_r; ss.
      + i. funtac. inversion e. subst.
        destruct (le_dec old_ts from); eauto. apply not_le in n.
        destruct (lt_dec to old_ts); eauto. apply not_lt in n0.
        unfold Memory.read in OLD_MSG. destruct old_ts; try lia. ss. des_ifs.
        exfalso. eapply LATEST0; eauto.
      + rewrite VRNVPR. apply join_l.
      + apply join_r.
    - econs; viewtac.
      + inv COHMAX0. ss.
      + inv COHMAX0. ss.
      + i. viewtac.
      + inv COHMAX. inv COHMAX0. inv COHMAX1. econs; s; eauto.
        * viewtac. specialize (MAX0 x). inv MAX0. unfold Order.le in *. lia.
        * viewtac. specialize (MAX0 x). inv MAX0. unfold Order.le in *. lia.
        * i. viewtac.
      + i. rewrite <- join_l. eapply NFWD; eauto.
      + rewrite VRNVPR. apply join_l.
      + apply join_r.
    - econs; viewtac.
      + inv COHMAX0. ss.
      + i. viewtac.
      + inv COHMAX. inv COHMAX0. inv COHMAX1. econs; s; eauto.
        * viewtac. specialize (MAX0 x). inv MAX0. unfold Order.le in *. lia.
        * i. viewtac.
      + rewrite VRNVPR. apply join_l.
    - econs; viewtac.
      + i. viewtac. inv COHMAX0. ss.
      + i. viewtac. inv COHMAX0. ss.
      + inv COHMAX. inv COHMAX0. inv COHMAX1. econs; s; eauto.
        * i. viewtac.
          specialize (MAX0 x). inv MAX0. unfold Order.le in *. lia.
        * i. viewtac.
          specialize (MAX0 x). inv MAX0. unfold Order.le in *. lia.
      + i. rewrite VPACL at 1; eauto. viewtac. unfold ifc. repeat condtac; ss.
        * exploit Loc.cl_trans; eauto. rewrite X0. ss.
        * apply Loc.cl_sym in X0. exploit Loc.cl_trans; try exact CL; eauto.
          intro Z. apply Loc.cl_sym in Z. rewrite X in Z. ss.
      + i. rewrite VPCCL at 1; eauto. viewtac. unfold ifc. repeat condtac; ss.
          * exploit Loc.cl_trans; eauto. rewrite X0. ss.
          * apply Loc.cl_sym in X0. exploit Loc.cl_trans; try exact CL; eauto.
            intro Z. apply Loc.cl_sym in Z. rewrite X in Z. ss.
    - econs; viewtac.
      + i. viewtac. inv COHMAX_CL. unfold ifc. condtac; ss. apply bot_spec.
      + inv COHMAX. inv COHMAX0. econs; s; eauto. i. viewtac.
        inv COHMAX_CL. unfold ifc. condtac; [|apply bot_spec].
        specialize (MAX x0). inv MAX. unfold Order.le in *. ss.
      + i. rewrite VPACL at 1; eauto. unfold ifc. repeat condtac; ss.
        * exploit Loc.cl_trans; eauto. rewrite X0. ss.
        * apply Loc.cl_sym in X0. exploit Loc.cl_trans; try exact CL; eauto.
          intro Z. apply Loc.cl_sym in Z. rewrite X in Z. ss.
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
    - i. rewrite VPA. lia.
    - i. rewrite VPC. lia.
    - i. destruct (FWDBANK loc0). des. econs; esplits; ss.
      apply Memory.read_mon; eauto.
    - i. revert IN. rewrite Promises.set_o. condtac.
      + inversion e. i. inv IN. lia.
      + i. exploit PROMISES; eauto. lia.
    - i. rewrite Promises.set_o. apply Memory.get_msg_snoc_inv in MSG. des.
      + destruct ts; ss. condtac; ss.
        eapply PROMISES0; eauto.
      + subst. condtac; ss. congr.
    - inv COHMAX. inv COHMAX0. econs; viewtac.
    - i. apply Memory.get_msg_snoc_inv in MSG. des.
      + eapply NFWD; eauto.
      + rewrite <- MSG0 in TID. ss.
    - i. apply NINTERVENING. eapply Memory.latest_app_inv. eauto.
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

  Lemma rtc_state_step_incr
        tid eu1 eu2
        (STEP: rtc (state_step tid) eu1 eu2):
    le eu1 eu2.
  Proof.
    induction STEP; try refl.
    exploit state_step_incr; eauto. i.
    etrans; eauto.
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
        inversion e. subst. etrans; eauto.
      + inv STEP0. rewrite LC2. ss. rewrite fun_add_spec. condtac; ss.
        inversion e. subst. exploit Local.writable_lt_coh_ts; eauto. lia.
      + inv STEP0. rewrite LC2. ss. rewrite fun_add_spec. condtac; ss.
        inversion e. subst. exploit Local.writable_lt_coh_ts; eauto. lia.
      + inv STEP0. rewrite LC2. ss. rewrite fun_add_spec. condtac; ss.
        inversion e. subst. etrans; eauto.
      + inv STEP0. rewrite LC2. ss.
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
    unfold Order.le in COH.
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

  Lemma rtc_step_state_step_wf
        m1 m2
        (STEP: rtc (step ExecUnit.state_step) m1 m2)
        (WF: wf m1):
    wf m2.
  Proof.
    revert WF. induction STEP; ss. i. apply IHSTEP.
    eapply step_state_step_wf; eauto.
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
      + i. rewrite VPA. lia.
      + i. rewrite VPC. lia.
      + i. destruct (FWDBANK loc0). des. econs; esplits; ss.
        apply Memory.read_mon; eauto.
      + i. exploit PROMISES; eauto. lia.
      + i. apply Memory.get_msg_snoc_inv in MSG. des.
        { eapply PROMISES0; eauto. }
        { subst. ss. congr. }
      + i. apply Memory.get_msg_snoc_inv in MSG. des.
        * eapply NFWD; eauto.
        * rewrite MSG in TS. specialize (COH (Msg.loc msg)). lia.
      + i. apply NINTERVENING. eapply Memory.latest_app_inv. eauto.
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
        * rewrite app_length. lia.
        * i. rewrite VPA. rewrite app_length. lia.
        * i. rewrite VPC. rewrite app_length. lia.
        * i. apply Local.wf_fwdbank_mon. ss.
        * i. exploit PROMISES; eauto. rewrite List.app_length. lia.
        * i. apply Memory.get_msg_snoc_inv in MSG. des.
          { eapply PROMISES0; eauto. }
          { subst. ss. congr. }
        * i. apply Memory.get_msg_snoc_inv in MSG. des.
          { eapply NFWD; eauto. }
          { rewrite MSG in TS. specialize (COH (Msg.loc msg)). lia. }
        * i. apply NINTERVENING. eapply Memory.latest_app_inv. eauto.
      + inv STEP. inv MEM. econs; ss.
        * i. rewrite COH. rewrite app_length. lia.
        * rewrite app_length. lia.
        * rewrite app_length. lia.
        * i. rewrite VPA. rewrite app_length. lia.
        * i. rewrite VPC. rewrite app_length. lia.
        * i. apply Local.wf_fwdbank_mon. ss.
        * i. exploit PROMISES; eauto. rewrite List.app_length. lia.
        * i. apply Memory.get_msg_snoc_inv in MSG. des.
          { eapply PROMISES0; eauto. }
          { subst. ss. congr. }
        * i. apply Memory.get_msg_snoc_inv in MSG. des.
          { eapply NFWD; eauto. }
          { rewrite MSG in TS. specialize (COH (Msg.loc msg)). lia. }
        * i. apply NINTERVENING. eapply Memory.latest_app_inv. eauto.
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

  Lemma rtc_step_view_step_no_promise
        m1 m2
        (STEP: rtc (step ExecUnit.view_step) m1 m2)
        (NOPROMISE: no_promise m1):
    no_promise m2.
  Proof.
    induction STEP; ss.
    exploit step_view_step_no_promise; eauto.
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

  Inductive persisted_loc (m:t) (loc:Loc.t) (val:Val.t): Prop :=
  | persisted_loc_intro
      ts
      (TS: Memory.read loc ts m.(mem) = Some val)
      (LATEST: IdMap.Forall (fun _ sl =>
                 Memory.latest loc ts ((snd sl).(Local.vpc) loc).(View.ts) m.(mem))
                 m.(tpool))
  .
  Hint Constructors persisted_loc.

  Definition persisted m smem := forall loc, persisted_loc m loc (smem loc).

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
