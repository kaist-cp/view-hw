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
    view: View.t (A:=A);
    ex: bool;
  }.
  Hint Constructors t.

  Definition init: t := mk bot bot false.

  Definition read_view (fwd:t) (tsx:Time.t) (ord:OrdR.t): View.t (A:=A) :=
    if andb (fwd.(ts) == tsx) (negb (andb fwd.(ex) (OrdR.ge ord OrdR.acquire_pc)))
    then fwd.(view)
    else View.mk tsx bot.
End FwdItem.
End FwdItem.

Section Eqts.
  Context `{A: Type, B: Type, _: orderC A eq, _: orderC B eq}.

  Inductive eqts_view (v1: View.t (A:=A)) (v2: View.t (A:=B)): Prop :=
  | eqts_view_intro
      (TS: v1.(View.ts) = v2.(View.ts))
  .
  Hint Constructors eqts_view.

  Inductive eqts_fwd (fwd1:FwdItem.t (A:=A)) (fwd2:FwdItem.t (A:=B)): Prop :=
  | eqts_fwd_intro
      (TS: fwd1.(FwdItem.ts) = fwd2.(FwdItem.ts))
      (VIEW: eqts_view fwd1.(FwdItem.view) fwd2.(FwdItem.view))
      (EX: fwd1.(FwdItem.ex) = fwd2.(FwdItem.ex))
  .
  Hint Constructors eqts_fwd.

  Inductive eqts_val (v1:ValA.t (A:=View.t (A:=A))) (v2:ValA.t (A:=View.t (A:=B))): Prop :=
  | eqts_val_intro
      (VAL: v1.(ValA.val) = v2.(ValA.val))
      (VIEW: eqts_view v1.(ValA.annot) v2.(ValA.annot))
  .
  Hint Constructors eqts_val.

  Inductive eqts_event: forall (e1:Event.t (A:=View.t (A:=A))) (e2:Event.t (A:=View.t (A:=B))), Prop :=
  | eqts_event_internal:
      eqts_event Event.internal Event.internal
  | eqts_event_read
      ex rmw_fail ord vloc1 vloc2 res1 res2
      (VLOC: eqts_val vloc1 vloc2)
      (RES: eqts_val res1 res2):
      eqts_event (Event.read ex rmw_fail ord vloc1 res1) (Event.read ex rmw_fail ord vloc2 res2)
  | eqts_event_write
      ex ord vloc1 vloc2 vval1 vval2 res1 res2
      (VLOC: eqts_val vloc1 vloc2)
      (VVAL: eqts_val vval1 vval2)
      (RES: eqts_val res1 res2):
      eqts_event (Event.write ex ord vloc1 vval1 res1) (Event.write ex ord vloc2 vval2 res2)
  | eqts_event_rmw
      ordr ordw vloc1 vloc2 old1 old2 new1 new2:
      eqts_event (Event.rmw ordr ordw vloc1 old1 new1) (Event.rmw ordr ordw vloc2 old2 new2)
  | eqts_event_barrier
      b:
      eqts_event (Event.barrier b) (Event.barrier b)
  | eqts_event_control
      ctrl1 ctrl2
      (CTRL: eqts_view ctrl1 ctrl2):
      eqts_event (Event.control ctrl1) (Event.control ctrl2)
  .
  Hint Constructors eqts_event.
End Eqts.

Section EqtsEquiv.
  Context `{A: Type, _: orderC A eq}.

  Global Program Instance eqts_view_equiv: Equivalence (@eqts_view A A).
  Next Obligation. econs. ss. Qed.
  Next Obligation. econs. inv H1. ss. Qed.
  Next Obligation. econs. inv H1. inv H2. etrans; eauto. Qed.

  Global Program Instance eqts_fwd_equiv: Equivalence (@eqts_fwd A A).
  Next Obligation. econs; ss. Qed.
  Next Obligation. ii. destruct x, y. inv H1. ss. subst. econs; ss. symmetry. ss. Qed.
  Next Obligation. ii. destruct x, y, z. inv H1. inv H2. ss. subst. econs; ss. etrans; eauto. Qed.

  Global Program Instance eqts_val_equiv: Equivalence eqts_val.
  Next Obligation. econs; ss. Qed.
  Next Obligation. ii. destruct x, y. inv H1. ss. subst. econs; ss. symmetry. ss. Qed.
  Next Obligation. ii. destruct x, y, z. inv H1. inv H2. ss. subst. econs; ss. etrans; eauto. Qed.

  Global Program Instance eqts_event_equiv: Equivalence eqts_event.
  Next Obligation. ii. destruct x; econs; ss. Qed.
  Next Obligation.
    ii. inv H1; econs; ss.
    all: symmetry; ss.
  Qed.
  Next Obligation.
    ii. inv H1; inv H2; econs; ss.
    all: etrans; eauto.
  Qed.
End EqtsEquiv.

Module Local.
Section Local.
  Context `{A: Type, _: orderC A eq}.

  Inductive t := mk {
    coh: Loc.t -> View.t (A:=A);
    vrn: View.t (A:=A);
    vwn: View.t (A:=A);
    vro: View.t (A:=A);
    vwo: View.t (A:=A);
    vrel: View.t (A:=A);
    fwdbank: Loc.t -> (FwdItem.t (A:=A));
  }.
  Hint Constructors t.

  Definition init: t := mk bot bot bot bot bot bot (fun _ => FwdItem.init).

  Inductive read (ex:bool) (ord:OrdR.t) (vloc res:ValA.t (A:=View.t (A:=A))) (ts:Time.t) (lc1:t) (mem1: Memory.t) (lc2:t): Prop :=
  | read_intro
      loc val view
      view_pre view_msg view_post
      (LOC: loc = vloc.(ValA.val))
      (VIEW: view = vloc.(ValA.annot))
      (VIEW_PRE: view_pre = joins [view; lc1.(vrn); (ifc (OrdR.ge ord OrdR.acquire) lc1.(vrel))])
      (COH: Memory.latest loc ts (lc1.(coh) loc).(View.ts) mem1)
      (LATEST: Memory.latest loc ts view_pre.(View.ts) mem1)
      (MSG: Memory.read loc ts mem1 = Some val)
      (VIEW_MSG: view_msg = FwdItem.read_view (lc1.(fwdbank) loc) ts ord)
      (VIEW_POST: view_post = join view_pre view_msg)
      (RES: res = ValA.mk _ val view_post)
      (LC2: lc2 =
            mk
              (fun_add loc (join (lc1.(coh) loc) view_post) lc1.(coh))
              (join lc1.(vrn) (ifc (OrdR.ge ord OrdR.acquire_pc) view_post))
              (join lc1.(vwn) (ifc (OrdR.ge ord OrdR.acquire_pc) view_post))
              (join lc1.(vro) view_post)
              lc1.(vwo)
              lc1.(vrel)
              lc1.(fwdbank))
  .
  Hint Constructors read.

  Inductive write (ex:bool) (ord:OrdW.t) (vloc vval res:ValA.t (A:=View.t (A:=A))) (ts:Time.t) (tid:Id.t) (view_pre:View.t (A:=A)) (lc1:t) (mem1: Memory.t) (lc2:t) (mem2: Memory.t): Prop :=
  | write_intro
      loc val
      view_loc view_val
      (LOC: loc = vloc.(ValA.val))
      (VIEW_LOC: view_loc = vloc.(ValA.annot))
      (VAL: val = vval.(ValA.val))
      (VIEW_VAL: view_val = vval.(ValA.annot))
      (MEM: Memory.append (Msg.mk loc val tid) mem1 = (ts, mem2))
      (RES: res = ValA.mk _ 0 (View.mk bot view_pre.(View.annot)))
      (LC2: lc2 =
            mk
              (fun_add loc (View.mk ts bot) lc1.(coh))
              lc1.(vrn)
              lc1.(vwn)
              lc1.(vro)
              (join lc1.(vwo) (View.mk ts bot))
              (join lc1.(vrel) (View.mk (ifc (OrdW.ge ord OrdW.release) ts) bot))
              (fun_add loc (FwdItem.mk ts (join view_loc view_val) ex) lc1.(fwdbank)))
  .
  Hint Constructors write.

  (* writable *)
      (* (EX: ex -> exists eb, *)
      (*      <<TSX: lc1.(exbank) = Some eb>> /\ *)
      (*      <<EX: eb.(Exbank.loc) = loc -> Memory.exclusive tid loc eb.(Exbank.ts) ts mem1>>) *)

  Inductive rmw (ordr:OrdR.t) (ordw:OrdW.t) (vloc vold vnew:ValA.t (A:=View.t (A:=A))) (ts:Time.t) (tid:Id.t) (view_pre:View.t (A:=A)) (lc1:t) (mem1: Memory.t) (lc2:t) (mem2: Memory.t): Prop :=
  | rmw_intro
      loc val prev_ts prev_val (* CHECK: 파라미터로 prev_ts가 필요하지 않은가? *)
      view_loc view_val
      view_post
      (LOC: loc = vloc.(ValA.val))
      (VIEW: view_loc = vloc.(ValA.annot))

      (* pre = addr \/ rnew \/ (rk >= acq ? ts.rel) *)
      (VIEW_PRE: view_pre = joins [view_loc; lc1.(vrn); (ifc (OrdR.ge ordr OrdR.acquire) lc1.(vrel))])

      (* writable *)
      (COH: lt (lc1.(coh) loc).(View.ts) ts)
      (EXT: lt view_pre.(View.ts) ts)

      (* forall t', prev_t < t' <= t --> M(t').loc != l *)
      (LATEST: Memory.latest loc prev_ts ts mem1)

      (* CHECK: read(M,l,prev_t) = v = vold ? *)
      (MSG: Memory.read loc prev_ts mem1 = Some prev_val)
      (OLD: vold.(ValA.val) = prev_val)

      (* CHECK: post = t ? *)
      (VIEW_POST: view_post = (View.mk ts bot))

      (* [e2] = v@data *)
      (VAL: val = vnew.(ValA.val))
      (VIEW_VAL: view_val = vnew.(ValA.annot))

      (MEM: Memory.append (Msg.mk loc val tid) mem1 = (ts, mem2))

      (* CHECK: regs view는 사라지는 것? *)
      (* (RES: res = ValA.mk _ 0 (View.mk bot view_pre.(View.annot))) *)

      (LC2: lc2 =
            mk
              (fun_add loc view_post lc1.(coh)) (* read *)
              (join lc1.(vrn) (ifc (OrdR.ge ordr OrdR.acquire_pc) view_post)) (* read *)
              (join lc1.(vwn) (ifc (OrdR.ge ordr OrdR.acquire_pc) view_post)) (* read *)
              (join lc1.(vro) view_post) (* read *)
              (join lc1.(vwo) view_post) (* write *)
              (join lc1.(vrel) ((ifc (OrdW.ge ordw OrdW.release) view_post))) (* write *)
              (* CHECK: addr view와 data view가 둘 다 필요한가? *)
              (fun_add loc (FwdItem.mk ts (join view_loc view_val) false) lc1.(fwdbank))) (* write *)
  .
  Hint Constructors rmw.

  (* CHECK: dmb 처리 *)
  Inductive dmb (rr rw wr ww:bool) (lc1 lc2:t): Prop :=
  | dmb_intro
      (LC2: lc2 =
            mk
              lc1.(coh)
              (joins [lc1.(vrn); ifc rr lc1.(vro); ifc wr lc1.(vwo)])
              (joins [lc1.(vwn); ifc rw lc1.(vro); ifc ww lc1.(vwo)])
              lc1.(vro)
              lc1.(vwo)
              lc1.(vrel)
              lc1.(fwdbank))
  .
  Hint Constructors dmb.

  Inductive step (event:Event.t (A:=View.t (A:=A))) (tid:Id.t) (mem1 mem2:Memory.t) (lc1 lc2:t): Prop :=
  | step_internal
      (EVENT: event = Event.internal)
      (LC: lc2 = lc1)
      (MEM: mem2 = mem1)
  | step_read
      ord vloc res ts
      (EVENT: event = Event.read false false ord vloc res)
      (STEP: read false ord vloc res ts lc1 mem1 lc2)
      (MEM: mem2 = mem1)
  | step_write
      ord vloc vval res ts view_pre
      (EVENT: event = Event.write false ord vloc vval res)
      (STEP: write false ord vloc vval res ts tid view_pre lc1 mem1 lc2 mem2)
  | step_rmw
      ordr ordw vloc vold vnew ts view_pre
      (EVENT: event = Event.rmw ordr ordw vloc vold vnew)
      (STEP: rmw ordr ordw vloc vold vnew ts tid view_pre lc1 mem1 lc2 mem2)
  | step_dmb (* TODO: check it *)
      rr rw wr ww
      (EVENT: event = Event.barrier (Barrier.dmb rr rw wr ww))
      (STEP: dmb rr rw wr ww lc1 lc2)
      (MEM: mem2 = mem1)
  .
  Hint Constructors step.

  Inductive wf_fwdbank (loc:Loc.t) (mem:Memory.t) (coh: Time.t) (fwd:FwdItem.t (A:=A)): Prop :=
  | wf_fwdbank_intro
      (TS: fwd.(FwdItem.ts) <= Memory.latest_ts loc coh mem)
      (VIEW: fwd.(FwdItem.view).(View.ts) <= fwd.(FwdItem.ts))
      (VAL: exists val, Memory.read loc fwd.(FwdItem.ts) mem = Some val)
  .

  Inductive wf (tid:Id.t) (mem:Memory.t) (lc:t): Prop :=
  | wf_intro
      (COH: forall loc, (lc.(coh) loc).(View.ts) <= List.length mem)
      (VRN: lc.(vrn).(View.ts) <= List.length mem)
      (VWN: lc.(vwn).(View.ts) <= List.length mem)
      (VRO: lc.(vro).(View.ts) <= List.length mem)
      (VWO: lc.(vwo).(View.ts) <= List.length mem)
      (VREL: lc.(vrel).(View.ts) <= List.length mem)
      (FWDBANK: forall loc, wf_fwdbank loc mem (lc.(coh) loc).(View.ts) (lc.(fwdbank) loc))
  .
  Hint Constructors wf.

  Lemma init_wf tid: wf tid Memory.empty init.
  Proof.
    econs; ss; i; try by apply bot_spec.
    - econs; ss. eexists. ss.
  Qed.

  (* CHECK: 원래 주석처리 되어있었음 *)
  (* Lemma fwd_read_view_coh_le *)
  (*       tid mem lc *)
  (*       (WF: wf tid mem lc) *)
  (*       loc ord ts *)
  (*       (COH: (lc.(coh) loc).(View.ts) <= ts): *)
  (*   ((lc.(Local.fwdbank) loc).(FwdItem.read_view) ts ord).(View.ts) <= ts. *)
  (* Proof. *)
  (*   inv WF. exploit FWDBANK; eauto. i. des. *)
  (*   unfold FwdItem.read_view. condtac; ss. etrans; eauto. etrans; eauto. *)
  (* Qed. *)

  Lemma fwd_view_le
        tid mem lc loc ts ord
        (WF: wf tid mem lc)
        (COH: Memory.latest loc ts (lc.(coh) loc).(View.ts) mem):
    (lc.(fwdbank) loc).(FwdItem.view).(View.ts) <=
    (FwdItem.read_view (lc.(fwdbank) loc) ts ord).(View.ts).
  Proof.
    unfold FwdItem.read_view. condtac; ss.
    inv WF. exploit FWDBANK. intro Y. inv Y.
    rewrite VIEW, TS. apply Memory.latest_latest_ts. ss.
  Qed.

  Lemma fwd_read_view_le
        tid mem lc loc ts ord
        (WF: wf tid mem lc)
        (COH: Memory.latest loc ts (lc.(coh) loc).(View.ts) mem):
    (FwdItem.read_view (lc.(fwdbank) loc) ts ord).(View.ts) <= ts.
  Proof.
    inv WF. destruct (FWDBANK loc). des.
    unfold FwdItem.read_view. condtac; ss.
    destruct (equiv_dec (FwdItem.ts (fwdbank lc loc)) ts); ss. inv e. ss.
  Qed.

  Lemma read_spec
        tid mem ex ord vloc res ts lc1 lc2
        (WF: Local.wf tid mem lc1)
        (READ: Local.read ex ord vloc res ts lc1 mem lc2):
    <<LATEST: Memory.latest vloc.(ValA.val) ts res.(ValA.annot).(View.ts) mem>> /\
    <<COH: ts = Memory.latest_ts vloc.(ValA.val) (lc2.(Local.coh) vloc.(ValA.val)).(View.ts) mem>>.
  Proof.
    inv READ. ss. rewrite fun_add_spec. condtac; [|congr]. splits.
    - apply Memory.latest_join; auto.
      apply Memory.ge_latest. eapply fwd_read_view_le; eauto.
    - unfold join. ss. apply le_antisym.
      + unfold FwdItem.read_view. des_ifs.
        * rewrite Bool.andb_true_iff in Heq. des.
          destruct (equiv_dec (FwdItem.ts (fwdbank lc1 (ValA.val vloc))) ts); ss.
          inv e0. inv WF. exploit FWDBANK. intro Y. inv Y.
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
  Qed.

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
  Qed.

  Inductive le (lhs rhs:t): Prop :=
  | le_intro
      (COH: forall loc, Order.le (lhs.(coh) loc).(View.ts) (rhs.(coh) loc).(View.ts))
      (VRN: Order.le lhs.(vrn).(View.ts) rhs.(vrn).(View.ts))
      (VWN: Order.le lhs.(vwn).(View.ts) rhs.(vwn).(View.ts))
      (VRO: Order.le lhs.(vro).(View.ts) rhs.(vro).(View.ts))
      (VWO: Order.le lhs.(vwo).(View.ts) rhs.(vwo).(View.ts))
      (VREL: Order.le lhs.(vrel).(View.ts) rhs.(vrel).(View.ts))
  .

  (* CHECK: move? *)
  Global Program Instance le_partial_order: PreOrder le.
  Next Obligation. econs; refl. Qed.
  Next Obligation. ii. inv H1. inv H2. econs; etrans; eauto. Qed.

  Lemma read_incr
        ex ord vloc res ts lc1 mem1 lc2
        (LC: read ex ord vloc res ts lc1 mem1 lc2):
    le lc1 lc2.
  Proof.
    inv LC. econs; ss; try refl; try apply join_l.
    i. rewrite fun_add_spec. condtac; try refl.
    clear X. inv e. s. apply join_l.
  Qed.

  Lemma write_incr
        ex ord vloc vval res ts tid view_pre lc1 mem1 lc2 mem2
        (LC: write ex ord vloc vval res ts tid view_pre lc1 mem1 lc2 mem2):
    le lc1 lc2.
  Proof.
    inv LC. econs; ss; try refl; try apply join_l.
    i. rewrite fun_add_spec. condtac; try refl.
    clear X. inv e. s.
    (* TODO: fulfill should update COH's taint, too. *)
    admit.
  Qed.

  (* TODO *)
  Lemma rmw_incr
        ordr ordw vloc vold vnew ts tid view_pre lc1 mem1 lc2 mem2
        (LC: rmw ordr ordw vloc vold vnew ts tid view_pre lc1 mem1 lc2 mem2):
    le lc1 lc2.
  Proof.
    inv LC. econs; ss; try refl; try apply join_l.
    i. rewrite fun_add_spec. condtac; try refl.
    clear X. inv e. s.
    (* TODO: fulfill should update COH's taint, too. *)
    admit.
  Qed.

  Lemma dmb_incr
        rr rw wr ww lc1 lc2
        (LC: dmb rr rw wr ww lc1 lc2):
    le lc1 lc2.
  Proof.
    inv LC. econs; ss; try refl; try apply join_l.
  Qed.

  Lemma step_incr
        e tid mem1 mem2 lc1 lc2
        (LC: step e tid mem1 mem2 lc1 lc2):
    le lc1 lc2.
  Proof.
    inv LC; try refl.
    - eapply read_incr. eauto.
    - eapply write_incr. eauto.
    - eapply rmw_incr. eauto.
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
  Context `{A: Type, _: orderC A eq}.

  Inductive t := mk {
    state: State.t (A:=View.t (A:=A));
    local: Local.t (A:=A);
    mem: Memory.t;
  }.
  Hint Constructors t.

  Inductive step0 (tid:Id.t) (e1 e2:Event.t (A:=View.t (A:=A))) (eu1 eu2:t): Prop :=
  | step0_intro
      (STATE: State.step e1 eu1.(state) eu2.(state))
      (LOCAL: Local.step e2 tid eu1.(mem) eu2.(mem) eu1.(local) eu2.(local))
      (MEM: eu2.(mem) = eu1.(mem))
  .
  Hint Constructors step0.

  Inductive step (tid:Id.t) (eu1 eu2:t): Prop :=
  | step_intro
      e
      (STEP: step0 tid e e eu1 eu2)
  .
  Hint Constructors step.

  Inductive rmap_wf (mem:Memory.t) (rmap:RMap.t (A:=View.t (A:=A))): Prop :=
  | rmap_wf_intro
      (RMAP: forall r, (RMap.find r rmap).(ValA.annot).(View.ts) <= List.length mem)
  .
  Hint Constructors rmap_wf.

  Inductive wf (tid:Id.t) (eu:t): Prop :=
  | wf_intro
      (STATE: rmap_wf eu.(mem) eu.(state).(State.rmap))
      (LOCAL: Local.wf tid eu.(mem) eu.(local))
  .
  Hint Constructors wf.

  Lemma rmap_add_wf
        mem rmap loc (val:ValA.t (A:=View.t (A:=A)))
        (WF: rmap_wf mem rmap)
        (VAL: val.(ValA.annot).(View.ts) <= List.length mem):
    rmap_wf mem (RMap.add loc val rmap).
  Proof.
    inv WF. econs. i. unfold RMap.find, RMap.add. rewrite IdMap.add_spec.
    condtac; viewtac.
  Qed.

  Lemma expr_wf
        mem rmap e
        (RMAP: rmap_wf mem rmap):
    (sem_expr rmap e).(ValA.annot).(View.ts) <= List.length mem.
  Proof.
    induction e; viewtac. apply RMAP.
  Qed.

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

  Lemma step0_wf tid e1 e2 eu1 eu2
        (STEP: step0 tid e1 e2 eu1 eu2)
        (EVENT: eqts_event e1 e2)
        (WF: wf tid eu1):
    wf tid eu2.
  Proof.
    destruct eu1 as [state1 local1 mem1].
    destruct eu2 as [state2 local2 mem2].
    inv WF. inv STEP. ss. subst.

    assert (FWDVIEW: forall loc ts ord,
               Memory.latest loc ts (View.ts (Local.coh local1 loc)) mem1 ->
               ts <= length mem1 ->
               View.ts (FwdItem.read_view (Local.fwdbank local1 loc) ts ord) <= length mem1).
    { i. rewrite Local.fwd_read_view_le; eauto. }
    generalize LOCAL. intro WF_LOCAL1.
    inv STATE0; inv LOCAL0; inv EVENT; inv LOCAL; ss.
    - econs; ss.
      eauto using rmap_add_wf, expr_wf.
    - inv RES. inv VIEW. inv VLOC. inv VIEW.
      exploit Local.read_spec; eauto. intro READ_SPEC. guardH READ_SPEC.
      inv STEP. ss. subst.
      exploit FWDVIEW; eauto.
      { eapply read_wf. eauto. }
      i. econs; ss.
      + apply rmap_add_wf; viewtac.
        rewrite TS, <- TS0. viewtac.
        eauto using expr_wf.
      + econs; viewtac; eauto using expr_wf.
        all: try by rewrite <- TS0; eauto using expr_wf.
        * i. rewrite fun_add_spec. condtac; viewtac.
          rewrite <- TS0. eauto using expr_wf.
        * i. exploit FWDBANK; eauto. intro Y. inv Y. des.
          econs; eauto. rewrite TS1, fun_add_spec. condtac; ss. inversion e. subst.
          apply Memory.latest_ts_mon. apply join_l.
    (* TODO: check *)
        (* * i. rewrite fun_add_spec in *. destruct ex0. *)
        (*   { inv H1. ss. condtac; [|congr]. econs; eauto. *)
        (*     - desH READ_SPEC. rewrite COH1 at 1. ss. *)
        (*     - s. apply join_r. *)
        (*   } *)
        (*   { exploit EXBANK; eauto. intro Y. inv Y. des. econs; eauto. *)
        (*     - rewrite TS1. apply Memory.latest_ts_mon. *)
        (*       condtac; ss. inversion e. apply join_l. *)
        (*     - rewrite VIEW. condtac; ss. inversion e. rewrite H3. apply join_l. *)
        (*   } *)
        (* * i. eapply PROMISES0; eauto. eapply Time.le_lt_trans; [|by eauto]. *)
        (*   rewrite fun_add_spec. condtac; ss. inversion e. rewrite H2. apply join_l. *)
    - inv RES. inv VIEW. inv VVAL. inv VIEW. inv VLOC. inv VIEW.
      admit. (* promise_step_wf *)
      (* inv STEP. inv WRITABLE. econs; ss. *)
      (* + apply rmap_add_wf; viewtac. *)
      (*   rewrite TS. unfold ifc. condtac; [|by apply bot_spec]. eapply get_msg_wf. eauto. *)
      (* + econs; viewtac; rewrite <- ? TS0, <- ? TS1; eauto using get_msg_wf, expr_wf. *)
      (*   * i. rewrite fun_add_spec. condtac; viewtac. *)
      (*   * i. rewrite ? fun_add_spec. condtac; viewtac. *)
      (*     inversion e. subst. *)
      (*     econs; viewtac; rewrite <- TS0, <- TS1 in *. *)
      (*     { unfold Memory.get_msg in MSG. destruct ts; ss. rewrite MSG. condtac; ss. } *)
      (*     { etrans; [|apply Nat.lt_le_incl; eauto]. rewrite <- join_l. ss. } *)
      (*     { etrans; [|apply Nat.lt_le_incl; eauto]. rewrite <- join_r, <- join_l. ss. } *)
      (*     { revert MSG. unfold Memory.read, Memory.get_msg. *)
      (*       destruct ts; ss. i. rewrite MSG. ss. eexists. des_ifs. *)
      (*     } *)
      (*   * destruct ex0; ss. i. exploit EXBANK; eauto. intro Y. inv Y. des. econs; eauto. *)
      (*     { rewrite TS2, fun_add_spec. condtac; ss. inversion e. rewrite H3. *)
      (*       apply Memory.latest_ts_mon. apply Nat.le_lteq. left. ss. *)
      (*     } *)
      (*     { rewrite VIEW, fun_add_spec. condtac; ss. inversion e. rewrite H3. clear -COH0. lia. } *)
      (*   * i. revert IN. rewrite Promises.unset_o. condtac; ss. eauto. *)
      (*   * i. rewrite Promises.unset_o. rewrite fun_add_spec in TS2. condtac. *)
      (*     { inversion e. subst. rewrite MSG in MSG0. destruct msg. inv MSG0. ss. *)
      (*       revert TS2. condtac; ss; intuition. *)
      (*     } *)
      (*     { eapply PROMISES0; eauto. revert TS2. condtac; ss. i. *)
      (*       inversion e. rewrite H2. rewrite COH0. ss. *)
      (*     } *)
    - admit.
      (* inv STEP. econs; ss. *)
    (* apply rmap_add_wf; viewtac. *)
    (* inv RES. inv VIEW. rewrite TS. s. apply bot_spec. *)
    - inv STEP. econs; ss. econs; viewtac.
    (* - inv STEP. econs; ss. econs; viewtac. *)
    (* - inv LC. econs; ss. econs; viewtac. *)
    (*   inv CTRL. rewrite <- TS. eauto using expr_wf. *)
  Qed.

  Lemma step_wf tid eu1 eu2
        (STEP: step tid eu1 eu2)
        (WF: wf tid eu1):
    wf tid eu2.
  Proof.
    inv STEP. eapply step0_wf; eauto. refl.
  Qed.

  Lemma rmap_append_wf
        mem msg rmap
        (WF: rmap_wf mem rmap):
    rmap_wf (mem ++ [msg]) rmap.
  Proof.
    inv WF. econs. i. rewrite RMAP. rewrite List.app_length. lia.
  Qed.

  Lemma rmap_interference_wf
        mem rmap mem_interference
        (WF: rmap_wf mem rmap):
    rmap_wf (mem ++ mem_interference) rmap.
  Proof.
    inv WF. econs. i. rewrite RMAP, app_length. lia.
  Qed.

  (* TODO: move above.. *)
  (* Lemma promise_step_wf tid eu1 eu2 *)
  (*       (STEP: promise_step tid eu1 eu2) *)
  (*       (WF: wf tid eu1): *)
  (*   wf tid eu2. *)
  (* Proof. *)
  (*   destruct eu1 as [state1 local1 mem1]. *)
  (*   destruct eu2 as [state2 local2 mem2]. *)
  (*   inv WF. inv STEP. ss. subst. *)
  (*   inv LOCAL. inv LOCAL0. inv MEM2. econs; ss. *)
  (*   - apply rmap_append_wf. ss. *)
  (*   - econs; eauto. *)
  (*     all: try rewrite List.app_length; s; try lia. *)
  (*     + i. rewrite COH. lia. *)
  (*     + i. destruct (FWDBANK loc0). des. econs; esplits; ss. *)
  (*       * rewrite TS. apply Memory.latest_ts_append. *)
  (*       * apply Memory.read_mon; eauto. *)
  (*     + i. exploit EXBANK; eauto. intro Y. inv Y. des. *)
  (*       econs; esplits; ss. *)
  (*       * rewrite TS. apply Memory.latest_ts_append. *)
  (*       * apply Memory.read_mon. eauto. *)
  (*     + i. revert IN. rewrite Promises.set_o. condtac. *)
  (*       * inversion e. i. inv IN. lia. *)
  (*       * i. exploit PROMISES; eauto. lia. *)
  (*     + i. rewrite Promises.set_o. apply Memory.get_msg_snoc_inv in MSG. des. *)
  (*       * destruct ts; ss. condtac; ss. *)
  (*         eapply PROMISES0; eauto. *)
  (*       * subst. condtac; ss. congr. *)
  (* Qed. *)

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
    ii. inv H1. inv H2. econs; etrans; eauto.
    rewrite MEM, app_assoc. eauto.
  Qed.

  Lemma step_incr tid eu1 eu2
        (STEP: step tid eu1 eu2):
    le eu1 eu2.
  Proof.
    inv STEP. inv STEP0. econs.
    - eapply Local.step_incr. eauto.
    - rewrite MEM, app_nil_r. ss.
  Qed.
End ExecUnit.
End ExecUnit.

Module Machine.
  Inductive t := mk {
    tpool: IdMap.t (State.t (A:=View.t (A:=unit)) * Local.t (A:=unit));
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
           (FIND: IdMap.find tid m.(tpool) = Some (st, lc)), State.is_terminal st)
  .
  Hint Constructors is_terminal.

  Inductive step (eustep: forall (tid:Id.t) (eu1 eu2:ExecUnit.t (A:=unit)), Prop) (m1 m2:t): Prop :=
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
    econs; ss.
    - econs. i. unfold RMap.find, RMap.init. rewrite IdMap.gempty. ss.
    - apply Local.init_wf.
  Qed.

  Lemma step_step_wf
        m1 m2
        (STEP: step ExecUnit.step m1 m2)
        (WF: wf m1):
    wf m2.
  Proof.
    destruct m1 as [tpool1 mem1].
    destruct m2 as [tpool2 mem2].
    inv STEP. inv STEP0. inv WF. econs. ss. subst.
    i. revert FIND0. rewrite IdMap.add_spec. condtac.
    - inversion e0. i. inv FIND0.
      eapply ExecUnit.step_wf; eauto. econs; eauto.
    - inv STEP. ss. i. subst. exploit WF0; eauto.
  Qed.

  (* TODO: necessary? *)
  (* Lemma step_promise_step_wf *)
  (*       m1 m2 *)
  (*       (STEP: step ExecUnit.promise_step m1 m2) *)
  (*       (WF: wf m1): *)
  (*   wf m2. *)
  (* Proof. *)
  (*   destruct m1 as [tpool1 mem1]. *)
  (*   destruct m2 as [tpool2 mem2]. *)
  (*   inv STEP. inv STEP0. inv LOCAL. inv MEM2. inv WF. econs. ss. subst. *)
  (*   i. revert FIND0. rewrite IdMap.add_spec. condtac. *)
  (*   - inversion e. i. inv FIND0. *)
  (*     eapply ExecUnit.promise_step_wf; eauto. econs; eauto. econs; eauto. *)
  (*     + econs; eauto. *)
  (*     + refl. *)
  (*   - i. exploit WF0; eauto. i. inv x. ss. econs; ss. *)
  (*     + apply ExecUnit.rmap_append_wf. ss. *)
  (*     + inv LOCAL. econs; eauto. *)
  (*       all: try rewrite List.app_length; s; try lia. *)
  (*       * i. rewrite COH. lia. *)
  (*       * i. destruct (FWDBANK loc0). des. econs; esplits; ss. *)
  (*         { rewrite TS. apply Memory.latest_ts_append. } *)
  (*         { apply Memory.read_mon; eauto. } *)
  (*       * i. exploit EXBANK; eauto. intro Y. inv Y. des. *)
  (*         econs; esplits; ss. *)
  (*         { rewrite TS. apply Memory.latest_ts_append. } *)
  (*         { apply Memory.read_mon. eauto. } *)
  (*       * i. exploit PROMISES; eauto. lia. *)
  (*       * i. apply Memory.get_msg_snoc_inv in MSG. des. *)
  (*         { eapply PROMISES0; eauto. } *)
  (*         { subst. ss. congr. } *)
  (* Qed. *)

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
  .
  Hint Constructors exec.

  Inductive state_exec (m1 m2:t): Prop :=
  | state_exec_intro
      (TPOOL: IdMap.Forall2
                (fun tid sl1 sl2 =>
                   rtc (ExecUnit.step tid)
                       (ExecUnit.mk (fst sl1) (snd sl1) m1.(mem))
                       (ExecUnit.mk (fst sl2) (snd sl2) m1.(mem)))
                m1.(tpool) m2.(tpool))
      (MEM: m1.(mem) = m2.(mem))
  .

  Inductive equiv (m1 m2:t): Prop :=
  | equiv_intro
      (TPOOL: IdMap.Equal m1.(tpool) m2.(tpool))
      (MEM: m1.(mem) = m2.(mem))
  .

  Lemma unlift_step_step
        m1 m2 tid st1 lc1
        (STEPS: rtc (step ExecUnit.step) m1 m2)
        (TPOOL: IdMap.find tid m1.(tpool) = Some (st1, lc1)):
    exists st2 lc2,
      <<TPOOL: IdMap.find tid m2.(tpool) = Some (st2, lc2)>> /\
      <<STEPS: rtc (ExecUnit.step tid)
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
      inv STEP0.
      admit.
      (* inv STEP. ss. subst. eauto. *)
    (* - rewrite IdMap.add_spec. condtac; eauto. *)
    (*   inv STEP0. ss. subst. inv LOCAL. inv MEM2. *)
    (*   apply Memory.get_msg_snoc_inv in MSG. des; eauto. subst. *)
    (*   ss. congr. *)
  Qed.
End Machine.
