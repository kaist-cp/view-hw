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
  }.
  Hint Constructors t.

  Definition read_view (coh:View.t (A:=unit)) (tsx:Time.t): View.t (A:=unit) :=
    if coh.(View.ts) == tsx
    then View.mk bot bot
    else View.mk tsx bot.

  Definition init: t := mk bot bot.

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
              (join lc1.(vrn) view_post))
  .
  Hint Constructors read.

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
              lc1.(vrn))
  .
  Hint Constructors write.

  Inductive rmw (vloc vold vnew:ValA.t (A:=unit)) (old_ts:Time.t) (ts:Time.t) (tid:Id.t) (lc1:t) (mem1:Memory.t) (lc2:t) (mem2: Memory.t): Prop :=
  | rmw_intro
      loc old new
      view_post
      (LOC: loc = vloc.(ValA.val))
      (COH: (lc1.(coh) loc).(View.ts) <= old_ts)
      (EX: Memory.exclusive tid loc old_ts ts mem1)
      (OLD_MSG: Memory.read loc old_ts mem1 = Some old)
      (OLD: old = vold.(ValA.val))
      (NEW: new = vnew.(ValA.val))
      (VIEW_POST: view_post = View.mk ts bot)
      (MEM: Memory.append (Msg.mk loc new tid) mem1 = (ts, mem2))
      (LC2: lc2 =
            mk
              (fun_add loc view_post lc1.(coh))
              (join lc1.(vrn) view_post))
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
              (join lc1.(vrn) view_post))
  .
  Hint Constructors rmw_failure.

  Inductive cohmax (mloc:Loc.t) (lc:t): Prop :=
  | cohmax_intro
      (COHMAX: forall loc, (lc.(coh) loc).(View.ts) <= (lc.(coh) mloc).(View.ts))
  .
  Hint Constructors cohmax.

  Inductive dmb (rr rw wr ww:bool) (lc1 lc2:t): Prop :=
  | dmb_intro
      mloc
      (COHMAX: cohmax mloc lc1)
      (LC2: lc2 =
            mk
              lc1.(coh)
              (joins [lc1.(vrn); ifc wr (lc1.(coh) mloc)]))
  .
  Hint Constructors dmb.

  Inductive step (event:Event.t (A:=unit)) (tid:Id.t) (mem1 mem2:Memory.t) (lc1 lc2:t): Prop :=
  | step_internal
      (EVENT: event = Event.internal)
      (LC: lc2 = lc1)
      (MEM: mem2 = mem1)
  | step_read
      vloc res ts ord
      (EVENT: event = Event.read false false ord vloc res)
      (STEP: read vloc res ts lc1 mem1 lc2)
      (MEM: mem2 = mem1)
  | step_write
      vloc vval res ts ord
      (EVENT: event = Event.write false ord vloc vval res)
      (STEP: write vloc vval res ts tid lc1 mem1 lc2 mem2)
  | step_rmw
      vloc vold vnew old_ts ts ordr ordw
      (EVENT: event = Event.rmw ordr ordw vloc vold vnew)
      (STEP: rmw vloc vold vnew old_ts ts tid lc1 mem1 lc2 mem2)
  | step_rmw_failure
      vloc vold old_ts ord res
      (EVENT: event = Event.read false true ord vloc res)
      (STEP: rmw_failure vloc vold res old_ts lc1 mem1 lc2)
      (MEM: mem2 = mem1)
  | step_dmb
      rr rw wr ww
      (EVENT: event = Event.barrier (Barrier.dmb rr rw wr ww))
      (STEP: dmb rr rw wr ww lc1 lc2)
      (MEM: mem2 = mem1)
  .
  Hint Constructors step.

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
      (FWDBANK: forall loc, wf_fwdbank loc mem (lc.(coh) loc).(View.ts))
      (COHMAX: wf_cohmax lc)
  .
  Hint Constructors wf.

  Lemma init_wf tid: wf tid Memory.empty init.
  Proof.
    econs; ss; i; try by apply bot_spec.
    - econs; ss. eexists. ss.
    - exists Loc.default; ss.
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

  Inductive le (lhs rhs:t): Prop :=
  | le_intro
      (COH: forall loc, Order.le (lhs.(coh) loc).(View.ts) (rhs.(coh) loc).(View.ts))
      (VRN: Order.le lhs.(vrn).(View.ts) rhs.(vrn).(View.ts))
  .

  Global Program Instance le_partial_order: PreOrder le.
  Next Obligation. econs; refl. Qed.
  Next Obligation. ii. inv H. inv H0. econs; etrans; eauto. Qed.

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
        tid e mem1 mem2 lc1 lc2
        (STEP: step e tid mem1 mem2 lc1 lc2)
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
    - inversion MEM. subst. econs; try rewrite app_length.
      all: try by viewtac; ss; lia.
      + i. funtac; try rewrite COH; lia.
      + i. funtac; cycle 1.
        { apply wf_fwdbank_mon. specialize (FWDBANK loc). ss. }
        inversion e. subst. econs.
        exploit Memory.append_spec; eauto.
        unfold Memory.read, Memory.get_msg. destruct (S (length mem1)); ss. intro MSG. des.
        rewrite MSG. ss. eexists. des_ifs.
      + unfold Memory.append in MEM. inv MEM.
        econs; ss. instantiate (1 := ValA.val vloc).
        * econs. i. funtac.
        * funtac.
    - inversion MEM. subst. econs; try rewrite app_length.
      all: try by viewtac; ss; lia.
      + i. funtac; try rewrite COH; lia.
      + i. funtac; cycle 1.
        { apply wf_fwdbank_mon. specialize (FWDBANK loc). ss. }
        inversion e. subst. econs.
        exploit Memory.append_spec; eauto.
        unfold Memory.read, Memory.get_msg. destruct (S (length mem1)); ss. intro MSG. des.
        rewrite MSG. ss. eexists. des_ifs.
      + unfold Memory.append in MEM. inv MEM.
        econs; ss. instantiate (1 := ValA.val vloc).
        * econs. i. funtac.
        * funtac. viewtac.
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
    - econs; viewtac.
      inv COHMAX0. econs; [econs|]; ss.
      viewtac. inv COHMAX. specialize (COHMAX1 mloc0). lia.
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

  Inductive step0 (tid:Id.t) (e1 e2:Event.t (A:=unit)) (eu1 eu2:t): Prop :=
  | step0_intro
      (STATE: State.step e1 eu1.(state) eu2.(state))
      (LOCAL: Local.step e2 tid eu1.(mem) eu2.(mem) eu1.(local) eu2.(local))
  .
  Hint Constructors step0.

  Inductive step (tid:Id.t) (eu1 eu2:t): Prop :=
  | step_intro
      e
      (STEP: step0 tid e e eu1 eu2)
  .
  Hint Constructors step.

  Inductive wf (tid:Id.t) (eu:t): Prop :=
  | wf_intro
      (LOCAL: Local.wf tid eu.(mem) eu.(local))
  .
  Hint Constructors wf.

  Lemma step0_wf tid e eu1 eu2
        (STEP: step0 tid e e eu1 eu2)
        (WF: wf tid eu1):
    wf tid eu2.
  Proof.
    inv WF. inv STEP. econs; ss.
    eapply Local.step_wf; eauto.
  Qed.

  Lemma step_wf tid eu1 eu2
        (STEP: step tid eu1 eu2)
        (WF: wf tid eu1):
    wf tid eu2.
  Proof.
    inv STEP. eapply step0_wf; eauto.
  Qed.

  Lemma rtc_step_wf tid eu1 eu2
        (STEP: rtc (step tid) eu1 eu2)
        (WF: wf tid eu1):
    wf tid eu2.
  Proof.
    revert WF. induction STEP; ss. i. apply IHSTEP.
    eapply step_wf; eauto.
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
           State.is_terminal st)
  .
  Hint Constructors is_terminal.

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
    - i. inv STEP. exploit WF0; eauto. i. inv x. ss. econs; ss.
      inv LOCAL0. inv LOCAL. econs; eauto.
      all: ss.
      + inv STEP. inv MEM. econs; ss.
        * i. rewrite COH. rewrite app_length. lia.
        * rewrite app_length. lia.
        * i. apply Local.wf_fwdbank_mon. ss.
      + inv STEP. inv MEM. econs; ss.
        * i. rewrite COH. rewrite app_length. lia.
        * rewrite app_length. lia.
        * i. apply Local.wf_fwdbank_mon. ss.
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
  .
  Hint Constructors exec.

  Inductive equiv (m1 m2:t): Prop :=
  | equiv_intro
      (TPOOL: IdMap.Equal m1.(tpool) m2.(tpool))
      (MEM: m1.(mem) = m2.(mem))
  .

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
    rewrite IdMap.add_spec. condtac; eauto.
    inv STEP0. ss. inv LOCAL; eauto.
    - inv STEP. inv MEM. apply Memory.get_msg_snoc_inv in MSG. des; eauto. subst.
      ss. congr.
    - inv STEP. inv MEM. apply Memory.get_msg_snoc_inv in MSG. des; eauto. subst.
      ss. congr.
  Qed.
End Machine.
