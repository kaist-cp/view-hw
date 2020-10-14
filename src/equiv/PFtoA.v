Require Import Relations.
Require Import Permutation.
Require Import NArith.
Require Import PArith.
Require Import ZArith.
Require Import Lia.
Require Import FMapPositive.
Require Import FSetPositive.
Require Import EquivDec.
Require Import sflib.
Require Import PacoNotation.
Require Import HahnRelationsBasic.
Require Import HahnSets.

Require Import PromisingArch.lib.Basic.
Require Import PromisingArch.lib.HahnRelationsMore.
Require Import PromisingArch.lib.Order.
Require Import PromisingArch.lib.Time.
Require Import PromisingArch.lib.Lang.
Require Import PromisingArch.promising.Promising.
Require Import PromisingArch.promising.CommonPromising.
Require Import PromisingArch.promising.StateExecFacts.
Require Import PromisingArch.axiomatic.Axiomatic.
Require Import PromisingArch.axiomatic.SimLocal.
Require Import PromisingArch.equiv.PtoPF.
Require Import PromisingArch.equiv.PFtoA1.
Require Import PromisingArch.equiv.PFtoA2.
Require Import PromisingArch.equiv.PFtoA3.
Require Import PromisingArch.equiv.PFtoA4OBW.
Require Import PromisingArch.equiv.PFtoA4OBR.
Require Import PromisingArch.equiv.PFtoA4FR.
Require Import PromisingArch.equiv.PFtoA4Atomic.
Require Import PromisingArch.equiv.PFtoA4FOB.
Require Import PromisingArch.equiv.PFtoA4FP.
Require Import PromisingArch.equiv.PFtoA4SL.

Set Implicit Arguments.


Lemma sim_traces_sim_th'_step
      p trs atrs ws rs fs covs vexts
      m ex
      (STEP: Machine.pf_exec p m)
      (SIM: sim_traces p m.(Machine.mem) trs atrs ws rs fs covs vexts)
      (PRE: Valid.pre_ex p ex)
      (CO: ex.(Execution.co) = co_gen ws)
      (RF: ex.(Execution.rf) = rf_gen ws rs)
      (PF: ex.(Execution.pf) = pf_gen ws fs m.(Machine.mem))
      (INTERNAL: acyclic (Execution.internal ex))
      (CO1: Valid.co1 ex)
      (CO2: Valid.co2 ex)
      (RF1: Valid.rf1 ex)
      (RF2: Valid.rf2 ex)
      (RF_WF: Valid.rf_wf ex)
      (PF1: Valid.pf1 ex)
      (PF2: Valid.pf2 ex)
      (TR: IdMap.Forall2
             (fun _ tr sl => exists l, tr = (ExecUnit.mk (fst sl) (snd sl) m.(Machine.mem)) :: l)
             trs m.(Machine.tpool))
      (ATR: IdMap.Forall2
              (fun _ atr aeu => exists l, atr = aeu :: l)
              atrs (Valid.aeus PRE)):
  forall tid tr atr wl rl fl covl vextl
    n eu1 eu2 tr' aeu1 aeu2 atr' w1 w2 wl' r1 r2 rl' f1 f2 fl' cov1 cov2 covl' vext1 vext2 vextl'
    (FIND_TR: IdMap.find tid trs = Some tr)
    (FIND_ATR: IdMap.find tid atrs = Some atr)
    (FIND_WL: IdMap.find tid ws = Some wl)
    (FIND_RL: IdMap.find tid rs = Some rl)
    (FIND_FL: IdMap.find tid fs = Some fl)
    (FIND_COVL: IdMap.find tid covs = Some covl)
    (FIND_VEXTL: IdMap.find tid vexts = Some vextl)
    (EU: lastn (S n) tr = eu2 :: eu1 :: tr')
    (AEU: lastn (S n) atr = aeu2 :: aeu1 :: atr')
    (WL: lastn (S n) wl = w2 :: w1 :: wl')
    (RL: lastn (S n) rl = r2 :: r1 :: rl')
    (FL: lastn (S n) fl = f2 :: f1 :: fl')
    (COV: lastn (S n) covl = cov2 :: cov1 :: covl')
    (VEXT: lastn (S n) vextl = vext2 :: vext1 :: vextl')
    (SIM_TH': sim_th' tid m.(Machine.mem) ex (v_gen vexts) eu1 aeu1),
    sim_th' tid m.(Machine.mem) ex (v_gen vexts) eu2 aeu2.
Proof.
  i. econs.
  - eapply sim_traces_sim_th'_sl; eauto.
  - eapply sim_traces_sim_th'_sl; eauto.
  - eapply sim_traces_sim_th'_ob_write; eauto.
  - eapply sim_traces_sim_th'_ob_read; eauto.
  - eapply sim_traces_sim_th'_fr; eauto.
  - eapply sim_traces_sim_th'_atomic; eauto.
  - eapply sim_traces_sim_th'_fob; eauto.
  - eapply sim_traces_sim_th'_fp; eauto.
Qed.

Lemma sim_traces_sim_th'
      p trs atrs ws rs fs covs vexts
      m ex
      (STEP: Machine.pf_exec p m)
      (SIM: sim_traces p m.(Machine.mem) trs atrs ws rs fs covs vexts)
      (PRE: Valid.pre_ex p ex)
      (CO: ex.(Execution.co) = co_gen ws)
      (RF: ex.(Execution.rf) = rf_gen ws rs)
      (PF: ex.(Execution.pf) = pf_gen ws fs m.(Machine.mem))
      (INTERNAL: acyclic (Execution.internal ex))
      (CO1: Valid.co1 ex)
      (CO2: Valid.co2 ex)
      (RF1: Valid.rf1 ex)
      (RF2: Valid.rf2 ex)
      (RF_WF: Valid.rf_wf ex)
      (PF1: Valid.pf1 ex)
      (PF2: Valid.pf2 ex)
      (TR: IdMap.Forall2
             (fun _ tr sl => exists l, tr = (ExecUnit.mk (fst sl) (snd sl) m.(Machine.mem)) :: l)
             trs m.(Machine.tpool))
      (ATR: IdMap.Forall2
              (fun _ atr aeu => exists l, atr = aeu :: l)
              atrs (Valid.aeus PRE)):
  forall tid tr atr wl rl fl covl vextl
    n eu tr' aeu atr' w wl' r rl' f fl' cov covl' vext vextl'
    (N: n < length tr)
    (FIND_TR: IdMap.find tid trs = Some tr)
    (FIND_ATR: IdMap.find tid atrs = Some atr)
    (FIND_WL: IdMap.find tid ws = Some wl)
    (FIND_RL: IdMap.find tid rs = Some rl)
    (FIND_FL: IdMap.find tid fs = Some fl)
    (FIND_COVL: IdMap.find tid covs = Some covl)
    (FIND_VEXTL: IdMap.find tid vexts = Some vextl)
    (EU: lastn (S n) tr = eu :: tr')
    (AEU: lastn (S n) atr = aeu :: atr')
    (WL: lastn (S n) wl = w :: wl')
    (RL: lastn (S n) rl = r :: rl')
    (FL: lastn (S n) fl = f :: fl')
    (COV: lastn (S n) covl = cov :: covl')
    (VEXT: lastn (S n) vextl = vext :: vextl'),
    sim_th' tid m.(Machine.mem) ex (v_gen vexts) eu aeu.
Proof.
  intro tid. generalize (SIM tid). intro X. inv X; [by i|]. induction n.
  { (* init *)
    i. simplify.
    generalize (SIM tid). intro X. inv X; simplify.
    exploit (lastn_one tr).
    { exploit sim_trace_last; eauto. }
    i. des.
    exploit (lastn_one atr).
    { exploit sim_trace_last; eauto. i. des. subst. ss. lia. }
    i. des.
    exploit (lastn_one wl).
    { exploit sim_trace_last; eauto. i. des. subst. ss. lia. }
    i. des.
    exploit (lastn_one rl).
    { exploit sim_trace_last; eauto. i. des. subst. ss. lia. }
    i. des.
    exploit (lastn_one covl).
    { exploit sim_trace_last; eauto. i. des. subst. ss. lia. }
    i. des.
    exploit (lastn_one vextl).
    { exploit sim_trace_last; eauto. i. des. subst. ss. lia. }
    i. des.
    repeat match goal with
           | [H1: lastn ?a ?b = ?c, H2: lastn ?a ?b = ?d |- _] =>
             rewrite H1 in H2
           end.
    exploit sim_trace_last; eauto. i. des. subst. simplify.
    exploit sim_trace_length; eauto. s. intro LEN. guardH LEN.
    simplify. exploit sim_trace_lastn; eauto. instantiate (1 := 0).
    rewrite EU, AEU, WL, RL, COV, VEXT. i.
    exploit sim_trace_sim_th; eauto. intro TH.
    inv x0.
    unfold Machine.init_with_promises in FIND. ss. rewrite IdMap.mapi_spec, STMT in FIND. inv FIND.

    Ltac inv_po :=
      repeat match goal with
             | [H: Execution.po ?a ?b |- _] => inv H; ss; try lia
      end.

    econs; ss.
    - econs; ss. econs. ii. unfold RMap.init. rewrite ? IdMap.gempty. ss.
    - econs; ss.
      + ii. inv EID. inv REL. obtac. inv_po.
      + ii. inv EID. inv REL. des_union; obtac; inv_po.
        obtac. inv_po.
      + ii. inv EID. inv REL. des_union; obtac; inv_po.
        obtac. inv_po.
      + ii. inv EID. inv REL. obtac. inv_po.
      + ii. inv EID. inv REL. obtac. inv_po.
      + ii. inv EID. inv REL; inv H1; obtac; inv_po.
      + ii. inv EID. inv REL; inv H1; obtac; inv_po.
      + right. esplits; eauto. ii. inv H1. inv REL. obtac. inv_po.
      + i. destruct view; ss. exploit Promises.promises_from_mem_inv; eauto. i. des.
        hexploit sim_traces_ex; try exact SIM.
        all: try rewrite lastn_all; ss.
        all: eauto.
        all: try by clear -LEN; unguardH LEN; des; s; lia.
        intro EX.
        exploit sim_trace_last; eauto. i. des. simplify.
        exploit sim_trace_sim_th; eauto. intro L.
        exploit L.(WPROP1); eauto.
        { instantiate (3 := S view). unfold Memory.get_msg. eauto. }
        generalize (TR tid). rewrite <- H0. intro X. inv X. des. simplify. s. destruct b.
        inv STEP.  inv NOPROMISE. erewrite PROMISES; eauto. i. des.
        { inv x1. }
        exploit L.(WPROP2); eauto. i. des.
        exploit L.(WPROP3); eauto. i. des. subst. rewrite x2 in x4. inv x4.
        exploit EX.(LABELS_REV); eauto. i.
        esplits; cycle 1.
        * econs; eauto.
        * rewrite EX.(XVEXT); ss.
          { etrans; eauto. }
          { apply List.nth_error_Some. congr. }
        * clear. lia.
      + intro loc. exists loc. splits; ss.
        { apply Loc.cl_refl. }
        ii. inv EID. inv REL. obtac; inv_po.
      + ii. inv EID. inv REL; obtac; inv_po.
      + ii. inv EID. inv REL. obtac. inv_po.
      + ii. inv EID. inv REL. obtac. inv_po.
    - ii. ss. lia.
    - ii. ss. lia.
    - ii. ss. lia.
    - ii. ss. lia.
    - ii. ss. lia.
    - ii. ss. lia.
  }
  i. simplify.
  exploit sim_trace_length; eauto. intro LEN. guardH LEN.
  exploit lastn_S1; try exact EU; [unguardH LEN; des; lia|].
  exploit lastn_S1; try exact AEU; [unguardH LEN; des; lia|i].
  exploit lastn_S1; try exact WL; [unguardH LEN; des; lia|i].
  exploit lastn_S1; try exact RL; [unguardH LEN; des; lia|i].
  exploit lastn_S1; try exact FL; [unguardH LEN; des; lia|i].
  exploit lastn_S1; try exact COV; [unguardH LEN; des; lia|i].
  exploit lastn_S1; try exact VEXT; [unguardH LEN; des; lia|i].
  subst. exploit sim_trace_lastn; eauto. instantiate (1 := n). i.
  exploit sim_trace_last; eauto. i. des.
  exploit IHn; try exact HDTR; eauto; [lia|]. i.
  eapply sim_traces_sim_th'_step; eauto.
  - rewrite EU, HDTR. ss.
  - rewrite AEU, HDATR. ss.
  - rewrite WL, HDWL. ss.
  - rewrite RL, HDRL. ss.
  - rewrite FL, HDFL. ss.
  - rewrite COV, HDCOVL. ss.
  - rewrite VEXT, HDVEXTL. ss.
Qed.

Lemma sim_traces_vext_valid
      p trs atrs ws rs fs covs vexts
      m ex
      (STEP: Machine.pf_exec p m)
      (SIM: sim_traces p m.(Machine.mem) trs atrs ws rs fs covs vexts)
      (NOPROMISE: Machine.no_promise m)
      (PRE: Valid.pre_ex p ex)
      (CO: ex.(Execution.co) = co_gen ws)
      (RF: ex.(Execution.rf) = rf_gen ws rs)
      (PF: ex.(Execution.pf) = pf_gen ws fs m.(Machine.mem))
      (INTERNAL: acyclic (Execution.internal ex))
      (CO1: Valid.co1 ex)
      (CO2: Valid.co2 ex)
      (RF1: Valid.rf1 ex)
      (RF2: Valid.rf2 ex)
      (RF_WF: Valid.rf_wf ex)
      (PF1: Valid.pf1 ex)
      (PF2: Valid.pf2 ex)
      (TR: IdMap.Forall2
             (fun _ tr sl => exists l, tr = (ExecUnit.mk (fst sl) (snd sl) m.(Machine.mem)) :: l)
             trs m.(Machine.tpool))
      (ATR: IdMap.Forall2
              (fun _ atr aeu => exists l, atr = aeu :: l)
              atrs (Valid.aeus PRE)):
  <<FR:
    forall eid1 eid2
      (FR: Execution.fr ex eid1 eid2),
      Time.lt ((v_gen vexts) eid1) ((v_gen vexts) eid2)>> /\
  <<OB_WRITE:
    forall eid1 eid2
      (OB: ob' ex eid1 eid2)
      (EID2: ex.(Execution.label_is) Label.is_write eid2),
      Time.lt ((v_gen vexts) eid1) ((v_gen vexts) eid2)>> /\
  <<OB_READ:
    forall eid1 eid2
      (OB: ob' ex eid1 eid2)
      (EID2: ex.(Execution.label_is) Label.is_read eid2),
      Time.le ((v_gen vexts) eid1) ((v_gen vexts) eid2)>> /\
  <<ATOMIC:
    forall eid1 eid2 eid
      (ATOMIC: ex.(Execution.rmw) eid1 eid2)
      (FRE: Execution.fre ex eid1 eid)
      (COE: Execution.coe ex eid eid2),
      False>> /\
  <<FOB:
    forall eid1 eid2
      (FOB: Execution.fob ex eid1 eid2),
      Time.le ((v_gen vexts) eid1) ((v_gen vexts) eid2)>> /\
  <<FP:
    forall eid1 eid2
      (FP: Execution.fp ex eid1 eid2),
      Time.lt ((v_gen vexts) eid1) ((v_gen vexts) eid2)>>.
Proof.
  splits; i.
  - destruct eid1 as [tid1 eid1].
    destruct eid2 as [tid2 eid2].
    inversion FR.
    + inv H. des. exploit RF2; eauto. i. des.
      revert READ. unfold Execution.label. s. rewrite PRE.(Valid.LABELS), IdMap.map_spec.
      generalize (ATR tid1). generalize (SIM tid1). intros X Y; inv X; inv Y; simplify; ss.
      i. des. subst.
      exploit sim_trace_last; eauto. i. des. simplify.
      exploit sim_trace_length; eauto. s. i. des.
      hexploit sim_traces_sim_th'; eauto.
      { s. instantiate (1 := length tr'). lia. }
      all: try rewrite lastn_all; s; eauto; try lia.
      intro TH'. eapply TH'.(PFtoA3.FR); eauto.
      apply List.nth_error_Some. congr.
    + inv H. inv H1. inv H. inv H1. destruct l; ss.
      revert EID. unfold Execution.label. s. rewrite PRE.(Valid.LABELS), IdMap.map_spec.
      generalize (ATR tid1). generalize (SIM tid1). intros X Y; inv X; inv Y; simplify; ss.
      i. des. subst.
      exploit sim_trace_last; eauto. i. des. simplify.
      exploit sim_trace_length; eauto. s. i. des.
      hexploit sim_traces_sim_th'; eauto.
      { s. instantiate (1 := length tr'). lia. }
      all: try rewrite lastn_all; s; eauto; try lia.
      intro TH'. eapply TH'.(PFtoA3.FR); eauto.
      apply List.nth_error_Some. congr.
  - destruct eid1 as [tid1 eid1].
    destruct eid2 as [tid2 eid2].
    inversion EID2. destruct l; ss.
    revert EID. unfold Execution.label. s. rewrite PRE.(Valid.LABELS), IdMap.map_spec.
    generalize (ATR tid2). generalize (SIM tid2). intros X Y; inv X; inv Y; simplify; ss.
    i. des. subst.
    exploit sim_trace_last; eauto. i. des. simplify.
    exploit sim_trace_length; eauto. s. i. des.
    hexploit sim_traces_sim_th'; eauto.
    { s. instantiate (1 := length tr'). lia. }
    all: try rewrite lastn_all; s; eauto; try lia.
    intro TH'. eapply TH'.(PFtoA3.OBW); eauto.
    apply List.nth_error_Some. congr.
  - destruct eid1 as [tid1 eid1].
    destruct eid2 as [tid2 eid2].
    inversion EID2. destruct l; ss.
    revert EID. unfold Execution.label. s. rewrite PRE.(Valid.LABELS), IdMap.map_spec.
    generalize (ATR tid2). generalize (SIM tid2). intros X Y; inv X; inv Y; simplify; ss.
    i. des. subst.
    exploit sim_trace_last; eauto. i. des. simplify.
    exploit sim_trace_length; eauto. s. i. des.
    hexploit sim_traces_sim_th'; eauto.
    { s. instantiate (1 := length tr'). lia. }
    all: try rewrite lastn_all; s; eauto; try lia.
    intro TH'. eapply TH'.(PFtoA3.OBR); eauto.
    apply List.nth_error_Some. congr.
  - destruct eid1 as [tid1 eid1].
    destruct eid2 as [tid2 eid2].
    exploit Valid.rmw_spec; eauto. i. des.
    inversion LABEL2. des. destruct l; ss.
    revert EID. unfold Execution.label. s. rewrite PRE.(Valid.LABELS), IdMap.map_spec.
    generalize (ATR tid2). generalize (SIM tid2). intros X Y; inv X; inv Y; simplify; ss.
    i. des. subst.
    exploit sim_trace_last; eauto. i. des. simplify.
    exploit sim_trace_length; eauto. s. i. des.
    hexploit sim_traces_sim_th'; eauto.
    { s. instantiate (1 := length tr'). lia. }
    all: try rewrite lastn_all; s; eauto; try lia.
    intro TH'. eapply TH'.(PFtoA3.ATOMIC); eauto.
    apply List.nth_error_Some. congr.
  - destruct eid1 as [tid1 eid1].
    destruct eid2 as [tid2 eid2].
    exploit Execution.fob_flushopt; eauto. intro EID2. inversion EID2.
    revert EID. unfold Execution.label. s. rewrite PRE.(Valid.LABELS), IdMap.map_spec.
    generalize (ATR tid2). generalize (SIM tid2). intros X Y; inv X; inv Y; simplify; ss.
    i. des. subst.
    exploit sim_trace_last; eauto. i. des. simplify.
    exploit sim_trace_length; eauto. s. i. des.
    hexploit sim_traces_sim_th'; eauto.
    { s. instantiate (1 := length tr'). lia. }
    all: try rewrite lastn_all; s; eauto; try lia.
    intro TH'. eapply TH'.(PFtoA3.FOB); eauto.
    apply List.nth_error_Some. congr.
  - destruct eid1 as [tid1 eid1].
    destruct eid2 as [tid2 eid2].
    dup FP. guardH FP. obtac.
    + exploit PF2; eauto. i. des. inv PERSIST. destruct l; ss.
      revert EID. unfold Execution.label. s. rewrite PRE.(Valid.LABELS), IdMap.map_spec.
      generalize (ATR tid1). generalize (SIM tid1). intros X Y; inv X; inv Y; simplify; ss.
      i. des. subst.
      exploit sim_trace_last; eauto. i. des. simplify.
      exploit sim_trace_length; eauto. s. i. des.
      hexploit sim_traces_sim_th'; eauto.
      { s. instantiate (1 := length tr'). lia. }
      all: try rewrite lastn_all; s; eauto; try lia.
      intro TH'. eapply TH'.(PFtoA3.FP); eauto.
      apply List.nth_error_Some. congr.
    + revert EID0. unfold Execution.label. s. rewrite PRE.(Valid.LABELS), IdMap.map_spec.
      generalize (ATR tid1). generalize (SIM tid1). intros Z W. inv Z; inv W; simplify; ss.
      i. des. subst.
      exploit sim_trace_last; eauto. i. des. simplify.
      exploit sim_trace_length; eauto. s. i. des.
      hexploit sim_traces_sim_th'; eauto.
      { s. instantiate (1 := length tr'). lia. }
      all: try rewrite lastn_all; s; eauto; try lia.
      intro TH'. eapply TH'.(PFtoA3.FP); eauto.
      apply List.nth_error_Some. congr.
Qed.

Lemma sim_traces_valid_internal
      p trs atrs ws rs fs covs vexts
      m ex
      (STEP: Machine.pf_exec p m)
      (SIM: sim_traces p m.(Machine.mem) trs atrs ws rs fs covs vexts)
      (PRE: Valid.pre_ex p ex)
      (CO: ex.(Execution.co) = co_gen ws)
      (RF: ex.(Execution.rf) = rf_gen ws rs)
      (CO1: Valid.co1 ex)
      (CO2: Valid.co2 ex)
      (RF1: Valid.rf1 ex)
      (RF2: Valid.rf2 ex)
      (RF_WF: Valid.rf_wf ex)
      (TR: IdMap.Forall2
             (fun _ tr sl => exists l, tr = (ExecUnit.mk (fst sl) (snd sl) m.(Machine.mem)) :: l)
             trs m.(Machine.tpool))
      (ATR: IdMap.Forall2
              (fun _ atr aeu => exists l, atr = aeu :: l)
              atrs (Valid.aeus PRE)):
  <<INTERNAL:
    forall eid1 eid2
      (INTERNAL: Execution.internal ex eid1 eid2),
      (Time.lt ((v_gen covs) eid1) ((v_gen covs) eid2) /\ ex.(Execution.label_is) Label.is_write eid2) \/
      (Time.le ((v_gen covs) eid1) ((v_gen covs) eid2) /\ ex.(Execution.label_is) Label.is_read eid2)>>.
Proof.
  generalize STEP. intro X. inv X.
  ii. exploit Valid.internal_rw; eauto. i. des.
  inv EID2. destruct l; ss.
  - right. des_union.
    + exploit sim_traces_cov_po_loc; eauto. i. des.
      exploit PO_LOC_READ; eauto.
    + exploit sim_traces_cov_fr; eauto. i.
      split; eauto using Nat.lt_le_incl.
    + exploit sim_traces_cov_co; eauto. i.
      split; eauto using Nat.lt_le_incl.
    + exploit sim_traces_cov_rf; eauto. i.
      split; eauto. rewrite x0. auto.
  - left. des_union.
    + exploit sim_traces_cov_po_loc; eauto. i. des.
      exploit PO_LOC_WRITE; eauto.
    + exploit sim_traces_cov_fr; eauto.
    + exploit sim_traces_cov_co; eauto.
    + exploit RF2; eauto. i. des. congr.
Qed.

Lemma sim_traces_valid_external_atomic
      p trs atrs ws rs fs covs vexts
      m ex
      (STEP: Machine.pf_exec p m)
      (SIM: sim_traces p m.(Machine.mem) trs atrs ws rs fs covs vexts)
      (PRE: Valid.pre_ex p ex)
      (CO: ex.(Execution.co) = co_gen ws)
      (RF: ex.(Execution.rf) = rf_gen ws rs)
      (PF: ex.(Execution.pf) = pf_gen ws fs m.(Machine.mem))
      (INTERNAL: acyclic (Execution.internal ex))
      (CO1: Valid.co1 ex)
      (CO2: Valid.co2 ex)
      (RF1: Valid.rf1 ex)
      (RF2: Valid.rf2 ex)
      (RF_WF: Valid.rf_wf ex)
      (PF1: Valid.pf1 ex)
      (PF2: Valid.pf2 ex)
      (TR: IdMap.Forall2
             (fun _ tr sl => exists l, tr = (ExecUnit.mk (fst sl) (snd sl) m.(Machine.mem)) :: l)
             trs m.(Machine.tpool))
      (ATR: IdMap.Forall2
              (fun _ atr aeu => exists l, atr = aeu :: l)
              atrs (Valid.aeus PRE)):
  <<EXTERNAL:
    forall eid1 eid2
      (OB: Execution.ob ex eid1 eid2)
      (LABEL1: Execution.label_is ex Label.is_access_persist eid1)
      (LABEL2: Execution.label_is ex Label.is_access_persist eid2),
      (Time.lt ((v_gen vexts) eid1) ((v_gen vexts) eid2) /\ ex.(Execution.label_is) Label.is_write eid2) \/
      (Time.le ((v_gen vexts) eid1) ((v_gen vexts) eid2) /\ ex.(Execution.label_is) Label.is_read eid2) \/
      (Time.le ((v_gen vexts) eid1) ((v_gen vexts) eid2) /\ ex.(Execution.label_is) Label.is_flushopt eid2)>> /\
  <<ATOMIC: le (ex.(Execution.rmw) ∩ ((Execution.fre ex) ⨾ (Execution.coe ex))) bot>>.
Proof.
  generalize STEP. intro X. inv X. splits.
  - exploit sim_traces_vext_valid; eauto. i. des.
    inv LABEL2. destruct l; ss.
    + right. left. rewrite ob_ob' in OB. des_union; eauto.
      * obtac; cycle 1.
        { destruct l; ss. congr. }
        exploit CO2; eauto. i. des. congr.
      * exploit CO2; eauto. i. des. congr.
      * obtac; cycle 1.
        { destruct l; ss. congr. }
        exploit CO2; eauto. i. des. congr.
    + left. rewrite ob_ob' in OB. des_union; eauto.
      * exploit sim_traces_vext_co; eauto.
      * exploit Execution.fob_flushopt; eauto. intro Z. inv Z.
        destruct l; ss. congr.
    + repeat right. rewrite ob_ob' in OB. des_union; eauto.
      * obtac; cycle 1.
        { destruct l; ss. congr. }
        exploit CO2; eauto. i. des. congr.
      * exploit CO2; eauto. i. des. congr.
      * obtac; cycle 1.
        { destruct l; ss. congr. }
        exploit CO2; eauto. i. des. congr.
      * exfalso. eapply ob'_flushopt; eauto.
  - exploit sim_traces_vext_valid; eauto. i. des.
    ii. inv H. inv H1. des. exfalso. eauto.
Qed.

Lemma sim_traces_valid_per
      p trs atrs ws rs fs covs vexts
      m ex smem
      (STEP: Machine.pf_exec p m)
      (PMEM: Machine.persisted m smem)
      (SIM: sim_traces p m.(Machine.mem) trs atrs ws rs fs covs vexts)
      (NOPROMISE: Machine.no_promise m)
      (PRE: Valid.pre_ex p ex)
      (CO: ex.(Execution.co) = co_gen ws)
      (RF: ex.(Execution.rf) = rf_gen ws rs)
      (PF: ex.(Execution.pf) = pf_gen ws fs m.(Machine.mem))
      (INTERNAL: acyclic (Execution.internal ex))
      (CO1: Valid.co1 ex)
      (CO2: Valid.co2 ex)
      (RF1: Valid.rf1 ex)
      (RF2: Valid.rf2 ex)
      (RF_WF: Valid.rf_wf ex)
      (PF1: Valid.pf1 ex)
      (PF2: Valid.pf2 ex)
      (TR: IdMap.Forall2
             (fun _ tr sl => exists l, tr = (ExecUnit.mk (fst sl) (snd sl) m.(Machine.mem)) :: l)
             trs m.(Machine.tpool))
      (ATR: IdMap.Forall2
              (fun _ atr aeu => exists l, atr = aeu :: l)
              atrs (Valid.aeus PRE)):
  forall eid loc
    (EID: ex.(Execution.label_is) (Label.is_writing loc) eid)
    (DOM: dom_rel (Execution.per ex) eid),
    exists tid sl msg,
      <<SL: IdMap.find tid m.(Machine.tpool) = Some sl>> /\
      <<MSG: Memory.get_msg ((v_gen vexts) eid) m.(Machine.mem) = Some msg>> /\
      msg.(Msg.loc) = loc /\
      Time.le ((v_gen vexts) eid) ((snd sl).(Local.per) loc).(View.ts).
Proof.
  i. destruct eid as [tid iid]. obtac.
  generalize EID0. unfold Execution.label. s. rewrite PRE.(Valid.LABELS), IdMap.map_spec.
  generalize (ATR tid). generalize (SIM tid). intros X Y; inv X; inv Y; simplify; ss.
  i. des. subst.
  generalize (TR tid). intro X. inv X; simplify. destruct b as [st lc].
  exploit sim_trace_last; eauto. i. des. simplify.
  exploit sim_trace_length; eauto. s. i. des.
  hexploit sim_trace_sim_th; eauto; ss. intro L.
  move EID0 at bottom. destruct l; ss. eqvtac.
  exploit L.(WPROP2); eauto. i. des.
  exploit L.(WPROP3); eauto. i. des. subst.
  move DOM at bottom. inv DOM. obtac.

  exploit PF2; eauto. i. des. obtac. labtac. eqvtac.
  destruct x8 as [ftid0 fiid]. destruct x as [ftid fiid1].
  generalize H11. intro Z. inv Z. ss. subst.
  generalize EID2. unfold Execution.label. s. rewrite PRE.(Valid.LABELS), IdMap.map_spec.
  generalize (ATR ftid). generalize (SIM ftid). intros Z W; inv Z; inv W; simplify; ss.
  i. des. subst.
  generalize (TR ftid). intro Z. inv Z; simplify. destruct b as [st0 lc0]. ss.
  symmetry in H20. esplits; try exact H20; eauto; s.
  { unfold v_gen. s. rewrite <- H6. rewrite x4. eauto. }
  { ss. }

  exploit sim_traces_vext_pf; eauto. etrans; eauto.
  exploit sim_trace_last; eauto. i. des. simplify.
  exploit sim_trace_length; eauto. s. i. des.
  hexploit sim_traces_sim_th'; eauto.
  { s. instantiate (1 := length tr'0). lia. }
  all: try rewrite lastn_all; s; eauto; try lia.
  intro TH'.
  eapply TH'.(LC).(PER). econs; eauto.
  econs. split; econs; simtac.
  econs; eauto. apply List.nth_error_Some. ss. rewrite EID3. ss.
Qed.

Lemma sim_traces_persisted
      p trs atrs ws rs fs covs vexts
      m ex smem
      (STEP: Machine.pf_exec p m)
      (PMEM: Machine.persisted m smem)
      (SIM: sim_traces p m.(Machine.mem) trs atrs ws rs fs covs vexts)
      (NOPROMISE: Machine.no_promise m)
      (PRE: Valid.pre_ex p ex)
      (CO: ex.(Execution.co) = co_gen ws)
      (RF: ex.(Execution.rf) = rf_gen ws rs)
      (PF: ex.(Execution.pf) = pf_gen ws fs m.(Machine.mem))
      (INTERNAL: acyclic (Execution.internal ex))
      (CO1: Valid.co1 ex)
      (CO2: Valid.co2 ex)
      (RF1: Valid.rf1 ex)
      (RF2: Valid.rf2 ex)
      (RF_WF: Valid.rf_wf ex)
      (PF1: Valid.pf1 ex)
      (PF2: Valid.pf2 ex)
      (TR: IdMap.Forall2
             (fun _ tr sl => exists l, tr = (ExecUnit.mk (fst sl) (snd sl) m.(Machine.mem)) :: l)
             trs m.(Machine.tpool))
      (ATR: IdMap.Forall2
              (fun _ atr aeu => exists l, atr = aeu :: l)
              atrs (Valid.aeus PRE)):
  Valid.persisted ex smem.
Proof.
  ii. generalize (PMEM loc). intro X. inv X.
  exploit Memory.read_get_msg; eauto. i. des.
  - econs; eauto. i. inversion PEID.
    exploit sim_traces_valid_per; eauto. i. des.
    specialize (LATEST tid sl). eapply LATEST in SL.
    unfold Memory.get_msg in MSG. destruct (v_gen vexts eid); ss. eapply SL; try exact MSG; eauto.
    subst. unfold Time.bot. lia.
  - exploit sim_traces_memory; eauto. i. des.
    generalize (SIM tid). intro X. inv X; simplify.
    generalize (TR tid). intro X. inv X; simplify.
    generalize (ATR tid). intro X. inv X; simplify.
    exploit sim_trace_last; eauto. i. des.
    exploit sim_trace_length; eauto. s. i. des. subst; ss.
    hexploit sim_trace_sim_th; eauto. simplify. intro L.
    exploit L.(WPROP1); eauto. i. des.
    { symmetry in H7. destruct b0 as [st0 lc0]. ss.
      inv NOPROMISE. eapply PROMISES in H7.
      rewrite H7 in x2. rewrite Promises.lookup_bot in x2. ss.
    }
    exploit L.(WPROP3); eauto. i. des. subst.
    assert (SMEID: Execution.label (tid, eid) ex = Some (Label.write ex0 ord loc (smem loc))).
    { unfold Execution.label. s.  rewrite PRE.(Valid.LABELS), IdMap.map_spec, <- H8. ss. }
    econs 2; eauto.
    i. inv PEID. obtac. destruct l; ss. eqvtac. exploit CO1.
    { esplits; [try exact EID0 | try exact SMEID]; eauto. }
    i. des.
    { subst. econs. ss. }
    { econs 2. ss. }
    exfalso.
    exploit sim_traces_vext_co; eauto; try by (subst; ss). i.
    exploit sim_traces_valid_per; eauto with axm. i. des.
    move LATEST at bottom. eapply LATEST in SL.
    unfold Memory.get_msg in MSG. destruct (v_gen vexts eid0); ss.
    eapply SL; try exact MSG; eauto.
    unfold v_gen in *. ss. rewrite <- H6 in *. rewrite <- x7. unfold Time.lt in *. ss.
Qed.

Lemma internal_acyclic
      ex cov
      (INTERNAL: forall eid1 eid2 (INTERNAL: (Execution.internal ex)⁺ eid1 eid2),
          Time.lt (cov eid1) (cov eid2) \/
          (Time.le (cov eid1) (cov eid2) /\
           Execution.po eid1 eid2 /\
           ex.(Execution.label_is) Label.is_read eid1 /\
           ex.(Execution.label_is) Label.is_read eid2) \/
          (Time.le (cov eid1) (cov eid2) /\
           ex.(Execution.label_is) Label.is_write eid1 /\
           ex.(Execution.label_is) Label.is_read eid2)):
  acyclic (Execution.internal ex).
Proof.
  ii. exploit INTERNAL; eauto. i. des.
  - inv x0; lia.
  - inv x1. lia.
  - inv x1. inv x2. rewrite EID in EID0. inv EID0. destruct l0; ss; congr.
Qed.

Lemma promising_pf_valid
      p m smem
      (STEP: Machine.pf_exec p m)
      (PMEM: Machine.persisted m smem):
  exists ex (PRE: Valid.pre_ex p ex) (cov: forall (eid: eidT), Time.t) (vext: forall (eid: eidT), Time.t),
    <<CO1: Valid.co1 ex>> /\
    <<CO2: Valid.co2 ex>> /\
    <<RF1: Valid.rf1 ex>> /\
    <<RF2: Valid.rf2 ex>> /\
    <<RF_WF: Valid.rf_wf ex>> /\
    <<PF1: Valid.pf1 ex>> /\
    <<PF2: Valid.pf2 ex>> /\
    <<INTERNAL:
      forall eid1 eid2
        (INTERNAL: (Execution.internal ex)⁺ eid1 eid2),
        Time.lt (cov eid1) (cov eid2) \/
        (Time.le (cov eid1) (cov eid2) /\
         Execution.po eid1 eid2 /\
         ex.(Execution.label_is) Label.is_read eid1 /\
         ex.(Execution.label_is) Label.is_read eid2) \/
        (Time.le (cov eid1) (cov eid2) /\
         ex.(Execution.label_is) Label.is_write eid1 /\
         ex.(Execution.label_is) Label.is_read eid2)>> /\
    <<EXTERNAL:
      forall eid1 eid2
        (OB: (Execution.ob ex ∩ (ex.(Execution.label_is_rel) Label.is_access_persist))⁺ eid1 eid2),
        Time.lt (vext eid1) (vext eid2) \/
        (Time.le (vext eid1) (vext eid2) /\
         ((Execution.po eid1 eid2 /\
           ex.(Execution.label_is) Label.is_read eid1 /\
           ex.(Execution.label_is) Label.is_read eid2) \/
          (ex.(Execution.label_is) Label.is_write eid1 /\
           ex.(Execution.label_is) Label.is_read eid2) \/
          (ex.(Execution.label_is) Label.is_access eid1 /\
           ex.(Execution.label_is) Label.is_flushopt eid2)))>> /\
    <<ATOMIC: le (ex.(Execution.rmw) ∩ ((Execution.fre ex) ⨾ (Execution.coe ex))) bot>> /\
    <<STATE: IdMap.Forall2
               (fun tid sl aeu => sim_state_weak (fst sl) aeu.(AExecUnit.state))
               m.(Machine.tpool) PRE.(Valid.aeus)>> /\
    <<PMEM: Valid.persisted ex smem>>.
Proof.
  exploit promising_pf_sim_traces; eauto. i. des.
  destruct PRE, ex. ss.
  remember (Execution.mk labels addr data ctrl0 rmw (co_gen ws) (rf_gen ws rs) (pf_gen ws fs m.(Machine.mem))) as ex'.
  replace labels with ex'.(Execution.labels) in LABELS; [|subst; ss].
  replace addr with ex'.(Execution.addr) in ADDR; [|subst; ss].
  replace data with ex'.(Execution.data) in DATA; [|subst; ss].
  replace ctrl0 with ex'.(Execution.ctrl0) in CTRL; [|subst; ss].
  replace rmw with ex'.(Execution.rmw) in RMW; [|subst; ss].
  remember (@Valid.mk_pre_ex p ex' aeus AEUS LABELS ADDR DATA CTRL RMW) as PRE'.
  replace aeus with PRE'.(Valid.aeus) in ATR; [|subst; ss].
  exists ex'. exists PRE'. exists (v_gen covs). exists (v_gen vexts).
  generalize STEP. intro X. inversion X.
  generalize (sim_traces_co1 PRE' SIM ATR). intro CO1.
  generalize (sim_traces_co2 PRE' SIM ATR). intro CO2.
  generalize (sim_traces_rf1 STEP PRE' NOPROMISE SIM TR ATR). intro RF1.
  generalize (sim_traces_rf2 PRE' SIM ATR). intro RF2.
  generalize (sim_traces_rf_wf SIM). intro RF_WF.
  generalize (sim_traces_pf1 STEP PRE' NOPROMISE SIM TR ATR). intro PF1.
  generalize (sim_traces_pf2 STEP PRE' SIM TR ATR). intro PF2.
  replace (co_gen ws) with (ex'.(Execution.co)) in CO1, CO2;[|subst; ss].
  replace (rf_gen ws rs) with (ex'.(Execution.rf)) in RF1, RF2, RF_WF; [|subst; ss].
  replace (pf_gen ws fs m.(Machine.mem)) with (ex'.(Execution.pf)) in PF1, PF2; [|subst; ss].
  hexploit sim_traces_valid_internal; eauto; try by (subst; ss). intro INTERNAL.
  assert (INTERNAL': forall eid1 eid2 (INTERNAL: (Execution.internal ex')⁺ eid1 eid2),
             Time.lt (v_gen covs eid1) (v_gen covs eid2) \/
             (Time.le (v_gen covs eid1) (v_gen covs eid2) /\
              Execution.po eid1 eid2 /\
              ex'.(Execution.label_is) Label.is_read eid1 /\
              ex'.(Execution.label_is) Label.is_read eid2) \/
             (Time.le (v_gen covs eid1) (v_gen covs eid2) /\
              ex'.(Execution.label_is) Label.is_write eid1 /\
              ex'.(Execution.label_is) Label.is_read eid2)).
  { i. induction INTERNAL0.
    + exploit INTERNAL; eauto. i. des; eauto.
      { exploit Valid.internal_rw; eauto. i. des.
        inversion EID1. inversion EID2.
        destruct l0; ss.
        - destruct l; ss.
          + exploit Valid.internal_read_read_po; eauto. i.
            right. left. splits; eauto.
          + right. right. split; eauto.
        - inversion x1. rewrite EID0 in EID3. inversion EID3.
          rewrite H1 in *. destruct l0; ss; congr. }
    + des.
      * left. etrans; eauto.
      * left. eapply le_lt_trans; eauto.
      * left. eapply le_lt_trans; eauto.
      * left. eapply lt_le_trans; eauto.
      * right. left. splits; try etrans; eauto.
      * right. right. splits; try etrans; eauto.
      * left. eapply lt_le_trans; eauto.
      * inversion IHINTERNAL0_6. inversion IHINTERNAL0_0.
        rewrite EID in EID0. inversion EID0. rewrite H0 in *.
        destruct l0; ss; congr.
      * inversion IHINTERNAL0_5. inversion IHINTERNAL0_0.
        rewrite EID in EID0. inversion EID0. rewrite H0 in *.
        destruct l0; ss; congr. }
  generalize (internal_acyclic _ INTERNAL'). intro ACYCLIC.
  exploit sim_traces_valid_external_atomic; eauto; try by (subst; ss). i. des.
  esplits; eauto.
  - clear INTERNAL'. i. induction OB.
    + inversion H. inversion H1.
      exploit EXTERNAL; eauto. i. des; eauto; cycle 1.
      { right. exploit Valid.ob_persist_spec; eauto. i. des. eauto. }
      right. splits; eauto.
      inversion x1. destruct l; ss.
      destruct (Label.is_flushopt l1) eqn:LAB.
      { exploit Valid.persist_ob_write; eauto with axm. intro WR. inversion WR.
        destruct l; ss; congr.
      }
      destruct l1; ss; [left|right]; splits; eauto with axm.
      eapply Valid.ob_read_read_po; eauto with axm.
    + des.
      all: try by left; eapply le_lt_trans; eauto.
      all: try by left; eapply lt_le_trans; eauto.
      all: try by right; split; try etrans; eauto.
      * left. etrans; eauto.
      * right. split; try etrans; eauto.
        left. simtac. rewrite <- IHOB0. ss.
      * inversion IHOB3. inversion IHOB6.
        rewrite EID in EID0. inversion EID0. rewrite H0 in *. destruct l0; ss.
      * inversion IHOB0. inversion IHOB6.
        rewrite EID in EID0. inversion EID0. rewrite H0 in *. destruct l0; ss.
      * inversion IHOB0. inversion IHOB5.
        rewrite EID in EID0. inversion EID0. rewrite H0 in *. destruct l0; ss.
      * right. split; try etrans; eauto.
        right. right. inversion IHOB5. split; simtac.
      * right. split; try etrans; eauto.
        right. right. inversion IHOB4. split; simtac.
  - clear - SIM TR ATR.
    ii. generalize (SIM id). i. inv H; ss.
    + generalize (TR id). i. inv H; try congr.
      generalize (ATR id). i. inv H; try congr.
      econs.
    + generalize (TR id). i. inv H; try congr.
      generalize (ATR id). i. inv H; try congr.
      des. simplify. inv REL7; auto.
      { econs. unfold Machine.init_with_promises in *. ss.
        rewrite IdMap.mapi_spec in *. rewrite STMT in FIND. ss.
        symmetry in FIND. inv FIND. rewrite H0.
        apply sim_state_weak_init. }
  - (* PMEM *)
    hexploit sim_traces_persisted; eauto; try by (subst; ss).
Qed.

Theorem promising_pf_to_axiomatic
        p m smem
        (STEP: Machine.pf_exec p m)
        (PMEM: Machine.persisted m smem):
  exists ex (EX: Valid.ex p ex),
    <<TERMINAL: Machine.is_terminal m -> Valid.is_terminal EX>> /\
    <<STATE: IdMap.Forall2
               (fun tid sl aeu => sim_state_weak (fst sl) aeu.(AExecUnit.state))
               m.(Machine.tpool) EX.(Valid.aeus)>> /\
    <<PMEM: Valid.persisted ex smem>>.
Proof.
  exploit promising_pf_valid; eauto. i. des.
  exists ex. eexists (Valid.mk_ex PRE CO1 CO2 RF1 RF2 RF_WF PF1 PF2 _ _ ATOMIC).
  s. esplits; eauto.
  ii. inv H. specialize (STATE tid). inv STATE; try congr.
  rewrite FIND in H. inv H. destruct a. destruct aeu. ss.
  exploit TERMINAL; eauto. i. des. inv REL. inv x. congr.
Grab Existential Variables.
{ (* external *)
  ii. exploit Valid.ob_cycle; eauto. i. des. rename x1 into NONBARRIER.
  clear - EXTERNAL NONBARRIER.
  exploit EXTERNAL; eauto. i. des.
  - inv x; lia.
  - inv x0. lia.
  - obtac. destruct l; destruct l0; ss; congr.
  - obtac. destruct l; destruct l0; ss; congr.
}
{ (* internal *)
  clear - INTERNAL.
  eapply internal_acyclic. auto.
}
Qed.

Theorem promising_to_axiomatic
        p m smem
        (STEP: Machine.exec p m)
        (PMEM: Machine.persisted m smem):
  exists ex (EX: Valid.ex p ex),
    <<TERMINAL: Machine.is_terminal m -> Valid.is_terminal EX>> /\
    <<STATE: IdMap.Forall2
               (fun tid sl aeu => sim_state_weak (fst sl) aeu.(AExecUnit.state))
               m.(Machine.tpool) EX.(Valid.aeus)>> /\
    <<PMEM: Valid.persisted ex smem>>.
Proof.
  apply promising_to_promising_pf in STEP.
  apply promising_pf_to_axiomatic; auto.
Qed.
