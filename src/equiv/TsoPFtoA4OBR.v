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
Require Import PromisingArch.promising.TsoPromising.
Require Import PromisingArch.promising.CommonPromising.
Require Import PromisingArch.promising.TsoStateExecFacts.
Require Import PromisingArch.axiomatic.TsoAxiomatic.
Require Import PromisingArch.axiomatic.TsoSimLocal.
Require Import PromisingArch.equiv.TsoPFtoA1.
Require Import PromisingArch.equiv.TsoPFtoA2.
Require Import PromisingArch.equiv.TsoPFtoA3.

Set Implicit Arguments.


Lemma sim_traces_sim_th'_ob_read
      p trs atrs ws rs covs vexts
      m ex
      (STEP: Machine.pf_exec p m)
      (SIM: sim_traces p m.(Machine.mem) trs atrs ws rs covs vexts)
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
  forall tid tr atr wl rl covl vextl
    n eu1 eu2 tr' aeu1 aeu2 atr' w1 w2 wl' r1 r2 rl' cov1 cov2 covl' vext1 vext2 vextl'
    (FIND_TR: IdMap.find tid trs = Some tr)
    (FIND_ATR: IdMap.find tid atrs = Some atr)
    (FIND_WL: IdMap.find tid ws = Some wl)
    (FIND_RL: IdMap.find tid rs = Some rl)
    (FIND_COVL: IdMap.find tid covs = Some covl)
    (FIND_VEXTL: IdMap.find tid vexts = Some vextl)
    (EU: lastn (S n) tr = eu2 :: eu1 :: tr')
    (AEU: lastn (S n) atr = aeu2 :: aeu1 :: atr')
    (WL: lastn (S n) wl = w2 :: w1 :: wl')
    (RL: lastn (S n) rl = r2 :: r1 :: rl')
    (COV: lastn (S n) covl = cov2 :: cov1 :: covl')
    (VEXT: lastn (S n) vextl = vext2 :: vext1 :: vextl')
    (SIM_TH': sim_th' tid m.(Machine.mem) ex (v_gen vexts) eu1 aeu1),
    sim_ob_read tid ex (v_gen vexts) eu2 aeu2.
Proof.
  i. rename SIM_TH' into L.
  generalize (SIM tid). intro X. inv X; simplify.
  destruct n.
  { generalize (lastn_length 1 tr). rewrite EU. destruct tr; ss. }
  exploit sim_trace_lastn; eauto. instantiate (1 := S n). intro SIMTR.
  generalize (TR tid). intro TR_TID. inv TR_TID; try congr.
  destruct b as [st_l lc_l]. destruct REL as [trt].
  rename H into PFSL. rename H1 into TRL.
  rewrite FIND_TR in H0. inversion H0. rewrite H1 in *. cleartriv. clear H1.
  exploit sim_trace_rtc_step; try exact REL6; eauto. intro RTC_STEP.
  hexploit sim_traces_ex; eauto. intro EX2.
  inversion SIMTR; subst; simplify; [congr|].
  repeat match goal with
         | [H1: lastn ?a ?b = ?c, H2: ?d = lastn ?a ?b |- _] =>
           rewrite H1 in H2; inv H2
         end.
  exploit sim_trace_sim_state_weak; eauto. intro STATE1.

  ii.
  destruct (le_lt_dec (length (ALocal.labels (AExecUnit.local aeu1))) eid2); cycle 1.
  { eapply L; eauto. }
  inv EID2.
  destruct eu1 as [st1 lc1 mem1] eqn: EU1. guardH EU1.
  destruct eu2 as [st2 lc2 mem2] eqn: EU2. guardH EU2.
  destruct aeu1 as [ast1 alc1].
  destruct aeu2 as [ast2 alc2].
  inv ASTATE_STEP; inv EVENT; inv ALOCAL_STEP; inv EVENT; repeat (ss; subst).
  all: try (clear - LABEL l; lia).
  all: rewrite List.app_length in LABEL; ss.
  all: assert (EID2: eid2 = length (ALocal.labels alc1)) by (clear - LABEL l; lia); subst.
  all: exploit LABELS; eauto; ss.
  all: try by clear; rewrite List.app_length; s; lia.
  all: destruct l0; ss.
  all: intro NTH; apply nth_error_snoc_inv_last in NTH; inv NTH.
  all: rewrite EU, AEU, WL, RL, COV, VEXT in SIMTR.
  { (* read *)
    exploit sim_trace_sim_th; try exact SIMTR; eauto. intro TH_tmp.
    exploit lastn_sub_S1; try exact EU; eauto. intro TRT. des.
    exploit TH_tmp; eauto.
    clear TH_tmp. intro L'.
    exploit L'.(RPROP1); ss.
    { split; eauto with tso. apply nth_error_last. apply Nat.eqb_eq. ss. }
    unfold ALocal.next_eid in *. condtac; cycle 1.
    { apply Nat.eqb_neq in X. congr. }
    i. des. inv x0.
    exploit L'.(RPROP2); eauto.
    { rewrite X. eauto. }
    s. rewrite X. i. des; cycle 1.
    { apply nth_error_snoc_inv_last in x2. inv x2. inv x4. }
    apply nth_error_snoc_inv_last in x2. inv x2.
    rewrite EX2.(XVEXT); s; cycle 1.
    { rewrite List.app_length. s. clear. lia. }
    rewrite X.
    inv STEP0. ss. subst. inv LOCAL; inv EVENT; cycle 1.
    { inv STATE0. inv STATE1. ss. }
    exploit sim_trace_sim_th; try exact TRACE; eauto. intro TH_tmp.
    exploit TH_tmp; eauto.
    { instantiate (1 := l1 ++ [eu2]). rewrite <- List.app_assoc. rewrite EU2. ss. }
    clear TH_tmp. intro SIM_TH.
    destruct SIM_TH.(EU_WF).
    specialize (Local.read_spec LOCAL STEP0). intro READ_SPEC. guardH READ_SPEC.
    clear LOCAL. inv STEP0. ss.
    exploit EX2.(LABELS); eauto; ss.
    { rewrite List.app_length. s. clear. lia. }
    i.
    move AOB at bottom. unfold ob' in AOB. des_union.
    - (* rfe *)
      rename H1 into H.
      assert (v_gen vexts eid1 = ts).
      { inv H. destruct eid1 as [tid1 eid1]. inv H2. ss.
        generalize H1. intro Y. rewrite RF in Y. inv Y. ss.
        erewrite EX2.(XR) in R; eauto; cycle 1.
        { s. rewrite List.app_length. s. clear. lia. }
        destruct (length (ALocal.labels alc1) =? length (ALocal.labels alc1)); ss.
        move READ_SPEC at bottom. rewrite fun_add_spec in *.
        destruct (equiv_dec (ValA.val vloc) (ValA.val vloc)); cycle 1.
        { exfalso. apply c. ss. }
        generalize SIM_TH.(MEM). s. i. subst.
        unguardH READ_SPEC. des. rewrite <- COH0 in R. inv R.
        generalize (SIM tid1). intro SIM1. inv SIM1; simplify.
        exploit sim_trace_last; try exact REL0. i. des. simplify.
        exploit sim_trace_sim_th; try exact REL0; eauto. intro TH_tmp.
        exploit TH_tmp; eauto.
        { instantiate (1 := []). ss. }
        clear TH_tmp. intro L1.
        exploit L1.(WPROP3); eauto. i. des.
        unfold v_gen. ss. rewrite <- H7. auto.
      }
      subst.
      unfold FwdItem.read_view. condtac; ss; [|apply join_r].
      clear X0. inv e.
      generalize (L.(LC).(FWDBANK) (ValA.val vloc)). s. i. des; cycle 1.
      { rewrite H1. ss. apply bot_spec. }
      rewrite <- TS in H2.
      destruct eid as [tid2 eid2], eid1 as [tid1 eid1].
      assert (tid1 = tid2).
      { inv H. exploit RF2; eauto. i. des.
        inv WRITE0. rename EID0 into WRITE0.
        unfold Execution.label in WRITE0. ss.
        rewrite PRE.(Valid.LABELS) in WRITE0.
        rewrite IdMap.map_spec in WRITE0.
        destruct (IdMap.find tid1 (Valid.aeus PRE)) eqn:FIND1; ss.
        generalize (ATR tid1). intro ATR1. inv ATR1; try congr. des. simplify.
        generalize (SIM tid1). intro SIM1. inv SIM1; simplify.
        exploit sim_trace_last; try exact REL0. i. des. simplify.
        exploit sim_trace_sim_th; try exact REL0; eauto. intro TH_tmp.
        exploit TH_tmp; eauto.
        { instantiate (1 := []). ss. }
        clear TH_tmp. intro L1.
        inv WRITE. inv WRITE1.
        unfold Execution.label in EID0. ss.
        rewrite PRE.(Valid.LABELS) in EID0.
        rewrite IdMap.map_spec in EID0.
        destruct (IdMap.find tid2 (Valid.aeus PRE)) eqn:FIND2; ss.
        generalize (ATR tid2). intro ATR2. inv ATR2; try congr. des. simplify.
        generalize (SIM tid2). intro SIM2. inv SIM2; simplify.
        exploit sim_trace_last; try exact REL1. i. des. simplify.
        exploit sim_trace_sim_th; try exact REL1; eauto. intro TH_tmp.
        exploit TH_tmp; eauto.
        { instantiate (1 := []). ss. }
        clear TH_tmp. intro L2.
        move H2 at bottom.
        unfold v_gen in H2. ss.
        rewrite <- H10, <- H16 in H2.
        exploit L1.(WPROP2); eauto. i. des.
        exploit L2.(WPROP2'); eauto. i. des.
        exploit L1.(WPROP3); eauto. i. des.
        exploit L2.(WPROP3); eauto. i. des.
        rewrite x10, x17 in H2. inv H2.
        rewrite H in x21. rewrite x14 in x21. inv x21. ss.
      }
      subst.
      inv WRITE. inv PO. ss. subst. inv H. inv H3. ss.
    - (* dob *)
      rename H1 into H.
      unfold Execution.dob in H. rewrite ? seq_assoc in *. des_union.
      + inv H1. des. inv H. des. inv H1.
        rewrite L.(LC).(VRN); ss.
        * repeat rewrite <- join_l. ss.
        * econs; eauto. unfold sim_local_vrn. left. econs; eauto.
      + inv H1. des. inv H. des. inv H1.
        inv H4. destruct l0; ss; congr.
    - (* bob *)
      unfold Execution.bob in H. rewrite ? seq_assoc in *. des_union.
      rewrite L.(LC).(VRN); ss.
      + repeat rewrite <- join_l. ss.
      + econs; eauto. unfold sim_local_vrn. right.
        rewrite ? seq_assoc. inv H. des. inv H2. ss.
  }
  { (* update *)
    exploit sim_trace_sim_th; try exact SIMTR; eauto. intro TH_tmp.
    exploit lastn_sub_S1; try exact EU; eauto. intro TRT. des.
    exploit TH_tmp; eauto.
    clear TH_tmp. intro L'.
    exploit L'.(RPROP1); ss.
    { split.
      - apply nth_error_last. apply Nat.eqb_eq. ss.
      - eauto with tso.
    }
    unfold ALocal.next_eid in *. condtac; cycle 1.
    { apply Nat.eqb_neq in X. congr. }
    i. des. inv x0.
    exploit L'.(RPROP2); eauto.
    { rewrite X. eauto. }
    s. rewrite X. i. des.
    { apply nth_error_snoc_inv_last in x2. inv x2. ss. }
    apply nth_error_snoc_inv_last in x2. inv x2.
    rewrite EX2.(XVEXT); s; cycle 1.
    { rewrite List.app_length. s. clear. lia. }
    rewrite X.
    inversion STEP0. inv LOCAL; ss. subst. inv EVENT.
    {
      exploit sim_trace_sim_th; try exact TRACE; eauto. intro TH_tmp.
      exploit TH_tmp; eauto.
      { instantiate (1 := l1 ++ [eu2]). rewrite <- List.app_assoc. rewrite EU2. ss. }
      clear TH_tmp. intro SIM_TH.
      destruct SIM_TH.(EU_WF).
      inversion STEP1. guardH LC2. ss.
      exploit EX2.(LABELS); eauto; ss.
      { rewrite List.app_length. s. clear. lia. }
      i.
      move AOB at bottom. unfold ob' in AOB. des_union.
      - (* rfe *)
        rename H1 into H.
        assert (v_gen vexts eid1 = old_ts).
        { inv H. destruct eid1 as [tid1 eid1]. inv H2. ss.
          generalize H1. intro Y. rewrite RF in Y. inv Y. ss.
          erewrite EX2.(XR) in R; eauto; cycle 1.
          { s. rewrite List.app_length. s. clear. lia. }
          destruct (length (ALocal.labels alc1) =? length (ALocal.labels alc1)); ss.
          generalize SIM_TH.(MEM). s. i. subst. ss.
          assert (old_ts = Memory.latest_ts (ValA.val vloc) (Init.Nat.pred ts) (Machine.mem m)).
          { replace (Machine.mem m) with (ExecUnit.mem eu1); cycle 1.
            { rewrite EU1. ss. }
            eapply ExecUnit.no_promise_rmw_spec; try exact RTC_STEP; try rewrite EU1; eauto.
            inv STEP. inv NOPROMISE. generalize PFSL. intro PROMBOT.
            symmetry in PROMBOT. eapply PROMISES in PROMBOT. ss.
          }
          i. subst. inv R.
          generalize (SIM tid1). intro SIM1. inv SIM1; simplify.
          exploit sim_trace_last; try exact REL0. i. des. simplify.
          exploit sim_trace_sim_th; try exact REL0; eauto. intro TH_tmp.
          exploit TH_tmp; eauto.
          { instantiate (1 := []). ss. }
          clear TH_tmp. intro L1.
          exploit L1.(WPROP3); eauto. i. des.
          unfold v_gen. ss. rewrite <- H7. rewrite x7.
          clear - LC2. unguardH LC2. inv LC2. ss.
          rewrite fun_add_spec. destruct (equiv_dec (ValA.val vloc) (ValA.val vloc)); auto.
          exfalso. apply c. ss.
        }
        subst.
        unguardH LC2. inv LC2. ss.
        rewrite fun_add_spec. condtac; ss; cycle 1.
        { exfalso. apply c. ss. }
        unfold Time.le. lia.
      - (* dob *)
        unguardH LC2. inv LC2. ss.
        unfold Execution.dob in H1. rewrite ? seq_assoc in *. des_union.
        + inv H. des. inv H1. des. inv H2. inv H. inv H3.
          rewrite L.(LC).(VWN); ss.
          * rewrite fun_add_spec. condtac; ss; cycle 1.
            { exfalso. apply c. ss. }
            inv WRITABLE. unfold Time.le. lia.
          * econs; eauto. unfold sim_local_vwn. econs. econs; eauto. econs; eauto with tso.
        + inv H. des. inv H1. des. inv H2.
          rewrite L.(LC).(VWN); ss.
          * rewrite fun_add_spec. condtac; ss; cycle 1.
            { exfalso. apply c. ss. }
            inv WRITABLE. unfold Time.le. lia.
          * econs; eauto. unfold sim_local_vwn.
            inv H. inv H3.
            econs. econs; eauto. econs; eauto with tso.
      - (* bob *)
        unguardH LC2. inv LC2. ss.
        unfold Execution.bob in H. rewrite ? seq_assoc in *. des_union.
        rewrite L.(LC).(VWN); ss.
        * rewrite fun_add_spec. condtac; ss; cycle 1.
          { exfalso. apply c. ss. }
          inv WRITABLE. unfold Time.le. lia.
        * econs; eauto. unfold sim_local_vwn.
          inv H. inv H1. inv H. inv H1. inv H. des. inv H1. des. inv H2. inv H4. inv H.
          exploit Execution.po_chain.
          { econs. split; try exact H1. econs 2. eauto. }
          intro PO. inv H4.
          econs. econs; eauto. econs; eauto with tso.
    }
  }
  { (* rmw_failure *)
    exploit sim_trace_sim_th; try exact SIMTR; eauto. intro TH_tmp.
    exploit lastn_sub_S1; try exact EU; eauto. intro TRT. des.
    exploit TH_tmp; eauto.
    clear TH_tmp. intro L'.
    exploit L'.(RPROP1); ss.
    { split; eauto with tso. apply nth_error_last. apply Nat.eqb_eq. ss. }
    unfold ALocal.next_eid in *. condtac; cycle 1.
    { apply Nat.eqb_neq in X. congr. }
    i. des. inv x0.
    exploit L'.(RPROP2); eauto.
    { rewrite X. eauto. }
    s. rewrite X. i. des; cycle 1.
    { apply nth_error_snoc_inv_last in x2. inv x2. inv x4. }
    apply nth_error_snoc_inv_last in x2. inv x2.
    rewrite EX2.(XVEXT); s; cycle 1.
    { rewrite List.app_length. s. clear. lia. }
    rewrite X.
    inv STEP0. ss. subst. inv LOCAL; inv EVENT.
    { inv STATE0. inv STATE1. ss. }
    exploit sim_trace_sim_th; try exact TRACE; eauto. intro TH_tmp.
    exploit TH_tmp; eauto.
    { instantiate (1 := l1 ++ [eu2]). rewrite <- List.app_assoc. rewrite EU2. ss. }
    clear TH_tmp. intro SIM_TH.
    destruct SIM_TH.(EU_WF).
    specialize (Local.rmw_failure_spec LOCAL STEP0). intro RMW_FAILURE_SPEC. guardH RMW_FAILURE_SPEC.
    clear LOCAL. inv STEP0. ss.
    exploit EX2.(LABELS); eauto; ss.
    { rewrite List.app_length. s. clear. lia. }
    i.
    move AOB at bottom. unfold ob' in AOB. des_union.
    - (* rfe *)
      rename H1 into H.
      assert (v_gen vexts eid1 = old_ts).
      { inv H. destruct eid1 as [tid1 eid1]. inv H2. ss.
        generalize H1. intro Y. rewrite RF in Y. inv Y. ss.
        erewrite EX2.(XR) in R; eauto; cycle 1.
        { s. rewrite List.app_length. s. clear. lia. }
        destruct (length (ALocal.labels alc1) =? length (ALocal.labels alc1)); ss.
        move RMW_FAILURE_SPEC at bottom. rewrite fun_add_spec in *.
        destruct (equiv_dec (ValA.val vloc) (ValA.val vloc)); cycle 1.
        { exfalso. apply c. ss. }
        generalize SIM_TH.(MEM). s. i. subst.
        unguardH RMW_FAILURE_SPEC. des. rewrite <- COH0 in R. inv R.
        generalize (SIM tid1). intro SIM1. inv SIM1; simplify.
        exploit sim_trace_last; try exact REL0. i. des. simplify.
        exploit sim_trace_sim_th; try exact REL0; eauto. intro TH_tmp.
        exploit TH_tmp; eauto.
        { instantiate (1 := []). ss. }
        clear TH_tmp. intro L1.
        exploit L1.(WPROP3); eauto. i. des.
        unfold v_gen. ss. rewrite <- H7. auto.
      }
      subst.
      unfold FwdItem.read_view. condtac; ss; [| apply join_r].
      clear X0. inv e.
      generalize (L.(LC).(FWDBANK) (ValA.val vloc)). s. i. des; cycle 1.
      { rewrite H1. ss. apply bot_spec. }
      rewrite <- TS in H2.
      destruct eid as [tid2 eid2], eid1 as [tid1 eid1].
      assert (tid1 = tid2).
      { inv H. exploit RF2; eauto. i. des.
        inv WRITE0. rename EID0 into WRITE0.
        unfold Execution.label in WRITE0. ss.
        rewrite PRE.(Valid.LABELS) in WRITE0.
        rewrite IdMap.map_spec in WRITE0.
        destruct (IdMap.find tid1 (Valid.aeus PRE)) eqn:FIND1; ss.
        generalize (ATR tid1). intro ATR1. inv ATR1; try congr. des. simplify.
        generalize (SIM tid1). intro SIM1. inv SIM1; simplify.
        exploit sim_trace_last; try exact REL0. i. des. simplify.
        exploit sim_trace_sim_th; try exact REL0; eauto. intro TH_tmp.
        exploit TH_tmp; eauto.
        { instantiate (1 := []). ss. }
        clear TH_tmp. intro L1.
        inv WRITE. inv WRITE1.
        unfold Execution.label in EID0. ss.
        rewrite PRE.(Valid.LABELS) in EID0.
        rewrite IdMap.map_spec in EID0.
        destruct (IdMap.find tid2 (Valid.aeus PRE)) eqn:FIND2; ss.
        generalize (ATR tid2). intro ATR2. inv ATR2; try congr. des. simplify.
        generalize (SIM tid2). intro SIM2. inv SIM2; simplify.
        exploit sim_trace_last; try exact REL1. i. des. simplify.
        exploit sim_trace_sim_th; try exact REL01; eauto. intro TH_tmp.
        exploit TH_tmp; eauto.
        { instantiate (1 := []). ss. }
        clear TH_tmp. intro L2.
        move H2 at bottom.
        unfold v_gen in H2. ss.
        rewrite <- H10, <- H16 in H2.
        exploit L1.(WPROP2); eauto. i. des.
        exploit L2.(WPROP2'); eauto. i. des.
        exploit L1.(WPROP3); eauto. i. des.
        exploit L2.(WPROP3); eauto. i. des.
        rewrite x10, x17 in H2. inv H2.
        rewrite H in x21. rewrite x14 in x21. inv x21. ss.
      }
      subst.
      inv WRITE. inv PO. ss. subst. inv H. inv H3. ss.
    - (* dob *)
      rename H1 into H.
      unfold Execution.dob in H. rewrite ? seq_assoc in *. des_union.
      + inv H1. des. inv H. des. inv H1.
        rewrite L.(LC).(VRN); ss.
        * repeat rewrite <- join_l. ss.
        * econs; eauto. unfold sim_local_vrn. left. econs; eauto.
      + inv H1. des. inv H. des. inv H1.
        inv H4. destruct l0; ss; congr.
    - (* bob *)
      unfold Execution.bob in H. rewrite ? seq_assoc in *. des_union.
      rewrite L.(LC).(VRN); ss.
      + repeat rewrite <- join_l. ss.
      + econs; eauto. unfold sim_local_vrn. right.
        rewrite ? seq_assoc. inv H. des. inv H2. ss.
  }
Qed.
