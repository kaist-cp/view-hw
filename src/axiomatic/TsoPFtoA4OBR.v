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
Require Import PromisingArch.promising.TsoPromising2.
Require Import PromisingArch.promising.CommonPromising.
Require Import PromisingArch.promising.TsoStateExecFacts.
Require Import PromisingArch.axiomatic.TsoAxiomatic.
Require Import PromisingArch.axiomatic.TsoCommonAxiomatic.
Require Import PromisingArch.axiomatic.TsoPFtoA1.
Require Import PromisingArch.axiomatic.TsoPFtoA2.
Require Import PromisingArch.axiomatic.TsoPFtoA3.

Set Implicit Arguments.


Lemma sim_traces_sim_th'_ob_read
      p trs atrs ws rs covs vexts
      m ex
      (STEP: Machine.pf_exec p m)
      (SIM: sim_traces p m.(Machine.mem) trs atrs ws rs covs vexts)
      (PRE: Valid.pre_ex p ex)
      (CO: ex.(Execution.co) = co_gen ws)
      (RF: ex.(Execution.rf) = rf_gen ws rs)
      (* (INTERNAL: acyclic (Execution.internal ex)) *)
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
  exploit rtc_step_sim_trace; [exact REL6 | exact SIMTR| | |]; eauto. intro RTC_STEP.
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
  destruct eu1 as [st1 lc1 mem1].
  destruct eu2 as [st2 lc2 mem2].
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
  { (* read *)
    rewrite EU, AEU, WL, RL, COV, VEXT in SIMTR.
    exploit sim_trace_sim_th; try exact SIMTR; eauto. intro L'.
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
    inv STEP0. ss. subst. inv LOCAL0; inv EVENT.
    { (* read *)
      exploit sim_trace_sim_th; try exact TRACE; eauto. intro SIM_TH.
      destruct SIM_TH.(EU_WF).
      specialize (Local.read_spec LOCAL0 STEP0). intro READ_SPEC. guardH READ_SPEC.
      clear LOCAL0. inv STEP0. ss.
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
          exploit sim_trace_sim_th; try exact REL0; eauto. intro L1.
          exploit L1.(WPROP3); eauto. i. des.
          unfold v_gen. ss. rewrite <- H7. auto.
        }
        subst.
        repeat rewrite <- join_r. unfold FwdItem.read_view. condtac; ss. clear X0. inv e.
        generalize (L.(LC).(FWDBANK) (ValA.val vloc)). s. i. des.
        + rewrite <- TS in H2.
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
            exploit sim_trace_sim_th; try exact REL0; eauto. intro L1.
            inv WRITE. inv WRITE1.
            unfold Execution.label in EID0. ss.
            rewrite PRE.(Valid.LABELS) in EID0.
            rewrite IdMap.map_spec in EID0.
            destruct (IdMap.find tid2 (Valid.aeus PRE)) eqn:FIND2; ss.
            generalize (ATR tid2). intro ATR2. inv ATR2; try congr. des. simplify.
            generalize (SIM tid2). intro SIM2. inv SIM2; simplify.
            exploit sim_trace_last; try exact REL1. i. des. simplify.
            exploit sim_trace_sim_th; try exact REL1; eauto. intro L2.
            move H2 at bottom.
            unfold v_gen in H2. ss.
            rewrite <- H10, <- H16 in H2.
            exploit L1.(WPROP2); eauto. i. des.
            exploit L2.(WPROP2'); eauto. i. des.
            exploit L1.(WPROP3); eauto. i. des.
            exploit L2.(WPROP3); eauto. i. des.
            rewrite x11, x18 in H2. inv H2.
            rewrite H in x22. rewrite x15 in x22. inv x22. ss. }
          subst.
          inv WRITE. inv PO. ss. subst. inv H. inv H3. ss.
        + rewrite H1. refl.
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
    { (* rmw_failure *)
      exploit sim_trace_sim_th; try exact TRACE; eauto. intro SIM_TH.
      destruct SIM_TH.(EU_WF).
      specialize (Local.rmw_failure_spec LOCAL0 STEP0). intro RMW_FAILURE_SPEC. guardH RMW_FAILURE_SPEC.
      clear LOCAL0. inv STEP0. ss.
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
          exploit sim_trace_sim_th; try exact REL0; eauto. intro L1.
          exploit L1.(WPROP3); eauto. i. des.
          unfold v_gen. ss. rewrite <- H7. auto.
        }
        subst.
        repeat rewrite <- join_r. ss. unfold FwdItem.read_view. condtac; ss. clear X0. inv e.
        generalize (L.(LC).(FWDBANK) (ValA.val vloc)). s. i. des.
        + rewrite <- TS in H2.
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
            exploit sim_trace_sim_th; try exact REL0; eauto. intro L1.
            inv WRITE. inv WRITE1.
            unfold Execution.label in EID0. ss.
            rewrite PRE.(Valid.LABELS) in EID0.
            rewrite IdMap.map_spec in EID0.
            destruct (IdMap.find tid2 (Valid.aeus PRE)) eqn:FIND2; ss.
            generalize (ATR tid2). intro ATR2. inv ATR2; try congr. des. simplify.
            generalize (SIM tid2). intro SIM2. inv SIM2; simplify.
            exploit sim_trace_last; try exact REL1. i. des. simplify.
            exploit sim_trace_sim_th; try exact REL1; eauto. intro L2.
            move H2 at bottom.
            unfold v_gen in H2. ss.
            rewrite <- H10, <- H16 in H2.
            exploit L1.(WPROP2); eauto. i. des.
            exploit L2.(WPROP2'); eauto. i. des.
            exploit L1.(WPROP3); eauto. i. des.
            exploit L2.(WPROP3); eauto. i. des.
            rewrite x11, x18 in H2. inv H2.
            rewrite H in x22. rewrite x15 in x22. inv x22. ss. }
          subst.
          inv WRITE. inv PO. ss. subst. inv H. inv H3. ss.
        + rewrite H1. refl.
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
  }
  { (* update *)
    rewrite EU, AEU, WL, RL, COV, VEXT in SIMTR.
    exploit sim_trace_sim_th; try exact SIMTR; eauto. intro L'.
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
    { apply nth_error_snoc_inv_last in x2. inv x2.
      exfalso. apply x4. eauto with tso.
    }
    apply nth_error_snoc_inv_last in x2. inv x2.
    rewrite EX2.(XVEXT); s; cycle 1.
    { rewrite List.app_length. s. clear. lia. }
    rewrite X.
    inversion STEP0. inv LOCAL0; ss. subst. inv EVENT.
    {
      exploit sim_trace_sim_th; try exact TRACE; eauto. intro SIM_TH.
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
          { eapply le_antisym; ss.
            - eapply Memory.latest_ts_read_le; eauto. lia.
            - eapply Memory.latest_latest_ts. ii.
              unfold Memory.exclusive in EX. unfold Memory.no_msgs in EX.
              exploit EX; eauto.
              { etrans; eauto. lia. }
              esplits; eauto. destruct msg as [ts' val' tidtmp']. destruct (tidtmp' == tid); ss. inv e.
              unfold Memory.latest in COH. unfold Memory.no_msgs in COH.
              exploit COH; eauto.
              destruct (lt_eq_lt_dec (S ts0) (View.ts (Local.coh lc1 (ValA.val vloc)))). inv s; try lia.
              inv LOCAL0. exploit PROMISES0; [| | instantiate (1 := S ts0)|]; eauto. intro PROMISE_TS.
              assert (PROMISE_TS0: Promises.lookup (S ts0) (Local.promises lc2)).
              { rewrite LC2. ss. exploit Promises.unset_o. intro UNSET. rewrite UNSET. condtac; ss. inversion e. lia. }
              move PFSL at bottom.
              inv STEP. inv NOPROMISE. generalize PFSL. intro PROMBOT. symmetry in PROMBOT. eapply PROMISES1 in PROMBOT.
              move RTC_STEP at bottom.
              exploit ExecUnit.rtc_state_step_promise_remained.
              2: exact RTC_STEP.
              4: exact PROMISE_TS0.
              { eapply ExecUnit.state_step0_wf; eauto. econs. ss. }
              { instantiate (1 := ValA.val vloc). rewrite LC2. ss.
                rewrite fun_add_spec. condtac; cycle 1.
                { exfalso. apply c. ss. }
                etrans; eauto. ss. lia.
              }
              { unfold Memory.get_msg. ss. rewrite MSG0. ss. }
              unfold Promises.lookup. ss. rewrite PROMBOT. ss.
          }
          subst. inv R.
          generalize (SIM tid1). intro SIM1. inv SIM1; simplify.
          exploit sim_trace_last; try exact REL0. i. des. simplify.
          exploit sim_trace_sim_th; try exact REL0; eauto. intro L1.
          exploit L1.(WPROP3); eauto. i. des.
          unfold v_gen. ss. rewrite <- H7. rewrite x7.
          clear - LC2. unguardH LC2. inv LC2. ss.
          rewrite fun_add_spec. destruct (equiv_dec (ValA.val vloc) (ValA.val vloc)); auto.
          exfalso. apply c. ss.
        }
        subst.
        rewrite fun_add_spec. condtac; ss; cycle 1.
        { exfalso. apply c. ss. }
        unfold Time.le. lia.
      - (* dob *)
        rename H1 into H.
        unfold Execution.dob in H. rewrite ? seq_assoc in *. des_union.
        + inv H1. des. inv H. des. inv H1.
          rewrite L.(LC).(VWN); ss.
          * rewrite fun_add_spec. condtac; ss; cycle 1.
            { exfalso. apply c. ss. }
            inv WRITABLE. unfold Time.le. lia.
          * econs; eauto. unfold sim_local_vwn. left. econs; eauto.
        + inv H1. des. inv H. des. inv H1.
          rewrite L.(LC).(VWN); ss.
          * rewrite fun_add_spec. condtac; ss; cycle 1.
            { exfalso. apply c. ss. }
            inv WRITABLE. unfold Time.le. lia.
          * econs; eauto. unfold sim_local_vwn.
            inv H2. inv H1. destruct l0; ss.
            -- left. econs. split; eauto. econs; eauto with tso.
            -- right. econs. split; eauto. econs; eauto with tso.
            -- right. econs. split; eauto. econs; eauto with tso.
      - (* bob *)
        unfold Execution.bob in H. rewrite ? seq_assoc in *. des_union.
        rewrite L.(LC).(VWN); ss.
        * rewrite fun_add_spec. condtac; ss; cycle 1.
            { exfalso. apply c. ss. }
            inv WRITABLE. unfold Time.le. lia.
          * econs; eauto. unfold sim_local_vwn.
            inv H. inv H1. inv H. inv H1. inv H. des. inv H1. des. inv H2. inv H4.
            right. econs. split; eauto. eapply Execution.po_chain. econs. split; eauto.
    }
  }
  { (* rmw_failure *)
    rewrite EU, AEU, WL, RL, COV, VEXT in SIMTR.
    exploit sim_trace_sim_th; try exact SIMTR; eauto. intro L'.
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
    inv STEP0. ss. subst. inv LOCAL0; inv EVENT.
    { (* read *)
      exploit sim_trace_sim_th; try exact TRACE; eauto. intro SIM_TH.
      destruct SIM_TH.(EU_WF).
      specialize (Local.read_spec LOCAL0 STEP0). intro READ_SPEC. guardH READ_SPEC.
      clear LOCAL0. inv STEP0. ss.
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
          exploit sim_trace_sim_th; try exact REL0; eauto. intro L1.
          exploit L1.(WPROP3); eauto. i. des.
          unfold v_gen. ss. rewrite <- H7. auto.
        }
        subst.
        repeat rewrite <- join_r. ss. unfold FwdItem.read_view. condtac; ss. clear X0. inv e.
        generalize (L.(LC).(FWDBANK) (ValA.val vloc)). s. i. des.
        + rewrite <- TS in H2.
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
            exploit sim_trace_sim_th; try exact REL0; eauto. intro L1.
            inv WRITE. inv WRITE1.
            unfold Execution.label in EID0. ss.
            rewrite PRE.(Valid.LABELS) in EID0.
            rewrite IdMap.map_spec in EID0.
            destruct (IdMap.find tid2 (Valid.aeus PRE)) eqn:FIND2; ss.
            generalize (ATR tid2). intro ATR2. inv ATR2; try congr. des. simplify.
            generalize (SIM tid2). intro SIM2. inv SIM2; simplify.
            exploit sim_trace_last; try exact REL1. i. des. simplify.
            exploit sim_trace_sim_th; try exact REL1; eauto. intro L2.
            move H2 at bottom.
            unfold v_gen in H2. ss.
            rewrite <- H10, <- H16 in H2.
            exploit L1.(WPROP2); eauto. i. des.
            exploit L2.(WPROP2'); eauto. i. des.
            exploit L1.(WPROP3); eauto. i. des.
            exploit L2.(WPROP3); eauto. i. des.
            rewrite x11, x18 in H2. inv H2.
            rewrite H in x22. rewrite x15 in x22. inv x22. ss. }
          subst.
          inv WRITE. inv PO. ss. subst. inv H. inv H3. ss.
        + rewrite H1. refl.
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
    { (* rmw_failure *)
      exploit sim_trace_sim_th; try exact TRACE; eauto. intro SIM_TH.
      destruct SIM_TH.(EU_WF).
      specialize (Local.rmw_failure_spec LOCAL0 STEP0). intro RMW_FAILURE_SPEC. guardH RMW_FAILURE_SPEC.
      clear LOCAL0. inv STEP0. ss.
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
          exploit sim_trace_sim_th; try exact REL0; eauto. intro L1.
          exploit L1.(WPROP3); eauto. i. des.
          unfold v_gen. ss. rewrite <- H7. auto.
        }
        subst.
        repeat rewrite <- join_r. ss. unfold FwdItem.read_view. condtac; ss. clear X0. inv e.
        generalize (L.(LC).(FWDBANK) (ValA.val vloc)). s. i. des.
        + rewrite <- TS in H2.
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
            exploit sim_trace_sim_th; try exact REL0; eauto. intro L1.
            inv WRITE. inv WRITE1.
            unfold Execution.label in EID0. ss.
            rewrite PRE.(Valid.LABELS) in EID0.
            rewrite IdMap.map_spec in EID0.
            destruct (IdMap.find tid2 (Valid.aeus PRE)) eqn:FIND2; ss.
            generalize (ATR tid2). intro ATR2. inv ATR2; try congr. des. simplify.
            generalize (SIM tid2). intro SIM2. inv SIM2; simplify.
            exploit sim_trace_last; try exact REL1. i. des. simplify.
            exploit sim_trace_sim_th; try exact REL1; eauto. intro L2.
            move H2 at bottom.
            unfold v_gen in H2. ss.
            rewrite <- H10, <- H16 in H2.
            exploit L1.(WPROP2); eauto. i. des.
            exploit L2.(WPROP2'); eauto. i. des.
            exploit L1.(WPROP3); eauto. i. des.
            exploit L2.(WPROP3); eauto. i. des.
            rewrite x11, x18 in H2. inv H2.
            rewrite H in x22. rewrite x15 in x22. inv x22. ss. }
          subst.
          inv WRITE. inv PO. ss. subst. inv H. inv H3. ss.
        + rewrite H1. refl.
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
  }
Qed.
