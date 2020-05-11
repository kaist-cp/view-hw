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
    { apply nth_error_last. apply Nat.eqb_eq. ss. }
    unfold ALocal.next_eid in *. condtac; cycle 1.
    { apply Nat.eqb_neq in X. congr. }
    i. des. inv x0.
    exploit L'.(RPROP2); eauto.
    { rewrite X. eauto. }
    s. rewrite X. i. des.
    apply nth_error_snoc_inv_last in x3. inv x3.
    clear x4 H1 tid'0 x2 x0.
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
        repeat rewrite <- join_r. ss.
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
        repeat rewrite <- join_r. ss.
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
    admit.
  }
  { (* rmw_failure *)
    rewrite EU, AEU, WL, RL, COV, VEXT in SIMTR.
    exploit sim_trace_sim_th; try exact SIMTR; eauto. intro L'.
    exploit L'.(RPROP1); ss.
    { apply nth_error_last. apply Nat.eqb_eq. ss. }
    unfold ALocal.next_eid in *. condtac; cycle 1.
    { apply Nat.eqb_neq in X. congr. }
    i. des. inv x0.
    exploit L'.(RPROP2); eauto.
    { rewrite X. eauto. }
    s. rewrite X. i. des.
    apply nth_error_snoc_inv_last in x3. inv x3.
    clear x4 H1 tid'0 x2 x0.
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
        repeat rewrite <- join_r. ss.
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
        repeat rewrite <- join_r. ss.
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
