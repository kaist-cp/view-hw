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
Require Import PromisingArch.equiv.TsoSimLocal.
Require Import PromisingArch.equiv.TsoPFtoA1.
Require Import PromisingArch.equiv.TsoPFtoA2.
Require Import PromisingArch.equiv.TsoPFtoA3.

Set Implicit Arguments.


Lemma sim_traces_sim_th'_ob_read
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
  exploit sim_trace_rtc_step; try exact REL7; eauto. intro RTC_STEP.
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
  all: rewrite EU, AEU, WL, RL, FL, COV, VEXT in SIMTR.
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
    inv STEP0. ss.
    exploit EX2.(LABELS); eauto; ss.
    { rewrite List.app_length. s. clear. lia. }
    i.
    move AOB at bottom. unfold ob' in AOB. des_union.
    - (* rfe *)
      obtac. destruct eid1 as [tid1 eid1]. inv H2. ss.
      generalize H. intro Y. rewrite RF in Y. inv Y. ss.
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
      assert (VGEN_TS: v_gen vexts (tid1, eid1) = ts2).
      { unfold v_gen. ss. rewrite <- H8. auto. }
      rewrite VGEN_TS in *.
      unfold Local.read_view. condtac; ss; [|apply join_r].
      rewrite (bot_join (View.ts (Local.vrn lc1))).
      inversion LOCAL. eapply NFWD; eauto.
    - (* dob *)
      rewrite ? seq_assoc in *. des_union; obtac.
      + rewrite L.(LC).(VRN); ss.
        * repeat rewrite <- join_l. ss.
        * econs; eauto. unfold sim_local_vrn. left. econs. econs; eauto. simtac.
      + destruct l2; ss; congr.
    - (* bob *)
      obtac.
      rewrite L.(LC).(VRN); ss; [apply join_l|].
      econs; ss. right. rewrite ? seq_assoc.
      econs. split; eauto. econs. split; econs; eauto with tso.
      split; eauto. econs; eauto with tso.
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
        assert (v_gen vexts eid1 = old_ts).
        { obtac. destruct eid1 as [tid1 eid1]. inv H2. ss.
          generalize H. intro Y. rewrite RF in Y. inv Y. ss.
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
          unfold v_gen. ss. rewrite <- H8. rewrite x7.
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
        generalize L.(LC).(VWN). intro VWN. des.
        obtac.
        + rewrite VWN0; ss.
          * rewrite fun_add_spec. condtac; ss; cycle 1.
            { exfalso. apply c. ss. }
            inv WRITABLE. unfold Time.le. inv COHMAX. specialize (MAX mloc).
            inv MAX. unfold le in *. lia.
          * econs; eauto. unfold sim_local_vwn. econs. econs; eauto. econs; eauto with tso.
        + rewrite VWN0; ss.
          * rewrite fun_add_spec. condtac; ss; cycle 1.
            { exfalso. apply c. ss. }
            inv WRITABLE. unfold Time.le. inv COHMAX. specialize (MAX mloc).
            inv MAX. unfold le in *. lia.
          * econs; eauto. unfold sim_local_vwn.
            econs. econs; eauto. econs; eauto with tso.
      - (* bob *)
        unguardH LC2. inv LC2. ss.
        generalize L.(LC).(VWN). intro VWN. des.
        funtac. obtac.
        rewrite VWN0; ss.
        { inv WRITABLE. unfold Time.le. inv COHMAX. specialize (MAX mloc).
          inv MAX. unfold le in *. lia.
        }
        econs; eauto. unfold sim_local_vwn.
        econs. split; [simtac|]. etrans; eauto.
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
    inv STEP0. ss.
    exploit EX2.(LABELS); eauto; ss.
    { rewrite List.app_length. s. clear. lia. }
    i.
    move AOB at bottom. unfold ob' in AOB. des_union.
    - (* rfe *)
      obtac. destruct eid1 as [tid1 eid1]. inv H2. ss.
      generalize H. intro Y. rewrite RF in Y. inv Y. ss.
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
      assert (VGEN_TS: v_gen vexts (tid1, eid1) = ts2).
      { unfold v_gen. ss. rewrite <- H8. auto. }
      rewrite VGEN_TS in *.
      unfold Local.read_view. condtac; ss; [|apply join_r].
      rewrite (bot_join (View.ts (Local.vrn lc1))).
      inversion LOCAL. eapply NFWD; eauto.
    - (* dob *)
      rewrite ? seq_assoc in *. des_union; obtac.
      + rewrite L.(LC).(VRN); ss.
        * repeat rewrite <- join_l. ss.
        * econs; eauto. unfold sim_local_vrn. left. econs. econs; eauto. simtac.
      + destruct l2; ss; congr.
    - (* bob *)
      obtac.
      rewrite L.(LC).(VRN); ss; [apply join_l|].
      econs; ss. right. rewrite ? seq_assoc.
      econs. split; eauto. econs. split; econs; eauto with tso.
      split; eauto. econs; eauto with tso.
  }
Qed.
