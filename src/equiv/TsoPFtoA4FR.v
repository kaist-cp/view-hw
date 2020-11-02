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


Lemma sim_traces_sim_th'_fr
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
    sim_fre tid ex (v_gen vexts) eu2 aeu2.
Proof.
  i. rename SIM_TH' into L.
  generalize (SIM tid). intro X. inv X; simplify.
  destruct n.
  { generalize (lastn_length 1 tr). rewrite EU. destruct tr; ss. }
  exploit sim_trace_lastn; eauto. instantiate (1 := S n). intro SIMTR.
  exploit sim_trace_memory; eauto. intro MEM1.
  hexploit sim_traces_ex; eauto. intro EX2.
  inversion SIMTR; subst; simplify; [congr|].
  repeat match goal with
         | [H1: lastn ?a ?b = ?c, H2: ?d = lastn ?a ?b |- _] =>
           rewrite H1 in H2; inv H2
         end.
  exploit sim_trace_sim_state_weak; eauto. intro STATE1.

  ii.
  destruct (le_lt_dec (length (ALocal.labels (AExecUnit.local aeu1))) eid1); cycle 1.
  { eapply L; eauto. }
  assert (exists loc,
             <<LABEL1: Execution.label_is ex (fun label : Label.t => Label.is_kinda_reading loc label) (tid, eid1)>> /\
             <<LABEL2: Execution.label_is ex (fun label : Label.t => Label.is_kinda_writing loc label) eid2>>).
  { inv FR. inv H.
    - inv H1. des.
      exploit RF2; eauto. i. des.
      exploit CO2; eauto. i. des.
      inv READ. rename EID into READ. rename LABEL2 into R_VAL.
      inv WRITE. rename EID into WRITE. rename LABEL2 into W_VAL.
      inv LABEL0. rename EID into LABEL0. rename LABEL2 into WRITING0.
      inv LABEL1. rename EID into LABEL1. rename LABEL2 into WRITING1.
      eapply Label.kinda_writing_val_is_kinda_writing in W_VAL.
      rewrite WRITE in LABEL0. inv LABEL0.
      exploit Label.kinda_writing_same_loc. instantiate (1 := l2). eauto. instantiate (1 := loc). ss.
      i. subst.
      esplits; econs; eauto with tso.
    - inv H1. inv H2. inv H1. inv H3. inv H2. inv H. rewrite EID1 in EID0. inv EID0. rewrite EID2 in EID. inv EID.
      destruct l0; destruct l1; inv LABEL2; ss; eqvtac.
      all: esplits; econs; eauto with tso.
  }
  i. des.
  inv LABEL1.
  inv LABEL2.
  destruct eid2 as [tid2 eid2].
  generalize (SIM tid2). intro SIMTR2. inv SIMTR2.
  { generalize (ATR tid2). rewrite <- H. intro X. inv X.
    unfold Execution.label in EID0. ss.
    rewrite PRE.(Valid.LABELS), IdMap.map_spec, <- H1 in EID0. ss.
  }
  rename REL0 into SIMTR2, a into tr2, b into atr2, c into wl2, d into rl2, e0 into fl2, f into covl2, g into vextl2.
  rename H0 into TR2, H into ATR2, H2 into WL2, H3 into RL2, H4 into FL2, H5 into COVL4, H6 into VEXTL5.
  exploit sim_trace_last; eauto. i. des. subst.
  destruct eu1 as [st1 lc1 mem1] eqn: EU1. guardH EU1.
  destruct eu2 as [st2 lc2 mem2] eqn: EU2. guardH EU2.
  destruct aeu1 as [ast1 alc1].
  destruct aeu2 as [ast2 alc2].
  inv ASTATE_STEP; inv EVENT; inv ALOCAL_STEP; inv EVENT; repeat (ss; subst).
  all: try (clear - LABEL l; lia).
  all: rewrite List.app_length in LABEL; ss.
  all: assert (EID1: eid1 = length (ALocal.labels alc1)) by (clear - LABEL l; lia); subst.
  all: exploit LABELS; eauto; ss.
  all: try by clear; rewrite List.app_length; s; lia.
  all: destruct l0; ss.
  all: eqvtac.
  all: intro NTH; apply nth_error_snoc_inv_last in NTH; inv NTH.
  all: inv FR.
  all: rewrite EU, AEU, WL, RL, FL, COV, VEXT in SIMTR.
  all: rename l1 into wr_lab.
  { (* read -> kinda_write *)
    exploit sim_trace_sim_th; try exact SIMTR; eauto. intro TH_tmp.
    exploit lastn_sub_S1; try exact EU; eauto. i. des.
    exploit TH_tmp; eauto.
    clear TH_tmp. intro L2.
    exploit sim_trace_sim_th; try exact TRACE; eauto. intro TH_tmp.
    exploit TH_tmp; eauto.
    { instantiate (1 := l1 ++ [eu2]). rewrite <- List.app_assoc. rewrite EU2. ss. }
    clear TH_tmp. intro L1.
    exploit L2.(RPROP1); ss.
    { split; eauto with tso. apply nth_error_last. apply Nat.eqb_eq. ss. }
    unfold ALocal.next_eid in *. condtac; cycle 1.
    { apply Nat.eqb_neq in X. congr. }
    i. des. inv x0. rewrite EX2.(XVEXT) in *; s; cycle 1.
    { rewrite List.app_length. s. clear. lia. }
    rewrite X.
    inv STEP0. ss. subst. inv LOCAL; inv EVENT; cycle 1.
    { inv STATE1. inv STATE0. ss. }
    generalize L1.(EU_WF). intro WF. inv WF. ss.
    generalize (Local.read_spec LOCAL STEP0). i. des. subst.
    exploit sim_traces_cov_fr; eauto.
    { inv STEP. ss. }
    rewrite EX2.(XCOV) in *; s; cycle 1.
    { rewrite List.app_length. s. clear. lia. }
    rewrite X. intro FR_COV. guardH FR_COV.
    exploit sim_trace_sim_th; try exact SIMTR2; eauto. intro TH_tmp.
    exploit lastn_sub_S1; try exact EU; eauto. i. des.
    exploit TH_tmp; eauto.
    { instantiate (1 := []). ss. }
    clear TH_tmp. intro L1'.
    exploit sim_trace_length; try exact SIMTR2; eauto. intro LEN. guardH LEN.
    symmetry in ATR2. hexploit sim_traces_ex; try exact ATR2; eauto.
    1: instantiate (3 := length atr'0).
    all: try rewrite lastn_all; ss.
    all: try by clear -LEN; unguardH LEN; des; lia.
    intro EX2'.
    revert EID0. unfold Execution.label. s. rewrite PRE.(Valid.LABELS), IdMap.map_spec.
    generalize (ATR tid2). rewrite ATR2. intros Y Z; inv Y; ss.
    rewrite <- H3 in Z. inv Z. des. simplify. rewrite H4 in *.
    exploit Label.kinda_write_exists_loc_val; eauto with tso. i. des.
    exploit L1'.(WPROP2); eauto with tso. i. des.
    exploit L1'.(WPROP3); eauto. i. des. subst.
    rewrite EX2'.(XVEXT) in *; eauto; cycle 1.
    { apply List.nth_error_Some. congr. }
    rewrite EX2'.(XCOV) in *; eauto; cycle 1.
    { apply List.nth_error_Some. congr. }
    rewrite x6 in *. rewrite x3 in x10. inv x10.
    unguardH FR_COV. des.
    - eapply Memory.latest_lt; eauto. destruct wr_lab; ss; eqvtac.
    - inv FR_COV0. inv H0. ss.
  }
  { (* update -> kinda_write *)
    exploit sim_trace_sim_th; try exact SIMTR; eauto. intro TH_tmp.
    exploit lastn_sub_S1; try exact EU; eauto. i. des.
    exploit TH_tmp; eauto.
    clear TH_tmp. intro L2.
    exploit sim_trace_sim_th; try exact TRACE; eauto. intro TH_tmp.
    exploit TH_tmp; eauto.
    { instantiate (1 := l1 ++ [eu2]). rewrite <- List.app_assoc. rewrite EU2. ss. }
    clear TH_tmp. intro L1.
    exploit L2.(RPROP1); ss.
    { split.
      - instantiate (1 := (Label.update (ValA.val (sem_expr rmap eloc)) (ValA.val voldv) (ValA.val vnewv))).
        apply nth_error_last. apply Nat.eqb_eq. ss.
      - eauto with tso.
    }
    unfold ALocal.next_eid in *. condtac; cycle 1.
    { apply Nat.eqb_neq in X. congr. }
    i. des. inv x0. rewrite EX2.(XVEXT) in *; s; cycle 1.
    { rewrite List.app_length. s. clear. lia. }
    rewrite X.
    inv STEP0. ss. subst. inv LOCAL; inv EVENT.
    generalize L1.(EU_WF). intro WF. inv WF. ss.
    exploit sim_traces_cov_fr; eauto.
    { inv STEP. ss. }
    rewrite EX2.(XCOV) in *; s; cycle 1.
    { rewrite List.app_length. s. clear. lia. }
    rewrite X. intro FR_COV. guardH FR_COV.
    exploit sim_trace_sim_th; try exact SIMTR2; eauto. intro TH_tmp.
    exploit lastn_sub_S1; try exact EU; eauto. i. des.
    exploit TH_tmp; eauto.
    { instantiate (1 := []). ss. }
    clear TH_tmp. intro L1'.
    exploit sim_trace_length; try exact SIMTR2; eauto. intro LEN. guardH LEN.
    symmetry in ATR2. hexploit sim_traces_ex; try exact ATR2; eauto.
    1: instantiate (3 := length atr'0).
    all: try rewrite lastn_all; ss.
    all: try by clear -LEN; unguardH LEN; des; lia.
    intro EX2'.
    revert EID0. unfold Execution.label. s. rewrite PRE.(Valid.LABELS), IdMap.map_spec.
    generalize (ATR tid2). rewrite ATR2. intros Y Z; inv Y; ss.
    rewrite <- H3 in Z. inv Z. des. simplify. rewrite H4 in *.
    exploit Label.kinda_write_exists_loc_val; eauto with tso. i. des.
    exploit L1'.(WPROP2); eauto with tso. i. des.
    exploit L1'.(WPROP3); eauto. i. des. subst.
    rewrite EX2'.(XVEXT) in *; eauto; cycle 1.
    { apply List.nth_error_Some. congr. }
    rewrite EX2'.(XCOV) in *; eauto; cycle 1.
    { apply List.nth_error_Some. congr. }
    rewrite x6 in *. rewrite x3 in x10. inv x10.
    unguardH FR_COV. des; ss.
    inv FR_COV0. inv H0. ss.
  }
  { (* rmw_failure -> kinda_write *)
    exploit sim_trace_sim_th; try exact SIMTR; eauto. intro TH_tmp.
    exploit lastn_sub_S1; try exact EU; eauto. i. des.
    exploit TH_tmp; eauto.
    clear TH_tmp. intro L2.
    exploit sim_trace_sim_th; try exact TRACE; eauto. intro TH_tmp.
    exploit TH_tmp; eauto.
    { instantiate (1 := l1 ++ [eu2]). rewrite <- List.app_assoc. rewrite EU2. ss. }
    clear TH_tmp. intro L1.
    exploit L2.(RPROP1); ss.
    { split; eauto with tso. apply nth_error_last. apply Nat.eqb_eq. ss. }
    unfold ALocal.next_eid in *. condtac; cycle 1.
    { apply Nat.eqb_neq in X. congr. }
    i. des. inv x0. rewrite EX2.(XVEXT) in *; s; cycle 1.
    { rewrite List.app_length. s. clear. lia. }
    rewrite X.
    inv STEP0. ss. subst. inv LOCAL; inv EVENT.
    { inv STATE1. inv STATE0. ss. }
    generalize L1.(EU_WF). intro WF. inv WF. ss.
    generalize (Local.rmw_failure_spec LOCAL STEP0). i. des. subst.
    exploit sim_traces_cov_fr; eauto.
    { inv STEP. ss. }
    rewrite EX2.(XCOV) in *; s; cycle 1.
    { rewrite List.app_length. s. clear. lia. }
    rewrite X. intro FR_COV. guardH FR_COV.
    exploit sim_trace_sim_th; try exact SIMTR2; eauto. intro TH_tmp.
    exploit lastn_sub_S1; try exact EU; eauto. i. des.
    exploit TH_tmp; eauto.
    { instantiate (1 := []). ss. }
    clear TH_tmp. intro L1'.
    exploit sim_trace_length; try exact SIMTR2; eauto. intro LEN. guardH LEN.
    symmetry in ATR2. hexploit sim_traces_ex; try exact ATR2; eauto.
    1: instantiate (3 := length atr'0).
    all: try rewrite lastn_all; ss.
    all: try by clear -LEN; unguardH LEN; des; lia.
    intro EX2'.
    revert EID0. unfold Execution.label. s. rewrite PRE.(Valid.LABELS), IdMap.map_spec.
    generalize (ATR tid2). rewrite ATR2. intros Y Z; inv Y; ss.
    rewrite <- H3 in Z. inv Z. des. simplify. rewrite H4 in *.
    exploit Label.kinda_write_exists_loc_val; eauto with tso. i. des.
    exploit L1'.(WPROP2); eauto with tso. i. des.
    exploit L1'.(WPROP3); eauto. i. des. subst.
    rewrite EX2'.(XVEXT) in *; eauto; cycle 1.
    { apply List.nth_error_Some. congr. }
    rewrite EX2'.(XCOV) in *; eauto; cycle 1.
    { apply List.nth_error_Some. congr. }
    rewrite x6 in *. rewrite x3 in x10. inv x10.
    unguardH FR_COV. des.
    - eapply Memory.latest_lt; eauto. destruct wr_lab; ss; eqvtac.
    - inv FR_COV0. inv H0. ss.
  }
Qed.
