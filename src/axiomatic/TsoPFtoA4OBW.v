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


Lemma sim_traces_sim_th'_ob_write
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
    sim_ob_write tid ex (v_gen vexts) eu2 aeu2.
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
  { (* write *)
    rewrite EU, AEU, WL, RL, COV, VEXT in SIMTR.
    exploit sim_trace_sim_th; try exact SIMTR; eauto. intro L'.
    inv RES. destruct res1. ss. subst.
    exploit L'.(WPROP2); ss.
    { split.
      - apply nth_error_last. apply Nat.eqb_eq. ss.
      - eauto with tso.
    }
    unfold ALocal.next_eid in *. condtac; cycle 1.
    { apply Nat.eqb_neq in X. congr. }
    i. des. inv x0.
    exploit L'.(WPROP3); eauto.
    { rewrite X. eauto. }
    s. rewrite X. i. des.
    apply nth_error_snoc_inv_last in x5. inv x5. inv x6.
    destruct (equiv_dec (ValA.val (sem_expr rmap eloc)) (ValA.val vloc1)); ss. clear e.
    destruct (equiv_dec (ValA.val (sem_expr rmap eval))); ss. inv e.
    rewrite x1 in x7. inv x7. clear x3 x4 H1.
    rewrite EX2.(XVEXT); s; cycle 1.
    { rewrite List.app_length. s. clear. lia. }
    rewrite X.
    inv STEP0. ss. subst. inv LOCAL0; inv EVENT; inv STEP0; ss.
    move OB at bottom. unfold ob' in OB. des_union.
    - (* rfe *)
      rename H1 into H.
      inv H. exploit RF2; eauto. i. des.
      inv READ. inv WRITE. destruct l0; destruct l1; ss; congr.
    - (* dob *)
      rename H1 into H.
      unfold Execution.dob in H. rewrite ? seq_assoc in *. des_union.
      + inv H1. des.
        inv H1. eapply Nat.le_lt_trans.
        { apply L.(LC).(VWN); ss. econs; ss. left. ss. }
        s. rewrite fun_add_spec. condtac; [|congr].
        inv WRITABLE. ss.
      + inv H1. des.
        inv H1. eapply Nat.le_lt_trans.
        { apply L.(LC).(VWN); ss. econs; ss. inv H. des. inv H1. inv H5.
          destruct l0; ss.
          - left. econs; ss. econs; eauto. econs; ss. econs; eauto.
          - right. econs; ss. econs; eauto. econs; ss. econs; eauto.
          - right. econs; ss. econs; eauto. econs; ss. econs; eauto.
        }
        s. rewrite fun_add_spec. condtac; [|congr].
        inv WRITABLE. ss.
    - (* bob *)
      unfold Execution.bob in H. rewrite ? seq_assoc in *.
      inv H. des. inv H3. inv H4. destruct l0; ss; congr.
  }
  { (* update *)
    admit.
  }
Qed.
