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
Require Import PromisingArch.equiv.PFtoA1.
Require Import PromisingArch.equiv.PFtoA2.
Require Import PromisingArch.equiv.PFtoA3.

Set Implicit Arguments.


Lemma sim_traces_sim_th'_fob
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
    sim_fob tid ex (v_gen vexts) eu2 aeu2.
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
  { inv L. eapply FOB0; eauto. }
  exploit Execution.fob_flushopt; eauto. intro X. inv X. destruct l0; ss.
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
  all: intro NTH; apply nth_error_snoc_inv_last in NTH; inv NTH.
  rewrite EU, AEU, WL, RL, COV, VEXT in SIMTR.
  exploit sim_trace_sim_th; try exact SIMTR; eauto. intro L'.
  exploit L'.(FPROP1); ss.
  { apply nth_error_last. apply Nat.eqb_eq. ss. }
  unfold ALocal.next_eid in *. condtac; cycle 1.
  { apply Nat.eqb_neq in X. congr. }
  i. des. inv x0.
  exploit L'.(FPROP2); eauto.
  { rewrite X. eauto. }
  s. rewrite X. i. des.
  apply nth_error_snoc_inv_last in x2. inv x2.
  rewrite EX2.(XVEXT); s; cycle 1.
  { rewrite List.app_length. s. clear. lia. }
  rewrite X.
  inv STEP0. ss. subst. inv LOCAL0; inv EVENT.
  exploit sim_trace_sim_th; try exact TRACE; eauto. intro SIM_TH.
  destruct SIM_TH.(EU_WF).
  clear STATE2 LOCAL0. inv STEP0. ss.
  exploit EX2.(LABELS); eauto; ss.
  { rewrite List.app_length. s. clear. lia. }
  i. funtac.
  move EID at bottom. move FOB at bottom. unfold Execution.fob in *. des_union.
  - (* W U R; po_cl; FO *)
    rewrite L.(LC).(COH2); ss.
    + rewrite <- join_r, <- join_l. eapply Memory.latest_ts_spec.
    + obtac.
      econs; eauto. unfold sim_local_coh2.
      inv H. obtac. simtac.
      rewrite EID in EID3. simplify. ss. eqvtac. rewrite <- H1.
      destruct l0; destruct l2; ss; try congr; eqvtac; simtac.
  - (* W U R; po; [dmb.sy U dsb.sy]; po; FO *)
    rewrite L.(LC).(VPN); ss.
    + rewrite <- join_r, <- join_r. ss.
    + obtac.
      econs; eauto. unfold sim_local_vpn.
      inv H. obtac. simtac.
Qed.
