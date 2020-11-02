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


Lemma sim_traces_sim_th'_sl
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
    sim_state tid (v_gen vexts) eu2.(ExecUnit.state) aeu2.(AExecUnit.state) /\
    sim_local tid m.(Machine.mem) ex (v_gen vexts) eu2.(ExecUnit.local) aeu2.(AExecUnit.local).
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
  destruct eu1 as [[stmts1 rmap1] lc1 mem1] eqn: EU1. guardH EU1.
  destruct eu2 as [[stmts2 rmap2] lc2 mem2] eqn: EU2. guardH EU2.
  destruct aeu1 as [[astmts1 armap1] alc1].
  destruct aeu2 as [[astmts2 armap2] alc2].
  ss. inv STEP0. ss. subst.
  inv STATE. inv STATE1. ss. subst.
  inv STATE0; inv LOCAL; ss; inv EVENT0; inv EVENT; ss.
  - (* skip *)
    inv ASTATE_STEP; inv ALOCAL_STEP; ss; inv EVENT; ss. splits.
    + econs; ss. apply L.
    + econs; ss; try by apply L.
  - (* assign *)
    inv ASTATE_STEP; inv ALOCAL_STEP; ss; inv EVENT; ss. splits.
    + econs; ss. apply sim_rmap_add; try by apply L.
      apply sim_rmap_expr. apply L.
    + econs; ss; try by apply L.
  - (* read *)
    exploit sim_trace_sim_th; try exact TRACE; eauto. intro TH_tmp.
    exploit lastn_sub_S1; try exact EU; eauto. intro TRT. des.
    exploit TH_tmp; eauto.
    { instantiate (1 := l1 ++ [eu2]). rewrite <- List.app_assoc. rewrite EU2. ss. }
    clear TH_tmp. intro SIM_TH.
    destruct SIM_TH.(EU_WF). ss.
    generalize (Local.read_spec LOCAL STEP0). intro READ_SPEC.
    generalize SIM_TH.(MEM). s. i. rewrite H in READ_SPEC.
    guardH READ_SPEC. clear H.
    inv STEP0. inv ASTATE_STEP; inv ALOCAL_STEP; ss; inv EVENT; ss. splits.
    { econs; ss. apply sim_rmap_add; try apply L.
      inv VAL. ss.
    }
    destruct L.(LC). ss. econs; ss.
    all: try rewrite List.app_length, Nat.add_1_r.
    + i. rewrite sim_local_coh_step. rewrite inverse_step.
      rewrite inverse_union. rewrite fun_add_spec. condtac.
      { ii. des.
        { etrans; try eapply COH0; eauto. rewrite e. ss. }
        inv EID. inv REL. des. inv H. inv H2. inv H0.
        - exploit EX2.(LABELS); eauto; ss.
          { rewrite List.app_length. s. lia. }
          rewrite List.nth_error_app2, Nat.sub_diag; ss.
          destruct l; ss.
        - (* rfe *)
          inv H. exploit RF2; eauto. i. des.
          destruct x as [tid1 eid1]. ss.
          inv WRITE. inv READ. rename EID0 into WRITE.
          unfold Execution.label in WRITE. ss.
          rewrite PRE.(Valid.LABELS) in WRITE.
          rewrite IdMap.map_spec in WRITE.
          destruct (IdMap.find tid1 (Valid.aeus PRE)) eqn:FIND1; ss.
          generalize (ATR tid1). intro ATR1. inv ATR1; try congr. des. simplify.
          generalize (SIM tid1). intro SIM1. inv SIM1; simplify.
          exploit sim_trace_last; try exact REL0. i. des. simplify.
          exploit sim_trace_sim_th; try exact REL0; eauto. intro TH_tmp.
          exploit TH_tmp; eauto.
          { instantiate (1 := []). ss. }
          clear TH_tmp. intro L1.
          rewrite RF in H0. inv H0. ss. simplify.
          exploit WPROP3; eauto. i. des. simplify.
          unfold v_gen. ss. rewrite <- H9. rewrite x2.
          exploit EX2.(XR); eauto.
          { instantiate (1 := ALocal.next_eid alc1).
            ss. rewrite List.app_length. ss. unfold ALocal.next_eid. clear. lia. }
          condtac; cycle 1.
          { rewrite Nat.eqb_neq in X0. ss. }
          funtac.
          i. unfold ALocal.next_eid in *.
          rewrite R in x7. inv x7. ss.
      }
      ii. des; [apply COH0|]; eauto.
      inv EID. inv REL. inv H. inv H0. inv H2. inv H1.
      * exploit EX2.(LABELS); eauto; ss.
        { rewrite List.app_length. s. lia. }
        rewrite List.nth_error_app2, Nat.sub_diag; ss.
        destruct l; ss.
      * inv H. exploit RF2; eauto. i. des.
        inv WRITE. inv READ.
        rename EID0 into WRITE. rewrite EID in WRITE. inv WRITE.
        exploit EX2.(LABELS); eauto; ss.
        { rewrite List.app_length. s. lia. }
        rewrite List.nth_error_app2, Nat.sub_diag; ss. i.
        inv x1. inv VLOC. inv LABEL1. eqvtac.
        assert (LOC: loc = (ValA.val (sem_expr armap1 eloc))); eauto with tso.
        congr.
    + rewrite sim_local_vrn_step. rewrite inverse_step.
      rewrite ? inverse_union. ii. des.
      * exploit VRN; eauto. i. rewrite <- join_l. ss.
      * inv EID. inv REL. inv H0.
        exploit EX2.(LABELS); eauto; ss.
        { rewrite List.app_length. s. lia. }
        rewrite List.nth_error_app2, Nat.sub_diag; ss. i. inv x0.
        rewrite EX2.(XVEXT); cycle 1.
        { ss. rewrite List.app_length. ss. unfold ALocal.next_eid. clear. lia. }
        destruct (length (ALocal.labels alc1) =? ALocal.next_eid alc1) eqn:Heq; ss.
        rewrite Nat.eqb_neq in Heq. ss.
      * inv EID. inv REL. inv H. inv H1. inv H. inv H2. inv H3.
        exploit EX2.(LABELS); eauto; ss.
        { rewrite List.app_length. s. lia. }
        { rewrite List.nth_error_app2, Nat.sub_diag; ss. i. inv x1. inv LABEL. }
    + move VWN at bottom. des.
      inversion LOCAL. inv COHMAX. inv COHMAX0.
      destruct (lt_eq_lt_dec ts (View.ts (Local.coh lc1 mloc))).
      { (* <= *)
        exists mloc. split.
        - i. funtac.
          + viewtac. inv s; ss; lia.
          + inversion e. subst.
            rewrite VWN. ss.
        - rewrite sim_local_vwn_step. rewrite inverse_step.
          rewrite ? inverse_union.
          ii. des; ss.
          + etrans; try eapply VWN0; eauto.
            rewrite fun_add_spec. condtac; ss.
            inversion e. ss.
          + inv EID. inv REL. inv H0.
            exploit EX2.(LABELS); eauto; ss.
            { rewrite List.app_length. s. lia. }
            rewrite List.nth_error_app2, Nat.sub_diag; ss. i. inv x1.
            rewrite EX2.(XVEXT); cycle 1.
            { ss. rewrite List.app_length. ss. unfold ALocal.next_eid. clear. lia. }
            destruct (length (ALocal.labels alc1) =? ALocal.next_eid alc1) eqn:Heq; ss; cycle 1.
            { rewrite Nat.eqb_neq in Heq. ss. }
            unfold le. specialize (VWN x).
            funtac.
            * viewtac.
              { inversion e. subst. unfold le in *. lia. }
              unfold Local.read_view. condtac; ss. apply bot_spec.
            * viewtac; [lia |].
              rewrite Local.fwd_read_view_le; eauto. inv s; lia.
      }
      { (* > *)
        exploit Local.high_ts_spec; eauto.
        { i. eapply le_lt_trans; try exact l; eauto. }
        i. des.
        eexists (ValA.val (sem_expr rmap1 eloc)). split.
        { i. funtac. specialize (VWN loc). lia. }
        rewrite sim_local_vwn_step. rewrite inverse_step.
        rewrite ? inverse_union.
        ii. des; ss.
        - etrans; try eapply VWN0; eauto.
          rewrite fun_add_spec. condtac; ss; cycle 1.
          { exfalso. apply c. ss. }
          unfold le. lia.
        - inv EID. inv REL. inv H0.
          exploit EX2.(LABELS); eauto; ss.
          { rewrite List.app_length. s. lia. }
          rewrite List.nth_error_app2, Nat.sub_diag; ss. i. inv x1.
          rewrite EX2.(XVEXT); cycle 1.
          { ss. rewrite List.app_length. ss. unfold ALocal.next_eid. clear. lia. }
          destruct (length (ALocal.labels alc1) =? ALocal.next_eid alc1) eqn:Heq; ss; cycle 1.
          { rewrite Nat.eqb_neq in Heq. ss. }
          unfold le. specialize (VWN x).
          funtac. viewtac.
          { unfold le in *. lia. }
          unfold Local.read_view. condtac; ss. apply bot_spec.
      }
    + i. exploit PROMISES; eauto. i. des. esplits; cycle 1; eauto.
      inv N.
      * inv WRITE. exploit EX2.(LABELS); eauto; ss.
        { rewrite List.app_length. s. lia. }
        rewrite List.nth_error_app2, Nat.sub_diag; ss.
        destruct l; ss.
      * clear -H. lia.
    + move COH_CL at bottom. i. specialize (COH_CL loc). des.
      destruct (Loc.cl loc (ValA.val (sem_expr rmap1 eloc))) eqn:H_CL; cycle 1.
      { exists mloc_cl. splits; ss.
        - i. funtac.
          + inversion e. subst.
            eapply Loc.cl_sym in CL0. exploit Loc.cl_trans; try exact CL; eauto.
            rewrite H_CL. ss.
          + inversion e. subst.
            rewrite H_CL in CL. ss.
        - rewrite sim_local_coh_cl_step. rewrite inverse_step.
          rewrite ? inverse_union. ii. des.
          { exploit COH_CL; eauto. intro X. rewrite X.
            funtac. inversion e. subst. rewrite H_CL in CL. ss.
          }
          inv EID. obtac. inv H0.
          { exploit EX2.(LABELS); eauto; ss.
            { rewrite List.app_length. s. lia. }
            rewrite List.nth_error_app2, Nat.sub_diag; ss. i. inv x0. ss.
          }
          inv H. exploit RF2; eauto. i. des. obtac. labtac.
          exploit EX2.(LABELS); eauto; ss.
          { rewrite List.app_length. s. lia. }
          rewrite List.nth_error_app2, Nat.sub_diag; ss. i.
          inv x1. inv VLOC. rewrite VAL0 in *.
          inv LABEL1. eqvtac.
          destruct l0; ss; eqvtac; rewrite H_CL in *; ss.
      }
      destruct (lt_eq_lt_dec ts (View.ts (Local.coh lc1 mloc_cl))).
      { (* <= *)
        exists mloc_cl. splits; ss.
        - i. funtac.
          + viewtac. inv s; ss; lia.
          + apply COH_MAX_CL in CL0.
            inversion e. subst. unfold le in *. inv s; lia.
        - rewrite sim_local_coh_cl_step. rewrite inverse_step.
          rewrite ? inverse_union.
          ii. des; ss.
          + etrans; try eapply COH_CL; eauto.
            funtac. inversion e. ss.
          + inv EID. obtac. inv H0.
            { exploit EX2.(LABELS); eauto; ss.
              { rewrite List.app_length. s. lia. }
              rewrite List.nth_error_app2, Nat.sub_diag; ss. i. inv x0. ss.
            }
            inv H. exploit RF2; eauto. i. des. obtac. labtac.
            destruct x as [tid1 eid1]. rename EID into WRITE.
            unfold Execution.label in WRITE. ss.
            rewrite PRE.(Valid.LABELS) in WRITE.
            rewrite IdMap.map_spec in WRITE.
            destruct (IdMap.find tid1 (Valid.aeus PRE)) eqn:FIND1; ss.
            generalize (ATR tid1). intro ATR1. inv ATR1; try congr. des. simplify.
            generalize (SIM tid1). intro SIM1. inv SIM1; simplify.
            exploit sim_trace_last; try exact REL0. i. des. simplify.
            exploit sim_trace_sim_th; try exact REL0; eauto. intro TH_tmp.
            exploit TH_tmp; eauto.
            { instantiate (1 := []). ss. }
            clear TH_tmp. intro L1.
            rewrite RF in H0. inv H0. ss. simplify.
            exploit WPROP3; eauto. i. des. simplify.
            rewrite WRITE in x4. simplify.
            unfold v_gen. ss. rewrite <- H9. rewrite x2.
            exploit EX2.(XR); eauto.
            { instantiate (1 := ALocal.next_eid alc1).
              ss. rewrite List.app_length. ss. unfold ALocal.next_eid. clear. lia.
            }
            condtac; cycle 1.
            { rewrite Nat.eqb_neq in X. ss. }
            funtac.
            { unfold ALocal.next_eid. intro Z. rewrite R in Z. simplify. ss. }
            unfold ALocal.next_eid. intro Z. rewrite R in Z. simplify.
            unfold le. inv s; lia.
      }
      { (* > *)
        exploit Local.high_ts_spec_cl; eauto.
        { i. eapply le_lt_trans; try exact l; eauto. }
        i. des.
        eexists (ValA.val (sem_expr rmap1 eloc)). splits; ss.
        - i. funtac. rewrite COH_MAX_CL; try lia.
          eapply Loc.cl_trans; eauto. eapply Loc.cl_trans; eauto. eapply Loc.cl_sym. ss.
        - rewrite sim_local_coh_cl_step. rewrite inverse_step.
          rewrite ? inverse_union.
          ii. des; ss.
          + etrans; try eapply COH_CL; eauto.
            funtac. unfold le. lia.
          + inv EID. obtac. inv H0.
            { exploit EX2.(LABELS); eauto; ss.
              { rewrite List.app_length. s. lia. }
              rewrite List.nth_error_app2, Nat.sub_diag; ss. i. inv x0. ss.
            }
            inv H. exploit RF2; eauto. i. des. obtac. labtac.
            destruct x as [tid1 eid1]. rename EID into WRITE.
            unfold Execution.label in WRITE. ss.
            rewrite PRE.(Valid.LABELS) in WRITE.
            rewrite IdMap.map_spec in WRITE.
            destruct (IdMap.find tid1 (Valid.aeus PRE)) eqn:FIND1; ss.
            generalize (ATR tid1). intro ATR1. inv ATR1; try congr. des. simplify.
            generalize (SIM tid1). intro SIM1. inv SIM1; simplify.
            exploit sim_trace_last; try exact REL0. i. des. simplify.
            exploit sim_trace_sim_th; try exact REL0; eauto. intro TH_tmp.
            exploit TH_tmp; eauto.
            { instantiate (1 := []). ss. }
            clear TH_tmp. intro L1.
            rewrite RF in H0. inv H0. ss. simplify.
            exploit WPROP3; eauto. i. des. simplify.
            rewrite WRITE in x4. simplify.
            unfold v_gen. ss. rewrite <- H9. rewrite x2.
            exploit EX2.(XR); eauto.
            { instantiate (1 := ALocal.next_eid alc1).
              ss. rewrite List.app_length. ss. unfold ALocal.next_eid. clear. lia.
            }
            condtac; cycle 1.
            { rewrite Nat.eqb_neq in X. ss. }
            funtac.
            unfold ALocal.next_eid. intro Z. rewrite R in Z. simplify. ss.
      }
    + i. rewrite sim_local_vpr_step. rewrite inverse_step.
      rewrite ? inverse_union. ii. des.
      * exploit VPR; eauto. i. rewrite <- join_l. ss.
      * inv EID. inv REL. inv H0.
        exploit EX2.(LABELS); eauto; ss.
        { rewrite List.app_length. s. lia. }
        rewrite List.nth_error_app2, Nat.sub_diag; ss. i. inv x0.
        rewrite EX2.(XVEXT); cycle 1.
        { ss. rewrite List.app_length. ss. unfold ALocal.next_eid. clear. lia. }
        destruct (length (ALocal.labels alc1) =? ALocal.next_eid alc1) eqn:Heq; cycle 1.
        { rewrite Nat.eqb_neq in Heq. ss. }
        apply join_spec; [rewrite <- join_l | rewrite <- join_r]; ss.
        inv LOCAL. rewrite VRNVPR. ss.
      * inv EID. inv REL. obtac. destruct l; ss.
        all: exploit EX2.(LABELS); eauto; ss.
        all: try by rewrite List.app_length; s; lia.
        all: rewrite List.nth_error_app2, Nat.sub_diag; ss.
        intro X. inv X. ss.
    + i. rewrite sim_local_vpa_step. rewrite inverse_step.
      rewrite inverse_union. ii. des; [apply VPA|]; eauto.
      inv EID. obtac.
      all: exploit EX2.(LABELS); eauto; ss.
      all: try by rewrite List.app_length; s; lia.
      all: rewrite List.nth_error_app2, Nat.sub_diag; ss.
      all: destruct l; ss.
    + i. rewrite sim_local_vpc_step. rewrite inverse_step.
      rewrite inverse_union. ii. des; [apply VPC|]; eauto.
      inv EID. obtac.
      all: exploit EX2.(LABELS); eauto; ss.
      all: try by rewrite List.app_length; s; lia.
      all: try rewrite List.nth_error_app2, Nat.sub_diag; ss; i; simplify; ss.
  - (* write *)
    exploit sim_trace_sim_th; try exact TRACE; eauto. intro TH_tmp.
    exploit lastn_sub_S1; try exact EU; eauto. intro TRT. des.
    exploit TH_tmp; eauto.
    { instantiate (1 := l1 ++ [eu2]). rewrite <- List.app_assoc. rewrite EU2. ss. }
    clear TH_tmp. intro SIM_TH.
    inv STEP0. inv ASTATE_STEP; inv ALOCAL_STEP; ss; inv EVENT; inv RES; ss. splits.
    { econs; ss. apply sim_rmap_add; try apply L. econs; ss. }
    destruct L.(LC). ss. econs; ss.
    all: try rewrite List.app_length, Nat.add_1_r.
    + i. rewrite sim_local_coh_step. rewrite inverse_step.
      rewrite inverse_union. rewrite fun_add_spec. condtac.
      { ii. des.
        - inv EID. inv WRITABLE.
          apply Nat.lt_le_incl. eapply Nat.le_lt_trans; try eapply EXT.
          etrans; try apply COH; eauto.
          inv COHMAX. specialize (MAX loc). inv MAX. unfold le in *. ss.
        - inv EID. inv REL. des. inv H. inv H2. inv H0.
          + exploit EX2.(LABELS); eauto; ss.
            { rewrite List.app_length. s. lia. }
            rewrite List.nth_error_app2, Nat.sub_diag; ss. i. inv x0.
            rewrite EX2.(XVEXT); cycle 1.
            { ss. rewrite List.app_length. ss. clear. lia. }
            condtac; cycle 1.
            { rewrite Nat.eqb_neq in X0. unfold ALocal.next_eid in X0. ss. }
            rewrite fun_add_spec. condtac; ss.
            exfalso. apply c. ss.
          + inv H. exploit RF2; eauto. i. des.
            inv WRITE. inv READ.
            rename EID0 into WRITE. rewrite EID in WRITE. inv WRITE.
            exploit EX2.(LABELS); eauto; ss.
            { rewrite List.app_length. s. lia. }
            rewrite List.nth_error_app2, Nat.sub_diag; ss. i.
            inv x1. ss.
      }
      ii. des; [apply COH|]; eauto.
      inv EID. inv REL. inv H. inv H0. inv H2. inv H1.
      * exploit EX2.(LABELS); eauto; ss.
        { rewrite List.app_length. s. lia. }
        rewrite List.nth_error_app2, Nat.sub_diag; ss. i.
        inv x0. inv VLOC. inv LABEL. eqvtac.
        symmetry in VAL0. ss.
      * inv H. exploit RF2; eauto. i. des.
        inv WRITE. inv READ.
        rename EID0 into WRITE. rewrite EID in WRITE. inv WRITE.
        exploit EX2.(LABELS); eauto; ss.
        { rewrite List.app_length. s. lia. }
        rewrite List.nth_error_app2, Nat.sub_diag; ss.
        destruct l2; ss.
    + rewrite sim_local_vrn_step. rewrite inverse_step.
      rewrite ? inverse_union. ii. des.
      * exploit VRN; eauto.
      * inv EID. inv REL. inv H0.
        exploit EX2.(LABELS); eauto; ss.
        { rewrite List.app_length. s. lia. }
        rewrite List.nth_error_app2, Nat.sub_diag; ss. i. inv x0. inv LABEL.
      * inv EID. inv REL. inv H. inv H1. inv H. inv H2. inv H3.
        exploit EX2.(LABELS); eauto; ss.
        { rewrite List.app_length. s. lia. }
        { rewrite List.nth_error_app2, Nat.sub_diag; ss. i. inv x1. inv LABEL. }
    + move VWN at bottom. des.
      inv WRITABLE. inv COHMAX.
      eexists (ValA.val (sem_expr rmap1 eloc)). split.
      { i. funtac. specialize (MAX loc). inv MAX. unfold le in *. lia. }
      funtac.
      rewrite sim_local_vwn_step. rewrite inverse_step.
      rewrite ? inverse_union. ii. des.
      * exploit VWN0; eauto. i.
        specialize (MAX mloc). inv MAX. unfold le in *. lia.
      * inv EID. inv REL. inv H0.
        exploit EX2.(LABELS); eauto; ss.
        { rewrite List.app_length. s. lia. }
        rewrite List.nth_error_app2, Nat.sub_diag; ss. i. simplify.
        rewrite EX2.(XVEXT); cycle 1.
        { ss. rewrite List.app_length. ss. clear. lia. }
        destruct (length (ALocal.labels alc1) =? ALocal.next_eid alc1) eqn:Heq; cycle 1.
        { rewrite Nat.eqb_neq in Heq. unfold ALocal.next_eid in Heq. ss. }
        funtac.
    + intro. rewrite Promises.unset_o. condtac; ss. i.
      exploit PROMISES; eauto. i. des. esplits; cycle 1; eauto.
      inv N.
      * exfalso. apply c.
        rewrite EX2.(XVEXT); cycle 1.
        { ss. rewrite List.app_length. ss. clear. lia. }
        destruct (length (ALocal.labels alc1) =? ALocal.next_eid alc1) eqn:Heq; cycle 1.
        { rewrite Nat.eqb_neq in Heq. unfold ALocal.next_eid in Heq. ss. }
        rewrite fun_add_spec.
        destruct (equiv_dec (ValA.val (sem_expr rmap1 eloc)) (ValA.val (sem_expr rmap1 eloc))) eqn:Heq1; ss.
        exfalso. apply c0. ss.
      * clear -H. lia.
    + move COH_CL at bottom. intro loc. specialize (COH_CL loc). des.
      destruct (Loc.cl loc (ValA.val (sem_expr rmap1 eloc))) eqn:H_CL; cycle 1.
      { exists mloc_cl. splits; ss.
        - i. funtac.
          + inversion e. subst.
            eapply Loc.cl_sym in CL0. exploit Loc.cl_trans; try exact CL; eauto.
            rewrite H_CL. ss.
          + inversion e. subst.
            rewrite H_CL in CL. ss.
        - rewrite sim_local_coh_cl_step. rewrite inverse_step.
          rewrite ? inverse_union. ii. des.
          { exploit COH_CL; eauto. intro X. rewrite X.
            funtac. inversion e. subst. rewrite H_CL in CL. ss.
          }
          inv EID. obtac. inv H0; cycle 1.
          { inv H. exploit RF2; eauto. i. des. obtac. labtac.
            exploit EX2.(LABELS); eauto; ss.
            { rewrite List.app_length. s. lia. }
            rewrite List.nth_error_app2, Nat.sub_diag; ss. i. simplify. ss.
          }
          exploit EX2.(LABELS); eauto; ss.
          { rewrite List.app_length. s. lia. }
          rewrite List.nth_error_app2, Nat.sub_diag; ss. i. simplify. ss.
          inv VLOC. rewrite VAL0 in *.
          rewrite H_CL in *. ss.
      }
      inv WRITABLE. inv COHMAX.
      exists (ValA.val (sem_expr rmap1 eloc)). splits; ss.
      { i. funtac. specialize (MAX loc0). inv MAX. unfold le in *. lia. }
      funtac.
      rewrite sim_local_coh_cl_step. rewrite inverse_step.
      rewrite ? inverse_union. ii. des.
      { exploit COH_CL; eauto. i.
        specialize (MAX mloc_cl). inv MAX. unfold le in *. lia.
      }
      inv EID. obtac. inv H0; cycle 1.
      { inv H. exploit RF2; eauto. i. des. obtac. labtac.
        exploit EX2.(LABELS); eauto; ss.
        { rewrite List.app_length. s. lia. }
        rewrite List.nth_error_app2, Nat.sub_diag; ss. i. simplify. ss.
      }
      exploit EX2.(LABELS); eauto; ss.
      { rewrite List.app_length. s. lia. }
      rewrite List.nth_error_app2, Nat.sub_diag; ss. i. simplify.
      rewrite EX2.(XVEXT); cycle 1.
      { ss. rewrite List.app_length. ss. clear. lia. }
      destruct (length (ALocal.labels alc1) =? ALocal.next_eid alc1) eqn:Heq; cycle 1.
      { rewrite Nat.eqb_neq in Heq. unfold ALocal.next_eid in Heq. ss. }
      funtac.
    + i. rewrite sim_local_vpr_step. rewrite inverse_step.
      rewrite inverse_union. ii. des; [exploit VPR; eauto|].
      inv EID. obtac.
      all: exploit EX2.(LABELS); eauto; ss.
      all: try by rewrite List.app_length; s; lia.
      all: try rewrite List.nth_error_app2, Nat.sub_diag; ss.
      all: destruct l; ss.
    + i. rewrite sim_local_vpa_step. rewrite inverse_step.
      rewrite inverse_union. ii. des; [apply VPA|]; eauto.
      inv EID. obtac.
      all: exploit EX2.(LABELS); eauto; ss.
      all: try by rewrite List.app_length; s; lia.
      all: rewrite List.nth_error_app2, Nat.sub_diag; ss.
      all: destruct l; ss.
    + i. rewrite sim_local_vpc_step. rewrite inverse_step.
      rewrite inverse_union. ii. des; [apply VPC|]; eauto.
      inv EID. obtac.
      all: exploit EX2.(LABELS); eauto; ss.
      all: try by rewrite List.app_length; s; lia.
      all: try rewrite List.nth_error_app2, Nat.sub_diag; ss; i; simplify; ss.
  - (* rmw *)
    exploit sim_trace_sim_th; try exact TRACE; eauto. intro TH_tmp.
    exploit lastn_sub_S1; try exact EU; eauto. intro TRT. des.
    exploit TH_tmp; eauto.
    { instantiate (1 := l1 ++ [eu2]). rewrite <- List.app_assoc. rewrite EU2. ss. }
    clear TH_tmp. intro SIM_TH.
    generalize STEP0. intro STEP0'. inv STEP0'.
    inv ASTATE_STEP; inv ALOCAL_STEP; ss; inv EVENT; ss. splits.
    { econs; ss. inv RMAP. apply L. }
    destruct L.(LC). ss. econs; ss.
    all: try rewrite List.app_length, Nat.add_1_r.
    + i. rewrite sim_local_coh_step. rewrite inverse_step.
      rewrite inverse_union. rewrite fun_add_spec. condtac.
      { ii. des.
        - inv EID. inv WRITABLE.
          apply Nat.lt_le_incl. eapply Nat.le_lt_trans; try eapply EXT.
          etrans; try apply COH0; eauto.
          inv COHMAX. specialize (MAX loc). inv MAX. unfold le in *. ss.
        - inv EID. inv REL. des. inv H. inv H2. inv H0.
          + exploit EX2.(LABELS); eauto; ss.
            { rewrite List.app_length. s. lia. }
            rewrite List.nth_error_app2, Nat.sub_diag; ss. i.
            destruct l; ss. inv x0.
            rewrite EX2.(XVEXT); cycle 1.
            { ss. rewrite List.app_length. ss. clear. lia. }
            condtac; cycle 1.
            { rewrite Nat.eqb_neq in X0. unfold ALocal.next_eid in X0. ss. }
            rewrite fun_add_spec. condtac; ss.
            exfalso. apply c. ss.
          + (* rfe *)
            inv H. exploit RF2; eauto. i. des.
            destruct x as [tid1 eid1]. ss.
            inv WRITE. inv READ. rename EID0 into WRITE.
            unfold Execution.label in WRITE. ss.
            rewrite PRE.(Valid.LABELS) in WRITE.
            rewrite IdMap.map_spec in WRITE.
            destruct (IdMap.find tid1 (Valid.aeus PRE)) eqn:FIND1; ss.
            generalize (ATR tid1). intro ATR1. inv ATR1; try congr. des. simplify.
            generalize (SIM tid1). intro SIM1. inv SIM1; simplify.
            exploit sim_trace_last; try exact REL0. i. des. simplify.
            exploit sim_trace_sim_th; try exact REL0; eauto. intro TH_tmp.
            exploit TH_tmp; eauto.
            { instantiate (1 := []). ss. }
            clear TH_tmp. intro L1.
            rewrite RF in H0. inv H0. ss. simplify.
            exploit WPROP3; eauto. i. des. simplify.
            unfold v_gen. ss. rewrite <- H9. rewrite x2.
            exploit EX2.(XR); eauto.
            { instantiate (1 := ALocal.next_eid alc1).
              ss. rewrite List.app_length. ss. unfold ALocal.next_eid. clear. lia. }
            condtac; cycle 1.
            { rewrite Nat.eqb_neq in X0. ss. }
            rewrite fun_add_spec. condtac; cycle 1.
            { exfalso. apply c. ss. }
            i. unfold ALocal.next_eid in *.
            rewrite R in x7. inv x7.
            etrans.
            { apply Memory.latest_ts_spec. }
            unfold le. lia.
      }
      ii. des; [apply COH0|]; eauto.
      inv EID. inv REL. inv H. inv H0. inv H2. inv H1.
      * exploit EX2.(LABELS); eauto; ss.
        { rewrite List.app_length. s. lia. }
        rewrite List.nth_error_app2, Nat.sub_diag; ss. i.
        inv x0. inv VLOC. inv LABEL. eqvtac.
        symmetry in VAL. ss.
      * inv H. exploit RF2; eauto. i. des.
        inv WRITE. inv READ.
        rename EID0 into WRITE. rewrite EID in WRITE. inv WRITE.
        exploit EX2.(LABELS); eauto; ss.
        { rewrite List.app_length. s. lia. }
        rewrite List.nth_error_app2, Nat.sub_diag; ss. i.
        inv x1. inv VLOC. inv LABEL1. eqvtac.
        assert (LOC: loc = (ValA.val (sem_expr armap2 eloc))); eauto with tso.
        congr.
    + rewrite sim_local_vrn_step. rewrite inverse_step.
      rewrite ? inverse_union. ii. des.
      * exploit VRN; eauto. i. rewrite <- join_l. ss.
      * inv EID. inv REL. inv H0.
        exploit EX2.(LABELS); eauto; ss.
        { rewrite List.app_length. s. lia. }
        rewrite List.nth_error_app2, Nat.sub_diag; ss. i. inv x0.
        rewrite <- join_r.
        rewrite EX2.(XVEXT); cycle 1.
        { ss. rewrite List.app_length. ss. unfold ALocal.next_eid. clear. lia. }
        destruct (length (ALocal.labels alc1) =? ALocal.next_eid alc1) eqn:Heq; ss.
        -- rewrite fun_add_spec. condtac; ss.
           exfalso. apply c. ss.
        -- rewrite Nat.eqb_neq in Heq. ss.
      * inv EID. inv REL. inv H. inv H1. inv H. inv H2. inv H3.
        exploit EX2.(LABELS); eauto; ss.
        { rewrite List.app_length. s. lia. }
        { rewrite List.nth_error_app2, Nat.sub_diag; ss. i. inv x1. inv LABEL. }
    + move VWN at bottom. des.
      inv WRITABLE. inv COHMAX.
      eexists (ValA.val (sem_expr rmap2 eloc)). split.
      { i. funtac. specialize (MAX loc). inv MAX. unfold le in *. lia. }
      funtac.
      rewrite sim_local_vwn_step. rewrite inverse_step.
      rewrite ? inverse_union. ii. des.
      * exploit VWN0; eauto. i.
        specialize (MAX mloc). inv MAX. unfold le in *. lia.
      * inv EID. inv REL. inv H0.
        exploit EX2.(LABELS); eauto; ss.
        { rewrite List.app_length. s. lia. }
        rewrite List.nth_error_app2, Nat.sub_diag; ss. i. simplify.
        rewrite EX2.(XVEXT); cycle 1.
        { ss. rewrite List.app_length. ss. clear. lia. }
        destruct (length (ALocal.labels alc1) =? ALocal.next_eid alc1) eqn:Heq; cycle 1.
        { rewrite Nat.eqb_neq in Heq. unfold ALocal.next_eid in Heq. ss. }
        funtac.
    + intro. rewrite Promises.unset_o. condtac; ss. i.
      exploit PROMISES; eauto. i. des. esplits; cycle 1; eauto.
      inv N.
      * exfalso. apply c.
        rewrite EX2.(XVEXT); cycle 1.
        { ss. rewrite List.app_length. ss. clear. lia. }
        destruct (length (ALocal.labels alc1) =? ALocal.next_eid alc1) eqn:Heq; cycle 1.
        { rewrite Nat.eqb_neq in Heq. unfold ALocal.next_eid in Heq. ss. }
        rewrite fun_add_spec. condtac; ss.
        exfalso. apply c0. ss.
      * clear -H. lia.
    + move COH_CL at bottom. intro loc. specialize (COH_CL loc). des.
      destruct (Loc.cl loc (ValA.val (sem_expr rmap2 eloc))) eqn:H_CL; cycle 1.
      { exists mloc_cl. splits; ss.
        - i. funtac.
          + inversion e. subst.
            eapply Loc.cl_sym in CL0. exploit Loc.cl_trans; try exact CL; eauto.
            rewrite H_CL. ss.
          + inversion e. subst.
            rewrite H_CL in CL. ss.
        - rewrite sim_local_coh_cl_step. rewrite inverse_step.
          rewrite ? inverse_union. ii. des.
          { exploit COH_CL; eauto. intro X. rewrite X.
            funtac. inversion e. subst. rewrite H_CL in CL. ss.
          }
          inv EID. obtac. inv H0.
          + exploit EX2.(LABELS); eauto; ss.
            { rewrite List.app_length. s. lia. }
            rewrite List.nth_error_app2, Nat.sub_diag; ss. i. simplify. ss.
            inv VLOC. rewrite VAL in *.
            rewrite H_CL in *. ss.
          + inv H. exploit RF2; eauto. i. des. obtac. labtac.
            exploit EX2.(LABELS); eauto; ss.
            { rewrite List.app_length. s. lia. }
            rewrite List.nth_error_app2, Nat.sub_diag; ss. i. simplify. ss. eqvtac.
            inv VLOC. rewrite VAL in *.
            destruct l0; ss; eqvtac; rewrite H_CL in *; ss.
      }
      inv WRITABLE. inv COHMAX.
      exists (ValA.val (sem_expr rmap2 eloc)). splits; ss.
      { i. funtac. specialize (MAX loc0). inv MAX. unfold le in *. lia. }
      funtac.
      rewrite sim_local_coh_cl_step. rewrite inverse_step.
      rewrite ? inverse_union. ii. des.
      { exploit COH_CL; eauto. i.
        specialize (MAX mloc_cl). inv MAX. unfold le in *. lia.
      }
      inv EID. obtac. inv H0.
      * exploit EX2.(LABELS); eauto; ss.
        { rewrite List.app_length. s. lia. }
        rewrite List.nth_error_app2, Nat.sub_diag; ss. i. simplify.
        rewrite EX2.(XVEXT); cycle 1.
        { ss. rewrite List.app_length. ss. clear. lia. }
        destruct (length (ALocal.labels alc1) =? ALocal.next_eid alc1) eqn:Heq; cycle 1.
        { rewrite Nat.eqb_neq in Heq. unfold ALocal.next_eid in Heq. ss. }
        funtac.
      * inv H. exploit RF2; eauto. i. des.
        destruct x0 as [tid1 eid1]. ss.
        inv WRITE. inv READ. rename EID0 into WRITE.
        unfold Execution.label in WRITE. ss.
        rewrite PRE.(Valid.LABELS) in WRITE.
        rewrite IdMap.map_spec in WRITE.
        destruct (IdMap.find tid1 (Valid.aeus PRE)) eqn:FIND1; ss.
        generalize (ATR tid1). intro ATR1. inv ATR1; try congr. des. simplify.
        generalize (SIM tid1). intro SIM1. inv SIM1; simplify.
        exploit sim_trace_last; try exact REL0. i. des. simplify.
        exploit sim_trace_sim_th; try exact REL0; eauto. intro TH_tmp.
        exploit TH_tmp; eauto.
        { instantiate (1 := []). ss. }
        clear TH_tmp. intro L1.
        rewrite RF in H0. inv H0. ss. simplify.
        exploit WPROP3; eauto. i. des. simplify.
        unfold v_gen. ss. rewrite <- H9. rewrite x2.
        exploit EX2.(XR); eauto.
        { instantiate (1 := ALocal.next_eid alc1).
          ss. rewrite List.app_length. ss. unfold ALocal.next_eid. clear. lia. }
        condtac; cycle 1.
        { rewrite Nat.eqb_neq in X. ss. }
        rewrite fun_add_spec. condtac; cycle 1.
        { exfalso. apply c. ss. }
        i. unfold ALocal.next_eid in *.
        rewrite R in x8. inv x8.
        etrans.
        { apply Memory.latest_ts_spec. }
        unfold le. lia.
    + i. rewrite sim_local_vpr_step. rewrite inverse_step.
      rewrite ? inverse_union. ii. inv EID.
      { exploit VPR; eauto. i. rewrite <- join_l. ss. }
      des.
      { inv H. obtac.
        exploit EX2.(LABELS); eauto; ss.
        { rewrite List.app_length. s. lia. }
        rewrite List.nth_error_app2, Nat.sub_diag; ss. i. inv x0.
        rewrite EX2.(XVEXT); cycle 1.
        { ss. rewrite List.app_length. ss. unfold ALocal.next_eid. clear. lia. }
        destruct (length (ALocal.labels alc1) =? ALocal.next_eid alc1) eqn:Heq; cycle 1.
        { rewrite Nat.eqb_neq in Heq. ss. }
        funtac. apply join_r.
      }
      all: inv H; obtac.
      all: exploit EX2.(LABELS); eauto; ss.
      all: try by rewrite List.app_length; s; lia.
      all: try by rewrite List.nth_error_app2, Nat.sub_diag; ss; i; simplify; ss.
    + i. rewrite sim_local_vpa_step. rewrite inverse_step.
      rewrite inverse_union. ii. des; [apply VPA|]; eauto.
      inv EID. obtac.
      all: exploit EX2.(LABELS); eauto; ss.
      all: try by rewrite List.app_length; s; lia.
      all: rewrite List.nth_error_app2, Nat.sub_diag; ss.
      all: destruct l; ss.
    + i. rewrite sim_local_vpc_step. rewrite inverse_step.
      rewrite ? inverse_union. ii. des.
      * exploit VPC; eauto. i. rewrite <- join_l. ss.
      * inv EID. inv REL. obtac.
        exploit EX2.(LABELS); eauto; ss.
        { rewrite List.app_length. s. lia. }
        rewrite List.nth_error_app2, Nat.sub_diag; ss. i. inv x0. inv LABEL.
      * inv EID. inv REL. obtac.
        rewrite <- join_r. inv L. inv LC. ss. apply VPA0. econs; eauto.
  - (* rmw_failure *)
    exploit sim_trace_sim_th; try exact TRACE; eauto. intro TH_tmp.
    exploit lastn_sub_S1; try exact EU; eauto. intro TRT. des.
    exploit TH_tmp; eauto.
    { instantiate (1 := l1 ++ [eu2]). rewrite <- List.app_assoc. rewrite EU2. ss. }
    clear TH_tmp. intro SIM_TH.
    destruct SIM_TH.(EU_WF). ss.
    generalize (Local.rmw_failure_spec LOCAL STEP0). intro READ_SPEC.
    generalize SIM_TH.(MEM). s. i. rewrite H in READ_SPEC.
    guardH READ_SPEC. clear H.
    inv STEP0. inv ASTATE_STEP; inv ALOCAL_STEP; ss; inv EVENT; ss. splits.
    { econs; ss. inv RMAP. apply L. }
    destruct L.(LC). ss. econs; ss.
    all: try rewrite List.app_length, Nat.add_1_r.
    + i. rewrite sim_local_coh_step. rewrite inverse_step.
      rewrite inverse_union. rewrite fun_add_spec. condtac.
      { ii. des.
        { etrans; try eapply COH0; eauto. rewrite e. ss. }
        inv EID. inv REL. des. inv H. inv H2. inv H0.
        - exploit EX2.(LABELS); eauto; ss.
          { rewrite List.app_length. s. lia. }
          rewrite List.nth_error_app2, Nat.sub_diag; ss.
          destruct l; ss.
        - (* rfe *)
          inv H. exploit RF2; eauto. i. des.
          destruct x as [tid1 eid1]. ss.
          inv WRITE. inv READ. rename EID0 into WRITE.
          unfold Execution.label in WRITE. ss.
          rewrite PRE.(Valid.LABELS) in WRITE.
          rewrite IdMap.map_spec in WRITE.
          destruct (IdMap.find tid1 (Valid.aeus PRE)) eqn:FIND1; ss.
          generalize (ATR tid1). intro ATR1. inv ATR1; try congr. des. simplify.
          generalize (SIM tid1). intro SIM1. inv SIM1; simplify.
          exploit sim_trace_last; try exact REL0. i. des. simplify.
          exploit sim_trace_sim_th; try exact REL0; eauto. intro TH_tmp.
          exploit TH_tmp; eauto.
          { instantiate (1 := []). ss. }
          clear TH_tmp. intro L1.
          rewrite RF in H0. inv H0. ss. simplify.
          exploit WPROP3; eauto. i. des. simplify.
          unfold v_gen. ss. rewrite <- H9. rewrite x2.
          exploit EX2.(XR); eauto.
          { instantiate (1 := ALocal.next_eid alc1).
            ss. rewrite List.app_length. ss. unfold ALocal.next_eid. clear. lia. }
          condtac; cycle 1.
          { rewrite Nat.eqb_neq in X0. ss. }
          funtac.
          i. unfold ALocal.next_eid in *.
          rewrite R in x7. inv x7. ss.
      }
      ii. des; [apply COH0|]; eauto.
      inv EID. inv REL. inv H. inv H0. inv H2. inv H1.
      * exploit EX2.(LABELS); eauto; ss.
        { rewrite List.app_length. s. lia. }
        rewrite List.nth_error_app2, Nat.sub_diag; ss.
        destruct l; ss.
      * inv H. exploit RF2; eauto. i. des.
        inv WRITE. inv READ.
        rename EID0 into WRITE. rewrite EID in WRITE. inv WRITE.
        exploit EX2.(LABELS); eauto; ss.
        { rewrite List.app_length. s. lia. }
        rewrite List.nth_error_app2, Nat.sub_diag; ss. i.
        inv x1. inv VLOC. inv LABEL1. eqvtac.
        assert (LOC: loc = (ValA.val (sem_expr armap2 eloc))); eauto with tso.
        congr.
    + rewrite sim_local_vrn_step. rewrite inverse_step.
      rewrite ? inverse_union. ii. des.
      * exploit VRN; eauto. i. rewrite <- join_l. ss.
      * inv EID. inv REL. inv H0.
        exploit EX2.(LABELS); eauto; ss.
        { rewrite List.app_length. s. lia. }
        rewrite List.nth_error_app2, Nat.sub_diag; ss. i. inv x0.
        rewrite EX2.(XVEXT); cycle 1.
        { ss. rewrite List.app_length. ss. unfold ALocal.next_eid. clear. lia. }
        destruct (length (ALocal.labels alc1) =? ALocal.next_eid alc1) eqn:Heq; ss.
        rewrite Nat.eqb_neq in Heq. ss.
      * inv EID. inv REL. inv H. inv H1. inv H. inv H2. inv H3.
        exploit EX2.(LABELS); eauto; ss.
        { rewrite List.app_length. s. lia. }
        { rewrite List.nth_error_app2, Nat.sub_diag; ss. i. inv x1. inv LABEL. }
    + move VWN at bottom. des.
      inversion LOCAL. inv COHMAX. inv COHMAX0.
      destruct (lt_eq_lt_dec old_ts (View.ts (Local.coh lc1 mloc))).
      { (* <= *)
        exists mloc. split.
        - i. funtac.
          + viewtac. inv s; ss; lia.
          + inversion e. subst.
            rewrite VWN. ss.
        - rewrite sim_local_vwn_step. rewrite inverse_step.
          rewrite ? inverse_union.
          ii. des; ss.
          + etrans; try eapply VWN0; eauto.
            rewrite fun_add_spec. condtac; ss.
            inversion e. ss.
          + inv EID. inv REL. inv H0.
            exploit EX2.(LABELS); eauto; ss.
            { rewrite List.app_length. s. lia. }
            rewrite List.nth_error_app2, Nat.sub_diag; ss. i. inv x1.
            rewrite EX2.(XVEXT); cycle 1.
            { ss. rewrite List.app_length. ss. unfold ALocal.next_eid. clear. lia. }
            destruct (length (ALocal.labels alc1) =? ALocal.next_eid alc1) eqn:Heq; ss; cycle 1.
            { rewrite Nat.eqb_neq in Heq. ss. }
            unfold le. specialize (VWN x).
            funtac.
            * viewtac.
              { inversion e. subst. unfold le in *. lia. }
              unfold Local.read_view. condtac; ss. apply bot_spec.
            * viewtac; [lia |].
              rewrite Local.fwd_read_view_le; eauto. inv s; lia.
      }
      { (* > *)
        exploit Local.high_ts_spec; eauto.
        { i. eapply le_lt_trans; try exact l; eauto. }
        i. des.
        eexists (ValA.val (sem_expr rmap2 eloc)). split.
        { i. funtac. specialize (VWN loc). lia. }
        rewrite sim_local_vwn_step. rewrite inverse_step.
        rewrite ? inverse_union.
        ii. des; ss.
        - etrans; try eapply VWN0; eauto.
          rewrite fun_add_spec. condtac; ss; cycle 1.
          { exfalso. apply c. ss. }
          unfold le. lia.
        - inv EID. inv REL. inv H0.
          exploit EX2.(LABELS); eauto; ss.
          { rewrite List.app_length. s. lia. }
          rewrite List.nth_error_app2, Nat.sub_diag; ss. i. inv x1.
          rewrite EX2.(XVEXT); cycle 1.
          { ss. rewrite List.app_length. ss. unfold ALocal.next_eid. clear. lia. }
          destruct (length (ALocal.labels alc1) =? ALocal.next_eid alc1) eqn:Heq; ss; cycle 1.
          { rewrite Nat.eqb_neq in Heq. ss. }
          unfold le. specialize (VWN x).
          funtac. viewtac.
          { unfold le in *. lia. }
          unfold Local.read_view. condtac; ss. apply bot_spec.
      }
    + i. exploit PROMISES; eauto. i. des. esplits; cycle 1; eauto.
      inv N.
      * inv WRITE. exploit EX2.(LABELS); eauto; ss.
        { rewrite List.app_length. s. lia. }
        rewrite List.nth_error_app2, Nat.sub_diag; ss.
        destruct l; ss.
      * clear -H. lia.
    + move COH_CL at bottom. i. specialize (COH_CL loc). des.
      destruct (Loc.cl loc (ValA.val (sem_expr rmap2 eloc))) eqn:H_CL; cycle 1.
      { exists mloc_cl. splits; ss.
        - i. funtac.
          + inversion e. subst.
            eapply Loc.cl_sym in CL0. exploit Loc.cl_trans; try exact CL; eauto.
            rewrite H_CL. ss.
          + inversion e. subst.
            rewrite H_CL in CL. ss.
        - rewrite sim_local_coh_cl_step. rewrite inverse_step.
          rewrite ? inverse_union. ii. des.
          { exploit COH_CL; eauto. intro X. rewrite X.
            funtac. inversion e. subst. rewrite H_CL in CL. ss.
          }
          inv EID. obtac. inv H0.
          { exploit EX2.(LABELS); eauto; ss.
            { rewrite List.app_length. s. lia. }
            rewrite List.nth_error_app2, Nat.sub_diag; ss. i. inv x0. ss.
          }
          inv H. exploit RF2; eauto. i. des. obtac. labtac.
          exploit EX2.(LABELS); eauto; ss.
          { rewrite List.app_length. s. lia. }
          rewrite List.nth_error_app2, Nat.sub_diag; ss. i.
          inv x1. inv VLOC. rewrite VAL0 in *.
          inv LABEL1. eqvtac.
          destruct l0; ss; eqvtac; rewrite H_CL in *; ss.
      }
      destruct (lt_eq_lt_dec old_ts (View.ts (Local.coh lc1 mloc_cl))).
      { (* <= *)
        exists mloc_cl. splits; ss.
        - i. funtac.
          + viewtac. inv s; ss; lia.
          + apply COH_MAX_CL in CL0.
            inversion e. subst. unfold le in *. inv s; lia.
        - rewrite sim_local_coh_cl_step. rewrite inverse_step.
          rewrite ? inverse_union.
          ii. des; ss.
          + etrans; try eapply COH_CL; eauto.
            funtac. inversion e. ss.
          + inv EID. obtac. inv H0.
            { exploit EX2.(LABELS); eauto; ss.
              { rewrite List.app_length. s. lia. }
              rewrite List.nth_error_app2, Nat.sub_diag; ss. i. inv x0. ss.
            }
            inv H. exploit RF2; eauto. i. des. obtac. labtac.
            destruct x as [tid1 eid1]. rename EID into WRITE.
            unfold Execution.label in WRITE. ss.
            rewrite PRE.(Valid.LABELS) in WRITE.
            rewrite IdMap.map_spec in WRITE.
            destruct (IdMap.find tid1 (Valid.aeus PRE)) eqn:FIND1; ss.
            generalize (ATR tid1). intro ATR1. inv ATR1; try congr. des. simplify.
            generalize (SIM tid1). intro SIM1. inv SIM1; simplify.
            exploit sim_trace_last; try exact REL0. i. des. simplify.
            exploit sim_trace_sim_th; try exact REL0; eauto. intro TH_tmp.
            exploit TH_tmp; eauto.
            { instantiate (1 := []). ss. }
            clear TH_tmp. intro L1.
            rewrite RF in H0. inv H0. ss. simplify.
            exploit WPROP3; eauto. i. des. simplify.
            rewrite WRITE in x4. simplify.
            unfold v_gen. ss. rewrite <- H9. rewrite x2.
            exploit EX2.(XR); eauto.
            { instantiate (1 := ALocal.next_eid alc1).
              ss. rewrite List.app_length. ss. unfold ALocal.next_eid. clear. lia.
            }
            condtac; cycle 1.
            { rewrite Nat.eqb_neq in X. ss. }
            funtac.
            { unfold ALocal.next_eid. intro Z. rewrite R in Z. simplify. ss. }
            unfold ALocal.next_eid. intro Z. rewrite R in Z. simplify.
            unfold le. inv s; lia.
      }
      { (* > *)
        exploit Local.high_ts_spec_cl; eauto.
        { i. eapply le_lt_trans; try exact l; eauto. }
        i. des.
        eexists (ValA.val (sem_expr rmap2 eloc)). splits; ss.
        - i. funtac. rewrite COH_MAX_CL; try lia.
          eapply Loc.cl_trans; eauto. eapply Loc.cl_trans; eauto. eapply Loc.cl_sym. ss.
        - rewrite sim_local_coh_cl_step. rewrite inverse_step.
          rewrite ? inverse_union.
          ii. des; ss.
          + etrans; try eapply COH_CL; eauto.
            funtac. unfold le. lia.
          + inv EID. obtac. inv H0.
            { exploit EX2.(LABELS); eauto; ss.
              { rewrite List.app_length. s. lia. }
              rewrite List.nth_error_app2, Nat.sub_diag; ss. i. inv x0. ss.
            }
            inv H. exploit RF2; eauto. i. des. obtac. labtac.
            destruct x as [tid1 eid1]. rename EID into WRITE.
            unfold Execution.label in WRITE. ss.
            rewrite PRE.(Valid.LABELS) in WRITE.
            rewrite IdMap.map_spec in WRITE.
            destruct (IdMap.find tid1 (Valid.aeus PRE)) eqn:FIND1; ss.
            generalize (ATR tid1). intro ATR1. inv ATR1; try congr. des. simplify.
            generalize (SIM tid1). intro SIM1. inv SIM1; simplify.
            exploit sim_trace_last; try exact REL0. i. des. simplify.
            exploit sim_trace_sim_th; try exact REL0; eauto. intro TH_tmp.
            exploit TH_tmp; eauto.
            { instantiate (1 := []). ss. }
            clear TH_tmp. intro L1.
            rewrite RF in H0. inv H0. ss. simplify.
            exploit WPROP3; eauto. i. des. simplify.
            rewrite WRITE in x4. simplify.
            unfold v_gen. ss. rewrite <- H9. rewrite x2.
            exploit EX2.(XR); eauto.
            { instantiate (1 := ALocal.next_eid alc1).
              ss. rewrite List.app_length. ss. unfold ALocal.next_eid. clear. lia.
            }
            condtac; cycle 1.
            { rewrite Nat.eqb_neq in X. ss. }
            funtac.
            unfold ALocal.next_eid. intro Z. rewrite R in Z. simplify. ss.
      }
    + i. rewrite sim_local_vpr_step. rewrite inverse_step.
      rewrite ? inverse_union. ii. des.
      * exploit VPR; eauto. i. rewrite <- join_l. ss.
      * inv EID. inv REL. inv H0.
        exploit EX2.(LABELS); eauto; ss.
        { rewrite List.app_length. s. lia. }
        rewrite List.nth_error_app2, Nat.sub_diag; ss. i. inv x0.
        rewrite EX2.(XVEXT); cycle 1.
        { ss. rewrite List.app_length. ss. unfold ALocal.next_eid. clear. lia. }
        destruct (length (ALocal.labels alc1) =? ALocal.next_eid alc1) eqn:Heq; cycle 1.
        { rewrite Nat.eqb_neq in Heq. ss. }
        apply join_spec; [rewrite <- join_l | rewrite <- join_r]; ss.
        inv LOCAL. rewrite VRNVPR. ss.
      * inv EID. inv REL. obtac. destruct l; ss.
        all: exploit EX2.(LABELS); eauto; ss.
        all: try by rewrite List.app_length; s; lia.
        all: rewrite List.nth_error_app2, Nat.sub_diag; ss.
        intro X. inv X. ss.
    + i. rewrite sim_local_vpa_step. rewrite inverse_step.
      rewrite inverse_union. ii. des; [apply VPA|]; eauto.
      inv EID. obtac.
      all: exploit EX2.(LABELS); eauto; ss.
      all: try by rewrite List.app_length; s; lia.
      all: rewrite List.nth_error_app2, Nat.sub_diag; ss.
      all: destruct l; ss.
    + i. rewrite sim_local_vpc_step. rewrite inverse_step.
      rewrite inverse_union. ii. des; [apply VPC|]; eauto.
      inv EID. obtac.
      all: exploit EX2.(LABELS); eauto; ss.
      all: try by rewrite List.app_length; s; lia.
      all: try rewrite List.nth_error_app2, Nat.sub_diag; ss; i; simplify; ss.
  - (* mfence *)
    inv STEP0. inv ASTATE_STEP; inv ALOCAL_STEP; ss; inv EVENT; ss; cycle 1.
    { destruct b; ss. destruct wr; ss. }
    splits. econs; ss.
    { econs; ss. apply L. }
    destruct L.(LC). ss. econs; ss.
    + rewrite List.app_length, Nat.add_1_r.
      i. rewrite sim_local_coh_step. rewrite inverse_step.
      rewrite inverse_union. ii. des; [apply COH|]; eauto.
      inv EID. inv REL. inv H. inv H0. inv H2. inv H1.
      * exploit EX2.(LABELS); eauto; ss.
        { rewrite List.app_length. s. lia. }
        rewrite List.nth_error_app2, Nat.sub_diag; ss.
        destruct l; ss.
      * inv H. exploit RF2; eauto. i. des.
        inv WRITE. inv READ.
        rename EID0 into WRITE. rewrite EID in WRITE. inv WRITE.
        exploit EX2.(LABELS); eauto; ss.
        { rewrite List.app_length. s. lia. }
        rewrite List.nth_error_app2, Nat.sub_diag; ss.
        destruct l1; ss.
    + rewrite List.app_length, Nat.add_1_r.
      i. rewrite sim_local_vrn_step. rewrite inverse_step.
      rewrite ? inverse_union. ii. des.
      * exploit VRN; eauto. i. rewrite <- join_l. ss.
      * inv EID. inv REL. inv H0.
        exploit EX2.(LABELS); eauto; ss.
        { rewrite List.app_length. s. lia. }
        rewrite List.nth_error_app2, Nat.sub_diag; ss. i. inv x0. inv LABEL.
      * inv EID. obtac.
        exploit EX2.(LABELS); eauto; ss.
        { rewrite List.app_length. s. lia. }
        rewrite List.nth_error_app2, Nat.sub_diag; ss. i. simplify.
        destruct l; ss.
        -- rewrite <- join_l. apply L. econs; eauto.
           left. simtac.
        -- rewrite <- join_r.
           inv COHMAX. specialize (MAX loc). inv MAX. unfold le in *. rewrite <- TS.
           apply L. econs; eauto.
           econs. split; [| econs]; econs; eauto with tso.
        -- rewrite <- join_r.
           inv COHMAX. specialize (MAX loc). inv MAX. unfold le in *. rewrite <- TS.
           apply L. econs; eauto.
           econs. split; [| econs]; econs; eauto with tso.
    + move VWN at bottom. des.
      eexists mloc. split; ss.
      rewrite List.app_length, Nat.add_1_r.
      i. rewrite sim_local_vwn_step. rewrite inverse_step.
      rewrite ? inverse_union. ii. des; eauto.
      inv EID. inv REL. inv H0.
      exploit EX2.(LABELS); eauto; ss.
      { rewrite List.app_length. s. lia. }
      rewrite List.nth_error_app2, Nat.sub_diag; ss. i. inv x0. inv LABEL.
    + i. exploit PROMISES; eauto. i. des. esplits; cycle 1; eauto.
      rewrite List.app_length, Nat.add_1_r. inv N.
      * inv WRITE. exploit EX2.(LABELS); eauto; ss.
        { rewrite List.app_length. s. lia. }
        rewrite List.nth_error_app2, Nat.sub_diag; ss.
        destruct l; ss.
      * clear -H. lia.
    + move COH_CL at bottom.
      intro loc. specialize (COH_CL loc). des.
      eexists mloc_cl. splits; ss.
      rewrite List.app_length, Nat.add_1_r.
      rewrite sim_local_coh_cl_step. rewrite inverse_step.
      rewrite ? inverse_union. ii. des; eauto.
      inv EID. obtac. inv H0.
      * exploit EX2.(LABELS); eauto; ss.
        { rewrite List.app_length. s. lia. }
        rewrite List.nth_error_app2, Nat.sub_diag; ss.
        destruct l; ss.
      * inv H. exploit RF2; eauto. i. des.
        inv WRITE. inv READ.
        rename EID0 into WRITE. rewrite EID in WRITE. inv WRITE.
        exploit EX2.(LABELS); eauto; ss.
        { rewrite List.app_length. s. lia. }
        rewrite List.nth_error_app2, Nat.sub_diag; ss.
        destruct l1; ss.
    + rewrite List.app_length, Nat.add_1_r.
      i. rewrite sim_local_vpr_step. rewrite inverse_step.
      rewrite ? inverse_union. ii. des.
      * exploit VPR; eauto. i. rewrite <- join_l. ss.
      * inv EID. obtac.
        exploit EX2.(LABELS); eauto; ss.
        { rewrite List.app_length. s. lia. }
        rewrite List.nth_error_app2, Nat.sub_diag; ss. i. inv x0. inv LABEL.
      * inv EID. obtac.
        all: exploit EX2.(LABELS); eauto; ss.
        all: try by rewrite List.app_length; s; lia.
        all: rewrite List.nth_error_app2, Nat.sub_diag; ss; i; simplify; ss; cycle 1.
        { destruct b; ss. destruct wr; ss. }
        destruct (Label.is_kinda_read l0) eqn:READ.
        { rewrite <- join_l. apply L. econs; eauto. left. simtac. }
        destruct l0; ss.
        rewrite <- join_r.
        inv COHMAX. specialize (MAX loc). inv MAX. unfold le in *. rewrite <- TS.
        apply L. econs; eauto. econs. simtac.
    + rewrite List.app_length, Nat.add_1_r.
      i. rewrite sim_local_vpa_step. rewrite inverse_step.
      rewrite inverse_union. ii. des; [apply VPA|]; eauto.
      inv EID. obtac.
      all: exploit EX2.(LABELS); eauto; ss.
      all: try by rewrite List.app_length; s; lia.
      all: rewrite List.nth_error_app2, Nat.sub_diag; ss.
      all: destruct l; ss.
    + rewrite List.app_length, Nat.add_1_r.
      i. rewrite sim_local_vpc_step. rewrite inverse_step.
      rewrite ? inverse_union. ii. des.
      * exploit VPC; eauto. i. rewrite <- join_l. ss.
      * inv EID. inv REL. obtac.
        exploit EX2.(LABELS); eauto; ss.
        { rewrite List.app_length. s. lia. }
        rewrite List.nth_error_app2, Nat.sub_diag; ss. i. inv x0. inv LABEL.
      * inv EID. inv REL. obtac.
        rewrite <- join_r. inv L. inv LC. ss. apply VPA0. econs; eauto.
  - (* sfence *)
    inv STEP0. inv ASTATE_STEP; inv ALOCAL_STEP; ss; inv EVENT; ss.
    { destruct b; ss. destruct wr; ss. }
    splits. econs; ss.
    { econs; ss. apply L. }
    destruct L.(LC). ss. econs; ss.
    + rewrite List.app_length, Nat.add_1_r.
      i. rewrite sim_local_coh_step. rewrite inverse_step.
      rewrite inverse_union. ii. des; [apply COH|]; eauto.
      inv EID. inv REL. inv H. inv H0. inv H2. inv H1.
      * exploit EX2.(LABELS); eauto; ss.
        { rewrite List.app_length. s. lia. }
        rewrite List.nth_error_app2, Nat.sub_diag; ss.
        destruct l; ss.
      * inv H. exploit RF2; eauto. i. des.
        inv WRITE. inv READ.
        rename EID0 into WRITE. rewrite EID in WRITE. inv WRITE.
        exploit EX2.(LABELS); eauto; ss.
        { rewrite List.app_length. s. lia. }
        rewrite List.nth_error_app2, Nat.sub_diag; ss.
        destruct l1; ss.
    + rewrite List.app_length, Nat.add_1_r.
      i. rewrite sim_local_vrn_step. rewrite inverse_step.
      rewrite ? inverse_union. ii. des.
      * exploit VRN; eauto.
      * inv EID. inv REL. inv H0.
        exploit EX2.(LABELS); eauto; ss.
        { rewrite List.app_length. s. lia. }
        rewrite List.nth_error_app2, Nat.sub_diag; ss. i. inv x0. inv LABEL.
      * inv EID. obtac.
        exploit EX2.(LABELS); eauto; ss.
        { rewrite List.app_length. s. lia. }
        rewrite List.nth_error_app2, Nat.sub_diag; ss. i. simplify.
        destruct b; ss. destruct wr; ss.
    + move VWN at bottom. des.
      eexists mloc. split; ss.
      rewrite List.app_length, Nat.add_1_r.
      i. rewrite sim_local_vwn_step. rewrite inverse_step.
      rewrite ? inverse_union. ii. des; eauto.
      inv EID. inv REL. inv H0.
      exploit EX2.(LABELS); eauto; ss.
      { rewrite List.app_length. s. lia. }
      rewrite List.nth_error_app2, Nat.sub_diag; ss. i. inv x0. inv LABEL.
    + i. exploit PROMISES; eauto. i. des. esplits; cycle 1; eauto.
      rewrite List.app_length, Nat.add_1_r. inv N.
      * inv WRITE. exploit EX2.(LABELS); eauto; ss.
        { rewrite List.app_length. s. lia. }
        rewrite List.nth_error_app2, Nat.sub_diag; ss.
        destruct l; ss.
      * clear -H. lia.
    + move COH_CL at bottom.
      intro loc. specialize (COH_CL loc). des.
      eexists mloc_cl. splits; ss.
      rewrite List.app_length, Nat.add_1_r.
      rewrite sim_local_coh_cl_step. rewrite inverse_step.
      rewrite ? inverse_union. ii. des; eauto.
      inv EID. obtac. inv H0.
      * exploit EX2.(LABELS); eauto; ss.
        { rewrite List.app_length. s. lia. }
        rewrite List.nth_error_app2, Nat.sub_diag; ss.
        destruct l; ss.
      * inv H. exploit RF2; eauto. i. des.
        inv WRITE. inv READ.
        rename EID0 into WRITE. rewrite EID in WRITE. inv WRITE.
        exploit EX2.(LABELS); eauto; ss.
        { rewrite List.app_length. s. lia. }
        rewrite List.nth_error_app2, Nat.sub_diag; ss.
        destruct l1; ss.
    + rewrite List.app_length, Nat.add_1_r.
      i. rewrite sim_local_vpr_step. rewrite inverse_step.
      rewrite ? inverse_union. ii. des.
      * exploit VPR; eauto. i. rewrite <- join_l. ss.
      * inv EID. obtac.
        exploit EX2.(LABELS); eauto; ss.
        { rewrite List.app_length. s. lia. }
        rewrite List.nth_error_app2, Nat.sub_diag; ss. i. inv x0. inv LABEL.
      * inv EID. obtac.
        all: exploit EX2.(LABELS); eauto; ss.
        all: try by rewrite List.app_length; s; lia.
        all: rewrite List.nth_error_app2, Nat.sub_diag; ss; i; simplify; ss.
        { destruct b; ss. destruct wr; ss. }
        destruct (Label.is_kinda_read l0) eqn:READ.
        { rewrite <- join_l. apply L. econs; eauto. left. simtac. }
        destruct l0; ss.
        rewrite <- join_r.
        inv COHMAX. specialize (MAX loc). inv MAX. unfold le in *. rewrite <- TS.
        apply L. econs; eauto. econs. simtac.
    + rewrite List.app_length, Nat.add_1_r.
      i. rewrite sim_local_vpa_step. rewrite inverse_step.
      rewrite inverse_union. ii. des; [apply VPA|]; eauto.
      inv EID. obtac.
      all: exploit EX2.(LABELS); eauto; ss.
      all: try by rewrite List.app_length; s; lia.
      all: rewrite List.nth_error_app2, Nat.sub_diag; ss.
      all: destruct l; ss.
    + rewrite List.app_length, Nat.add_1_r.
      i. rewrite sim_local_vpc_step. rewrite inverse_step.
      rewrite ? inverse_union. ii. des.
      * exploit VPC; eauto. i. rewrite <- join_l. ss.
      * inv EID. inv REL. obtac.
        exploit EX2.(LABELS); eauto; ss.
        { rewrite List.app_length. s. lia. }
        rewrite List.nth_error_app2, Nat.sub_diag; ss. i. inv x0. inv LABEL.
      * inv EID. inv REL. obtac.
        rewrite <- join_r. inv L. inv LC. ss. apply VPA0. econs; eauto.
  - (* dowhile *)
    inv ASTATE_STEP; inv ALOCAL_STEP; ss; inv EVENT; ss. splits.
    + econs; ss; try by apply L.
    + econs; ss; try by apply L.
  - (* flushopt *)
    exploit sim_trace_sim_th; try exact TRACE; eauto. intro TH_tmp.
    exploit lastn_sub_S1; try exact EU; eauto. intro TRT. des.
    exploit TH_tmp; eauto.
    { instantiate (1 := l1 ++ [eu2]). rewrite <- List.app_assoc. rewrite EU2. ss. }
    clear TH_tmp. intro SIM_TH.
    destruct SIM_TH.(EU_WF). ss.
    inv STEP0. inv ASTATE_STEP; inv ALOCAL_STEP; ss; inv EVENT; ss. splits.
    econs; ss.
    { econs; ss. apply L. }
    destruct L.(LC). ss. econs; ss.
    all: try rewrite List.app_length, Nat.add_1_r.
    + i. rewrite sim_local_coh_step. rewrite inverse_step.
      rewrite inverse_union. ii. des; [apply COH|]; eauto.
      inv EID. inv REL. inv H. inv H0. inv H2. inv H1.
      * exploit EX2.(LABELS); eauto; ss.
        { rewrite List.app_length. s. lia. }
        rewrite List.nth_error_app2, Nat.sub_diag; ss.
        destruct l; ss.
      * inv H. exploit RF2; eauto. i. des.
        inv WRITE. inv READ.
        rename EID0 into WRITE. rewrite EID in WRITE. inv WRITE.
        exploit EX2.(LABELS); eauto; ss.
        { rewrite List.app_length. s. lia. }
        rewrite List.nth_error_app2, Nat.sub_diag; ss.
        destruct l2; ss.
    + rewrite sim_local_vrn_step. rewrite inverse_step.
      rewrite ? inverse_union. ii. des.
      * exploit VRN; eauto.
      * inv EID. inv REL. inv H0.
        exploit EX2.(LABELS); eauto; ss.
        { rewrite List.app_length. s. lia. }
        rewrite List.nth_error_app2, Nat.sub_diag; ss. i. inv x0. inv LABEL.
      * inv EID. inv REL. inv H. inv H1. inv H. inv H2. inv H3.
        exploit EX2.(LABELS); eauto; ss.
        { rewrite List.app_length. s. lia. }
        { rewrite List.nth_error_app2, Nat.sub_diag; ss. i. inv x1. inv LABEL. }
    + move VWN at bottom. des.
      esplits; eauto.
      rewrite sim_local_vwn_step. rewrite inverse_step.
      rewrite ? inverse_union. ii. des; eauto.
      inv EID. inv REL. inv H0.
      exploit EX2.(LABELS); eauto; ss.
      { rewrite List.app_length. s. lia. }
      rewrite List.nth_error_app2, Nat.sub_diag; ss. i. inv x0. ss.
    + i. exploit PROMISES; eauto. i. des. esplits; cycle 1; eauto.
      inv N.
      * inv WRITE. exploit EX2.(LABELS); eauto; ss.
        { rewrite List.app_length. s. lia. }
        rewrite List.nth_error_app2, Nat.sub_diag; ss.
        destruct l; ss.
      * clear -H. lia.
    + move COH_CL at bottom.
      intro loc. specialize (COH_CL loc). des.
      eexists mloc_cl. splits; ss.
      rewrite sim_local_coh_cl_step. rewrite inverse_step.
      rewrite ? inverse_union. ii. des; eauto.
      inv EID. obtac. inv H0.
      * exploit EX2.(LABELS); eauto; ss.
        { rewrite List.app_length. s. lia. }
        rewrite List.nth_error_app2, Nat.sub_diag; ss.
        destruct l; ss.
      * inv H. exploit RF2; eauto. i. des.
        inv WRITE. inv READ.
        rename EID0 into WRITE. rewrite EID in WRITE. inv WRITE.
        exploit EX2.(LABELS); eauto; ss.
        { rewrite List.app_length. s. lia. }
        rewrite List.nth_error_app2, Nat.sub_diag; ss.
        destruct l2; ss.
    + i. rewrite sim_local_vpr_step. rewrite inverse_step.
      rewrite inverse_union. ii. des; [apply VPR|]; eauto.
      inv EID. obtac.
      all: exploit EX2.(LABELS); eauto; ss.
      all: try by rewrite List.app_length; s; lia.
      all: try rewrite List.nth_error_app2, Nat.sub_diag; ss.
      all: destruct l; ss.
    + i. rewrite sim_local_vpa_step. rewrite inverse_step.
      rewrite inverse_union. ii. des.
      * inv EID.
        rewrite <- join_l.
        inv L. inv LC. ss. apply VPA0. econs; eauto.
      * inv EID. obtac.
        all: exploit EX2.(LABELS); eauto; ss.
        all: try by rewrite List.app_length; s; lia.
        all: try rewrite List.nth_error_app2, Nat.sub_diag; ss.
        all: i; simplify; ss.
        rewrite EX2.(XVEXT); cycle 1.
        { ss. rewrite List.app_length. ss. unfold ALocal.next_eid. clear. lia. }
        condtac; cycle 1.
        { rewrite Nat.eqb_neq in *. ss. }
        inv VLOC. rewrite VAL.
        unfold ifc. rewrite Loc.cl_refl. rewrite Loc.cl_sym; ss.
        inv LOCAL. exploit VPACL; eauto. intro Z. rewrite Z. ss.
    + i. rewrite sim_local_vpc_step. rewrite inverse_step.
      rewrite inverse_union. ii. des; [apply VPC|]; eauto.
      inv EID. obtac.
      all: exploit EX2.(LABELS); eauto; ss.
      all: try by rewrite List.app_length; s; lia.
      all: try rewrite List.nth_error_app2, Nat.sub_diag; ss; i; simplify; ss.
  - (* flush *)
    exploit sim_trace_sim_th; try exact TRACE; eauto. intro TH_tmp.
    exploit lastn_sub_S1; try exact EU; eauto. intro TRT. des.
    exploit TH_tmp; eauto.
    { instantiate (1 := l1 ++ [eu2]). rewrite <- List.app_assoc. rewrite EU2. ss. }
    clear TH_tmp. intro SIM_TH.
    destruct SIM_TH.(EU_WF). ss.
    inv STEP0. inv ASTATE_STEP; inv ALOCAL_STEP; ss; inv EVENT; ss. splits.
    econs; ss.
    { econs; ss. apply L. }
    destruct L.(LC). ss. econs; ss.
    all: try rewrite List.app_length, Nat.add_1_r.
    + i. rewrite sim_local_coh_step. rewrite inverse_step.
      rewrite inverse_union. ii. des; [apply COH|]; eauto.
      inv EID. inv REL. inv H. inv H0. inv H2. inv H1.
      * exploit EX2.(LABELS); eauto; ss.
        { rewrite List.app_length. s. lia. }
        rewrite List.nth_error_app2, Nat.sub_diag; ss.
        destruct l; ss.
      * inv H. exploit RF2; eauto. i. des.
        inv WRITE. inv READ.
        rename EID0 into WRITE. rewrite EID in WRITE. inv WRITE.
        exploit EX2.(LABELS); eauto; ss.
        { rewrite List.app_length. s. lia. }
        rewrite List.nth_error_app2, Nat.sub_diag; ss.
        destruct l2; ss.
    + rewrite sim_local_vrn_step. rewrite inverse_step.
      rewrite ? inverse_union. ii. des.
      * exploit VRN; eauto.
      * inv EID. inv REL. inv H0.
        exploit EX2.(LABELS); eauto; ss.
        { rewrite List.app_length. s. lia. }
        rewrite List.nth_error_app2, Nat.sub_diag; ss. i. inv x0. inv LABEL.
      * inv EID. inv REL. inv H. inv H1. inv H. inv H2. inv H3.
        exploit EX2.(LABELS); eauto; ss.
        { rewrite List.app_length. s. lia. }
        { rewrite List.nth_error_app2, Nat.sub_diag; ss. i. inv x1. inv LABEL. }
    + move VWN at bottom. des.
      esplits; eauto.
      rewrite sim_local_vwn_step. rewrite inverse_step.
      rewrite ? inverse_union. ii. des; eauto.
      inv EID. inv REL. inv H0.
      exploit EX2.(LABELS); eauto; ss.
      { rewrite List.app_length. s. lia. }
      rewrite List.nth_error_app2, Nat.sub_diag; ss. i. inv x0. ss.
    + i. exploit PROMISES; eauto. i. des. esplits; cycle 1; eauto.
      inv N.
      * inv WRITE. exploit EX2.(LABELS); eauto; ss.
        { rewrite List.app_length. s. lia. }
        rewrite List.nth_error_app2, Nat.sub_diag; ss.
        destruct l; ss.
      * clear -H. lia.
    + move COH_CL at bottom.
      intro loc. specialize (COH_CL loc). des.
      eexists mloc_cl. splits; ss.
      rewrite sim_local_coh_cl_step. rewrite inverse_step.
      rewrite ? inverse_union. ii. des; eauto.
      inv EID. obtac. inv H0.
      * exploit EX2.(LABELS); eauto; ss.
        { rewrite List.app_length. s. lia. }
        rewrite List.nth_error_app2, Nat.sub_diag; ss.
        destruct l; ss.
      * inv H. exploit RF2; eauto. i. des.
        inv WRITE. inv READ.
        rename EID0 into WRITE. rewrite EID in WRITE. inv WRITE.
        exploit EX2.(LABELS); eauto; ss.
        { rewrite List.app_length. s. lia. }
        rewrite List.nth_error_app2, Nat.sub_diag; ss.
        destruct l2; ss.
    + i. rewrite sim_local_vpr_step. rewrite inverse_step.
      rewrite inverse_union. ii. des; [apply VPR|]; eauto.
      inv EID. obtac.
      all: exploit EX2.(LABELS); eauto; ss.
      all: try by rewrite List.app_length; s; lia.
      all: try rewrite List.nth_error_app2, Nat.sub_diag; ss.
      all: destruct l; ss.
    + i. rewrite sim_local_vpa_step. rewrite inverse_step.
      rewrite inverse_union. ii. des.
      { exploit VPA; eauto. rewrite <- join_l. ss. }
      inv EID. obtac.
      all: exploit EX2.(LABELS); eauto; ss.
      all: try by rewrite List.app_length; s; lia.
      all: try rewrite List.nth_error_app2, Nat.sub_diag; ss.
      all: i; simplify; ss.
      rewrite EX2.(XVEXT); cycle 1.
      { ss. rewrite List.app_length. ss. unfold ALocal.next_eid. clear. lia. }
      condtac; cycle 1.
      { rewrite Nat.eqb_neq in *. ss. }
      unfold ifc. inv VLOC. rewrite VAL.
      rewrite Loc.cl_refl. rewrite Loc.cl_sym; ss.
      inv LOCAL. inv COHMAX0.
      inv COHMAX. inv COHMAX1. specialize (MAX x0). inv MAX. unfold le in *.
      viewtac; rewrite <- join_r; ss.
      rewrite VPC1. ss.
    + i. rewrite sim_local_vpc_step. rewrite inverse_step.
      rewrite inverse_union. ii. des.
      { exploit VPC; eauto. i. rewrite <- join_l. ss. }
      inv EID. inv REL; cycle 1.
      { obtac.
        exploit EX2.(LABELS); eauto; ss.
        { rewrite List.app_length. s. lia. }
        rewrite List.nth_error_app2, Nat.sub_diag; ss. i. simplify. ss.
      }
      obtac.
      exploit EX2.(LABELS); eauto; ss.
      { rewrite List.app_length. s. lia. }
      rewrite List.nth_error_app2, Nat.sub_diag; ss. i. inv x0.
      rewrite EX2.(XVEXT); cycle 1.
      { ss. rewrite List.app_length. ss. unfold ALocal.next_eid. clear. lia. }
      condtac; cycle 1.
      { rewrite Nat.eqb_neq in *. ss. }
      ss. eqvtac. inv VLOC. rewrite VAL.
      unfold ifc. rewrite Loc.cl_refl. rewrite Loc.cl_sym; ss.
      inv LOCAL. exploit VPCCL; eauto. intro Z. rewrite Z. ss.
Qed.
