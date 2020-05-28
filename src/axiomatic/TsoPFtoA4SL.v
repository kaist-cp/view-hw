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


Lemma sim_traces_sim_th'_sl
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

  destruct eu1 as [[stmts1 rmap1] lc1 mem1].
  destruct eu2 as [[stmts2 rmap2] lc2 mem2].
  destruct aeu1 as [[astmts1 armap1] alc1].
  destruct aeu2 as [[astmts2 armap2] alc2].
  ss. inv STEP0. ss. subst.
  inv STATE. inv STATE1. ss. subst.
  inv STATE0; inv LOCAL0; ss; inv EVENT0; inv EVENT; ss.
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
    exploit sim_trace_sim_th; try exact TRACE; eauto. intro SIM_TH.
    destruct SIM_TH.(EU_WF). ss.
    generalize (Local.read_spec LOCAL0 STEP0). intro READ_SPEC.
    generalize SIM_TH.(MEM). s. i. rewrite H in READ_SPEC.
    guardH READ_SPEC. clear LOCAL0 H.
    inv STEP0. inv ASTATE_STEP; inv ALOCAL_STEP; ss; inv EVENT; ss. splits.
    { econs; ss. apply sim_rmap_add; try apply L.
      inv VAL. ss.
    }
    destruct L.(LC). ss. econs; ss.
    all: try rewrite List.app_length, Nat.add_1_r.
    + i. rewrite sim_local_coh_step. rewrite inverse_step.
      rewrite inverse_union. rewrite fun_add_spec. condtac.
      { ii. des.
        - inv EID. etrans; try eapply COH0; eauto. rewrite e.
          apply Memory.latest_ts_mon. unfold join. ss. apply join_l.
        - inv EID. inv REL. des. inv H. inv H2.
          destruct l; ss.
          all: inv LABEL; destruct (equiv_dec loc0 loc); ss; inv e0; clear H1.
          { (* write *)
            inv H0; cycle 1.
            - (* rfe *)
              inv H. exploit RF2; eauto. i. des.
              destruct x as [tid1 eid1]. ss.
              inv WRITE. inv READ. destruct l; destruct l0; ss; eqvtac.
              all: clear LABEL LABEL0.
              all: rename EID0 into WRITE.
              + (* write -> read *)
                unfold Execution.label in WRITE. ss.
                rewrite PRE.(Valid.LABELS) in WRITE.
                rewrite IdMap.map_spec in WRITE.
                destruct (IdMap.find tid1 (Valid.aeus PRE)) eqn:FIND1; ss.
                generalize (ATR tid1). intro ATR1. inv ATR1; try congr. des. simplify.
                generalize (SIM tid1). intro SIM1. inv SIM1; simplify.
                exploit sim_trace_last; try exact REL0. i. des. simplify.
                exploit sim_trace_sim_th; try exact REL0; eauto. intro L1.
                rewrite RF in H0. inv H0. ss. simplify.
                exploit WPROP3; eauto. i. des. simplify.
                unfold v_gen. ss. rewrite <- H8. rewrite x2.
                exploit EX2.(XR); eauto.
                { instantiate (1 := ALocal.next_eid alc1).
                  ss. rewrite List.app_length. ss. unfold ALocal.next_eid. clear. lia. }
                condtac; cycle 1.
                { rewrite Nat.eqb_neq in X0. ss. }
                rewrite fun_add_spec. condtac; cycle 1.
                { exfalso. apply c. ss. }
                i. unfold ALocal.next_eid in *.
                rewrite R in x7. inv x7. rewrite e. ss.
              + (* write -> update *)
                unfold Execution.label in WRITE. ss.
                rewrite PRE.(Valid.LABELS) in WRITE.
                rewrite IdMap.map_spec in WRITE.
                destruct (IdMap.find tid1 (Valid.aeus PRE)) eqn:FIND1; ss.
                generalize (ATR tid1). intro ATR1. inv ATR1; try congr. des. simplify.
                generalize (SIM tid1). intro SIM1. inv SIM1; simplify.
                exploit sim_trace_last; try exact REL0. i. des. simplify.
                exploit sim_trace_sim_th; try exact REL0; eauto. intro L1.
                rewrite RF in H0. inv H0. ss. simplify.
                exploit WPROP3; eauto. i. des. simplify.
                unfold v_gen. ss. rewrite <- H8. rewrite x2.
                exploit EX2.(XR); eauto.
                { instantiate (1 := ALocal.next_eid alc1).
                  ss. rewrite List.app_length. ss. unfold ALocal.next_eid. clear. lia. }
                condtac; cycle 1.
                { rewrite Nat.eqb_neq in X0. ss. }
                rewrite fun_add_spec. condtac; cycle 1.
                { exfalso. apply c. ss. }
                i. unfold ALocal.next_eid in *.
                rewrite R in x7. inv x7. rewrite e. ss.
              + (* update -> read *)
                unfold Execution.label in WRITE. ss.
                rewrite PRE.(Valid.LABELS) in WRITE.
                rewrite IdMap.map_spec in WRITE.
                destruct (IdMap.find tid1 (Valid.aeus PRE)) eqn:FIND1; ss.
                generalize (ATR tid1). intro ATR1. inv ATR1; try congr. des. simplify.
                generalize (SIM tid1). intro SIM1. inv SIM1; simplify.
                exploit sim_trace_last; try exact REL0. i. des. simplify.
                exploit sim_trace_sim_th; try exact REL0; eauto. intro L1.
                rewrite RF in H0. inv H0. ss. simplify.
                exploit WPROP3; eauto. i. des. simplify.
                unfold v_gen. ss. rewrite <- H8. rewrite x2.
                exploit EX2.(XR); eauto.
                { instantiate (1 := ALocal.next_eid alc1).
                  ss. rewrite List.app_length. ss. unfold ALocal.next_eid. clear. lia. }
                condtac; cycle 1.
                { rewrite Nat.eqb_neq in X0. ss. }
                rewrite fun_add_spec. condtac; cycle 1.
                { exfalso. apply c. ss. }
                i. unfold ALocal.next_eid in *.
                rewrite R in x7. inv x7. rewrite e. ss.
              + (* update -> update *)
                unfold Execution.label in WRITE. ss.
                rewrite PRE.(Valid.LABELS) in WRITE.
                rewrite IdMap.map_spec in WRITE.
                destruct (IdMap.find tid1 (Valid.aeus PRE)) eqn:FIND1; ss.
                generalize (ATR tid1). intro ATR1. inv ATR1; try congr. des. simplify.
                generalize (SIM tid1). intro SIM1. inv SIM1; simplify.
                exploit sim_trace_last; try exact REL0. i. des. simplify.
                exploit sim_trace_sim_th; try exact REL0; eauto. intro L1.
                rewrite RF in H0. inv H0. ss. simplify.
                exploit WPROP3; eauto. i. des. simplify.
                unfold v_gen. ss. rewrite <- H8. rewrite x2.
                exploit EX2.(XR); eauto.
                { instantiate (1 := ALocal.next_eid alc1).
                  ss. rewrite List.app_length. ss. unfold ALocal.next_eid. clear. lia. }
                condtac; cycle 1.
                { rewrite Nat.eqb_neq in X0. ss. }
                rewrite fun_add_spec. condtac; cycle 1.
                { exfalso. apply c. ss. }
                i. unfold ALocal.next_eid in *.
                rewrite R in x7. inv x7. rewrite e. ss.
            - exploit EX2.(LABELS); eauto; ss.
              { rewrite List.app_length. s. lia. }
              rewrite List.nth_error_app2, Nat.sub_diag; ss.
          }
          { (* update *)
            inv H0; cycle 1.
            - (* rfe *)
              inv H. exploit RF2; eauto. i. des.
              destruct x as [tid1 eid1]. ss.
              inv WRITE. inv READ. destruct l; destruct l0; ss; eqvtac.
              all: clear LABEL LABEL0.
              all: rename EID0 into WRITE.
              + (* write -> read *)
                unfold Execution.label in WRITE. ss.
                rewrite PRE.(Valid.LABELS) in WRITE.
                rewrite IdMap.map_spec in WRITE.
                destruct (IdMap.find tid1 (Valid.aeus PRE)) eqn:FIND1; ss.
                generalize (ATR tid1). intro ATR1. inv ATR1; try congr. des. simplify.
                generalize (SIM tid1). intro SIM1. inv SIM1; simplify.
                exploit sim_trace_last; try exact REL0. i. des. simplify.
                exploit sim_trace_sim_th; try exact REL0; eauto. intro L1.
                rewrite RF in H0. inv H0. ss. simplify.
                exploit WPROP3; eauto. i. des. simplify.
                unfold v_gen. ss. rewrite <- H8. rewrite x2.
                exploit EX2.(XR); eauto.
                { instantiate (1 := ALocal.next_eid alc1).
                  ss. rewrite List.app_length. ss. unfold ALocal.next_eid. clear. lia. }
                condtac; cycle 1.
                { rewrite Nat.eqb_neq in X0. ss. }
                rewrite fun_add_spec. condtac; cycle 1.
                { exfalso. apply c. ss. }
                i. unfold ALocal.next_eid in *.
                rewrite R in x7. inv x7. rewrite e. ss.
              + (* write -> update *)
                unfold Execution.label in WRITE. ss.
                rewrite PRE.(Valid.LABELS) in WRITE.
                rewrite IdMap.map_spec in WRITE.
                destruct (IdMap.find tid1 (Valid.aeus PRE)) eqn:FIND1; ss.
                generalize (ATR tid1). intro ATR1. inv ATR1; try congr. des. simplify.
                generalize (SIM tid1). intro SIM1. inv SIM1; simplify.
                exploit sim_trace_last; try exact REL0. i. des. simplify.
                exploit sim_trace_sim_th; try exact REL0; eauto. intro L1.
                rewrite RF in H0. inv H0. ss. simplify.
                exploit WPROP3; eauto. i. des. simplify.
                unfold v_gen. ss. rewrite <- H8. rewrite x2.
                exploit EX2.(XR); eauto.
                { instantiate (1 := ALocal.next_eid alc1).
                  ss. rewrite List.app_length. ss. unfold ALocal.next_eid. clear. lia. }
                condtac; cycle 1.
                { rewrite Nat.eqb_neq in X0. ss. }
                rewrite fun_add_spec. condtac; cycle 1.
                { exfalso. apply c. ss. }
                i. unfold ALocal.next_eid in *.
                rewrite R in x7. inv x7. rewrite e. ss.
              + (* update -> read *)
                unfold Execution.label in WRITE. ss.
                rewrite PRE.(Valid.LABELS) in WRITE.
                rewrite IdMap.map_spec in WRITE.
                destruct (IdMap.find tid1 (Valid.aeus PRE)) eqn:FIND1; ss.
                generalize (ATR tid1). intro ATR1. inv ATR1; try congr. des. simplify.
                generalize (SIM tid1). intro SIM1. inv SIM1; simplify.
                exploit sim_trace_last; try exact REL0. i. des. simplify.
                exploit sim_trace_sim_th; try exact REL0; eauto. intro L1.
                rewrite RF in H0. inv H0. ss. simplify.
                exploit WPROP3; eauto. i. des. simplify.
                unfold v_gen. ss. rewrite <- H8. rewrite x2.
                exploit EX2.(XR); eauto.
                { instantiate (1 := ALocal.next_eid alc1).
                  ss. rewrite List.app_length. ss. unfold ALocal.next_eid. clear. lia. }
                condtac; cycle 1.
                { rewrite Nat.eqb_neq in X0. ss. }
                rewrite fun_add_spec. condtac; cycle 1.
                { exfalso. apply c. ss. }
                i. unfold ALocal.next_eid in *.
                rewrite R in x7. inv x7. rewrite e. ss.
              + (* update -> update *)
                unfold Execution.label in WRITE. ss.
                rewrite PRE.(Valid.LABELS) in WRITE.
                rewrite IdMap.map_spec in WRITE.
                destruct (IdMap.find tid1 (Valid.aeus PRE)) eqn:FIND1; ss.
                generalize (ATR tid1). intro ATR1. inv ATR1; try congr. des. simplify.
                generalize (SIM tid1). intro SIM1. inv SIM1; simplify.
                exploit sim_trace_last; try exact REL0. i. des. simplify.
                exploit sim_trace_sim_th; try exact REL0; eauto. intro L1.
                rewrite RF in H0. inv H0. ss. simplify.
                exploit WPROP3; eauto. i. des. simplify.
                unfold v_gen. ss. rewrite <- H8. rewrite x2.
                exploit EX2.(XR); eauto.
                { instantiate (1 := ALocal.next_eid alc1).
                  ss. rewrite List.app_length. ss. unfold ALocal.next_eid. clear. lia. }
                condtac; cycle 1.
                { rewrite Nat.eqb_neq in X0. ss. }
                rewrite fun_add_spec. condtac; cycle 1.
                { exfalso. apply c. ss. }
                i. unfold ALocal.next_eid in *.
                rewrite R in x7. inv x7. rewrite e. ss.
            - exploit EX2.(LABELS); eauto; ss.
              { rewrite List.app_length. s. lia. }
              rewrite List.nth_error_app2, Nat.sub_diag; ss.
          }
      }
      ii. des; [apply COH0|]; eauto.
      inv EID. inv REL. inv H. inv H0. inv H2.
      destruct l; ss.
      all: inv LABEL; destruct (equiv_dec loc0 loc); ss; inv e; clear H0.
      { (* write *)
        inv H1.
        - exploit EX2.(LABELS); eauto; ss.
          { rewrite List.app_length. s. lia. }
          rewrite List.nth_error_app2, Nat.sub_diag; ss.
        - inv H. exploit RF2; eauto. i. des.
          inv WRITE. inv READ. destruct l; destruct l0; ss; eqvtac.
          all: rename EID0 into WRITE.
          all: try rewrite EID in WRITE; inv WRITE.
          + exploit EX2.(LABELS); eauto; ss.
            { rewrite List.app_length. s. lia. }
            rewrite List.nth_error_app2, Nat.sub_diag; ss. i. inv x1.
            inv VLOC. congr.
          + exploit EX2.(LABELS); eauto; ss.
            { rewrite List.app_length. s. lia. }
            rewrite List.nth_error_app2, Nat.sub_diag; ss.
      }
      { (* update *)
        inv H1.
        - exploit EX2.(LABELS); eauto; ss.
          { rewrite List.app_length. s. lia. }
          rewrite List.nth_error_app2, Nat.sub_diag; ss.
        - inv H. exploit RF2; eauto. i. des.
          inv WRITE. inv READ. destruct l; destruct l0; ss; eqvtac.
          all: rename EID0 into WRITE.
          all: try rewrite EID in WRITE; inv WRITE.
          + exploit EX2.(LABELS); eauto; ss.
            { rewrite List.app_length. s. lia. }
            rewrite List.nth_error_app2, Nat.sub_diag; ss. i. inv x1.
            inv VLOC. congr.
          + exploit EX2.(LABELS); eauto; ss.
            { rewrite List.app_length. s. lia. }
            rewrite List.nth_error_app2, Nat.sub_diag; ss.
      }
    + i. rewrite sim_local_vrn_step. rewrite inverse_step.
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
    + i. rewrite sim_local_vwn_step. rewrite inverse_step.
      rewrite ? inverse_union. ii. des.
      * exploit VWN; eauto. i. rewrite <- join_l. ss.
      * inv EID. inv REL. inv H0.
        exploit EX2.(LABELS); eauto; ss.
        { rewrite List.app_length. s. lia. }
        rewrite List.nth_error_app2, Nat.sub_diag; ss. i. inv x0.
        rewrite EX2.(XVEXT); cycle 1.
        { ss. rewrite List.app_length. ss. unfold ALocal.next_eid. clear. lia. }
        destruct (length (ALocal.labels alc1) =? ALocal.next_eid alc1) eqn:Heq; ss.
        -- unfold le. unfold join. unfold Time.join. lia.
        -- rewrite Nat.eqb_neq in Heq. ss.
      * inv EID. inv REL. inv H0.
        exploit EX2.(LABELS); eauto; ss.
        { rewrite List.app_length. s. lia. }
        rewrite List.nth_error_app2, Nat.sub_diag; ss. i. inv x0. inv LABEL.
    + i. rewrite sim_local_vro_step. rewrite inverse_step.
      rewrite ? inverse_union. ii. des.
      * exploit VRO; eauto. i. rewrite <- join_l. ss.
      * inv EID. inv REL. inv H0.
        exploit EX2.(LABELS); eauto; ss.
        { rewrite List.app_length. s. lia. }
        rewrite List.nth_error_app2, Nat.sub_diag; ss. i. inv x0.
        rewrite EX2.(XVEXT); cycle 1.
        { ss. rewrite List.app_length. ss. unfold ALocal.next_eid. clear. lia. }
        destruct (length (ALocal.labels alc1) =? ALocal.next_eid alc1) eqn:Heq.
        -- unfold le. unfold join. unfold Time.join. lia.
        -- rewrite Nat.eqb_neq in Heq. ss.
    + i. rewrite sim_local_vwo_step. rewrite inverse_step.
      rewrite ? inverse_union. ii. des.
      * exploit VWO; eauto.
      * inv EID. inv REL. inv H0.
        exploit EX2.(LABELS); eauto; ss.
        { rewrite List.app_length. s. lia. }
        rewrite List.nth_error_app2, Nat.sub_diag; ss. i. inv x0. inv LABEL.
    + i. specialize (FWDBANK loc). des.
      * left. esplits; eauto.
        rewrite sim_local_fwd_step. econs.
        econs; cycle 1.
        { instantiate (1 := (_, _)). econs; ss. }
        left. econs. split; eauto. econs; ss.
        exploit EX2.(LABELS_REV); ss.
        { apply nth_error_last. apply Nat.eqb_eq. ss. }
        i. econs; eauto.
      * right. esplits; eauto.
        i. specialize (FWDBANK0 eid).
        rewrite sim_local_fwd_none_step. rewrite inverse_step.
        ii. inv H. inv REL.
        { apply FWDBANK0. econs; eauto. }
        { inv H. inv H1. exploit EX2.(LABELS); eauto; ss.
          { rewrite List.app_length. s. lia. }
          rewrite List.nth_error_app2, Nat.sub_diag; ss.
          destruct l; ss. }
    + i. exploit PROMISES; eauto. i. des. esplits; cycle 1; eauto.
      inv N.
      * inv WRITE. exploit EX2.(LABELS); eauto; ss.
        { rewrite List.app_length. s. lia. }
        rewrite List.nth_error_app2, Nat.sub_diag; ss.
        destruct l; ss.
      * clear -H. lia.
  - (* write *)
    exploit sim_trace_sim_th; try exact TRACE; eauto. intro SIM_TH.
    inv STEP0. inv ASTATE_STEP; inv ALOCAL_STEP; ss; inv EVENT; inv RES; ss. splits.
    { econs; ss. apply sim_rmap_add; try apply L. econs; ss. }
    destruct L.(LC). ss. econs; ss.
    all: try rewrite List.app_length, Nat.add_1_r.
    + i. rewrite sim_local_coh_step. rewrite inverse_step.
      rewrite inverse_union. rewrite fun_add_spec. condtac.
      { ii. des.
        - inv EID. inv WRITABLE. ss. etrans; cycle 1.
          { eapply Memory.latest_ts_read_le; try refl.
            generalize SIM_TH.(MEM). s. i. subst.
            rewrite e. eapply Memory.get_msg_read; eauto. }
          apply Nat.lt_le_incl.
          eapply Nat.le_lt_trans; try eapply COH0. rewrite <- e.
          etrans; try apply COH; eauto. apply Memory.latest_ts_spec.
        - inv EID. inv REL. des. inv H. inv H2. destruct l; ss.
          all: inv LABEL; destruct (equiv_dec loc0 loc); ss; inv e0; clear H1.
          { (* write *)
            inv H0; cycle 1.
            - inv H. exploit RF2; eauto. i. des.
              inv WRITE. inv READ. destruct l; destruct l0; ss; eqvtac.
              all: rename EID0 into WRITE.
              all: try rewrite EID in WRITE; inv WRITE.
              + exploit EX2.(LABELS); eauto; ss.
                { rewrite List.app_length. s. lia. }
                rewrite List.nth_error_app2, Nat.sub_diag; ss.
              + exploit EX2.(LABELS); eauto; ss.
                { rewrite List.app_length. s. lia. }
                rewrite List.nth_error_app2, Nat.sub_diag; ss.
            - exploit EX2.(LABELS); eauto; ss.
              { rewrite List.app_length. s. lia. }
              rewrite List.nth_error_app2, Nat.sub_diag; ss. i. inv x0.
              rewrite EX2.(XVEXT); cycle 1.
              { ss. rewrite List.app_length. ss. clear. lia. }
              condtac; cycle 1.
              { rewrite Nat.eqb_neq in X0. unfold ALocal.next_eid in X0. ss. }
              rewrite fun_add_spec. condtac; cycle 1.
              { exfalso. apply c. ss. }
              s. eapply Memory.latest_ts_read_le; ss.
              generalize SIM_TH.(MEM). s. i. rewrite H in MSG. rewrite e.
              eapply Memory.get_msg_read; eauto.
          }
          { (* update *)
            inv H0; cycle 1.
            - inv H. exploit RF2; eauto. i. des.
              inv WRITE. inv READ. destruct l; destruct l0; ss; eqvtac.
              all: rename EID0 into WRITE.
              all: try rewrite EID in WRITE; inv WRITE.
              + exploit EX2.(LABELS); eauto; ss.
                { rewrite List.app_length. s. lia. }
                rewrite List.nth_error_app2, Nat.sub_diag; ss.
              + exploit EX2.(LABELS); eauto; ss.
                { rewrite List.app_length. s. lia. }
                rewrite List.nth_error_app2, Nat.sub_diag; ss.
            - exploit EX2.(LABELS); eauto; ss.
              { rewrite List.app_length. s. lia. }
              rewrite List.nth_error_app2, Nat.sub_diag; ss.
          }
      }
      ii. des; [apply COH|]; eauto.
      inv EID. inv REL. inv H. inv H0. inv H2. destruct l; ss.
      all: inv LABEL; destruct (equiv_dec loc0 loc); ss; inv e; clear H0.
      { (* write *)
        inv H1.
        - exploit EX2.(LABELS); eauto; ss.
          { rewrite List.app_length. s. lia. }
          rewrite List.nth_error_app2, Nat.sub_diag; ss. i. inv x0.
          inv VLOC. congr.
        - inv H. exploit RF2; eauto. i. des.
          inv WRITE. inv READ. destruct l; destruct l0; ss; eqvtac.
          all: rename EID0 into WRITE.
          all: try rewrite EID in WRITE; inv WRITE.
          + exploit EX2.(LABELS); eauto; ss.
            { rewrite List.app_length. s. lia. }
            rewrite List.nth_error_app2, Nat.sub_diag; ss.
          + exploit EX2.(LABELS); eauto; ss.
            { rewrite List.app_length. s. lia. }
            rewrite List.nth_error_app2, Nat.sub_diag; ss.
      }
      { (* update *)
        inv H1.
        - exploit EX2.(LABELS); eauto; ss.
          { rewrite List.app_length. s. lia. }
          rewrite List.nth_error_app2, Nat.sub_diag; ss.
        - inv H. exploit RF2; eauto. i. des.
          inv WRITE. inv READ. destruct l; destruct l0; ss; eqvtac.
          all: rename EID0 into WRITE.
          all: try rewrite EID in WRITE; inv WRITE.
          + exploit EX2.(LABELS); eauto; ss.
            { rewrite List.app_length. s. lia. }
            rewrite List.nth_error_app2, Nat.sub_diag; ss.
          + exploit EX2.(LABELS); eauto; ss.
            { rewrite List.app_length. s. lia. }
            rewrite List.nth_error_app2, Nat.sub_diag; ss.
      }
    + i. rewrite sim_local_vrn_step. rewrite inverse_step.
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
    + i. rewrite sim_local_vwn_step. rewrite inverse_step.
      rewrite ? inverse_union. ii. des.
      * exploit VWN; eauto. unfold le in *. i.
        unfold join. unfold Time.join. lia.
      * inv EID. inv REL. inv H0.
        exploit EX2.(LABELS); eauto; ss.
        { rewrite List.app_length. s. lia. }
        { rewrite List.nth_error_app2, Nat.sub_diag; ss. i. inv x0. inv LABEL. }
      * inv EID. inv REL. inv H0.
        exploit EX2.(LABELS); eauto; ss.
        { rewrite List.app_length. s. lia. }
        rewrite List.nth_error_app2, Nat.sub_diag; ss. i. inv x0.
        rewrite <- join_r.
        rewrite EX2.(XVEXT); cycle 1.
        { ss. rewrite List.app_length. ss. clear. lia. }
        destruct (length (ALocal.labels alc1) =? ALocal.next_eid alc1) eqn:Heq; cycle 1.
        { rewrite Nat.eqb_neq in Heq. unfold ALocal.next_eid in Heq. ss. }
        rewrite fun_add_spec.
        destruct (equiv_dec (ValA.val (sem_expr rmap1 eloc)) (ValA.val (sem_expr rmap1 eloc))) eqn:Heq1; ss.
        exfalso. apply c. ss.
    + i. rewrite sim_local_vro_step. rewrite inverse_step.
      rewrite ? inverse_union. ii. des.
      * exploit VRO; eauto.
      * inv EID. inv REL. inv H0.
        exploit EX2.(LABELS); eauto; ss.
        { rewrite List.app_length. s. lia. }
        rewrite List.nth_error_app2, Nat.sub_diag; ss. i. inv x0. inv LABEL.
    + i. rewrite sim_local_vwo_step. rewrite inverse_step.
      rewrite ? inverse_union. ii. des.
      * exploit VWO; eauto. i. rewrite <- join_l. ss.
      * inv EID. inv REL. inv H0.
        exploit EX2.(LABELS); eauto; ss.
        { rewrite List.app_length. s. lia. }
        rewrite List.nth_error_app2, Nat.sub_diag; ss. i. inv x0.
        rewrite <- join_r.
        rewrite EX2.(XVEXT); cycle 1.
        { ss. rewrite List.app_length. ss. clear. lia. }
        destruct (length (ALocal.labels alc1) =? ALocal.next_eid alc1) eqn:Heq; cycle 1.
        { rewrite Nat.eqb_neq in Heq. unfold ALocal.next_eid in Heq. ss. }
        rewrite fun_add_spec.
        destruct (equiv_dec (ValA.val (sem_expr rmap1 eloc)) (ValA.val (sem_expr rmap1 eloc))) eqn:Heq1; ss.
        exfalso. apply c. ss.
    + i. rewrite fun_add_spec. condtac; s.
      { inversion e. subst. left. esplits; eauto.
        - destruct ts; ss. clear. lia.
        - instantiate (1 := (tid, length (ALocal.labels alc1))). econs.
          + econs; ss.
          + exploit EX2.(LABELS_REV); ss.
            { apply nth_error_last. apply Nat.eqb_eq. ss. }
            i. econs; eauto. inv VLOC. rewrite VAL0. apply Label.write_is_writing.
          + i. inv PO. inv PO0. ss. subst. clear -N N0. lia.
        - rewrite EX2.(XVEXT); cycle 1.
          { ss. rewrite List.app_length. ss. clear. lia. }
          destruct (length (ALocal.labels alc1) =? ALocal.next_eid alc1) eqn:Heq; cycle 1.
          { rewrite Nat.eqb_neq in Heq. unfold ALocal.next_eid in Heq. ss. }
          rewrite fun_add_spec.
          destruct (equiv_dec (ValA.val (sem_expr rmap1 eloc)) (ValA.val (sem_expr rmap1 eloc))) eqn:Heq1; ss.
      }
      specialize (FWDBANK loc). des.
      * left. esplits; eauto.
        rewrite sim_local_fwd_step. econs.
        econs; cycle 1.
        { instantiate (1 := (_, _)). econs; ss. }
        left. econs. split; eauto. econs; ss.
        exploit EX2.(LABELS_REV); ss.
        { apply nth_error_last. apply Nat.eqb_eq. ss. }
        i. econs; eauto. ii. inv H.
        destruct (equiv_dec (ValA.val (sem_expr armap1 eloc)) loc); ss. inv e.
        inv VLOC. congr.
      * right. esplits; eauto.
        i. specialize (FWDBANK0 eid).
        rewrite sim_local_fwd_none_step. rewrite inverse_step.
        ii. inv H. inv REL.
        { apply FWDBANK0. econs; eauto. }
        { inv H. inv H1. exploit EX2.(LABELS); eauto; ss.
          { rewrite List.app_length. s. lia. }
            rewrite List.nth_error_app2, Nat.sub_diag; ss. i. inv x0. inv LABEL.
            destruct (equiv_dec (ValA.val (sem_expr armap1 eloc)) loc); ss. inv e.
            inv VLOC. congr. }
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
  - (* rmw *)
    exploit sim_trace_sim_th; try exact TRACE; eauto. intro SIM_TH.
    generalize STEP0. intro STEP0'. inv STEP0'.
    inv ASTATE_STEP; inv ALOCAL_STEP; ss; inv EVENT; ss. splits.
    { econs; ss. inv RMAP. admit. (* apply sim_rmap_add; try apply L. econs; ss. *) }
    destruct L.(LC). ss. econs; ss.
    all: try rewrite List.app_length, Nat.add_1_r.
    + i. rewrite sim_local_coh_step. rewrite inverse_step.
      rewrite inverse_union. rewrite fun_add_spec. condtac.
      { ii. des.
        - inv EID. inv WRITABLE. ss. etrans; cycle 1.
          { eapply Memory.latest_ts_read_le; try refl.
            generalize SIM_TH.(MEM). s. i. subst.
            rewrite e. eapply Memory.get_msg_read; eauto. }
          apply Nat.lt_le_incl.
          eapply Nat.le_lt_trans; try eapply COH1. rewrite <- e.
          etrans; try apply COH0; eauto. apply Memory.latest_ts_spec.
        - inv EID. inv REL. des. inv H. inv H2. destruct l; ss.
          all: inv LABEL; destruct (equiv_dec loc0 loc); ss; inv e0; clear H1.
          { (* write *)
            inv H0; cycle 1.
            - inv H. exploit RF2; eauto. i. des.
              inv WRITE. inv READ. destruct l; destruct l0; ss; eqvtac.
              all: rename EID0 into WRITE.
              all: try rewrite EID in WRITE; inv WRITE.
              + exploit EX2.(LABELS); eauto; ss.
                { rewrite List.app_length. s. lia. }
                rewrite List.nth_error_app2, Nat.sub_diag; ss.
              + (* write -> update *)
                rename EID into WRITE.
                unfold Execution.label in WRITE. ss.
                rewrite PRE.(Valid.LABELS) in WRITE.
                rewrite IdMap.map_spec in WRITE.
                destruct (IdMap.find (fst x) (Valid.aeus PRE)) eqn:FIND1; ss.
                generalize (ATR (fst x)). intro ATR1. inv ATR1; try congr. des. simplify.
                generalize (SIM (fst x)). intro SIM1. inv SIM1; simplify.
                exploit sim_trace_last; try exact REL0. i. des. simplify.
                exploit sim_trace_sim_th; try exact REL0; eauto. intro L1.
                rewrite RF in H0. inv H0. ss. simplify.
                exploit WPROP3; eauto. i. des. simplify.
                unfold v_gen. ss. rewrite <- H8. rewrite x2.
                exploit EX2.(XR); eauto.
                { instantiate (1 := ALocal.next_eid alc1).
                  ss. rewrite List.app_length. ss. unfold ALocal.next_eid. clear. lia. }
                condtac; cycle 1.
                { rewrite Nat.eqb_neq in X0. ss. }
                rewrite fun_add_spec. condtac; cycle 1.
                { exfalso. apply c. ss. }
                i. unfold ALocal.next_eid in *.
                rewrite R in x8. inv x8. rewrite e.
                (* easy: (latest_ts to-1) <= (latest_ts to) *)
                admit.
            - exploit EX2.(LABELS); eauto; ss.
              { rewrite List.app_length. s. lia. }
              rewrite List.nth_error_app2, Nat.sub_diag; ss.
          }
          { (* update *)
            inv H0; cycle 1.
            - inv H. exploit RF2; eauto. i. des.
              inv WRITE. inv READ. destruct l; destruct l0; ss; eqvtac.
              all: rename EID0 into WRITE.
              all: try rewrite EID in WRITE; inv WRITE.
              + exploit EX2.(LABELS); eauto; ss.
                { rewrite List.app_length. s. lia. }
                rewrite List.nth_error_app2, Nat.sub_diag; ss.
              + (* update -> update *)
                rename EID into WRITE.
                unfold Execution.label in WRITE. ss.
                rewrite PRE.(Valid.LABELS) in WRITE.
                rewrite IdMap.map_spec in WRITE.
                destruct (IdMap.find (fst x) (Valid.aeus PRE)) eqn:FIND1; ss.
                generalize (ATR (fst x)). intro ATR1. inv ATR1; try congr. des. simplify.
                generalize (SIM (fst x)). intro SIM1. inv SIM1; simplify.
                exploit sim_trace_last; try exact REL0. i. des. simplify.
                exploit sim_trace_sim_th; try exact REL0; eauto. intro L1.
                rewrite RF in H0. inv H0. ss. simplify.
                exploit WPROP3; eauto. i. des. simplify.
                unfold v_gen. ss. rewrite <- H8. rewrite x2.
                exploit EX2.(XR); eauto.
                { instantiate (1 := ALocal.next_eid alc1).
                  ss. rewrite List.app_length. ss. unfold ALocal.next_eid. clear. lia. }
                condtac; cycle 1.
                { rewrite Nat.eqb_neq in X0. ss. }
                rewrite fun_add_spec. condtac; cycle 1.
                { exfalso. apply c. ss. }
                i. unfold ALocal.next_eid in *.
                rewrite R in x8. inv x8. rewrite e.
                (* easy: (latest_ts to-1) <= (latest_ts to) *)
                admit.
            - exploit EX2.(LABELS); eauto; ss.
              { rewrite List.app_length. s. lia. }
              rewrite List.nth_error_app2, Nat.sub_diag; ss. i. inv x0.
              rewrite EX2.(XVEXT); cycle 1.
              { ss. rewrite List.app_length. ss. clear. lia. }
              condtac; cycle 1.
              { rewrite Nat.eqb_neq in X0. unfold ALocal.next_eid in X0. ss. }
              rewrite fun_add_spec. condtac; cycle 1.
              { exfalso. apply c. ss. }
              s. eapply Memory.latest_ts_read_le; ss.
              generalize SIM_TH.(MEM). s. i. rewrite H in MSG. rewrite e.
              eapply Memory.get_msg_read; eauto.
          }
      }
      ii. des; [apply COH0|]; eauto.
      inv EID. inv REL. inv H. inv H0. inv H2. destruct l; ss.
      all: inv LABEL; destruct (equiv_dec loc0 loc); ss; inv e; clear H0.
      { (* write *)
        inv H1.
        - exploit EX2.(LABELS); eauto; ss.
          { rewrite List.app_length. s. lia. }
          rewrite List.nth_error_app2, Nat.sub_diag; ss.
        - inv H. exploit RF2; eauto. i. des.
          inv WRITE. inv READ. destruct l; destruct l0; ss; eqvtac.
          all: rename EID0 into WRITE.
          all: try rewrite EID in WRITE; inv WRITE.
          + exploit EX2.(LABELS); eauto; ss.
            { rewrite List.app_length. s. lia. }
            rewrite List.nth_error_app2, Nat.sub_diag; ss.
          + exploit EX2.(LABELS); eauto; ss.
            { rewrite List.app_length. s. lia. }
            rewrite List.nth_error_app2, Nat.sub_diag; ss. i. inv x1.
            inv VLOC. congr.
      }
      { (* update *)
        inv H1.
        - exploit EX2.(LABELS); eauto; ss.
          { rewrite List.app_length. s. lia. }
          rewrite List.nth_error_app2, Nat.sub_diag; ss. i. inv x0.
          inv VLOC. congr.
        - inv H. exploit RF2; eauto. i. des.
          inv WRITE. inv READ. destruct l; destruct l0; ss; eqvtac.
          all: rename EID0 into WRITE.
          all: try rewrite EID in WRITE; inv WRITE.
          + exploit EX2.(LABELS); eauto; ss.
            { rewrite List.app_length. s. lia. }
            rewrite List.nth_error_app2, Nat.sub_diag; ss.
          + exploit EX2.(LABELS); eauto; ss.
            { rewrite List.app_length. s. lia. }
            rewrite List.nth_error_app2, Nat.sub_diag; ss. i. inv x1.
            inv VLOC. congr.
      }
    + i. rewrite sim_local_vrn_step. rewrite inverse_step.
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
    + i. rewrite sim_local_vwn_step. rewrite inverse_step.
      rewrite ? inverse_union. ii. des.
      * exploit VWN; eauto. unfold le in *. i.
        unfold join. unfold Time.join. lia.
      * inv EID. inv REL. inv H0.
        exploit EX2.(LABELS); eauto; ss.
        { rewrite List.app_length. s. lia. }
        rewrite List.nth_error_app2, Nat.sub_diag; ss. i. inv x0.
        rewrite <- join_r.
        rewrite EX2.(XVEXT); cycle 1.
        { ss. rewrite List.app_length. ss. unfold ALocal.next_eid. clear. lia. }
        destruct (length (ALocal.labels alc1) =? ALocal.next_eid alc1) eqn:Heq.
        -- rewrite fun_add_spec. condtac; ss.
           exfalso. apply c. ss.
        -- rewrite Nat.eqb_neq in Heq. ss.
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
    + i. rewrite sim_local_vro_step. rewrite inverse_step.
      rewrite ? inverse_union. ii. des.
      * exploit VRO; eauto. i. rewrite <- join_l. ss.
      * inv EID. inv REL. inv H0.
        exploit EX2.(LABELS); eauto; ss.
        { rewrite List.app_length. s. lia. }
        rewrite List.nth_error_app2, Nat.sub_diag; ss. i. inv x0.
        rewrite <- join_r.
        rewrite EX2.(XVEXT); cycle 1.
        { ss. rewrite List.app_length. ss. unfold ALocal.next_eid. clear. lia. }
        destruct (length (ALocal.labels alc1) =? ALocal.next_eid alc1) eqn:Heq.
        -- rewrite fun_add_spec. condtac; ss.
           exfalso. apply c. ss.
        -- rewrite Nat.eqb_neq in Heq. ss.
    + i. rewrite sim_local_vwo_step. rewrite inverse_step.
      rewrite ? inverse_union. ii. des.
      * exploit VWO; eauto. i. rewrite <- join_l. ss.
      * inv EID. inv REL. inv H0.
        exploit EX2.(LABELS); eauto; ss.
        { rewrite List.app_length. s. lia. }
        rewrite List.nth_error_app2, Nat.sub_diag; ss. i. inv x0.
        rewrite <- join_r.
        rewrite EX2.(XVEXT); cycle 1.
        { ss. rewrite List.app_length. ss. clear. lia. }
        destruct (length (ALocal.labels alc1) =? ALocal.next_eid alc1) eqn:Heq; cycle 1.
        { rewrite Nat.eqb_neq in Heq. unfold ALocal.next_eid in Heq. ss. }
        rewrite fun_add_spec. condtac; ss.
        exfalso. apply c. ss.
    + i. rewrite fun_add_spec. condtac; s.
      { inversion e. subst. left. esplits; eauto.
        - destruct ts; ss. clear. lia.
        - instantiate (1 := (tid, length (ALocal.labels alc1))). econs.
          + econs; ss.
          + exploit EX2.(LABELS_REV); ss.
            { apply nth_error_last. apply Nat.eqb_eq. ss. }
            i. econs; eauto. inv VLOC. rewrite VAL. apply Label.update_is_writing.
          + i. inv PO. inv PO0. ss. subst. clear -N N0. lia.
        - rewrite EX2.(XVEXT); cycle 1.
          { ss. rewrite List.app_length. ss. clear. lia. }
          destruct (length (ALocal.labels alc1) =? ALocal.next_eid alc1) eqn:Heq; cycle 1.
          { rewrite Nat.eqb_neq in Heq. unfold ALocal.next_eid in Heq. ss. }
          rewrite fun_add_spec.
          destruct (equiv_dec (ValA.val (sem_expr rmap2 eloc)) (ValA.val (sem_expr rmap2 eloc))) eqn:Heq1; ss.
      }
      specialize (FWDBANK loc). des.
      * left. esplits; eauto.
        rewrite sim_local_fwd_step. econs.
        econs; cycle 1.
        { instantiate (1 := (_, _)). econs; ss. }
        left. econs. split; eauto. econs; ss.
        exploit EX2.(LABELS_REV); ss.
        { apply nth_error_last. apply Nat.eqb_eq. ss. }
        i. econs; eauto. ii. inv H.
        destruct (equiv_dec (ValA.val (sem_expr armap2 eloc)) loc); ss. inv e.
        inv VLOC. congr.
      * right. esplits; eauto.
        i. specialize (FWDBANK0 eid).
        rewrite sim_local_fwd_none_step. rewrite inverse_step.
        ii. inv H. inv REL.
        { apply FWDBANK0. econs; eauto. }
        { inv H. inv H1. exploit EX2.(LABELS); eauto; ss.
          { rewrite List.app_length. s. lia. }
            rewrite List.nth_error_app2, Nat.sub_diag; ss. i. inv x0. inv LABEL.
            destruct (equiv_dec (ValA.val (sem_expr armap2 eloc)) loc); ss. inv e.
            inv VLOC. congr. }
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
  - (* rmw_failure *)
    exploit sim_trace_sim_th; try exact TRACE; eauto. intro SIM_TH.
    destruct SIM_TH.(EU_WF). ss.
    generalize (Local.rmw_failure_spec LOCAL0 STEP0). intro RMW_FAILURE_SPEC.
    generalize SIM_TH.(MEM). s. i. rewrite H in RMW_FAILURE_SPEC.
    guardH RMW_FAILURE_SPEC. clear LOCAL0 H.
    generalize STEP0. intro STEP0'. inv STEP0'.
    inv ASTATE_STEP; inv ALOCAL_STEP; ss; inv EVENT; ss. splits.
    { econs; ss. admit.
      (* apply sim_rmap_add; try apply L.
      inv VAL. ss. *)
    }
    destruct L.(LC). ss. econs; ss.
    all: try rewrite List.app_length, Nat.add_1_r.
    + i. rewrite sim_local_coh_step. rewrite inverse_step.
      rewrite inverse_union. rewrite fun_add_spec. condtac.
      { ii. des.
        - inv EID. etrans; try eapply COH0; eauto. rewrite e.
          apply Memory.latest_ts_mon. unfold join. ss. apply join_l.
        - inv EID. inv REL. des. inv H. inv H2.
          destruct l; ss.
          all: inv LABEL; destruct (equiv_dec loc0 loc); ss; inv e0; clear H1.
          { (* write *)
            inv H0; cycle 1.
            - (* rfe *)
              inv H. exploit RF2; eauto. i. des.
              destruct x as [tid1 eid1]. ss.
              inv WRITE. inv READ. destruct l; destruct l0; ss; eqvtac.
              all: clear LABEL LABEL0.
              all: rename EID0 into WRITE.
              + (* write -> read *)
                unfold Execution.label in WRITE. ss.
                rewrite PRE.(Valid.LABELS) in WRITE.
                rewrite IdMap.map_spec in WRITE.
                destruct (IdMap.find tid1 (Valid.aeus PRE)) eqn:FIND1; ss.
                generalize (ATR tid1). intro ATR1. inv ATR1; try congr. des. simplify.
                generalize (SIM tid1). intro SIM1. inv SIM1; simplify.
                exploit sim_trace_last; try exact REL0. i. des. simplify.
                exploit sim_trace_sim_th; try exact REL0; eauto. intro L1.
                rewrite RF in H0. inv H0. ss. simplify.
                exploit WPROP3; eauto. i. des. simplify.
                unfold v_gen. ss. rewrite <- H8. rewrite x2.
                exploit EX2.(XR); eauto.
                { instantiate (1 := ALocal.next_eid alc1).
                  ss. rewrite List.app_length. ss. unfold ALocal.next_eid. clear. lia. }
                condtac; cycle 1.
                { rewrite Nat.eqb_neq in X0. ss. }
                rewrite fun_add_spec. condtac; cycle 1.
                { exfalso. apply c. ss. }
                i. unfold ALocal.next_eid in *.
                rewrite R in x7. inv x7. rewrite e. ss.
              + (* write -> update *)
                unfold Execution.label in WRITE. ss.
                rewrite PRE.(Valid.LABELS) in WRITE.
                rewrite IdMap.map_spec in WRITE.
                destruct (IdMap.find tid1 (Valid.aeus PRE)) eqn:FIND1; ss.
                generalize (ATR tid1). intro ATR1. inv ATR1; try congr. des. simplify.
                generalize (SIM tid1). intro SIM1. inv SIM1; simplify.
                exploit sim_trace_last; try exact REL0. i. des. simplify.
                exploit sim_trace_sim_th; try exact REL0; eauto. intro L1.
                rewrite RF in H0. inv H0. ss. simplify.
                exploit WPROP3; eauto. i. des. simplify.
                unfold v_gen. ss. rewrite <- H8. rewrite x2.
                exploit EX2.(XR); eauto.
                { instantiate (1 := ALocal.next_eid alc1).
                  ss. rewrite List.app_length. ss. unfold ALocal.next_eid. clear. lia. }
                condtac; cycle 1.
                { rewrite Nat.eqb_neq in X0. ss. }
                rewrite fun_add_spec. condtac; cycle 1.
                { exfalso. apply c. ss. }
                i. unfold ALocal.next_eid in *.
                rewrite R in x7. inv x7. rewrite e. ss.
              + (* update -> read *)
                unfold Execution.label in WRITE. ss.
                rewrite PRE.(Valid.LABELS) in WRITE.
                rewrite IdMap.map_spec in WRITE.
                destruct (IdMap.find tid1 (Valid.aeus PRE)) eqn:FIND1; ss.
                generalize (ATR tid1). intro ATR1. inv ATR1; try congr. des. simplify.
                generalize (SIM tid1). intro SIM1. inv SIM1; simplify.
                exploit sim_trace_last; try exact REL0. i. des. simplify.
                exploit sim_trace_sim_th; try exact REL0; eauto. intro L1.
                rewrite RF in H0. inv H0. ss. simplify.
                exploit WPROP3; eauto. i. des. simplify.
                unfold v_gen. ss. rewrite <- H8. rewrite x2.
                exploit EX2.(XR); eauto.
                { instantiate (1 := ALocal.next_eid alc1).
                  ss. rewrite List.app_length. ss. unfold ALocal.next_eid. clear. lia. }
                condtac; cycle 1.
                { rewrite Nat.eqb_neq in X0. ss. }
                rewrite fun_add_spec. condtac; cycle 1.
                { exfalso. apply c. ss. }
                i. unfold ALocal.next_eid in *.
                rewrite R in x7. inv x7. rewrite e. ss.
              + (* update -> update *)
                unfold Execution.label in WRITE. ss.
                rewrite PRE.(Valid.LABELS) in WRITE.
                rewrite IdMap.map_spec in WRITE.
                destruct (IdMap.find tid1 (Valid.aeus PRE)) eqn:FIND1; ss.
                generalize (ATR tid1). intro ATR1. inv ATR1; try congr. des. simplify.
                generalize (SIM tid1). intro SIM1. inv SIM1; simplify.
                exploit sim_trace_last; try exact REL0. i. des. simplify.
                exploit sim_trace_sim_th; try exact REL0; eauto. intro L1.
                rewrite RF in H0. inv H0. ss. simplify.
                exploit WPROP3; eauto. i. des. simplify.
                unfold v_gen. ss. rewrite <- H8. rewrite x2.
                exploit EX2.(XR); eauto.
                { instantiate (1 := ALocal.next_eid alc1).
                  ss. rewrite List.app_length. ss. unfold ALocal.next_eid. clear. lia. }
                condtac; cycle 1.
                { rewrite Nat.eqb_neq in X0. ss. }
                rewrite fun_add_spec. condtac; cycle 1.
                { exfalso. apply c. ss. }
                i. unfold ALocal.next_eid in *.
                rewrite R in x7. inv x7. rewrite e. ss.
            - exploit EX2.(LABELS); eauto; ss.
              { rewrite List.app_length. s. lia. }
              rewrite List.nth_error_app2, Nat.sub_diag; ss.
          }
          { (* update *)
            inv H0; cycle 1.
            - (* rfe *)
              inv H. exploit RF2; eauto. i. des.
              destruct x as [tid1 eid1]. ss.
              inv WRITE. inv READ. destruct l; destruct l0; ss; eqvtac.
              all: clear LABEL LABEL0.
              all: rename EID0 into WRITE.
              + (* write -> read *)
                unfold Execution.label in WRITE. ss.
                rewrite PRE.(Valid.LABELS) in WRITE.
                rewrite IdMap.map_spec in WRITE.
                destruct (IdMap.find tid1 (Valid.aeus PRE)) eqn:FIND1; ss.
                generalize (ATR tid1). intro ATR1. inv ATR1; try congr. des. simplify.
                generalize (SIM tid1). intro SIM1. inv SIM1; simplify.
                exploit sim_trace_last; try exact REL0. i. des. simplify.
                exploit sim_trace_sim_th; try exact REL0; eauto. intro L1.
                rewrite RF in H0. inv H0. ss. simplify.
                exploit WPROP3; eauto. i. des. simplify.
                unfold v_gen. ss. rewrite <- H8. rewrite x2.
                exploit EX2.(XR); eauto.
                { instantiate (1 := ALocal.next_eid alc1).
                  ss. rewrite List.app_length. ss. unfold ALocal.next_eid. clear. lia. }
                condtac; cycle 1.
                { rewrite Nat.eqb_neq in X0. ss. }
                rewrite fun_add_spec. condtac; cycle 1.
                { exfalso. apply c. ss. }
                i. unfold ALocal.next_eid in *.
                rewrite R in x7. inv x7. rewrite e. ss.
              + (* write -> update *)
                unfold Execution.label in WRITE. ss.
                rewrite PRE.(Valid.LABELS) in WRITE.
                rewrite IdMap.map_spec in WRITE.
                destruct (IdMap.find tid1 (Valid.aeus PRE)) eqn:FIND1; ss.
                generalize (ATR tid1). intro ATR1. inv ATR1; try congr. des. simplify.
                generalize (SIM tid1). intro SIM1. inv SIM1; simplify.
                exploit sim_trace_last; try exact REL0. i. des. simplify.
                exploit sim_trace_sim_th; try exact REL0; eauto. intro L1.
                rewrite RF in H0. inv H0. ss. simplify.
                exploit WPROP3; eauto. i. des. simplify.
                unfold v_gen. ss. rewrite <- H8. rewrite x2.
                exploit EX2.(XR); eauto.
                { instantiate (1 := ALocal.next_eid alc1).
                  ss. rewrite List.app_length. ss. unfold ALocal.next_eid. clear. lia. }
                condtac; cycle 1.
                { rewrite Nat.eqb_neq in X0. ss. }
                rewrite fun_add_spec. condtac; cycle 1.
                { exfalso. apply c. ss. }
                i. unfold ALocal.next_eid in *.
                rewrite R in x7. inv x7. rewrite e. ss.
              + (* update -> read *)
                unfold Execution.label in WRITE. ss.
                rewrite PRE.(Valid.LABELS) in WRITE.
                rewrite IdMap.map_spec in WRITE.
                destruct (IdMap.find tid1 (Valid.aeus PRE)) eqn:FIND1; ss.
                generalize (ATR tid1). intro ATR1. inv ATR1; try congr. des. simplify.
                generalize (SIM tid1). intro SIM1. inv SIM1; simplify.
                exploit sim_trace_last; try exact REL0. i. des. simplify.
                exploit sim_trace_sim_th; try exact REL0; eauto. intro L1.
                rewrite RF in H0. inv H0. ss. simplify.
                exploit WPROP3; eauto. i. des. simplify.
                unfold v_gen. ss. rewrite <- H8. rewrite x2.
                exploit EX2.(XR); eauto.
                { instantiate (1 := ALocal.next_eid alc1).
                  ss. rewrite List.app_length. ss. unfold ALocal.next_eid. clear. lia. }
                condtac; cycle 1.
                { rewrite Nat.eqb_neq in X0. ss. }
                rewrite fun_add_spec. condtac; cycle 1.
                { exfalso. apply c. ss. }
                i. unfold ALocal.next_eid in *.
                rewrite R in x7. inv x7. rewrite e. ss.
              + (* update -> update *)
                unfold Execution.label in WRITE. ss.
                rewrite PRE.(Valid.LABELS) in WRITE.
                rewrite IdMap.map_spec in WRITE.
                destruct (IdMap.find tid1 (Valid.aeus PRE)) eqn:FIND1; ss.
                generalize (ATR tid1). intro ATR1. inv ATR1; try congr. des. simplify.
                generalize (SIM tid1). intro SIM1. inv SIM1; simplify.
                exploit sim_trace_last; try exact REL0. i. des. simplify.
                exploit sim_trace_sim_th; try exact REL0; eauto. intro L1.
                rewrite RF in H0. inv H0. ss. simplify.
                exploit WPROP3; eauto. i. des. simplify.
                unfold v_gen. ss. rewrite <- H8. rewrite x2.
                exploit EX2.(XR); eauto.
                { instantiate (1 := ALocal.next_eid alc1).
                  ss. rewrite List.app_length. ss. unfold ALocal.next_eid. clear. lia. }
                condtac; cycle 1.
                { rewrite Nat.eqb_neq in X0. ss. }
                rewrite fun_add_spec. condtac; cycle 1.
                { exfalso. apply c. ss. }
                i. unfold ALocal.next_eid in *.
                rewrite R in x7. inv x7. rewrite e. ss.
            - exploit EX2.(LABELS); eauto; ss.
              { rewrite List.app_length. s. lia. }
              rewrite List.nth_error_app2, Nat.sub_diag; ss.
          }
      }
      ii. des; [apply COH0|]; eauto.
      inv EID. inv REL. inv H. inv H0. inv H2.
      destruct l; ss.
      all: inv LABEL; destruct (equiv_dec loc0 loc); ss; inv e; clear H0.
      { (* write *)
        inv H1.
        - exploit EX2.(LABELS); eauto; ss.
          { rewrite List.app_length. s. lia. }
          rewrite List.nth_error_app2, Nat.sub_diag; ss.
        - inv H. exploit RF2; eauto. i. des.
          inv WRITE. inv READ. destruct l; destruct l0; ss; eqvtac.
          all: rename EID0 into WRITE.
          all: try rewrite EID in WRITE; inv WRITE.
          + exploit EX2.(LABELS); eauto; ss.
            { rewrite List.app_length. s. lia. }
            rewrite List.nth_error_app2, Nat.sub_diag; ss. i. inv x1.
            inv VLOC. congr.
          + exploit EX2.(LABELS); eauto; ss.
            { rewrite List.app_length. s. lia. }
            rewrite List.nth_error_app2, Nat.sub_diag; ss.
      }
      { (* update *)
        inv H1.
        - exploit EX2.(LABELS); eauto; ss.
          { rewrite List.app_length. s. lia. }
          rewrite List.nth_error_app2, Nat.sub_diag; ss.
        - inv H. exploit RF2; eauto. i. des.
          inv WRITE. inv READ. destruct l; destruct l0; ss; eqvtac.
          all: rename EID0 into WRITE.
          all: try rewrite EID in WRITE; inv WRITE.
          + exploit EX2.(LABELS); eauto; ss.
            { rewrite List.app_length. s. lia. }
            rewrite List.nth_error_app2, Nat.sub_diag; ss. i. inv x1.
            inv VLOC. congr.
          + exploit EX2.(LABELS); eauto; ss.
            { rewrite List.app_length. s. lia. }
            rewrite List.nth_error_app2, Nat.sub_diag; ss.
      }
    + i. rewrite sim_local_vrn_step. rewrite inverse_step.
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
    + i. rewrite sim_local_vwn_step. rewrite inverse_step.
      rewrite ? inverse_union. ii. des.
      * exploit VWN; eauto. i. rewrite <- join_l. ss.
      * inv EID. inv REL. inv H0.
        exploit EX2.(LABELS); eauto; ss.
        { rewrite List.app_length. s. lia. }
        rewrite List.nth_error_app2, Nat.sub_diag; ss. i. inv x0.
        rewrite <- join_r.
        rewrite EX2.(XVEXT); cycle 1.
        { ss. rewrite List.app_length. ss. unfold ALocal.next_eid. clear. lia. }
        destruct (length (ALocal.labels alc1) =? ALocal.next_eid alc1) eqn:Heq.
        -- unfold le. unfold join. unfold Time.join. lia.
        -- rewrite Nat.eqb_neq in Heq. ss.
      * inv EID. inv REL. inv H0.
        exploit EX2.(LABELS); eauto; ss.
        { rewrite List.app_length. s. lia. }
        rewrite List.nth_error_app2, Nat.sub_diag; ss. i. inv x0. inv LABEL.
    + i. rewrite sim_local_vro_step. rewrite inverse_step.
      rewrite ? inverse_union. ii. des.
      * exploit VRO; eauto. i. rewrite <- join_l. ss.
      * inv EID. inv REL. inv H0.
        exploit EX2.(LABELS); eauto; ss.
        { rewrite List.app_length. s. lia. }
        rewrite List.nth_error_app2, Nat.sub_diag; ss. i. inv x0.
        rewrite <- join_r.
        rewrite EX2.(XVEXT); cycle 1.
        { ss. rewrite List.app_length. ss. unfold ALocal.next_eid. clear. lia. }
        destruct (length (ALocal.labels alc1) =? ALocal.next_eid alc1) eqn:Heq.
        -- unfold le. unfold join. unfold Time.join. lia.
        -- rewrite Nat.eqb_neq in Heq. ss.
    + i. rewrite sim_local_vwo_step. rewrite inverse_step.
      rewrite ? inverse_union. ii. des.
      * exploit VWO; eauto.
      * inv EID. inv REL. inv H0.
        exploit EX2.(LABELS); eauto; ss.
        { rewrite List.app_length. s. lia. }
        rewrite List.nth_error_app2, Nat.sub_diag; ss. i. inv x0. inv LABEL.
    + i. specialize (FWDBANK loc). des.
      * left. esplits; eauto.
        rewrite sim_local_fwd_step. econs.
        econs; cycle 1.
        { instantiate (1 := (_, _)). econs; ss. }
        left. econs. split; eauto. econs; ss.
        exploit EX2.(LABELS_REV); ss.
        { apply nth_error_last. apply Nat.eqb_eq. ss. }
        i. econs; eauto.
      * right. esplits; eauto.
        i. specialize (FWDBANK0 eid).
        rewrite sim_local_fwd_none_step. rewrite inverse_step.
        ii. inv H. inv REL.
        { apply FWDBANK0. econs; eauto. }
        { inv H. inv H1. exploit EX2.(LABELS); eauto; ss.
          { rewrite List.app_length. s. lia. }
          rewrite List.nth_error_app2, Nat.sub_diag; ss.
          destruct l; ss. }
    + i. exploit PROMISES; eauto. i. des. esplits; cycle 1; eauto.
      inv N.
      * inv WRITE. exploit EX2.(LABELS); eauto; ss.
        { rewrite List.app_length. s. lia. }
        rewrite List.nth_error_app2, Nat.sub_diag; ss.
        destruct l; ss.
      * clear -H. lia.
  - (* dmb *)
    inv STEP0. inv ASTATE_STEP; inv ALOCAL_STEP; ss; inv EVENT; ss. splits.
    econs; ss.
    { econs; ss. apply L. }
    destruct L.(LC). ss. econs; ss.
    + rewrite List.app_length, Nat.add_1_r.
      i. rewrite sim_local_coh_step. rewrite inverse_step.
      rewrite inverse_union. ii. des; [apply COH|]; eauto.
      inv EID. inv REL. inv H. inv H0. inv H2. destruct l; ss.
      all: inv LABEL; destruct (equiv_dec loc0 loc); ss; inv e; clear H0.
      { (* write *)
        inv H1.
        - exploit EX2.(LABELS); eauto; ss.
          { rewrite List.app_length. s. lia. }
          rewrite List.nth_error_app2, Nat.sub_diag; ss.
        - inv H. exploit RF2; eauto. i. des.
          inv WRITE. inv READ. destruct l; destruct l0; ss; eqvtac.
          all: rename EID0 into WRITE.
          all: try rewrite EID in WRITE; inv WRITE.
          + exploit EX2.(LABELS); eauto; ss.
            { rewrite List.app_length. s. lia. }
            rewrite List.nth_error_app2, Nat.sub_diag; ss.
          + exploit EX2.(LABELS); eauto; ss.
            { rewrite List.app_length. s. lia. }
            rewrite List.nth_error_app2, Nat.sub_diag; ss.
      }
      { (* update *)
        inv H1.
        - exploit EX2.(LABELS); eauto; ss.
          { rewrite List.app_length. s. lia. }
          rewrite List.nth_error_app2, Nat.sub_diag; ss.
        - inv H. exploit RF2; eauto. i. des.
          inv WRITE. inv READ. destruct l; destruct l0; ss; eqvtac.
          all: rename EID0 into WRITE.
          all: try rewrite EID in WRITE; inv WRITE.
          + exploit EX2.(LABELS); eauto; ss.
            { rewrite List.app_length. s. lia. }
            rewrite List.nth_error_app2, Nat.sub_diag; ss.
          + exploit EX2.(LABELS); eauto; ss.
            { rewrite List.app_length. s. lia. }
            rewrite List.nth_error_app2, Nat.sub_diag; ss.
      }
    + rewrite List.app_length, Nat.add_1_r.
      i. rewrite sim_local_vrn_step. rewrite inverse_step.
      rewrite ? inverse_union. ii. des.
      * exploit VRN; eauto. i. rewrite <- join_l. ss.
      * inv EID. inv REL. inv H0.
        exploit EX2.(LABELS); eauto; ss.
        { rewrite List.app_length. s. lia. }
        rewrite List.nth_error_app2, Nat.sub_diag; ss. i. inv x0. inv LABEL.
      * inv EID. inv REL. inv H. inv H1. inv H. inv H2. inv H3.
        exploit EX2.(LABELS); eauto; ss.
        { rewrite List.app_length. s. lia. }
        rewrite List.nth_error_app2, Nat.sub_diag; ss. i. simplify.
        destruct wr0; ss.
        rewrite <- join_r, <- join_r, <- join_l. apply L. econs; eauto. econs; eauto.
    + rewrite List.app_length, Nat.add_1_r.
      i. rewrite sim_local_vwn_step. rewrite inverse_step.
      rewrite ? inverse_union. ii. des.
      * exploit VWN; eauto. i. rewrite <- join_l. ss.
      * inv EID. inv REL. inv H0.
        exploit EX2.(LABELS); eauto; ss.
        { rewrite List.app_length. s. lia. }
        rewrite List.nth_error_app2, Nat.sub_diag; ss. i. inv x0. inv LABEL.
      * inv EID. inv REL. inv H0.
        exploit EX2.(LABELS); eauto; ss.
        { rewrite List.app_length. s. lia. }
        rewrite List.nth_error_app2, Nat.sub_diag; ss. i. inv x0. inv LABEL.
    + rewrite List.app_length, Nat.add_1_r.
      i. rewrite sim_local_vro_step. rewrite inverse_step.
      rewrite ? inverse_union. ii. des.
      * exploit VRO; eauto.
      * inv EID. inv REL. inv H0.
        exploit EX2.(LABELS); eauto; ss.
        { rewrite List.app_length. s. lia. }
        rewrite List.nth_error_app2, Nat.sub_diag; ss. i. inv x0. inv LABEL.
    + rewrite List.app_length, Nat.add_1_r.
      i. rewrite sim_local_vwo_step. rewrite inverse_step.
      rewrite ? inverse_union. ii. des.
      * exploit VWO; eauto.
      * inv EID. inv REL. inv H0.
        exploit EX2.(LABELS); eauto; ss.
        { rewrite List.app_length. s. lia. }
        rewrite List.nth_error_app2, Nat.sub_diag; ss. i. inv x0. inv LABEL.
    + i. specialize (FWDBANK loc). des.
      * left. esplits; eauto.
        rewrite List.app_length, Nat.add_1_r.
        rewrite sim_local_fwd_step. econs.
        econs; cycle 1.
        { instantiate (1 := (_, _)). econs; ss. }
        left. econs. split; eauto. econs; ss.
        exploit EX2.(LABELS_REV); ss.
        { apply nth_error_last. apply Nat.eqb_eq. ss. }
        intro X. econs; eauto.
      * right. esplits; eauto.
        i. specialize (FWDBANK0 eid).
        rewrite List.app_length, Nat.add_1_r.
        rewrite sim_local_fwd_none_step. rewrite inverse_step.
        ii. inv H. inv REL.
        { apply FWDBANK0. econs; eauto. }
        { inv H. inv H1. exploit EX2.(LABELS); eauto; ss.
          { rewrite List.app_length. s. lia. }
          rewrite List.nth_error_app2, Nat.sub_diag; ss.
          destruct l; ss. }
    + i. exploit PROMISES; eauto. i. des. esplits; cycle 1; eauto.
      rewrite List.app_length, Nat.add_1_r. inv N.
      * inv WRITE. exploit EX2.(LABELS); eauto; ss.
        { rewrite List.app_length. s. lia. }
        rewrite List.nth_error_app2, Nat.sub_diag; ss.
        destruct l; ss.
      * clear -H. lia.
  - (* dowhile *)
    inv ASTATE_STEP; inv ALOCAL_STEP; ss; inv EVENT; ss. splits.
    + econs; ss; try by apply L.
    + econs; ss; try by apply L.
Qed.
