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

Require Import PromisingArch.lib.Basic.
Require Import PromisingArch.lib.HahnRelationsMore.
Require Import PromisingArch.lib.Order.
Require Import PromisingArch.lib.Time.
Require Import PromisingArch.lib.Lang.
Require Import PromisingArch.axiomatic.TsoAxiomatic.

Set Implicit Arguments.


Lemma inverse_step
      r tid n:
  inverse (r ⨾ Execution.po_adj) (eq (tid, S n)) = inverse r (eq (tid, n)).
Proof.
  funext. i. propext. econs; i.
  - inv H. inv REL. des. inv H0. destruct x, x0. ss. inv N. econs; eauto.
  - inv H. econs; eauto. econs; eauto. econs; eauto. econs; eauto.
Qed.

Inductive sim_val_weak (vala:ValA.t (A:=unit)) (avala:ValA.t (A:=unit)): Prop :=
| sim_val_weak_intro
    (VAL: vala.(ValA.val) = avala.(ValA.val))
.
Hint Constructors sim_val_weak.

Inductive sim_rmap_weak (rmap:RMap.t (A:=unit)) (armap:RMap.t (A:=unit)): Prop :=
| sim_rmap_weak_intro
    (RMAP: IdMap.Forall2 (fun reg => sim_val_weak) rmap armap)
.
Hint Constructors sim_rmap_weak.

Inductive sim_state_weak (state:State.t (A:=unit)) (astate:State.t (A:=unit)): Prop :=
| sim_state_weak_intro
    (STMTS: state.(State.stmts) = astate.(State.stmts))
    (RMAP: sim_rmap_weak state.(State.rmap) astate.(State.rmap))
.
Hint Constructors sim_state_weak.

Lemma sim_state_weak_init stmts:
  sim_state_weak (State.init stmts) (State.init stmts).
Proof.
  econs; ss. econs. ii. unfold RMap.init. rewrite ? IdMap.gempty. econs.
Qed.

Lemma sim_rmap_weak_add
      rmap armap reg vala avala
      (SIM: sim_rmap_weak rmap armap)
      (VAL: sim_val_weak vala avala):
  sim_rmap_weak (RMap.add reg vala rmap) (RMap.add reg avala armap).
Proof.
  econs. ii. unfold RMap.add. rewrite ? IdMap.add_spec.
  inv SIM. condtac; eauto.
Qed.

Lemma sim_rmap_weak_sem_expr
  rmap1 rmap2 e
  (SIM: sim_rmap_weak rmap1 rmap2):
  sem_expr rmap1 e = sem_expr rmap2 e.
Proof.

  inv SIM. induction e; ss.
  - unfold RMap.find. specialize (RMAP reg). inv RMAP; ss.
    inv REL. destruct a as [v1 []], b as [v2 []]. ss.
    rewrite VAL. ss.
  - rewrite IHe. ss.
  - rewrite IHe1, IHe2. ss.
Qed.

Lemma sim_rmap_weak_expr
      rmap armap e
      (SIM: sim_rmap_weak rmap armap):
  sim_val_weak (sem_expr rmap e) (sem_expr armap e).
Proof.
  exploit sim_rmap_weak_sem_expr; eauto. intro SEM. rewrite SEM. ss.
Qed.

Lemma sim_rmap_weak_sem_rmw
      rmap1 rmap2 rmw vold vnew
      (SIM: sim_rmap_weak rmap1 rmap2)
      (SEM: sem_rmw rmap1 rmw vold vnew):
  sem_rmw rmap2 rmw vold vnew.
Proof.
  inv SEM; econs; eauto.
  3: replace (sem_expr rmap2 eammount) with (sem_expr rmap1 eammount); ss.
  all: eapply sim_rmap_weak_sem_expr; ss.
Qed.

Inductive sim_event: forall (e1: Event.t (A:=unit)) (e2: Event.t (A:=unit)), Prop :=
| sim_event_internal:
    sim_event Event.internal Event.internal
| sim_event_read
    ex1 rmw_fail1 ord1 vloc1 val1
    ex2 rmw_fail2 ord2 vloc2 val2
    (EX: ex1 = ex2)
    (ORD: ord1 = ord2)
    (VLOC: sim_val_weak vloc1 vloc2)
    (VAL: sim_val_weak val1 val2):
    sim_event (Event.read ex1 rmw_fail1 ord1 vloc1 val1) (Event.read ex2 rmw_fail2 ord2 vloc2 val2)
| sim_event_write
    ex1 ord1 vloc1 vval1 res1
    ex2 ord2 vloc2 vval2 res2
    (EX: ex1 = ex2)
    (ORD: ord1 = ord2)
    (VLOC: sim_val_weak vloc1 vloc2)
    (VVAL: sim_val_weak vval1 vval2)
    (RES: sim_val_weak res1 res2):
    sim_event (Event.write ex1 ord1 vloc1 vval1 res1) (Event.write ex2 ord2 vloc2 vval2 res2)
| sim_event_rmw
    ex1 ord1 vloc1 old1 new1
    ex2 ord2 vloc2 old2 new2
    (EX: ex1 = ex2)
    (ORD: ord1 = ord2)
    (VLOC: sim_val_weak vloc1 vloc2)
    (OLD: sim_val_weak old1 old2)
    (NEW: sim_val_weak new1 new2):
    sim_event (Event.rmw ex1 ord1 vloc1 old1 new1) (Event.rmw ex2 ord2 vloc2 old2 new2)
| sim_event_barrier
    b1 b2
    (BARRIER: b1 = b2):
    sim_event (Event.barrier b1) (Event.barrier b2)
| sim_event_flush
    vloc1 vloc2
    (VLOC: sim_val_weak vloc1 vloc2):
    sim_event (Event.flush vloc1) (Event.flush vloc2)
| sim_event_flushopt
    vloc1 vloc2
    (VLOC: sim_val_weak vloc1 vloc2):
    sim_event (Event.flushopt vloc1) (Event.flushopt vloc2)
.
Hint Constructors sim_event.

Definition sim_local_coh ex loc :=
  ⦗ex.(Execution.label_is) (Label.is_kinda_writing loc)⦘ ⨾
  (Execution.rfe ex)^? ⨾
  Execution.po.

Lemma sim_local_coh_step ex loc:
  sim_local_coh ex loc =
  (sim_local_coh ex loc ∪
   ⦗ex.(Execution.label_is) (Label.is_kinda_writing loc)⦘ ⨾ (Execution.rfe ex)^?) ⨾
  Execution.po_adj.
Proof.
  unfold sim_local_coh. rewrite Execution.po_po_adj at 1.
  rewrite (clos_refl_union Execution.po), union_seq, eq_seq.
  rewrite ? seq_union, ? union_seq, ? seq_assoc.
  refl.
Qed.

Definition sim_local_vrn ex :=
  (⦗ex.(Execution.label_is) Label.is_kinda_read⦘ ⨾
   Execution.po) ∪

  (⦗ex.(Execution.label_is) Label.is_access⦘ ⨾
   Execution.po ⨾
   ⦗ex.(Execution.label_is) (Label.is_barrier_c Barrier.is_mfence)⦘ ⨾
   Execution.po).

Lemma sim_local_vrn_step ex:
  sim_local_vrn ex =
  (sim_local_vrn ex ∪
   ((⦗ex.(Execution.label_is) Label.is_kinda_read⦘) ∪

   (⦗ex.(Execution.label_is) Label.is_access⦘ ⨾
     Execution.po ⨾
     ⦗ex.(Execution.label_is) (Label.is_barrier_c Barrier.is_mfence)⦘))) ⨾
  Execution.po_adj.
Proof.
  unfold sim_local_vrn. rewrite ? (union_seq' Execution.po_adj), ? seq_assoc, ? union_assoc.
  rewrite Execution.po_po_adj at 1 3.
  rewrite (clos_refl_union Execution.po), union_seq, eq_seq.
  rewrite ? (seq_union' (Execution.po ⨾ Execution.po_adj) Execution.po_adj), ? seq_assoc, ? union_assoc.
  funext. i. funext. i. propext. econs; i.
  - repeat match goal with
           | [H: (_ ∪ _) _ _ |- _] => inv H
           end;
      eauto 10 using union_l, union_r.
  - repeat match goal with
           | [H: (_ ∪ _) _ _ |- _] => inv H
           end;
      eauto 10 using union_l, union_r.
Qed.

Lemma sim_local_vrn_spec
      p ex eid1 eid2
      (EX: Valid.ex p ex)
      (EID2: Execution.label_is ex Label.is_kinda_read eid2)
      (VRN: sim_local_vrn ex eid1 eid2):
  <<OB: Execution.ob ex eid1 eid2>>.
Proof.
  inv EID2. destruct l; inv LABEL. unfold sim_local_vrn in VRN.
  repeat match goal with
         | [H: (_ ∪ _) _ _ |- _] => inv H
         end.
  - left. left. left. right. left.
    inv H. des. econs. splits; eauto.
    econs. instantiate (1 := eid2). splits; ss.
    econs; eauto. econs; eauto.
  - left. left. right. obtac.
    rewrite ? seq_assoc. econs. splits; econs; eauto with tso. split; eauto.
    econs. split; econs; eauto with tso. split; eauto. econs; eauto with tso.
  - left. left. left. right. right.
    inv VRN; inv H; des; inv H0; inv H2.
    + rewrite seq_assoc. econs. splits; cycle 1.
      { econs; eauto. econs; eauto. }
      econs. econs; eauto. econs; eauto with tso.
    + rewrite seq_assoc. econs. splits; cycle 1.
      { econs; eauto. econs; eauto. }
      econs. splits.
      { destruct l; ss; econs; eauto with tso. }
      inv H1. des. inv H0. des. inv H1.
      etrans; eauto.
Qed.

Definition sim_local_vwn ex :=
  (⦗ex.(Execution.label_is) Label.is_access⦘ ⨾
   Execution.po).

Lemma sim_local_vwn_step ex:
  sim_local_vwn ex =
  (sim_local_vwn ex ∪
   (⦗ex.(Execution.label_is) Label.is_access⦘)) ⨾
  Execution.po_adj.
Proof.
  unfold sim_local_vwn. rewrite ? (union_seq' Execution.po_adj), ? seq_assoc, ? union_assoc.
  rewrite Execution.po_po_adj at 1.
  rewrite (clos_refl_union Execution.po), union_seq, eq_seq.
  rewrite ? (seq_union' (Execution.po ⨾ Execution.po_adj) Execution.po_adj), ? seq_assoc, ? union_assoc.
  refl.
Qed.

Lemma sim_local_vwn_spec
      p ex eid1 eid2
      (EX: Valid.ex p ex)
      (EID2: Execution.label_is ex Label.is_kinda_write eid2)
      (VWN: sim_local_vwn ex eid1 eid2):
  <<OB: Execution.ob ex eid1 eid2>>.
Proof.
  inv EID2. inv VWN. des.
  left. left. left. right. right.
  econs. econs; eauto. econs. econs; eauto. econs; eauto with tso.
Qed.

Inductive sim_local_fwd ex (loc:Loc.t) (eid1 eid2:eidT): Prop :=
| sim_local_fwd_intro
    (PO: Execution.po eid1 eid2)
    (WRITE: ex.(Execution.label_is) (Label.is_kinda_writing loc) eid1)
    (NWRITE: forall eid
               (PO: Execution.po eid1 eid)
               (PO: Execution.po eid eid2),
        ex.(Execution.label_is) (fun l => ~ Label.is_kinda_writing loc l) eid)
.

Lemma sim_local_fwd_step ex loc:
  sim_local_fwd ex loc =
  (sim_local_fwd ex loc ⨾ ⦗ex.(Execution.label_is) (fun l => ~ (Label.is_kinda_writing loc l))⦘ ∪
   ⦗ex.(Execution.label_is) (Label.is_kinda_writing loc)⦘) ⨾
  Execution.po_adj.
Proof.
  funext. i. funext. i. propext. econs.
  - i. inv H. rewrite Execution.po_po_adj in PO. inv PO. des.
    inv H0. destruct x0, x1. ss. subst.
    econs. splits; cycle 1.
    { instantiate (1 := (_, _)). econs; ss. }
    inv H.
    + right. econs; ss.
    + hexploit NWRITE; eauto with tso. i.
      left. econs. splits; cycle 1.
      { econs; eauto. }
      econs; eauto. i. apply NWRITE; eauto. etrans; eauto with tso.
  - i. inv H. des. inv H1. destruct x0, x1. ss. subst. inv H0.
    + inv H. des. inv H1. inv H2. inv H0.
      econs; eauto.
      * etrans; eauto with tso.
      * i. rewrite Execution.po_po_adj in PO1. inv PO1. des. inv H0. destruct x0. ss. inv N.
        inv H; eauto with tso.
    + inv H. inv H1. econs; eauto with tso.
      i. inv PO. inv PO0. ss. subst. lia.
Qed.

Lemma sim_local_fwd_functional ex loc eid1 eid2 eid3
      (EID1: sim_local_fwd ex loc eid1 eid3)
      (EID2: sim_local_fwd ex loc eid2 eid3):
  eid1 = eid2.
Proof.
  inv EID1. inv EID2.
  destruct eid1, eid2, eid3. inv PO. inv PO0. ss. subst. f_equal.
  destruct (Nat.compare_spec n n0); ss.
  - exploit (NWRITE (t1, n0)); eauto with tso. i.
    inv WRITE0. inv x0. rewrite EID in EID0. inv EID0. ss.
  - exploit (NWRITE0 (t1, n)); eauto with tso. i.
    inv WRITE. inv x0. rewrite EID in EID0. inv EID0. ss.
Qed.

Lemma rfi_sim_local_fwd
      p ex (EX: Valid.ex p ex)
      loc eid1 eid2
      (EID1: ex.(Execution.label_is) (Label.is_kinda_writing loc) eid1)
      (EID2: ex.(Execution.label_is) (Label.is_kinda_reading loc) eid2)
      (RFI: Execution.rfi ex eid1 eid2):
  sim_local_fwd ex loc eid1 eid2.
Proof.
  destruct eid1 as [tid1 n1].
  destruct eid2 as [tid2 n2].
  inv RFI. inv H0. ss. subst.
  destruct (Nat.compare_spec n1 n2).
  - subst. exfalso. eapply EX.(Valid.CORW).
    econs. esplits; try exact H. eauto.
  - econs; ss. i. destruct eid. inv PO. inv PO0. ss. subst.
    inv EID1. inv EID2.
    exploit Valid.po_label; eauto.
    { instantiate (1 := (t, n)). econs; ss. }
    i. des. econs; eauto. intro X.
    exploit Valid.coherence_ww.
    { eauto. }
    { econs; try exact EID; eauto. }
    { econs; try exact LABEL1; eauto. }
    { econs; ss. }
    i.
    exploit Valid.coherence_wr; try exact H; eauto.
    { econs; try exact LABEL1; eauto. }
    { econs; try exact EID0; eauto. }
    { econs; ss. }
    i. des.
    exploit EX.(Valid.RF_WF); [exact H|exact RF|]. i. subst.
    inv CO.
    + inv H1. lia.
    + exfalso. eapply EX.(Valid.EXTERNAL). econs 2; econs; left; left; left; left; right; eauto.
  - exfalso. eapply EX.(Valid.CORW). econs. esplits; [|exact H]. econs 2. ss.
Qed.

Lemma sim_local_fwd_spec
      p ex loc eid tid iid
      (EX: Valid.ex p ex)
      (LABEL: Execution.label_is ex (fun l : Label.t => ~ Label.is_kinda_writing loc l) (tid, iid))
      (VWN: sim_local_fwd ex loc eid (tid, iid)):
  <<FWD_S: sim_local_fwd ex loc eid (tid, S iid)>>.
Proof.
  rewrite sim_local_fwd_step. econs. instantiate (1 := (_, _)). splits; [|econs; ss].
  left. econs. splits; eauto. econs; eauto with tso.
Qed.

Definition sim_local_fwd_none ex loc :=
  ⦗ex.(Execution.label_is) (Label.is_kinda_writing loc)⦘ ⨾ Execution.po.

Lemma sim_local_fwd_none_step ex loc:
  sim_local_fwd_none ex loc =
  (sim_local_fwd_none ex loc ∪ ⦗ex.(Execution.label_is) (Label.is_kinda_writing loc)⦘) ⨾
  Execution.po_adj.
Proof.
  unfold sim_local_fwd_none. rewrite ? (union_seq' Execution.po_adj), ? seq_assoc, ? union_assoc.
  rewrite Execution.po_po_adj at 1.
  rewrite (clos_refl_union Execution.po), union_seq, eq_seq.
  rewrite ? (seq_union' (Execution.po ⨾ Execution.po_adj) Execution.po_adj), ? seq_assoc, ? union_assoc.
  refl.
Qed.

Lemma sim_local_fwd_none_spec
      p ex loc tid iid
      (EX: Valid.ex p ex)
      (LABEL: Execution.label_is ex (fun l : Label.t => ~ Label.is_kinda_writing loc l) (tid, iid))
      (FWDN: forall eid : eidT, ~ inverse (sim_local_fwd_none ex loc) (eq (tid, iid)) eid):
  <<FWDN_S: forall eid : eidT, ~ inverse (sim_local_fwd_none ex loc) (eq (tid, S iid)) eid>>.
Proof.
  ii.
  inv H. inv REL. inv H. rewrite Execution.po_po_adj in H1. inv H1. des.
  destruct x, x0. inv H1. ss. inv N. inv H.
  - inv H1. inv H0. inv H1. inv LABEL. rewrite EID in EID0. inv EID0. ss.
  - inv H1. ss. subst. eapply FWDN. econs; eauto. econs; eauto with tso.
Qed.

Definition sim_local_coh_cl ex loc :=
  ⦗ex.(Execution.label_is) (Label.is_kinda_writing_cl loc)⦘ ⨾
  (Execution.rfe ex)^? ⨾
  Execution.po.

Lemma sim_local_coh_cl_step ex loc:
  sim_local_coh_cl ex loc =
  (sim_local_coh_cl ex loc ∪
   ⦗ex.(Execution.label_is) (Label.is_kinda_writing_cl loc)⦘ ⨾ (Execution.rfe ex)^?) ⨾
  Execution.po_adj.
Proof.
  unfold sim_local_coh_cl. rewrite Execution.po_po_adj at 1.
  rewrite (clos_refl_union Execution.po), union_seq, eq_seq.
  rewrite ? seq_union, ? union_seq, ? seq_assoc.
  refl.
Qed.

Lemma sim_local_coh_cl_spec
      ex loc1 loc2 eid1 eid2
      (CL: Loc.cl loc1 loc2):
  sim_local_coh_cl ex loc1 eid1 eid2 <-> sim_local_coh_cl ex loc2 eid1 eid2.
Proof.
  split.
  - i. inv H. obtac.
    econs. simtac. econs; eauto.
    destruct l; ss; eapply Loc.cl_trans; eauto; eapply Loc.cl_sym; ss.
  - i. inv H. obtac.
    econs. simtac. econs; eauto.
    destruct l; ss; eapply Loc.cl_trans; eauto; eapply Loc.cl_sym; ss.
Qed.

Definition sim_local_vpn ex :=
  (⦗ex.(Execution.label_is) Label.is_kinda_read⦘ ⨾
   Execution.po) ∪

  (⦗ex.(Execution.label_is) (Label.is_access)⦘ ⨾
   Execution.po ⨾
   (⦗ex.(Execution.label_is) (Label.is_barrier_c Barrier.is_mfence)⦘ ∪
    ⦗ex.(Execution.label_is) (Label.is_barrier_c Barrier.is_sfence)⦘) ⨾
   Execution.po).

Lemma sim_local_vpn_step ex:
  sim_local_vpn ex =
  (sim_local_vpn ex ∪
   ((⦗ex.(Execution.label_is) Label.is_kinda_read⦘) ∪

    (⦗ex.(Execution.label_is) (Label.is_access)⦘ ⨾
     Execution.po ⨾
     (⦗ex.(Execution.label_is) (Label.is_barrier_c Barrier.is_mfence)⦘ ∪
      ⦗ex.(Execution.label_is) (Label.is_barrier_c Barrier.is_sfence)⦘)))) ⨾
  Execution.po_adj.
Proof.
  unfold sim_local_vpn. rewrite ? (union_seq' Execution.po_adj), ? seq_assoc, ? union_assoc.
  rewrite Execution.po_po_adj at 1 3.
  rewrite (clos_refl_union Execution.po), union_seq, eq_seq.
  rewrite ? (seq_union' (Execution.po ⨾ Execution.po_adj) Execution.po_adj), ? seq_assoc, ? union_assoc.
  funext. i. funext. i. propext. econs; i.
  - repeat match goal with
           | [H: (_ ∪ _) _ _ |- _] => inv H
           end;
      eauto 10 using union_l, union_r.
  - repeat match goal with
           | [H: (_ ∪ _) _ _ |- _] => inv H
           end;
      eauto 10 using union_l, union_r.
Qed.

Definition sim_local_lper ex loc :=
  (⦗ex.(Execution.label_is) (Label.is_flushopting_cl loc)⦘ ⨾
   Execution.po).

Lemma sim_local_lper_step ex loc:
  sim_local_lper ex loc =
  (sim_local_lper ex loc ∪
   (⦗ex.(Execution.label_is) (Label.is_flushopting_cl loc)⦘)) ⨾
  Execution.po_adj.
Proof.
  unfold sim_local_lper.
  rewrite ? (union_seq' Execution.po_adj), ? seq_assoc, ? union_assoc.
  rewrite Execution.po_po_adj at 1.
  rewrite (clos_refl_union Execution.po).
  replace ((Execution.po ∪ eq) ⨾ Execution.po_adj)
    with (Execution.po ⨾ Execution.po_adj ∪ eq ⨾ Execution.po_adj); cycle 1.
  { rewrite union_seq. ss. }
  rewrite eq_seq.
  rewrite ? (seq_union' (Execution.po ⨾ Execution.po_adj) Execution.po_adj), ? seq_assoc, ? union_assoc.
  funext. i. funext. i. propext. econs; i.
  - repeat match goal with
           | [H: (_ ∪ _) _ _ |- _] => inv H
           end;
      eauto 10 using union_l, union_r.
  - repeat match goal with
           | [H: (_ ∪ _) _ _ |- _] => inv H
           end;
      eauto 10 using union_l, union_r.
Qed.

Definition sim_local_per ex loc :=
  (⦗ex.(Execution.label_is) (Label.is_flushing_cl loc)⦘ ⨾
   Execution.po) ∪

  (sim_local_lper ex loc ⨾
   ⦗ex.(Execution.label_is) (Label.is_persist_barrier)⦘ ⨾
   Execution.po).

Lemma sim_local_per_step ex loc:
  sim_local_per ex loc =
  (sim_local_per ex loc ∪
   ((⦗ex.(Execution.label_is) (Label.is_flushing_cl loc)⦘) ∪

    (sim_local_lper ex loc ⨾
     ⦗ex.(Execution.label_is) (Label.is_persist_barrier)⦘))) ⨾
  Execution.po_adj.
Proof.
  unfold sim_local_per.
  rewrite ? (union_seq' Execution.po_adj), ? seq_assoc, ? union_assoc.
  rewrite Execution.po_po_adj at 1 2.
  rewrite (clos_refl_union Execution.po).
  replace ((Execution.po ∪ eq) ⨾ Execution.po_adj)
    with (Execution.po ⨾ Execution.po_adj ∪ eq ⨾ Execution.po_adj); cycle 1.
  { rewrite union_seq. ss. }
  rewrite eq_seq.
  rewrite ? (seq_union' (Execution.po ⨾ Execution.po_adj) Execution.po_adj), ? seq_assoc, ? union_assoc.
  funext. i. funext. i. propext. econs; i.
  - repeat match goal with
           | [H: (_ ∪ _) _ _ |- _] => inv H
           end;
      eauto 10 using union_l, union_r.
  - repeat match goal with
           | [H: (_ ∪ _) _ _ |- _] => inv H
           end;
      eauto 10 using union_l, union_r.
Qed.
