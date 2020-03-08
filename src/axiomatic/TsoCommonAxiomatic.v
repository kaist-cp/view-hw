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
Require Import PromisingArch.promising.TsoPromising2.
Require Import PromisingArch.promising.CommonPromising.
Require Import PromisingArch.promising.StateExecFacts.
Require Import PromisingArch.axiomatic.TsoAxiomatic.

Set Implicit Arguments.


Inductive inverse A (rel:relation A) (codom:A -> Prop) (a:A): Prop :=
| inverse_intro
    a'
    (REL: rel a a')
    (CODOM: codom a')
.
Hint Constructors inverse.

Lemma inverse_mon A (r1 r2:relation A)
      (REL: r1 ⊆ r2):
  inverse r1 <2= inverse r2.
Proof.
  i. inv PR. econs; eauto.
Qed.

Lemma inverse_union A (r1 r2:relation A) s:
  inverse (r1 ∪ r2) s = inverse r1 s \1/ inverse r2 s.
Proof.
  funext. i. propext. econs; i.
  - inv H. inv REL; eauto.
  - des; inv H; econs; eauto.
    + left. ss.
    + right. ss.
Qed.

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

Inductive sim_local_weak (local: Local.t) (alocal: ALocal.t): Prop :=
| sim_local_weak_none
| sim_local_weak_some
.
Hint Constructors sim_local_weak.

Lemma sim_state_weak_init stmts:
  sim_state_weak (State.init stmts) (State.init stmts).
Proof.
  econs; ss. econs. ii. unfold RMap.init. rewrite ? IdMap.gempty. econs.
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
| sim_event_barrier
    b1 b2
    (BARRIER: b1 = b2):
    sim_event (Event.barrier b1) (Event.barrier b2)
.
Hint Constructors sim_event.

Definition sim_local_coh ex loc :=
  ⦗ex.(Execution.label_is) (Label.is_writing loc)⦘ ⨾
  (Execution.rfe ex)^? ⨾
  Execution.po.

Lemma sim_local_coh_step ex loc:
  sim_local_coh ex loc =
  (sim_local_coh ex loc ∪
   ⦗ex.(Execution.label_is) (Label.is_writing loc)⦘ ⨾ (Execution.rfe ex)^?) ⨾
  Execution.po_adj.
Proof.
  unfold sim_local_coh. rewrite Execution.po_po_adj at 1.
  rewrite (clos_refl_union Execution.po), union_seq, eq_seq.
  rewrite ? seq_union, ? union_seq, ? seq_assoc.
  refl.
Qed.

Definition sim_local_vrn ex :=
  (⦗ex.(Execution.label_is) Label.is_read⦘ ⨾
   Execution.po) ∪

  (⦗ex.(Execution.label_is) Label.is_write⦘ ⨾
   Execution.po ⨾
   ⦗ex.(Execution.label_is) (Label.is_barrier_c Barrier.is_dmb_wr)⦘ ⨾
   Execution.po).

Lemma sim_local_vrn_step ex:
  sim_local_vrn ex =
  (sim_local_vrn ex ∪
   ((⦗ex.(Execution.label_is) Label.is_read⦘) ∪

   (⦗ex.(Execution.label_is) Label.is_write⦘ ⨾
     Execution.po ⨾
     ⦗ex.(Execution.label_is) (Label.is_barrier_c Barrier.is_dmb_wr)⦘))) ⨾
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
      (EID2: Execution.label_is ex Label.is_read eid2)
      (VRN: sim_local_vrn ex eid1 eid2):
  <<OB: Execution.ob ex eid1 eid2>>.
Proof.
  inv EID2. destruct l; inv LABEL. unfold sim_local_vrn in VRN.
  repeat match goal with
         | [H: (_ ∪ _) _ _ |- _] => inv H
         end.
  - left. right. left.
    inv H. des. econs. splits; eauto.
    econs. instantiate (1 := eid2). splits; ss.
    econs; eauto. econs; eauto.
  - right. inv H. des. econs. splits; eauto.
    rewrite ? seq_assoc. econs. instantiate (1 := eid2). splits; cycle 1.
    { econs; eauto. econs; eauto. }
    rewrite <- ? seq_assoc. ss.
  - left. right. right.
    inv VRN; inv H; des; inv H0; inv H2.
    + rewrite seq_assoc. econs. splits; cycle 1.
      { econs; eauto. econs; eauto. }
      econs. econs; eauto. econs; eauto with tso.
      destruct l; ss; econs; eauto with tso.
    + rewrite seq_assoc. econs. splits; cycle 1.
      { econs; eauto. econs; eauto. }
      econs. splits.
      { destruct l; ss; econs; eauto with tso. }
      inv H1. des. inv H0. des. inv H1.
      eapply Execution.po_chain. econs; eauto.
Qed.

Definition sim_local_vwn ex :=
  (⦗ex.(Execution.label_is) Label.is_read⦘ ⨾
   Execution.po) ∪

  (⦗ex.(Execution.label_is) Label.is_write⦘ ⨾
   Execution.po).

Lemma sim_local_vwn_step ex:
  sim_local_vwn ex =
  (sim_local_vwn ex ∪
   ((⦗ex.(Execution.label_is) Label.is_read⦘) ∪

   (⦗ex.(Execution.label_is) Label.is_write⦘))) ⨾
  Execution.po_adj.
Proof.
  unfold sim_local_vwn. rewrite ? (union_seq' Execution.po_adj), ? seq_assoc, ? union_assoc.
  rewrite Execution.po_po_adj at 1 2.
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

Lemma sim_local_vwn_spec
      p ex eid1 eid2
      (EX: Valid.ex p ex)
      (EID2: Execution.label_is ex Label.is_write eid2)
      (VWN: sim_local_vwn ex eid1 eid2):
  <<OB: Execution.ob ex eid1 eid2>>.
Proof.
  inv EID2. destruct l; inv LABEL. unfold sim_local_vwn in VWN.
  repeat match goal with
         | [H: (_ ∪ _) _ _ |- _] => inv H
         end.
  - left. right. right.
    inv H. des. inv H0. inv H2. econs. splits; cycle 1.
    { econs; eauto. econs; eauto. econs; eauto with tso. }
    econs; eauto. destruct l; econs; eauto with tso.
  - left. right. right.
    inv H. des. inv H0. inv H2. econs. splits; cycle 1.
    { econs; eauto. econs; eauto. econs; eauto with tso. }
    econs; eauto. destruct l; econs; eauto with tso.
  - left. right. right.
    inv VWN; inv H; inv H0; inv H; inv H2.
    + rewrite seq_assoc. econs. splits; cycle 1.
      { econs; eauto. econs; eauto. }
      econs. econs; eauto. econs; eauto with tso.
      destruct l; ss; econs; eauto with tso.
    + rewrite seq_assoc. econs. splits; cycle 1.
      { econs; eauto. econs; eauto. }
      econs. splits; eauto. econs; eauto.
      destruct l; ss; econs; eauto with tso.
Qed.

Definition sim_local_vro ex :=
  ⦗ex.(Execution.label_is) (Label.is_read)⦘ ⨾ Execution.po.

Lemma sim_local_vro_step ex:
  sim_local_vro ex =
  (sim_local_vro ex ∪ ⦗ex.(Execution.label_is) (Label.is_read)⦘) ⨾
  Execution.po_adj.
Proof.
  unfold sim_local_vro. rewrite ? (union_seq' Execution.po_adj), ? seq_assoc, ? union_assoc.
  rewrite Execution.po_po_adj at 1.
  rewrite (clos_refl_union Execution.po), union_seq, eq_seq.
  rewrite ? (seq_union' (Execution.po ⨾ Execution.po_adj) Execution.po_adj), ? seq_assoc, ? union_assoc.
  refl.
Qed.

Definition sim_local_vwo ex :=
  ⦗ex.(Execution.label_is) (Label.is_write)⦘ ⨾ Execution.po.

Lemma sim_local_vwo_step ex:
  sim_local_vwo ex =
  (sim_local_vwo ex ∪ ⦗ex.(Execution.label_is) (Label.is_write)⦘) ⨾
  Execution.po_adj.
Proof.
  unfold sim_local_vwo. rewrite ? (union_seq' Execution.po_adj), ? seq_assoc, ? union_assoc.
  rewrite Execution.po_po_adj at 1.
  rewrite (clos_refl_union Execution.po), union_seq, eq_seq.
  rewrite ? (seq_union' (Execution.po ⨾ Execution.po_adj) Execution.po_adj), ? seq_assoc, ? union_assoc.
  refl.
Qed.

