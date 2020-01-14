Require Import Relations.
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

Set Implicit Arguments.


Module Label.
  Inductive t :=
  | read (loc:Loc.t) (val:Val.t)
  | write (loc:Loc.t) (val:Val.t)
  | update (loc:Loc.t) (vold vnew:Val.t)
  | barrier (b:Barrier.t)
  .
  Hint Constructors t.

  Definition is_read (label:t): bool :=
    match label with
    | read _ _ => true
    | update _ _ _ => true
    | _ => false
    end.

  Definition is_reading (loc:Loc.t) (label:t): bool :=
    match label with
    | read loc' _ => loc' == loc
    | update loc' _ _ => loc' == loc
    | _ => false
    end.

  Definition is_reading_val (loc:Loc.t) (val:Val.t) (label:t): bool :=
    match label with
    | read loc' val' => (loc' == loc) && (val' == val)
    | update loc' val' _ => (loc' == loc) && (val' == val)
    | _ => false
    end.

  Definition is_write (label:t): bool :=
    match label with
    | write _ _ => true
    | update _ _ _ => true
    | _ => false
    end.

  Definition is_writing (loc:Loc.t) (label:t): bool :=
    match label with
    | write loc' _ => loc' == loc
    | update loc' _ _ => loc' == loc
    | _ => false
    end.

  Definition is_writing_val (loc:Loc.t) (val:Val.t) (label:t): bool :=
    match label with
    | write loc' val' => (loc' == loc) && (val' == val)
    | update loc' _ val' => (loc' == loc) && (val' == val)
    | _ => false
    end.

  Definition is_access (label:t): bool :=
    match label with
    | read _ _ => true
    | write _ _ => true
    | update _ _ _ => true
    | _ => false
    end.

  Definition is_accessing (loc:Loc.t) (label:t): bool :=
    match label with
    | read loc' _ => loc' == loc
    | write loc' _ => loc' == loc
    | update loc' _ _ => loc' == loc
    | _ => false
    end.

  Definition is_barrier (label:t): bool :=
    match label with
    | barrier b => true
    | _ => false
    end.

  Definition is_barrier_c (c:Barrier.t -> bool) (label:t): bool :=
    match label with
    | barrier b => c b
    | _ => false
    end.

  Lemma reading_is_read
        loc l
        (RD: is_reading loc l):
    is_read l.
  Proof.
    destruct l; ss.
  Qed.

  Lemma reading_is_access
        loc l
        (RD: is_reading loc l):
    is_access l.
  Proof.
    destruct l; ss.
  Qed.

  Lemma reading_is_accessing
        loc l
        (RD: is_reading loc l):
    is_accessing loc l.
  Proof.
    destruct l; ss.
  Qed.

  Lemma read_is_reading loc val:
    is_reading loc (read loc val).
  Proof.
    s. destruct (equiv_dec loc loc); ss. exfalso. apply c. ss.
  Qed.

  Lemma reading_exists_val
        loc l
        (RDING: is_reading loc l):
    exists val,
      is_reading_val loc val l.
  Proof.
    destruct l; ss; destruct (equiv_dec loc0 loc); ss.
    - eexists val. destruct (equiv_dec val val); ss. exfalso. apply c. ss.
    - eexists vold. destruct (equiv_dec vold vold); ss. exfalso. apply c. ss.
  Qed.

  Lemma reading_val_is_reading
        loc val l
        (RDING: is_reading_val loc val l):
    is_reading loc l.
  Proof.
    destruct l; ss; destruct (equiv_dec loc0 loc); ss.
  Qed.

  Lemma writing_is_write
        loc l
        (WR: is_writing loc l):
    is_write l.
  Proof.
    destruct l; ss.
  Qed.

  Lemma writing_is_access
        loc l
        (WR: is_writing loc l):
    is_access l.
  Proof.
    destruct l; ss.
  Qed.

  Lemma writing_is_accessing
        loc l
        (WR: is_writing loc l):
    is_accessing loc l.
  Proof.
    destruct l; ss.
  Qed.

  Lemma write_is_writing loc val:
    is_writing loc (write loc val).
  Proof.
    s. destruct (equiv_dec loc loc); ss. exfalso. apply c. ss.
  Qed.

  Lemma writing_val_is_writing
        loc val l
        (RDING: is_writing_val loc val l):
    is_writing loc l.
  Proof.
    destruct l; ss; destruct (equiv_dec loc0 loc); ss.
  Qed.

  Lemma read_is_accessing loc val:
    is_accessing loc (read loc val).
  Proof.
    s. destruct (equiv_dec loc loc); ss. exfalso. apply c. ss.
  Qed.

  Lemma write_is_accessing loc val:
    is_accessing loc (write loc val).
  Proof.
    s. destruct (equiv_dec loc loc); ss. exfalso. apply c. ss.
  Qed.

  Lemma update_is_accessing loc vold vnew:
    is_accessing loc (update loc vold vnew).
  Proof.
    s. destruct (equiv_dec loc loc); ss. exfalso. apply c. ss.
  Qed.

  (* TODO: how to migrate these lemmas? *)
  (* Lemma is_writing_inv *)
  (*       loc l *)
  (*       (WRITING: is_writing loc l): *)
  (*   exists val, *)
  (*     l = write loc val. *)
  (* Proof. *)
  (*   destruct l; ss. destruct (equiv_dec loc0 loc); ss. inv e. eauto. *)
  (* Qed. *)

  (* Lemma is_reading_inv *)
  (*       loc l *)
  (*       (READING: is_reading loc l): *)
  (*   exists val, *)
  (*     l = read loc val. *)
  (* Proof. *)
  (*   destruct l; ss. destruct (equiv_dec loc0 loc); ss. inv e. eauto. *)
  (* Qed. *)
End Label.

Module ALocal.
  Inductive t := mk {
    labels: list Label.t;
  }.
  Hint Constructors t.

  Definition init: t := mk [].

  Definition next_eid (eu:t): nat :=
    List.length eu.(labels).

  Inductive step (event:Event.t (A:=unit)) (alocal1:t) (alocal2:t): Prop :=
  | step_internal
      (EVENT: event = Event.internal)
      (ALOCAL: alocal2 =
               mk
                 alocal1.(labels))
  | step_read
      vloc res
      (EVENT: event = Event.read false false OrdR.pln vloc (ValA.mk _ res tt))
      (ALOCAL: alocal2 =
               mk
                 (alocal1.(labels) ++ [Label.read vloc.(ValA.val) res]))
  | step_write
      ord vloc vval
      (EVENT: event = Event.write false ord vloc vval (ValA.mk _ 0 tt))
      (ALOCAL: alocal2 =
               mk
                 (alocal1.(labels) ++ [Label.write vloc.(ValA.val) vval.(ValA.val)]))
  | step_update
      ordr ordw vloc voldv vnewv
      (EVENT: event = Event.rmw ordr ordw vloc voldv vnewv)
      (ALOCAL: alocal2 =
               mk
                 (alocal1.(labels) ++ [Label.update vloc.(ValA.val) voldv.(ValA.val) vnewv.(ValA.val)]))
  | step_barrier
      b
      (EVENT: event = Event.barrier b)
      (ALOCAL: alocal2 =
               mk
                 (alocal1.(labels) ++ [Label.barrier b]))
  .
  Hint Constructors step.

  Inductive le (alocal1 alocal2:t): Prop :=
  | le_intro
      (LABELS: exists l, alocal2.(labels) = alocal1.(labels) ++ l)
  .
  Hint Constructors le.

  Global Program Instance le_preorder: PreOrder le.
  Next Obligation.
    ii. econs.
    all: try by exists []; rewrite List.app_nil_r.
    all: try by apply inclusion_refl.
  Qed.
  Next Obligation.
    ii. inv H; inv H0. econs.
    all: try by eapply inclusion_trans; eauto.
    des. rewrite LABELS0, LABELS. rewrite <- List.app_assoc. eexists; eauto.
  Qed.
End ALocal.

Module AExecUnit.
  Inductive t := mk {
    state: State.t (A:=unit);
    local: ALocal.t;
  }.
  Hint Constructors t.

  Inductive step (eu1 eu2:t): Prop :=
  | step_intro
      e
      (STATE: State.step e eu1.(state) eu2.(state))
      (LOCAL: ALocal.step e eu1.(local) eu2.(local))
  .
  Hint Constructors step.

  Inductive label_is (labels:list Label.t) (pred:Label.t -> Prop) (iid:nat): Prop :=
  | label_is_intro
      l
      (EID: List.nth_error labels iid = Some l)
      (LABEL: pred l)
  .
  Hint Constructors label_is.

  Definition wf_rmap (rmap: RMap.t (A:=unit)) (labels:list Label.t): Prop := True.
  Hint Unfold wf_rmap.

  Inductive wf (aeu:t): Prop :=
  | wf_intro
      (REG: wf_rmap aeu.(state).(State.rmap) aeu.(local).(ALocal.labels))
  .
  Hint Constructors wf.

  Lemma label_is_lt
        labels pred iid
        (LABEL: label_is labels pred iid):
    iid < length labels.
  Proof.
    inv LABEL. apply List.nth_error_Some. congr.
  Qed.

  Lemma label_is_mon
        labels1 labels2 pred:
    label_is labels1 pred <1= label_is (labels1 ++ labels2) pred.
  Proof.
    ii. inv PR. econs; eauto.
    rewrite List.nth_error_app1; ss.
    apply List.nth_error_Some. congr.
  Qed.

  Lemma union_mon
        A
        (p1 p2 q1 q2: A -> Prop)
        (P: p1 <1= p2)
        (Q: q1 <1= q2):
    (p1 ∪₁ q1) <1= (p2 ∪₁ q2).
  Proof.
    ii. inv PR.
    - left. eauto.
    - right. eauto.
  Qed.

  Lemma times_mon
        A
        (p1 p2 q1 q2: A -> Prop)
        (P: p1 <1= p2)
        (Q: q1 <1= q2):
    p1 × q1 <2= p2 × q2.
  Proof.
    ii. inv PR. econs; eauto.
  Qed.

  Lemma wf_init stmts: wf (mk (State.init stmts) ALocal.init).
  Proof.
    econs; ss.
  Qed.

  Lemma step_future
        eu1 eu2
        (WF: wf eu1)
        (STEP: step eu1 eu2):
    <<WF: wf eu2>> /\
    <<LE: ALocal.le eu1.(local) eu2.(local)>>.
  Proof.
    destruct eu1 as [state1 local1].
    destruct eu2 as [state2 local2].
    inv STEP. ss.
    inv STATE; inv LOCAL; inv EVENT; ss;
      repeat match goal with
             | [|- context[bot × _]] => rewrite cross_bot_l
             | [|- context[_ ∪ bot]] => rewrite union_bot_r
             end.
    - splits.
      + inv WF. econs; ss.
      + destruct local1. refl.
    - splits.
      + inv WF. econs; ss.
      + destruct local1. refl.
    - splits.
      + inv WF. econs; ss.
        all: try rewrite List.app_length; s.
        all: unfold ALocal.next_eid in *.
      + econs; ss.
        * esplits; eauto.
    - splits.
      + inv WF. econs; ss.
        all: try rewrite List.app_length; s.
        all: unfold ALocal.next_eid in *.
      + econs; ss.
        * esplits; eauto.
    - splits.
      + inv WF. econs; ss.
        all: try rewrite List.app_length; s.
        all: unfold ALocal.next_eid in *.
      + econs; ss.
        * esplits; eauto.
    - splits.
      + inv WF. econs; ss.
        all: try rewrite List.app_length; s.
        all: unfold ALocal.next_eid in *.
      + econs; ss. eexists; eauto.
    - splits.
      + inv WF. econs; ss.
      + destruct local1. refl.
  Qed.

  Lemma rtc_step_future
        eu1 eu2
        (WF: wf eu1)
        (STEP: rtc step eu1 eu2):
    <<WF: wf eu2>> /\
    <<LE: ALocal.le eu1.(local) eu2.(local)>>.
  Proof.
    revert WF. induction STEP; eauto.
    - esplits; eauto. refl.
    - i. exploit step_future; eauto. i. des.
      exploit IHSTEP; eauto. i. des.
      esplits; ss. etrans; eauto.
  Qed.
End AExecUnit.

Definition eidT := (Id.t * nat)%type.

Module Execution.
  Inductive t := mk {
    labels: IdMap.t (list Label.t);
    co: relation eidT;
    rf: relation eidT;
  }.
  Hint Constructors t.

  Definition label (eid:eidT) (ex:t): option Label.t :=
    match IdMap.find (fst eid) ex.(labels) with
    | None => None
    | Some labels => List.nth_error labels (snd eid)
    end.

  Definition eids (ex:t): list eidT :=
    IdMap.fold
      (fun tid local eids => (List.map (fun i => (tid, i)) (List.seq 0 (List.length local))) ++ eids)
      ex.(labels)
      [].

  Lemma eids_spec ex:
    <<LABEL: forall eid, label eid ex <> None <-> List.In eid (eids ex)>> /\
    <<NODUP: List.NoDup (eids ex)>>.
  Proof.
    generalize (PositiveMap.elements_3w (labels ex)). intro NODUP.
    hexploit SetoidList.NoDupA_rev; eauto.
    { apply IdMap.eqk_equiv. }
    intro NODUP_REV. splits.
    - (* LABEL *)
      i. destruct eid. unfold label, eids. s.
      rewrite IdMap.fold_1, <- List.fold_left_rev_right, IdMap.elements_spec.
      rewrite SetoidList_findA_rev; eauto; cycle 1.
      { apply eq_equivalence. }
      { apply []. }
      revert NODUP_REV. induction (List.rev (IdMap.elements (labels ex))); ss.
      destruct a. i. inv NODUP_REV. s. rewrite List.in_app_iff, <- IHl; ss.
      match goal with
      | [|- context[if ?c then true else false]] => destruct c
      end; ss; i; cycle 1.
      { econs; eauto. i. des; ss.
        apply List.in_map_iff in H. des. inv H. congr.
      }
      inv e. rewrite List.nth_error_Some, List.in_map_iff.
      econs; i; des.
      + left. esplits; eauto. apply HahnList.in_seq0_iff. ss.
      + inv H. apply HahnList.in_seq0_iff. ss.
      + revert H.
        match goal with
        | [|- context[match ?f with Some _ => _ | None => _ end]] => destruct f eqn:FIND
        end; ss.
        apply SetoidList.findA_NoDupA in FIND; ss; cycle 1.
        { apply eq_equivalence. }
        exfalso. apply H1. revert FIND. clear. induction l; i; inv FIND.
        * destruct a. ss. des. inv H0. left. ss.
        * right. apply IHl. ss.
    - (* NODUP *)
      unfold eids. rewrite IdMap.fold_1, <- List.fold_left_rev_right.
      revert NODUP_REV. induction (List.rev (IdMap.elements (labels ex))); ss. i.
      inv NODUP_REV. destruct a. s.
      apply HahnList.nodup_app. splits; eauto.
      + apply FinFun.Injective_map_NoDup.
        * ii. inv H. ss.
        * apply List.seq_NoDup.
      + ii. apply List.in_map_iff in IN1. des. subst.
        apply H1. revert IN2. clear. induction l; ss.
        i. apply List.in_app_iff in IN2. des.
        * apply List.in_map_iff in IN2. des. inv IN2. left. ss.
        * right. eauto.
  Qed.

  Inductive label_is (ex:t) (pred:Label.t -> Prop) (eid:eidT): Prop :=
  | label_is_intro
      l
      (EID: label eid ex = Some l)
      (LABEL: pred l)
  .
  Hint Constructors label_is.

  Inductive label_rel (ex:t) (rel:relation Label.t) (eid1 eid2:eidT): Prop :=
  | label_rel_intro
      l1 l2
      (EID1: label eid1 ex = Some l1)
      (EID2: label eid2 ex = Some l2)
      (LABEL: rel l1 l2)
  .
  Hint Constructors label_rel.

  Inductive label_is_rel (ex: t) (pred: Label.t -> Prop) (eid1 eid2: eidT): Prop :=
  | label_is_rel_intro
      l1 l2
      (EID1: label eid1 ex = Some l1)
      (EID2: label eid2 ex = Some l2)
      (LABEL1: pred l1)
      (LABEL2: pred l2)
  .
  Hint Constructors label_is_rel.

  Inductive label_loc (x y:Label.t): Prop :=
  | label_loc_intro
      loc
      (X: Label.is_accessing loc x)
      (Y: Label.is_accessing loc y)
  .
  Hint Constructors label_loc.

  Lemma label_is_mon
        exec p1 p2 eid
        (PREL: p1 <1= p2)
        (P1: label_is exec p1 eid):
    label_is exec p2 eid.
  Proof.
    destruct P1; eauto.
  Qed.

  (* let obs = rfe | fr | co *)
  (* let dob = ([R]; po; [E]) U ([E]; po; [W]) *)
  (* let bob = [E]; po; [MF]; po; [E] ~~~> [W]; po; [dmb wr]; po; [R] *)
  (* let ob = obs | dob | bob *)
  (* irrefl po; rf as corw *)
  (* irrefl po; fr as cowr *)
  (* acyclic ob as external *)

  Inductive po (eid1 eid2:eidT): Prop :=
  | po_intro
      (TID: fst eid1 = fst eid2)
      (N: snd eid1 < snd eid2)
  .
  Hint Constructors po.

  Global Program Instance po_trans: Transitive po.
  Next Obligation.
    ii. destruct x, y, z. inv H. inv H0. ss. subst. econs; ss. lia.
  Qed.

  Inductive po_adj (eid1 eid2:eidT): Prop :=
  | po_adj_intro
      (TID: fst eid1 = fst eid2)
      (N: snd eid2 = S (snd eid1))
  .
  Hint Constructors po_adj.

  Lemma po_adj_po:
    po_adj ⊆ po.
  Proof.
    ii. destruct x, y. inv H. ss. subst. econs; ss.
  Qed.

  Lemma po_po_adj:
    po = po^? ⨾ po_adj.
  Proof.
    funext. i. funext. i. propext. econs; i.
    - inv H. destruct x, x0. ss. subst.
      destruct n0; [lia|].
      exists (t1, n0). splits; ss. inv N; [left|right]; eauto.
    - inv H. des. inv H0.
      + apply po_adj_po. ss.
      + etrans; eauto. apply po_adj_po. ss.
  Qed.

  Lemma po_po_adj_weak:
    (Execution.po ⨾ Execution.po_adj) ⊆ Execution.po.
  Proof.
    rewrite po_po_adj at 2. apply inclusion_seq_mon; ss.
    econs 2. ss.
  Qed.

  Lemma po_chain: Execution.po ⨾ Execution.po^? ⊆ Execution.po.
  Proof.
    ii. inv H. des. inv H0. destruct x, x0, y. ss. subst.
    inv H1; inv H; ss. subst. econs; ss. lia.
  Qed.

  Inductive i (eid1 eid2:eidT): Prop :=
  | i_intro
      (TID: fst eid1 = fst eid2)
  .
  Hint Constructors i.

  Inductive e (eid1 eid2:eidT): Prop :=
  | e_intro
      (TID: fst eid1 <> fst eid2)
  .
  Hint Constructors e.

  Definition fr (ex:t): relation eidT :=
    (ex.(rf)⁻¹ ⨾ ex.(co)) ∪
    ((ex.(label_rel) label_loc) ∩
     ((ex.(label_is) Label.is_read) \₁ codom_rel ex.(rf)) × (ex.(label_is) Label.is_write)).

  Definition rfe (ex:t): relation eidT := ex.(rf) ∩ e.

  Definition cowr (ex:t): relation eidT := po ⨾ (fr ex).
  Definition corw (ex:t): relation eidT := po ⨾ ex.(rf).

  Definition obs (ex:t): relation eidT := (rfe ex) ∪ (fr ex) ∪ ex.(co).

  Definition dob (ex:t): relation eidT :=
    (⦗ex.(label_is) Label.is_read⦘ ⨾
     po ⨾
     ⦗ex.(label_is) Label.is_access⦘) ∪
    (⦗ex.(label_is) Label.is_access⦘ ⨾
     po ⨾
     ⦗ex.(label_is) Label.is_write⦘).

  Definition bob (ex:t): relation eidT :=
    ⦗ex.(label_is) Label.is_write⦘ ⨾
     po ⨾
     ⦗ex.(label_is) (Label.is_barrier_c Barrier.is_dmb_wr)⦘ ⨾
     po ⨾
     ⦗ex.(label_is) Label.is_read⦘.

  Definition ob (ex:t): relation eidT :=
    (obs ex) ∪ (dob ex) ∪ (bob ex).
End Execution.

Inductive tid_lift (tid:Id.t) (rel:relation nat) (eid1 eid2:eidT): Prop :=
| tid_lift_intro
    (TID1: fst eid1 = tid)
    (TID1: fst eid2 = tid)
    (REL: rel (snd eid1) (snd eid2))
.
Hint Constructors tid_lift.

Lemma tid_lift_incl
      tid rel1 rel2
      (REL: rel1 ⊆ rel2):
  tid_lift tid rel1 ⊆ tid_lift tid rel2.
Proof.
  ii. inv H. econs; eauto.
Qed.

Inductive tid_join (rels: IdMap.t (relation nat)) (eid1 eid2:eidT): Prop :=
| tid_join_intro
    tid rel
    (RELS: IdMap.find tid rels = Some rel)
    (REL: tid_lift tid rel eid1 eid2)
.
Hint Constructors tid_join.


Module Valid.
  Inductive pre_ex (p:program) (ex:Execution.t) := mk_pre_ex {
    aeus: IdMap.t AExecUnit.t;

    AEUS: IdMap.Forall2
            (fun tid stmts aeu =>
               rtc AExecUnit.step
                   (AExecUnit.mk (State.init stmts) ALocal.init)
                   aeu)
            p aeus;
    LABELS: ex.(Execution.labels) = IdMap.map (fun aeu => aeu.(AExecUnit.local).(ALocal.labels)) aeus;
  }.
  Hint Constructors pre_ex.

  Definition co1 (ex: Execution.t) :=
    forall eid1 eid2,
      (exists loc,
          <<LABEL: ex.(Execution.label_is) (Label.is_writing loc) eid1>> /\
          <<LABEL: ex.(Execution.label_is) (Label.is_writing loc) eid2>>) ->
      (eid1 = eid2 \/ ex.(Execution.co) eid1 eid2 \/ ex.(Execution.co) eid2 eid1).

  Definition co2 (ex: Execution.t) :=
    forall eid1 eid2,
      ex.(Execution.co) eid1 eid2 ->
      exists loc,
        <<LABEL: ex.(Execution.label_is) (Label.is_writing loc) eid1>> /\
        <<LABEL: ex.(Execution.label_is) (Label.is_writing loc) eid2>>.

  Definition rf1 (ex: Execution.t) :=
    forall eid1 loc val
       (LABEL: ex.(Execution.label_is) (Label.is_reading_val loc val) eid1),
      (<<NORF: ~ codom_rel ex.(Execution.rf) eid1>> /\ <<VAL: val = Val.default>>) \/
      (exists eid2,
          <<LABEL: ex.(Execution.label_is) (Label.is_writing_val loc val) eid2>> /\
          <<RF: ex.(Execution.rf) eid2 eid1>>).

  Definition rf2 (ex: Execution.t) :=
    forall eid1 eid2 (RF: ex.(Execution.rf) eid2 eid1),
    exists loc val,
      <<READ: ex.(Execution.label_is) (Label.is_reading_val loc val) eid1>> /\
      <<WRITE: ex.(Execution.label_is) (Label.is_writing_val loc val) eid2>>.

  Definition rf_wf (ex: Execution.t) := functional (ex.(Execution.rf))⁻¹.

  Inductive ex (p:program) (ex:Execution.t) := mk_ex {
    PRE: pre_ex p ex;
    CO1: co1 ex;
    CO2: co2 ex;
    RF1: rf1 ex;
    RF2: rf2 ex;
    RF_WF: rf_wf ex;
    COWR: irreflexive (Execution.cowr ex);
    CORW: irreflexive (Execution.corw ex);
    EXTERNAL: acyclic (Execution.ob ex);
  }.
  Hint Constructors ex.
  Coercion PRE: ex >-> pre_ex.

  Definition is_terminal
             p ex (EX: pre_ex p ex): Prop :=
    forall tid aeu (FIND: IdMap.find tid EX.(aeus) = Some aeu),
      State.is_terminal aeu.(AExecUnit.state).

  Lemma po_label_pre
        p exec
        eid1 eid2 label2
        (PRE: pre_ex p exec)
        (PO: Execution.po eid1 eid2)
        (LABEL: Execution.label eid2 exec = Some label2):
    exists label1, <<LABEL: Execution.label eid1 exec = Some label1>>.
  Proof.
    destruct eid1, eid2. inv PO. ss. subst.
    revert LABEL. unfold Execution.label.
    rewrite PRE.(LABELS), ? IdMap.map_spec. s.
    destruct (IdMap.find t0 PRE.(aeus)) eqn:LOCAL; ss.
    generalize (PRE.(AEUS) t0). rewrite LOCAL. intro X. inv X. des.
    i. exploit List.nth_error_Some. rewrite LABEL. intros [X _]. exploit X; [congr|]. clear X. i.
    generalize (List.nth_error_Some t.(AExecUnit.local).(ALocal.labels) n). intros [_ X]. hexploit X; [lia|]. i.
    destruct (List.nth_error t.(AExecUnit.local).(ALocal.labels) n); ss. eauto.
  Qed.

  Lemma po_label
        p exec
        eid1 eid2 label2
        (EX: ex p exec)
        (PO: Execution.po eid1 eid2)
        (LABEL: Execution.label eid2 exec = Some label2):
    exists label1, <<LABEL: Execution.label eid1 exec = Some label1>>.
  Proof.
    inv EX. eapply po_label_pre; eauto.
  Qed.

  Lemma po_irrefl:
    forall eid,
      ~ Execution.po eid eid.
  Proof.
    ii. inv H. lia.
  Qed.

  Lemma coherence_ww
        p exec
        eid1 eid2 loc
        (EX: ex p exec)
        (EID1: exec.(Execution.label_is) (Label.is_writing loc) eid1)
        (EID2: exec.(Execution.label_is) (Label.is_writing loc) eid2)
        (PO: Execution.po eid1 eid2):
    exec.(Execution.co) eid1 eid2.
  Proof.
    inv EID1. inv EID2. exploit EX.(CO1).
    { esplits; econs; [exact EID| |exact EID0|]; eauto. }
    i. des; ss.
    - subst. apply po_irrefl in PO. inv PO.
    - exfalso. eapply EX.(EXTERNAL). apply t_step_rt. esplits.
      + left. left. right. eauto.
      + econs. left. right. right. econs. esplits.
        * econs; eauto. econs; eauto using Label.writing_is_access.
        * econs. esplits; eauto. econs; eauto. econs; eauto using Label.writing_is_write.
  Qed.

  Lemma coherence_wr
        p exec
        eid1 eid2 loc
        (EX: ex p exec)
        (EID1: exec.(Execution.label_is) (Label.is_writing loc) eid1)
        (EID2: exec.(Execution.label_is) (Label.is_reading loc) eid2)
        (PO: Execution.po eid1 eid2):
    exists eid3,
      <<RF: exec.(Execution.rf) eid3 eid2>> /\
      <<CO: exec.(Execution.co)^? eid1 eid3>>.
  Proof.
    inv EID1. inv EID2.
    inversion LABEL0. apply Label.reading_exists_val in H0. des.
    exploit EX.(RF1).
    { instantiate (1 := eid2). econs; eauto. }
    i. des.
    { exfalso. eapply EX.(COWR). econs; econs.
      - eauto.
      - right. econs; eauto.
        + econs; eauto.
          econs; eauto using Label.writing_is_accessing, Label.reading_is_accessing.
        + econs; econs; eauto using Label.reading_is_read, Label.writing_is_write.
    }
    esplits; eauto.
    exploit EX.(CO1).
    { esplits; [eauto|].
      eapply Execution.label_is_mon; eauto. s. i.
      eapply Label.writing_val_is_writing. eauto.
    }
    i. des; subst; ss.
    { refl. }
    { econs 2. ss. }
    exfalso. eapply EX.(COWR). econs; econs.
    - eauto.
    - econs; eauto. econs; eauto.
  Qed.

  Lemma coherence_rr
        p exec
        eid1 eid2 eid3 loc
        (EX: ex p exec)
        (EID1: exec.(Execution.label_is) (Label.is_reading loc) eid1)
        (EID2: exec.(Execution.label_is) (Label.is_reading loc) eid2)
        (EID3: exec.(Execution.label_is) (Label.is_writing loc) eid3)
        (RF: exec.(Execution.rf) eid3 eid1)
        (PO: Execution.po eid1 eid2):
    exists eid4,
      <<RF: exec.(Execution.rf) eid4 eid2>> /\
      <<CO: exec.(Execution.co)^? eid3 eid4>>.
  Proof.
    (* TODO *)
    (* (1): exploit EX.(RF1) *)
    (* (2): exploit EX.(CO1) *)
    (* (3): contradiction of po; fr; rf
            case rfe => ob "eid3 --rfe--> eid1 --co(from po)--> eid2 --fr--> eid3"
            case rfi => cowr "eid3 --po(from rfi)--> eid1 --po--> eid2 --fr--> eid3"
            *)
    admit.
  Qed.

  (*   inv EID1. apply Label.is_reading_inv in LABEL. des. subst. *)
  (*   inv EID2. apply Label.is_reading_inv in LABEL. des. subst. *)
  (*   inv EID3. apply Label.is_writing_inv in LABEL. des. subst. *)
  (*   exploit EX.(RF1); eauto. i. des. *)
  (*   { exfalso. eapply EX.(INTERNAL). econs 2; [econs|econs 2; econs]. *)
  (*     - left. econs; eauto. econs; eauto. *)
  (*       econs; eauto using Label.read_is_accessing, Label.write_is_accessing. *)
  (*     - admit. *)
  (*       (* - right. eauto. *) *)
  (*     - admit. *)
  (*     (* - left. left. left. econs; eauto. econs; eauto. *) *)
  (*     (*   econs; eauto using Label.read_is_accessing, Label.write_is_accessing. *) *)
  (*   } *)
  (*   esplits; eauto. *)
  (*   exploit EX.(CO1). *)
  (*   { rewrite EID1, LABEL. esplits; eauto. } *)
  (*   i. des. *)
  (*   - subst. eauto. *)
  (*   - econs 2. ss. *)
  (*   - exfalso. eapply EX.(INTERNAL). econs 2; [econs|econs 2; econs]. *)
  (*     + left. econs; eauto. econs; eauto. *)
  (*       econs; eauto using Label.read_is_accessing, Label.write_is_accessing. *)
  (*     + admit. *)
  (*       (* + left. left. right. left. econs; eauto. *) *)
  (*     + admit. *)
  (*     (* + right. ss. *) *)
  (* Grab Existential Variables. *)
  (* { admit. (* will be gone automatically.. *) } *)
  (* { admit. (* will be gone automatically.. *) } *)
  (* Qed. *)

  Lemma coherence_rw
        p exec
        eid1 eid2 eid3 loc
        (EX: ex p exec)
        (EID1: exec.(Execution.label_is) (Label.is_reading loc) eid1)
        (EID2: exec.(Execution.label_is) (Label.is_writing loc) eid2)
        (EID3: exec.(Execution.label_is) (Label.is_writing loc) eid3)
        (RF1: exec.(Execution.rf) eid3 eid1)
        (PO: Execution.po eid1 eid2):
    exec.(Execution.co) eid3 eid2.
  Proof.
    inv EID1. inv EID2. inv EID3.
    exploit EX.(CO1).
    { esplits; econs; [exact EID0| |exact EID1|]; eauto. }
    i. apply or_assoc in x0. destruct x0; [|done].
    destruct (fst eid1 == fst eid3).
    - (* rfi *)
      exfalso. eapply EX.(CORW). econs; eauto. esplits; [|by eauto].
      apply Execution.po_chain. econs. splits; eauto.
      des; [by left|right].
      destruct eid1 as [tid1 iid1].
      destruct eid2 as [tid2 iid2].
      destruct eid3 as [tid3 iid3].
      inv e. inversion PO. ss. subst.
      destruct (lt_eq_lt_dec iid3 iid2); ss.
      exfalso. eapply EX.(EXTERNAL). apply t_step_rt. esplits.
      { left. left. right. eauto. }
      destruct s.
      + econs 1. left. right. right. econs. esplits.
        * econs; eauto. econs; eauto using Label.writing_is_access.
        * econs. esplits; cycle 1.
          { econs; eauto. econs; eauto using Label.writing_is_write. }
          eauto.
      + subst. econs 2.
    - (* rfe *)
      exfalso. eapply EX.(EXTERNAL). apply t_step_rt. esplits.
      { inversion H.
        - left. left. left. left. econs; eauto.
        - left. left. left. left. econs; eauto.
      }
      etrans.
      + instantiate (1 := eid2). econs. left. right. left. econs. econs.
        * econs; eauto. econs; eauto using Label.reading_is_read.
        * econs; eauto. econs; eauto. econs; eauto. econs; eauto using Label.writing_is_access.
      + econs. inversion H.
        * exfalso. inv PO. eauto.
        * left. left. right. eauto.
  Qed.

  Lemma rf_inv_write
        p exec
        eid1 eid2 loc val
        (EX: ex p exec)
        (EID2: exec.(Execution.label_is) (Label.is_reading_val loc val) eid2)
        (RF3: exec.(Execution.rf) eid1 eid2):
    <<LABEL: exec.(Execution.label_is) (Label.is_writing_val loc val) eid1>>.
  Proof.
    exploit EX.(RF1); eauto. i. des.
    - contradict NORF. econs. eauto.
    - exploit EX.(RF_WF); [exact RF3|exact RF|]. i. subst. eauto.
  Qed.

  Ltac obtac :=
    repeat
      (try match goal with
           | [H: Execution.ob _ _ _ |- _] => inv H
           | [H: Execution.obs _ _ _ |- _] => inv H
           | [H: Execution.dob _ _ _ |- _] => inv H
           | [H: Execution.bob _ _ _ |- _] => inv H
           | [H: Execution.fr _ _ _ |- _] => inv H
           | [H: Execution.rfe _ _ _ |- _] => inv H
           | [H: (_⨾ _) _ _ |- _] => inv H
           | [H: ⦗_⦘ _ _ |- _] => inv H
           | [H: (_ ∪ _) _ _ |- _] => inv H
           | [H: (_ ∩ _) _ _ |- _] => inv H
           | [H: (_ × _) _ _ |- _] => inv H
           | [H: (minus_rel _ _) _ |- _] => inv H
           | [H: Execution.label_is _ _ _ |- _] => inv H
           | [H: Execution.label_rel _ _ _ _ |- _] => inv H
           | [H: Execution.label_loc _ _ |- _] => inv H
           end;
       des).

  Lemma barrier_ob_po
        p exec
        eid1 eid2
        (EX: pre_ex p exec)
        (CO2: co2 exec)
        (RF2: rf2 exec)
        (EID1: Execution.label_is exec Label.is_barrier eid1)
        (OB: Execution.ob exec eid1 eid2):
    Execution.po eid1 eid2.
  Proof.
    inv EID1. destruct l; ss. unfold co2, rf2 in *.
    obtac; ss.
    all: try by etrans; eauto.
    - exploit RF2; eauto. i. des. inv WRITE. inv READ.
      destruct l; ss. destruct l0; ss. congr. congr.
      destruct l0; ss. congr. congr.
    - exploit RF2; eauto. i. des. inv WRITE. inv READ.
      destruct l; ss. destruct l0; ss. congr. congr.
      destruct l0; ss. congr. congr.
    - destruct l1; try congr; ss.
    - exploit CO2; eauto. i. des. inv LABEL0. inv LABEL1.
      destruct l; ss. destruct l0; ss. congr. congr.
      destruct l0; ss. congr. congr.
  Qed.

  Lemma ob_barrier_ob
        p exec
        eid1 eid2 eid3
        (PRE: pre_ex p exec)
        (CO2: co2 exec)
        (RF2: rf2 exec)
        (EID2: Execution.label_is exec Label.is_barrier eid2)
        (OB1: Execution.ob exec eid1 eid2)
        (OB2: Execution.ob exec eid2 eid3):
    <<OB: Execution.ob exec eid1 eid3>>.
  Proof.
    inv EID2. destruct l; ss. exploit barrier_ob_po; eauto. i.
    unfold co2, rf2 in *. clear OB2.
    obtac.
    all: try by rewrite EID in EID1; inv EID1; ss.
    all: try by rewrite EID in EID2; inv EID2; ss.
    all: try by destruct l; try congr; ss.
    - exploit RF2; eauto. i. des. inv WRITE. inv READ.
      destruct l; ss. destruct l0; ss. congr. congr.
      destruct l0; ss. congr. congr.
    - exploit CO2; eauto. i. des. inv LABEL0. inv LABEL1.
      destruct l; ss. destruct l0; ss. congr. congr.
      destruct l0; ss. congr. congr.
    - exploit CO2; eauto. i. des. inv LABEL0. inv LABEL1.
      destruct l; ss. destruct l0; ss. congr. congr.
      destruct l0; ss. congr. congr.
  Qed.

  Lemma ob_label
        p exec
        eid1 eid2
        (PRE: pre_ex p exec)
        (CO2: co2 exec)
        (RF2: rf2 exec)
        (OB: Execution.ob exec eid1 eid2)
        (EID1: Execution.label eid1 exec = None):
    False.
  Proof.
    unfold co2, rf2 in *.
    obtac.
    all: try congr.
    - exploit RF2. eauto. i. des. inv WRITE. inv READ.
      destruct l; ss. destruct l0; ss. congr. congr.
      destruct l0; ss. congr. congr.
    - exploit RF2. eauto. i. des. inv WRITE. inv READ.
      destruct l; ss. destruct l0; ss. congr. congr.
      destruct l0; ss. congr. congr.
    - exploit CO2. eauto. i. des. inv LABEL. inv LABEL0.
      destruct l; ss. destruct l0; ss. congr. congr.
      destruct l0; ss. congr. congr.
  Qed.

  Lemma ob_cycle
        p exec eid
        (PRE: pre_ex p exec)
        (CO2: co2 exec)
        (RF2: rf2 exec)
        (CYCLE: (Execution.ob exec)⁺ eid eid):
    exists eid_nb,
      (Execution.ob exec ∩ (Execution.label_is_rel exec Label.is_access))⁺ eid_nb eid_nb.
  Proof.
    exploit minimalize_cycle; eauto.
    { instantiate (1 := Execution.label_is exec Label.is_access).
      i. destruct (Execution.label b exec) eqn:LABEL.
      - destruct t; try by contradict H1; econs; eauto.
        eapply ob_barrier_ob; eauto.
      - exfalso. eapply ob_label; eauto.
    }
    i. des.
    - esplits. eapply clos_trans_mon; eauto. s. i. des.
      econs; ss. inv H0. inv H1. econs; eauto.
    - destruct (Execution.label a exec) eqn:LABEL.
      + destruct t; try by contradict x0; econs; eauto.
        exploit barrier_ob_po; eauto. i. inv x2. lia.
      + exfalso. eapply ob_label; eauto.
  Qed.

  (* CHECK: 하는 것? *)
  (* Lemma internal_rw *)
  (*       p ex *)
  (*       eid1 eid2 *)
  (*       (PRE: pre_ex p ex) *)
  (*       (CO2: co2 ex) *)
  (*       (RF2: rf2 ex) *)
  (*       (INTERNAL: Execution.internal ex eid1 eid2): *)
  (*   <<EID1: ex.(Execution.label_is) Label.is_access eid1>> /\ *)
  (*   <<EID2: ex.(Execution.label_is) Label.is_access eid2>>. *)
  (* Proof. *)
  (*   unfold Execution.internal in *. obtac. *)
  (*   - inv H0. inv H1. inv LABEL. splits. *)
  (*     + destruct l1; ss; econs; eauto. *)
  (*     + destruct l2; ss; econs; eauto. *)
  (*   - exploit CO2; eauto. i. des. *)
  (*     exploit RF2; eauto. i. des. *)
  (*     splits; econs; eauto. *)
  (*   - splits. *)
  (*     + destruct l1; ss; econs; eauto. *)
  (*     + destruct l2; ss; econs; eauto. *)
  (* Qed. *)

  (* CHECK: 하는 것? *)
  (* Lemma internal_read_read_po *)
  (*       p ex *)
  (*       eid1 eid2 *)
  (*       (PRE: pre_ex p ex) *)
  (*       (CO2: co2 ex) *)
  (*       (RF2: rf2 ex) *)
  (*       (INTERNAL: Execution.internal ex eid1 eid2) *)
  (*       (EID1: ex.(Execution.label_is) Label.is_read eid1) *)
  (*       (EID2: ex.(Execution.label_is) Label.is_read eid2): *)
  (*   Execution.po eid1 eid2. *)
  (* Proof. *)
  (*   unfold Execution.internal in *. obtac. *)
  (*   - inv H. ss. *)
  (*   - exploit CO2; eauto. i. des. *)
  (*     destruct l; ss. congr. *)
  (*   - rewrite EID in EID0. inv EID0. destruct l0; ss. *)
  (* Qed. *)

  (* CHECK: 하는 것? *)
  Lemma ob_read_read_po
        p ex
        eid1 eid2
        (PRE: pre_ex p ex)
        (CO1: co1 ex)
        (CO2: co2 ex)
        (RF1: rf1 ex)
        (RF2: rf2 ex)
        (RF_WF: rf_wf ex)
        (* (INTERNAL: acyclic (Execution.internal ex)) *)
        (OB: Execution.ob ex eid1 eid2)
        (EID1: ex.(Execution.label_is) Label.is_read eid1)
        (EID2: ex.(Execution.label_is) Label.is_read eid2):
    Execution.po eid1 eid2.
  Proof.
    inv EID1. inv EID2. destruct l; ss. destruct l0; ss.
    unfold Execution.ob in *. obtac; try congr.
    all: try by etrans; eauto.
    - exploit RF2. eauto. i. des. inv WRITE. inv READ.
      destruct l; ss. destruct l0; ss. congr. congr.
      destruct l0; ss. congr. congr.
    - admit. (* r --fr--> r *)
    - inv H. rewrite EID0 in EID1. inv EID1. inv LABEL1.
    - exploit CO2. eauto. i. des. inv LABEL1. inv LABEL2.
      destruct l; ss. destruct l0; ss. congr. congr.
      destruct l0; ss. congr. congr.
    - admit. (* r --ob--> u *)
    - admit. (* u --ob--> r,u *)
  Qed.

  (* CHECK: 하는 것? *)
  (* Lemma po_loc_write_is_co *)
  (*       ex eid1 eid2 loc *)
  (*       (CO1: Valid.co1 ex) *)
  (*       (INTERNAL: acyclic (Execution.internal ex)) *)
  (*       (PO: Execution.po eid1 eid2) *)
  (*       (LABEL1: ex.(Execution.label_is) (Label.is_writing loc) eid1) *)
  (*       (LABEL2: ex.(Execution.label_is) (Label.is_writing loc) eid2): *)
  (*   ex.(Execution.co) eid1 eid2. *)
  (* Proof. *)
  (*   destruct eid1 as [tid1 eid1], eid2 as [tid2 eid2]. *)
  (*   inv LABEL1. inv LABEL2. destruct l, l0; ss. *)
  (*   destruct (equiv_dec loc0 loc) eqn:Heq1; ss. *)
  (*   destruct (equiv_dec loc1 loc) eqn:Heq2; ss. *)
  (*   rewrite e, e0 in *. *)
  (*   exploit CO1. *)
  (*   { esplits; [exact EID|exact EID0]. } *)
  (*   i. des; eauto. *)
  (*   - inv x. inv PO. ss. lia. *)
  (*   - exfalso. eapply INTERNAL. econs 2. *)
  (*     + econs 1. left. econs; eauto. *)
  (*       econs; eauto. econs; unfold Label.is_accessing; eauto. *)
  (*       * instantiate (1 := loc). *)
  (*         destruct (equiv_dec loc loc); ss. *)
  (*       * destruct (equiv_dec loc loc); ss. *)
  (*     + econs 1. *)
  (*       원래는 internal을 쪼개서 Execution.co를 건지는데 여기는 co가 없음 *)
  (*       admit. *)
  (*       TODO: admit 없는 버전이랑 비교해서 없애기 *)
  (*       econs 1. left. right. eauto. *)
  (* Qed. *)
End Valid.

Coercion Valid.PRE: Valid.ex >-> Valid.pre_ex.