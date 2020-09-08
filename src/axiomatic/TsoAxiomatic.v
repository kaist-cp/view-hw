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

Create HintDb tso discriminated.

Module Label.
  Inductive t :=
  | read (loc:Loc.t) (val:Val.t)
  | write (loc:Loc.t) (val:Val.t)
  | update (loc:Loc.t) (vold vnew:Val.t)
  | barrier (b:Barrier.t)
  | flush (loc:Loc.t)
  | flushopt (loc:Loc.t)
  .
  Hint Constructors t : tso.

  Definition is_read (label:t): bool :=
    match label with
    | read _ _ => true
    | _ => false
    end.

  Definition is_reading (loc:Loc.t) (label:t): bool :=
    match label with
    | read loc' _ => loc' == loc
    | _ => false
    end.

  Definition is_reading_val (loc:Loc.t) (val:Val.t) (label:t): bool :=
    match label with
    | read loc' val' => (loc' == loc) && (val' == val)
    | _ => false
    end.

  Definition is_write (label:t): bool :=
    match label with
    | write _ _ => true
    | _ => false
    end.

  Definition is_update (label:t): bool :=
    match label with
    | update _ _ _ => true
    | _ => false
    end.

  Definition is_flush (label:t): bool :=
    match label with
    | flush _ => true
    | _ => false
    end.

  Definition is_flushing (loc:Loc.t) (label:t): bool :=
    match label with
    | flush loc' => loc' == loc
    | _ => false
    end.

  Definition is_flushopt (label:t): bool :=
    match label with
    | flushopt _ => true
    | _ => false
    end.

  Definition is_flushopting (loc:Loc.t) (label:t): bool :=
    match label with
    | flushopt loc' => loc' == loc
    | _ => false
    end.

  Definition is_kinda_read (label:t): bool :=
    match label with
    | read _ _ => true
    | update _ _ _ => true
    | _ => false
    end.

  Definition is_kinda_reading (loc:Loc.t) (label:t): bool :=
    match label with
    | read loc' _ => loc' == loc
    | update loc' _ _ => loc' == loc
    | _ => false
    end.

  Definition is_kinda_reading_val (loc:Loc.t) (val:Val.t) (label:t): bool :=
    match label with
    | read loc' val' => (loc' == loc) && (val' == val)
    | update loc' val' _ => (loc' == loc) && (val' == val)
    | _ => false
    end.

  Definition is_kinda_write (label:t): bool :=
    match label with
    | write _ _ => true
    | update _ _ _ => true
    | _ => false
    end.

  Definition is_kinda_writing (loc:Loc.t) (label:t): bool :=
    match label with
    | write loc' _ => loc' == loc
    | update loc' _ _ => loc' == loc
    | _ => false
    end.

  Definition is_kinda_writing_val (loc:Loc.t) (val:Val.t) (label:t): bool :=
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

  Definition is_kinda_write_flush (label:t): bool :=
    match label with
    | write _ _ => true
    | update _ _ _ => true
    | flush _ => true
    | _ => false
    end.

  Definition is_persist (label:t): bool :=
    match label with
    | flush _ => true
    | flushopt _ => true
    | _ => false
    end.

  Definition is_persisting (loc:Loc.t) (label:t): bool :=
    match label with
    | flush loc' => loc' == loc
    | flushopt loc' => loc' == loc
    | _ => false
    end.

  Definition is_access_persist (label:t): bool :=
    match label with
    | read _ _ => true
    | write _ _ => true
    | update _ _ _ => true
    | flush _ => true
    | flushopt _ => true
    | _ => false
    end.

  Definition is_access_persisting (loc:Loc.t) (label:t): bool :=
    match label with
    | read loc' _ => loc' == loc
    | write loc' _ => loc' == loc
    | update loc' _ _ => loc' == loc
    | flush loc' => loc' == loc
    | flushopt loc' => loc' == loc
    | _ => false
    end.

  Definition is_kinda_write_persist (label:t): bool :=
    match label with
    | write _ _ => true
    | update _ _ _ => true
    | flush _ => true
    | flushopt _ => true
    | _ => false
    end.

  Definition is_persist_barrier (label:t): bool :=
    match label with
    | update _ _ _ => true
    | barrier b => orb (Barrier.is_mfence b) (Barrier.is_sfence b)
    | _ => false
    end.

  Lemma kinda_reading_is_kinda_read
        loc l
        (RD: is_kinda_reading loc l):
    is_kinda_read l.
  Proof.
    destruct l; ss.
  Qed.

  Lemma kinda_reading_is_accessing
        loc l
        (RD: is_kinda_reading loc l):
    is_accessing loc l.
  Proof.
    destruct l; ss.
  Qed.

  Lemma read_is_kinda_reading loc val:
    is_kinda_reading loc (read loc val).
  Proof.
    s. destruct (equiv_dec loc loc); ss. exfalso. apply c. ss.
  Qed.

  Lemma read_is_reading_val loc val:
    is_reading_val loc val (read loc val).
  Proof.
    s. destruct (equiv_dec loc loc); destruct (equiv_dec val val); ss; exfalso.
    all: apply c; ss.
  Qed.

  Lemma read_is_kinda_reading_val loc val:
    is_kinda_reading_val loc val (read loc val).
  Proof.
    s. destruct (equiv_dec loc loc); destruct (equiv_dec val val); ss; exfalso.
    all: apply c; ss.
  Qed.

  Lemma kinda_reading_exists_val
        loc l
        (RDING: is_kinda_reading loc l):
    exists val,
      is_kinda_reading_val loc val l.
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

  Lemma reading_is_read
        loc l
        (RDING: is_reading loc l):
    is_read l.
  Proof.
    destruct l; ss.
  Qed.

  Lemma kinda_reading_val_is_kinda_reading
        loc val l
        (RDING: is_kinda_reading_val loc val l):
    is_kinda_reading loc l.
  Proof.
    destruct l; ss; destruct (equiv_dec loc0 loc); ss.
  Qed.

  Lemma kinda_writing_is_kinda_write
        loc l
        (WR: is_kinda_writing loc l):
    is_kinda_write l.
  Proof.
    destruct l; ss.
  Qed.

  Lemma read_is_kinda_read
        l
        (RD: is_read l):
    is_kinda_read l.
  Proof.
    destruct l; ss.
  Qed.

  Lemma kinda_read_is_access
        l
        (WR: is_kinda_read l):
    is_access l.
  Proof.
    destruct l; ss.
  Qed.

  Lemma write_is_kinda_write
        l
        (WR: is_write l):
    is_kinda_write l.
  Proof.
    destruct l; ss.
  Qed.

  Lemma kinda_write_is_access
        l
        (WR: is_kinda_write l):
    is_access l.
  Proof.
    destruct l; ss.
  Qed.

  Lemma kinda_writing_is_accessing
        loc l
        (WR: is_kinda_writing loc l):
    is_accessing loc l.
  Proof.
    destruct l; ss.
  Qed.

  Lemma write_is_kinda_writing loc val:
    is_kinda_writing loc (write loc val).
  Proof.
    s. destruct (equiv_dec loc loc); ss. exfalso. apply c. ss.
  Qed.

  Lemma write_is_kinda_writing_val loc val:
    is_kinda_writing_val loc val (write loc val).
  Proof.
    s. destruct (equiv_dec loc loc); destruct (equiv_dec val val); ss; exfalso.
    all: apply c; ss.
  Qed.

  Lemma kinda_writing_exists_val
        loc l
        (WRING: is_kinda_writing loc l):
    exists val,
      is_kinda_writing_val loc val l.
  Proof.
    destruct l; ss; destruct (equiv_dec loc0 loc); ss.
    - eexists val. destruct (equiv_dec val val); ss. exfalso. apply c. ss.
    - eexists vnew. destruct (equiv_dec vnew vnew); ss. exfalso. apply c. ss.
  Qed.

  Lemma kinda_writing_val_is_kinda_writing
        loc val l
        (RDING: is_kinda_writing_val loc val l):
    is_kinda_writing loc l.
  Proof.
    destruct l; ss; destruct (equiv_dec loc0 loc); ss.
  Qed.

  Lemma update_is_kinda_reading loc vold vnew:
    is_kinda_reading loc (update loc vold vnew).
  Proof.
    s. destruct (equiv_dec loc loc); ss. exfalso. apply c. ss.
  Qed.

  Lemma update_is_kinda_writing loc vold vnew:
    is_kinda_writing loc (update loc vold vnew).
  Proof.
    s. destruct (equiv_dec loc loc); ss. exfalso. apply c. ss.
  Qed.

  Lemma update_is_kinda_writing_val loc vold vnew:
    is_kinda_writing_val loc vnew (update loc vold vnew).
  Proof.
    s. destruct (equiv_dec loc loc); destruct (equiv_dec vnew vnew); ss; exfalso.
    all: apply c; ss.
  Qed.

  Lemma accessing_is_access
        loc l
        (RD: is_accessing loc l):
    is_access l.
  Proof.
    destruct l; ss.
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

  Lemma kinda_writing_same_loc loc1 loc2 l
    (W1: is_kinda_writing loc1 l)
    (W2: is_kinda_writing loc2 l):
    loc1 = loc2.
  Proof.
    destruct l; ss.
    - destruct (equiv_dec loc loc1); ss. inv e. destruct (equiv_dec loc1 loc2); ss.
    - destruct (equiv_dec loc loc1); ss. inv e. destruct (equiv_dec loc1 loc2); ss.
  Qed.

  Lemma flushopting_is_flushopt
        loc l
        (RD: is_flushopting loc l):
    is_flushopt l.
  Proof.
    destruct l; ss.
  Qed.

  Lemma flushing_is_flush
        loc l
        (RD: is_flushing loc l):
    is_flush l.
  Proof.
    destruct l; ss.
  Qed.

  Lemma flushopt_is_flushopting loc:
    is_flushopting loc (flushopt loc).
  Proof.
    s. destruct (equiv_dec loc loc); ss. exfalso. apply c. ss.
  Qed.

  Lemma persisting_is_persist
        loc l
        (RD: is_persisting loc l):
    is_persist l.
  Proof.
    destruct l; ss.
  Qed.

  Lemma flush_is_persist
        l
        (LABEL: is_flush l):
    is_persist l.
  Proof.
    destruct l; ss.
  Qed.

  Lemma flushopt_is_persist
        l
        (LABEL: is_flushopt l):
    is_persist l.
  Proof.
    destruct l; ss.
  Qed.

  Lemma access_is_access_persist
        l
        (LABEL: is_access l):
    is_access_persist l.
  Proof.
    destruct l; ss.
  Qed.

  Lemma persist_is_kinda_write_persist
        l
        (LABEL: is_persist l):
    is_kinda_write_persist l.
  Proof.
    destruct l; ss.
  Qed.

  Lemma kinda_write_flush_is_kinda_write_persist
        l
        (LABEL: is_kinda_write_flush l):
    is_kinda_write_persist l.
  Proof.
    destruct l; ss.
  Qed.

  Lemma kinda_write_persist_is_access_persist
        l
        (LABEL: is_kinda_write_persist l):
    is_access_persist l.
  Proof.
    destruct l; ss.
  Qed.

  Lemma flushing_is_persisting
        loc l
        (LABEL: is_flushing loc l):
    is_persisting loc l.
  Proof.
    destruct l; ss.
  Qed.

  Lemma flushopting_is_persisting
        loc l
        (LABEL: is_flushopting loc l):
    is_persisting loc l.
  Proof.
    destruct l; ss.
  Qed.

  Lemma persisting_is_access_persisting
        loc l
        (LABEL: is_persisting loc l):
    is_access_persisting loc l.
  Proof.
    destruct l; ss.
  Qed.

  Lemma accessing_is_access_persisting
        loc l
        (LABEL: is_accessing loc l):
    is_access_persisting loc l.
  Proof.
    destruct l; ss.
  Qed.

  Lemma mfence_is_persist_barrier
        l
        (LABEL: Label.is_barrier_c Barrier.is_mfence l):
    is_persist_barrier l.
  Proof.
    destruct l; ss. unfold orb. condtac; ss.
  Qed.

  Lemma sfence_is_persist_barrier
        l
        (LABEL: Label.is_barrier_c Barrier.is_sfence l):
    is_persist_barrier l.
  Proof.
    destruct l; ss. unfold orb. condtac; ss.
  Qed.

  Hint Resolve
       read_is_reading_val reading_val_is_reading reading_is_read
       kinda_reading_is_kinda_read read_is_kinda_read kinda_read_is_access kinda_reading_is_accessing read_is_kinda_reading read_is_kinda_reading_val kinda_reading_exists_val kinda_reading_val_is_kinda_reading
       kinda_writing_is_kinda_write write_is_kinda_write kinda_write_is_access kinda_writing_is_accessing write_is_kinda_writing write_is_kinda_writing_val kinda_writing_exists_val kinda_writing_val_is_kinda_writing
       update_is_kinda_reading update_is_kinda_writing update_is_kinda_writing_val
       accessing_is_access read_is_accessing write_is_accessing update_is_accessing
       kinda_writing_same_loc
       access_is_access_persist
       flushopting_is_flushopt flushing_is_flush flushopt_is_flushopting
       persisting_is_persist flush_is_persist flushopt_is_persist persist_is_kinda_write_persist
       kinda_write_flush_is_kinda_write_persist kinda_write_persist_is_access_persist
       flushing_is_persisting flushopting_is_persisting persisting_is_access_persisting accessing_is_access_persisting
       mfence_is_persist_barrier sfence_is_persist_barrier
    : tso.
End Label.

Module ALocal.
  Inductive t := mk {
    labels: list Label.t;
  }.
  Hint Constructors t : tso.

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
      rmw_fail vloc res ord
      (EVENT: event = Event.read false rmw_fail ord vloc (ValA.mk _ res tt))
      (ALOCAL: alocal2 =
               mk
                 (alocal1.(labels) ++ [Label.read vloc.(ValA.val) res]))
  | step_write
      vloc vval ord
      (EVENT: event = Event.write false ord vloc vval (ValA.mk _ 0 tt))
      (ALOCAL: alocal2 =
               mk
                 (alocal1.(labels) ++ [Label.write vloc.(ValA.val) vval.(ValA.val)]))
  | step_update
      vloc voldv vnewv ordr ordw
      (EVENT: event = Event.rmw ordr ordw vloc voldv vnewv)
      (ALOCAL: alocal2 =
               mk
                 (alocal1.(labels) ++ [Label.update vloc.(ValA.val) voldv.(ValA.val) vnewv.(ValA.val)]))
  | step_mfence
      (EVENT: event = Event.barrier (Barrier.dmb false false true true))
      (ALOCAL: alocal2 =
               mk
                 (alocal1.(labels) ++ [Label.barrier (Barrier.dmb false false true true)]))
  | step_sfence
      (EVENT: event = Event.barrier (Barrier.dmb false false false true))
      (ALOCAL: alocal2 =
               mk
                 (alocal1.(labels) ++ [Label.barrier (Barrier.dmb false false false true)]))
  | step_flush
      vloc
      (EVENT: event = Event.flush vloc)
      (ALOCAL: alocal2 =
               mk
                 (alocal1.(labels) ++ [Label.flush vloc.(ValA.val)]))
  | step_flushopt
      vloc
      (EVENT: event = Event.flushopt vloc)
      (ALOCAL: alocal2 =
               mk
                 (alocal1.(labels) ++ [Label.flushopt vloc.(ValA.val)]))
  .
  Hint Constructors step : tso.

  Inductive le (alocal1 alocal2:t): Prop :=
  | le_intro
      (LABELS: exists l, alocal2.(labels) = alocal1.(labels) ++ l)
  .
  Hint Constructors le : tso.

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
  Hint Constructors t : tso.

  Inductive step (eu1 eu2:t): Prop :=
  | step_intro
      e
      (STATE: State.step e eu1.(state) eu2.(state))
      (LOCAL: ALocal.step e eu1.(local) eu2.(local))
  .
  Hint Constructors step : tso.

  Inductive label_is (labels:list Label.t) (pred:Label.t -> Prop) (iid:nat): Prop :=
  | label_is_intro
      l
      (EID: List.nth_error labels iid = Some l)
      (LABEL: pred l)
  .
  Hint Constructors label_is : tso.

  Definition wf_rmap (rmap: RMap.t (A:=unit)) (labels:list Label.t): Prop := True.
  Hint Unfold wf_rmap : tso.

  Inductive wf (aeu:t): Prop :=
  | wf_intro
      (REG: wf_rmap aeu.(state).(State.rmap) aeu.(local).(ALocal.labels))
  .
  Hint Constructors wf : tso.

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
      + econs; ss. eauto.
    - splits.
      + inv WF. econs; ss.
      + econs; ss. eauto.
    - splits.
      + inv WF. econs; ss.
      + econs; ss. eauto.
    - splits.
      + inv WF. econs; ss.
      + econs; ss. eauto.
    - splits.
      + inv WF. econs; ss.
      + econs; ss. eauto.
    - splits.
      + inv WF. econs; ss.
      + econs; ss. eauto.
    - splits.
      + inv WF. econs; ss.
      + destruct local1. refl.
    - splits.
      + inv WF. econs; ss.
      + econs; ss. eauto.
    - splits.
      + inv WF. econs; ss.
      + econs; ss. eauto.
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
    pf: relation eidT;
  }.
  Hint Constructors t : tso.

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
  Hint Constructors label_is : tso.

  Inductive label_rel (ex:t) (rel:relation Label.t) (eid1 eid2:eidT): Prop :=
  | label_rel_intro
      l1 l2
      (EID1: label eid1 ex = Some l1)
      (EID2: label eid2 ex = Some l2)
      (LABEL: rel l1 l2)
  .
  Hint Constructors label_rel : tso.

  Inductive label_is_rel (ex: t) (pred: Label.t -> Prop) (eid1 eid2: eidT): Prop :=
  | label_is_rel_intro
      l1 l2
      (EID1: label eid1 ex = Some l1)
      (EID2: label eid2 ex = Some l2)
      (LABEL1: pred l1)
      (LABEL2: pred l2)
  .
  Hint Constructors label_is_rel : tso.

  Inductive label_loc (x y:Label.t): Prop :=
  | label_loc_intro
      loc
      (X: Label.is_accessing loc x)
      (Y: Label.is_accessing loc y)
  .
  Hint Constructors label_loc : tso.

  (* TODO: add real cacheline *)
  Inductive label_cl (x y:Label.t): Prop :=
  | label_cl_intro
      loc
      (X: Label.is_access_persisting loc x)
      (Y: Label.is_access_persisting loc y)
  .
  Hint Constructors label_cl : tso.

  Lemma label_is_mon
        exec p1 p2 eid
        (PREL: p1 <1= p2)
        (P1: label_is exec p1 eid):
    label_is exec p2 eid.
  Proof.
    destruct P1; eauto with tso.
  Qed.

  (* let obs = rfe | fre | co *)
  (* let dob = ((W U U U R); po; (W U U U R)) \ (W × R) ~~~> ([R]; po; [W U U U R]) U ([W U U U R]; po; [W]) *)
  (* let bob = [W U U U R]; po; [MF]; po; [W U U U R] *)
  (* let fob =
      | [W U U U R]; po; [FL]
      | ([U U R] U ([W]; po; [MF U SF])); po; [FO]
      | [W]; (po; [FL])?; po_cl; [FO]
  *)
  (* let fobs = pf | fp *)
  (* let ob = obs | dob | bob | fob | fobs *)

  (* irrefl po?; rf as corw *)
  (* irrefl po; fr as cowr *)
  (* acyclic ob as external *)

  (* let per = [D]; pf; ([FL] U ([FO]; po; [MF U SF U U])) *)

  (* dom(per) <= P *)
  (* dom(co; [P]) <= P *)

  Inductive po (eid1 eid2:eidT): Prop :=
  | po_intro
      (TID: fst eid1 = fst eid2)
      (N: snd eid1 < snd eid2)
  .
  Hint Constructors po : tso.

  Global Program Instance po_trans: Transitive po.
  Next Obligation.
    ii. destruct x, y, z. inv H. inv H0. ss. subst. econs; ss. lia.
  Qed.

  Inductive po_adj (eid1 eid2:eidT): Prop :=
  | po_adj_intro
      (TID: fst eid1 = fst eid2)
      (N: snd eid2 = S (snd eid1))
  .
  Hint Constructors po_adj : tso.

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
      exists (t1, n0). splits; ss. inv N; [left|right]; eauto with tso.
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
  Hint Constructors i : tso.

  Inductive e (eid1 eid2:eidT): Prop :=
  | e_intro
      (TID: fst eid1 <> fst eid2)
  .
  Hint Constructors e : tso.

  Definition po_loc (ex:t): relation eidT := po ∩ ex.(label_rel) label_loc.

  Definition fr (ex:t): relation eidT :=
    (ex.(rf)⁻¹ ⨾ ex.(co)) ∪
    ((ex.(label_rel) label_loc) ∩
     ((ex.(label_is) Label.is_kinda_read) \₁ codom_rel ex.(rf)) × (ex.(label_is) Label.is_kinda_write)).
  Definition fre (ex:t): relation eidT := (fr ex) ∩ e.

  Definition rfi (ex:t): relation eidT := ex.(rf) ∩ i.
  Definition rfe (ex:t): relation eidT := ex.(rf) ∩ e.

  Definition cowr (ex:t): relation eidT := po ⨾ (fr ex).
  Definition corw (ex:t): relation eidT := po^? ⨾ ex.(rf).

  Definition obs (ex:t): relation eidT := (rfe ex) ∪ (fre ex) ∪ ex.(co).

  Definition dob (ex:t): relation eidT :=
    (⦗ex.(label_is) Label.is_kinda_read⦘ ⨾
     po ⨾
     ⦗ex.(label_is) Label.is_access⦘) ∪
    (⦗ex.(label_is) Label.is_access⦘ ⨾
     po ⨾
     ⦗ex.(label_is) Label.is_kinda_write⦘).

  Definition bob (ex:t): relation eidT :=
    ⦗ex.(label_is) Label.is_access⦘ ⨾
     po ⨾
     ⦗ex.(label_is) (Label.is_barrier_c Barrier.is_mfence)⦘ ⨾
     po ⨾
     ⦗ex.(label_is) Label.is_access⦘.

  Definition po_cl (ex:t): relation eidT := po ∩ ex.(label_rel) label_cl.

  Definition fp (ex:t): relation eidT :=
    (ex.(pf)⁻¹ ⨾ ex.(co)) ∪
    ((ex.(label_rel) label_cl) ∩
     ((ex.(label_is) Label.is_persist) \₁ codom_rel ex.(pf)) × (ex.(label_is) Label.is_kinda_write)).

  Definition fob (ex:t): relation eidT :=
    (⦗ex.(label_is) Label.is_access⦘ ⨾
     po ⨾
     ⦗ex.(label_is) Label.is_flush⦘) ∪
    ((⦗ex.(label_is) Label.is_kinda_read⦘ ∪
      (⦗ex.(label_is) Label.is_write⦘ ⨾
       po ⨾
       ⦗ex.(label_is) Label.is_persist_barrier⦘))⨾
     po ⨾
     ⦗ex.(label_is) Label.is_flushopt⦘) ∪
    (⦗ex.(label_is) Label.is_write⦘ ⨾
     (po ⨾
      ⦗ex.(label_is) Label.is_flush⦘)^? ⨾
     (po_cl ex) ⨾
     ⦗ex.(label_is) Label.is_flushopt⦘).

  Definition ob (ex:t): relation eidT :=
    (obs ex) ∪ (dob ex) ∪ (bob ex) ∪ (fob ex) ∪ (fp ex).

  Definition per (ex:t): relation eidT :=
    ⦗ex.(label_is) Label.is_kinda_write⦘ ⨾
    ((ob ex)⁺ ∩ ex.(label_rel) label_cl) ⨾
    (⦗ex.(label_is) Label.is_flush⦘ ∪
     (⦗ex.(label_is) Label.is_flushopt⦘ ⨾
      po ⨾
      ⦗ex.(label_is) Label.is_persist_barrier⦘)).

  Definition pf_min (ex:t) := ex.(pf) ⊆ (ob ex)⁺.

  Ltac obtac :=
    repeat
      (try match goal with
           | [H: Execution.ob _ _ _ |- _] => inv H
           | [H: Execution.obs _ _ _ |- _] => inv H
           | [H: Execution.dob _ _ _ |- _] => inv H
           | [H: Execution.bob _ _ _ |- _] => inv H
           | [H: Execution.fob _ _ _ |- _] => inv H
           | [H: Execution.fr _ _ _ |- _] => inv H
           | [H: Execution.fre _ _ _ |- _] => inv H
           | [H: Execution.rfe _ _ _ |- _] => inv H
           | [H: Execution.fp _ _ _ |- _] => inv H
           | [H: Execution.per _ _ _ |- _] => inv H
           | [H: (_⨾ _) _ _ |- _] => inv H
           | [H: ⦗_⦘ _ _ |- _] => inv H
           | [H: (_ ∪ _) _ _ |- _] => inv H
           | [H: (_ ∩ _) _ _ |- _] => inv H
           | [H: (_ × _) _ _ |- _] => inv H
           | [H: (minus_rel _ _) _ |- _] => inv H
           | [H: Execution.label_is _ _ _ |- _] => inv H
           | [H: Execution.label_rel _ _ _ _ |- _] => inv H
           | [H: Execution.label_loc _ _ |- _] => inv H
           | [H: Execution.label_cl _ _ |- _] => inv H
           end;
       des).

  Ltac simtac :=
  repeat match goal with
           | [H: _ |- (_⨾ _) _ _] => econs
           | [H: _ |- ⦗Execution.label_is _ _⦘ _ _ /\ _] => econs; econs; eauto with tso
           | [H: _ |- ⦗Execution.label_is _ _⦘ _ _] => econs; eauto with tso
           | [H: _ |- Execution.label_is _ _ _] => eauto with tso
           | [H: _ |- Execution.label_rel _ _ _ _] => econs; eauto with tso
           | [H: _ |- rc _ _ /\ _] => econs; eauto
           | [H: _ |- Execution.po _ _ /\ _] => econs; eauto
           | [H: _ |- Execution.po_cl _ _ _ /\ _] => econs; eauto
           | [H: _ |- Execution.pf _ _ _ /\ _] => econs; eauto
          end.

  Lemma fob_persist
        ex
        eid1 eid2
        (FOB: (fob ex) eid1 eid2):
    ex.(label_is) Label.is_persist eid2.
  Proof.
    obtac; simtac.
  Qed.

End Execution.

Ltac obtac := Execution.obtac.
Ltac simtac := Execution.simtac.

Inductive tid_lift (tid:Id.t) (rel:relation nat) (eid1 eid2:eidT): Prop :=
| tid_lift_intro
    (TID1: fst eid1 = tid)
    (TID1: fst eid2 = tid)
    (REL: rel (snd eid1) (snd eid2))
.
Hint Constructors tid_lift : tso.

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
Hint Constructors tid_join : tso.


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
  Hint Constructors pre_ex : tso.

  Definition co1 (ex: Execution.t) :=
    forall eid1 eid2,
      (exists loc,
          <<LABEL: ex.(Execution.label_is) (Label.is_kinda_writing loc) eid1>> /\
          <<LABEL: ex.(Execution.label_is) (Label.is_kinda_writing loc) eid2>>) ->
      (eid1 = eid2 \/ ex.(Execution.co) eid1 eid2 \/ ex.(Execution.co) eid2 eid1).

  Definition co2 (ex: Execution.t) :=
    forall eid1 eid2,
      ex.(Execution.co) eid1 eid2 ->
      exists loc,
        <<LABEL: ex.(Execution.label_is) (Label.is_kinda_writing loc) eid1>> /\
        <<LABEL: ex.(Execution.label_is) (Label.is_kinda_writing loc) eid2>>.

  Definition rf1 (ex: Execution.t) :=
    forall eid1 loc val
       (LABEL: ex.(Execution.label_is) (Label.is_kinda_reading_val loc val) eid1),
      (<<NORF: ~ codom_rel ex.(Execution.rf) eid1>> /\ <<VAL: val = Val.default>>) \/
      (exists eid2,
          <<LABEL: ex.(Execution.label_is) (Label.is_kinda_writing_val loc val) eid2>> /\
          <<RF: ex.(Execution.rf) eid2 eid1>>).

  Definition rf2 (ex: Execution.t) :=
    forall eid1 eid2 (RF: ex.(Execution.rf) eid2 eid1),
    exists loc val,
      <<READ: ex.(Execution.label_is) (Label.is_kinda_reading_val loc val) eid1>> /\
      <<WRITE: ex.(Execution.label_is) (Label.is_kinda_writing_val loc val) eid2>>.

  Definition rf_wf (ex: Execution.t) := functional (ex.(Execution.rf))⁻¹.

  (* TODO: add real cacheline *)
  Definition pf1 (ex: Execution.t) :=
    forall eid1 loc
       (LABEL: ex.(Execution.label_is) (Label.is_persisting loc) eid1),
      (<<NOPF: ~ codom_rel ex.(Execution.pf) eid1>>) \/
      (exists eid2,
          <<LABEL: ex.(Execution.label_is) (Label.is_kinda_writing loc) eid2>> /\
          <<PF: ex.(Execution.pf) eid2 eid1>>).

  (* TODO: add real cacheline *)
  Definition pf2 (ex: Execution.t) :=
    forall eid1 eid2 (RF: ex.(Execution.pf) eid2 eid1),
    exists loc,
      <<READ: ex.(Execution.label_is) (Label.is_persisting loc) eid1>> /\
      <<WRITE: ex.(Execution.label_is) (Label.is_kinda_writing loc) eid2>>.

  Inductive persisted_loc (ex:Execution.t) (loc:Loc.t) (val:Val.t): Prop :=
  | persisted_loc_uninit
      (UNINIT: val = Val.default)
      (NPER: forall eid (DOM: dom_rel (Execution.per ex) eid), False)
  | persisted_loc_init
      eid
      (EID: ex.(Execution.label_is) (Label.is_kinda_writing_val loc val) eid)
      (PER: forall eid2 (CO: ex.(Execution.co) eid eid2) (DOM: dom_rel (Execution.per ex) eid2), False)
  .
  Hint Constructors persisted_loc : tso.

  Definition persisted ex smem :=
    forall loc, persisted_loc ex loc (smem loc).

  Inductive ex (p:program) (ex:Execution.t) := mk_ex {
    PRE: pre_ex p ex;
    CO1: co1 ex;
    CO2: co2 ex;
    RF1: rf1 ex;
    RF2: rf2 ex;
    RF_WF: rf_wf ex;
    PF1: pf1 ex;
    PF2: pf2 ex;
    COWR: irreflexive (Execution.cowr ex);
    CORW: irreflexive (Execution.corw ex);
    EXTERNAL: acyclic (Execution.ob ex);
    PF_MIN: Execution.pf_min ex;
  }.
  Hint Constructors ex : tso.
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
    forall eid (PO: Execution.po eid eid), False.
  Proof.
    ii. inv PO. lia.
  Qed.

  Lemma coi_is_po
        p exec
        eid1 eid2
        (EX: ex p exec)
        (RF: exec.(Execution.co) eid1 eid2)
        (I: Execution.i eid1 eid2):
    Execution.po eid1 eid2.
  Proof.
    destruct eid1 as [tid1 iid1].
    destruct eid2 as [tid2 iid2].
    inv I. ss. subst.
    destruct (lt_eq_lt_dec iid2 iid1); ss.
    exfalso. eapply EX.(EXTERNAL). apply t_step_rt. esplits.
    { left. left. left. left. right. eauto. }
    exploit EX.(CO2); eauto. i. des. inv LABEL. inv LABEL0.
    destruct s.
    + econs 1.  left. left. left. right. right. econs. esplits.
      * econs; eauto with tso.
      * econs. esplits; cycle 1.
        { econs; eauto with tso. }
        eauto with tso.
    + subst. econs 2.
  Qed.

  Lemma rfi_is_po
        p exec
        eid1 eid2
        (EX: ex p exec)
        (RF: exec.(Execution.rf) eid1 eid2)
        (I: Execution.i eid1 eid2):
    Execution.po eid1 eid2.
  Proof.
    destruct eid1 as [tid1 iid1].
    destruct eid2 as [tid2 iid2].
    inv I. ss. subst. econs; ss.
    destruct (le_lt_dec iid2 iid1); ss.
    exfalso. eapply EX.(CORW). econs. econs; [|by eauto].
    apply Nat.le_lteq in l. des.
    - econs 2. ss.
    - econs 1. eauto.
  Qed.

  Lemma coherence_ww
        p exec
        eid1 eid2 loc
        (EX: ex p exec)
        (EID1: exec.(Execution.label_is) (Label.is_kinda_writing loc) eid1)
        (EID2: exec.(Execution.label_is) (Label.is_kinda_writing loc) eid2)
        (PO: Execution.po eid1 eid2):
    exec.(Execution.co) eid1 eid2.
  Proof.
    inv EID1. inv EID2. exploit EX.(CO1).
    { obtac. esplits; econs; [exact EID| |exact EID0|]; eauto. }
    i. des; ss.
    { subst. apply po_irrefl in PO. inv PO. }
    exfalso. eapply EX.(EXTERNAL). apply t_step_rt. esplits.
    - left. left. left. left. right. eauto.
    - econs. left. left. left. right. right. econs. esplits.
      + econs; eauto with tso.
      + econs. esplits; eauto. econs; eauto with tso.
  Qed.

  Lemma coherence_wr
        p exec
        eid1 eid2 loc
        (EX: ex p exec)
        (EID1: exec.(Execution.label_is) (Label.is_kinda_writing loc) eid1)
        (EID2: exec.(Execution.label_is) (Label.is_kinda_reading loc) eid2)
        (PO: Execution.po eid1 eid2):
    exists eid3,
      <<RF: exec.(Execution.rf) eid3 eid2>> /\
      <<CO: exec.(Execution.co)^? eid1 eid3>>.
  Proof.
    inv EID1. inv EID2.
    inversion LABEL0. apply Label.kinda_reading_exists_val in H0. des.
    exploit EX.(RF1).
    { instantiate (1 := eid2). econs; eauto. }
    i. des.
    { exfalso. eapply EX.(COWR). econs; econs; [by eauto|].
      right. econs.
      - econs; eauto with tso.
      - econs; econs; eauto with tso.
    }
    esplits; eauto.
    exploit EX.(CO1).
    { obtac. esplits; econs; [exact EID| |exact EID1|]; eauto with tso. }
    i. des; subst; ss.
    { refl. }
    { econs 2. ss. }
    exfalso. eapply EX.(COWR). econs; econs; [by eauto|].
    econs; eauto. econs; eauto.
  Qed.

  Lemma coherence_rr
        p exec
        eid1 eid2 eid3 loc
        (EX: ex p exec)
        (EID1: exec.(Execution.label_is) (Label.is_kinda_reading loc) eid1)
        (EID2: exec.(Execution.label_is) (Label.is_kinda_reading loc) eid2)
        (EID3: exec.(Execution.label_is) (Label.is_kinda_writing loc) eid3)
        (RF: exec.(Execution.rf) eid3 eid1)
        (PO: Execution.po eid1 eid2):
    exists eid4,
      <<RF: exec.(Execution.rf) eid4 eid2>> /\
      <<CO: exec.(Execution.co)^? eid3 eid4>>.
  Proof.
    inv EID1. inv EID2. inv EID3.
    destruct eid1 as [tid1 iid1].
    destruct eid2 as [tid2 iid2].
    destruct eid3 as [tid3 iid3].
    inversion PO. ss. subst.
    inv LABEL0. apply Label.kinda_reading_exists_val in H0. des.
    destruct (tid2 == tid3).
    - inv e. exploit rfi_is_po; eauto with tso. intro X. inv X. ss. subst.
      (* po-wr -> co?; rf *)
      exploit EX.(RF1); eauto with tso. i. des.
      + exfalso. exploit EX.(COWR); eauto. instantiate (1 := (tid3, iid3)). econs; esplits.
        * etrans; eauto. econs; ss.
        * right. econs.
          -- econs; eauto with tso.
          -- econs; eauto with tso. econs; eauto with tso.
      + inv LABEL0. rename eid2 into eid4. exploit EX.(CO1).
        { obtac. esplits; econs; [exact EID1| |exact EID2|]; eauto with tso. }
        intro X. rewrite <- or_assoc in X. destruct X; [by esplits; eauto|].
        exfalso. exploit EX.(COWR); eauto. instantiate (1 := (tid3, iid3)). econs; esplits.
        { etrans; eauto. econs; ss. }
        left. econs; eauto.
    - (* ob-wr -> co?; rf *)
      exploit EX.(RF1); eauto with tso. i. des.
      + exfalso. exploit EX.(EXTERNAL); eauto. instantiate (1 := (tid3, iid3)).
        apply t_step_rt. econs; eauto. esplits; [|etrans; [econs|econs]].
        * repeat left. econs; eauto with tso.
        * left. left. left. right. left. econs. esplits.
          -- econs; eauto with tso.
          -- econs. esplits; eauto. econs; eauto with tso.
        * left. left. left. left. left. right. split; ss. right. econs.
          -- econs; eauto with tso.
          -- econs; eauto with tso. econs; eauto with tso.
      + inv LABEL0. rename eid2 into eid4. exploit EX.(CO1).
        { obtac. esplits; econs; [exact EID1| |exact EID2|]; eauto with tso. }
        intro X. rewrite <- or_assoc in X. destruct X; [by esplits; eauto|].
        exfalso. exploit EX.(EXTERNAL); eauto. instantiate (1 := (tid3, iid3)).
        apply t_step_rt. econs; eauto. esplits; [|etrans; [econs|econs]].
        * repeat left. econs; eauto with tso.
        * left. left. left. right. left. econs. esplits.
          -- econs; eauto with tso.
          -- econs. esplits; eauto. econs; eauto with tso.
        * left. left. left. left. left. right. split; ss. econs. econs. econs; eauto.
  Qed.

  Lemma coherence_rw
        p exec
        eid1 eid2 eid3 loc
        (EX: ex p exec)
        (EID1: exec.(Execution.label_is) (Label.is_kinda_reading loc) eid1)
        (EID2: exec.(Execution.label_is) (Label.is_kinda_writing loc) eid2)
        (EID3: exec.(Execution.label_is) (Label.is_kinda_writing loc) eid3)
        (RF1: exec.(Execution.rf) eid3 eid1)
        (PO: Execution.po eid1 eid2):
    exec.(Execution.co) eid3 eid2.
  Proof.
    inv EID1. inv EID2. inv EID3.
    exploit EX.(CO1).
    { obtac. esplits; econs; [exact EID0| |exact EID1|]; eauto. }
    i. rewrite <- or_assoc in x0. destruct x0; [|done]. inv H.
    { exfalso. eapply EX.(CORW). econs; eauto. }
    destruct (fst eid1 == fst eid3).
    - (* rfi *)
      exfalso. eapply EX.(CORW). econs. instantiate (1 := eid1). esplits; [|by eauto].
      right. apply Execution.po_chain. econs. splits; eauto.
      inv PO. inv e. rewrite TID in H1. eapply coi_is_po in H0; eauto with tso.
    - (* rfe *)
      exfalso. eapply EX.(EXTERNAL). apply t_step_rt. esplits.
      { repeat left. econs; eauto with tso. }
      etrans.
      + instantiate (1 := eid2). econs. left. left. left. right. left. econs. econs.
        * econs; eauto with tso.
        * econs; eauto. econs; eauto. econs; eauto with tso.
      + econs. left. left. left. left. right. eauto.
  Qed.

  Lemma rf_inv_write
        p exec
        eid1 eid2 loc val
        (EX: ex p exec)
        (EID2: exec.(Execution.label_is) (Label.is_kinda_reading_val loc val) eid2)
        (RF3: exec.(Execution.rf) eid1 eid2):
    <<LABEL: exec.(Execution.label_is) (Label.is_kinda_writing_val loc val) eid1>>.
  Proof.
    exploit EX.(RF1); eauto. i. des.
    - contradict NORF. econs. eauto.
    - exploit EX.(RF_WF); [exact RF3|exact RF|]. i. subst. eauto.
  Qed.

  Lemma pf_is_t_ob_cl
        p exec
        eid1 eid2
        (EX: ex p exec)
        (PF: Execution.pf exec eid1 eid2):
    ((Execution.ob exec)⁺ ∩ exec.(Execution.label_rel) Execution.label_cl) eid1 eid2.
  Proof.
    econs.
    - eapply EX.(PF_MIN); eauto.
    - exploit EX.(PF2); eauto. i. des. obtac. simtac.
  Qed.

  Lemma barrier_ob
        p exec
        eid1 eid2
        (EX: pre_ex p exec)
        (CO2: co2 exec)
        (RF2: rf2 exec)
        (PF2: pf2 exec)
        (EID1: Execution.label_is exec Label.is_barrier eid1)
        (OB: Execution.ob exec eid1 eid2):
    False.
  Proof.
    inv EID1. destruct l; ss. unfold co2, rf2 in *.
    obtac; ss.
    all: try by destruct l; ss; congr.
    - exploit RF2; eauto. i. des. inv WRITE. inv READ.
      destruct l; ss. destruct l0; ss. congr. congr.
      destruct l0; ss. congr. congr.
    - exploit RF2; eauto. i. des.
      inv READ. destruct l; ss; try congr.
    - inv H0. destruct l1; ss; try congr.
    - exploit CO2; eauto. i. des; obtac; destruct l; destruct l0; ss; congr.
    - exploit PF2; eauto. i. des; obtac; destruct l; destruct l0; ss; congr.
    - inv H0. destruct l1; ss; try congr.
  Qed.

  Lemma ob_label
        p exec
        eid1 eid2
        (PRE: pre_ex p exec)
        (CO2: co2 exec)
        (RF2: rf2 exec)
        (PF2: pf2 exec)
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
    - exploit CO2. eauto. i. des; obtac; destruct l; destruct l0; ss; congr.
    - exploit PF2. eauto. i. des; obtac; destruct l; destruct l0; ss; congr.
  Qed.

  Lemma ob_cycle
        p exec eid
        (PRE: pre_ex p exec)
        (CO2: co2 exec)
        (RF2: rf2 exec)
        (PF2: pf2 exec)
        (CYCLE: (Execution.ob exec)⁺ eid eid):
    exists eid_nb,
      (Execution.ob exec ∩ (Execution.label_is_rel exec Label.is_access_persist))⁺ eid_nb eid_nb.
      (* TODO: check if this statement is right when prove PtoA *)
  Proof.
    exploit minimalize_cycle; eauto.
    { instantiate (1 := Execution.label_is exec Label.is_access_persist).
      i. destruct (Execution.label b exec) eqn:LABEL.
      - destruct t; try by contradict H1; econs; eauto.
        exfalso. eapply barrier_ob; eauto with tso.
      - exfalso. eapply ob_label; eauto.
    }
    i. des.
    - esplits. eapply clos_trans_mon; eauto. s. i. des.
      econs; ss. inv H0. inv H1. econs; eauto.
    - destruct (Execution.label a exec) eqn:LABEL.
      + destruct t; try by contradict x0; econs; eauto.
        exfalso. eapply barrier_ob; eauto with tso.
      + exfalso. eapply ob_label; eauto.
  Qed.

  Lemma ob_read_read_po
        p ex
        eid1 eid2
        (PRE: pre_ex p ex)
        (CO2: co2 ex)
        (RF2: rf2 ex)
        (PF2: pf2 ex)
        (OB: Execution.ob ex eid1 eid2)
        (EID1: ex.(Execution.label_is) Label.is_read eid1)
        (EID2: ex.(Execution.label_is) Label.is_read eid2):
    Execution.po eid1 eid2.
  Proof.
    inv EID1. inv EID2.
    destruct l; ss. destruct l0; ss.
    all: obtac; try congr.
    all: try by etrans; eauto.
    all: try by rewrite EID0 in EID1; inv EID1; ss.
    all: try by rewrite EID in EID1; inv EID1; ss.
    - exploit RF2; eauto. i. des.
      inv WRITE. rewrite EID in EID1. destruct l; ss.
    - exploit CO2; eauto. i. des; obtac; destruct l; ss; congr.
    - exploit CO2; eauto. i. des; obtac; destruct l; ss; congr.
    - exploit PF2; eauto. i. des.
      obtac. rewrite EID in EID2. inv EID2. ss.
  Qed.

  Lemma persist_ob_write
        ex
        eid1 eid2
        (CO2: co2 ex)
        (RF2: rf2 ex)
        (OB: Execution.ob ex eid1 eid2)
        (EID1: ex.(Execution.label_is) Label.is_persist eid1):
    ex.(Execution.label_is) Label.is_kinda_write eid2.
  Proof.
    obtac.
    all: try by destruct l; destruct l2; ss; congr.
    all: try by destruct l; destruct l1; ss; congr.
    - exploit RF2; eauto. i. des. obtac.
      destruct l0; destruct l; ss; congr.
    - exploit RF2; eauto. i. des. obtac.
      destruct l1; destruct l; ss; congr.
    - rewrite EID1 in EID0. inv EID0. destruct l0; ss.
    - exploit CO2; eauto. i. des. obtac.
      destruct l1; destruct l; ss; congr.
    - exploit CO2; eauto. i. des. obtac. simtac.
    - simtac.
  Qed.

  Lemma access_ob_persist
        ex
        eid1 eid2
        (CO2: co2 ex)
        (RF2: rf2 ex)
        (OB: Execution.ob ex eid1 eid2)
        (EID1: ex.(Execution.label_is) Label.is_persist eid2):
    ex.(Execution.label_is) Label.is_access eid1.
  Proof.
    obtac.
    all: try by destruct l0; destruct l2; ss; congr.
    all: try by destruct l0; destruct l1; ss; congr.
    all: try by destruct l0; destruct l; ss; congr.
    all: try by destruct l1; destruct l2; ss; congr.
    all: try simtac.
    - exploit RF2; eauto. i. des. obtac.
      destruct l; destruct l1; ss; congr.
    - exploit CO2; eauto. i. des. obtac.
      destruct l; destruct l0; ss; congr.
    - exploit CO2; eauto. i. des. obtac.
      destruct l; destruct l0; ss; congr.
    - exploit CO2; eauto. i. des. obtac.
      destruct l; destruct l0; ss; congr.
  Qed.

  Lemma ob_persist_po
        ex
        eid1 eid2
        (CO2: co2 ex)
        (RF2: rf2 ex)
        (EID1: Execution.label_is ex Label.is_persist eid2)
        (OB: Execution.ob ex eid1 eid2):
    Execution.po eid1 eid2.
  Proof.
    inv EID1. unfold co2, rf2 in *.
    obtac; ss.
    all: try by etrans; eauto.
    all: try by destruct l; destruct l0; ss; congr.
    - exploit RF2; eauto. i. des. obtac.
      destruct l; destruct l1; ss; congr.
    - exploit CO2; eauto. i. des. obtac.
      destruct l; destruct l0; ss; congr.
    - exploit CO2; eauto. i. des. obtac.
      destruct l; destruct l0; ss; congr.
    - inv H; inv H2; ss.
      obtac. eapply Execution.po_chain. econs. simtac.
    - exploit CO2; eauto. i. des. obtac.
      destruct l; destruct l0; ss; congr.
  Qed.
End Valid.

Coercion Valid.PRE: Valid.ex >-> Valid.pre_ex.
