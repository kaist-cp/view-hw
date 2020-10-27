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
Require Import PromisingArch.axiomatic.TsoSimLocal.
Require Import PromisingArch.equiv.TsoPFtoA1.
Require Import PromisingArch.equiv.TsoPFtoA2.

Set Implicit Arguments.


Definition ob' (ex: Execution.t): relation eidT :=
  Execution.rfe ex ∪ Execution.dob ex ∪ Execution.bob ex.

Ltac des_union :=
  repeat
    (try match goal with
         | [H: Execution.cowr _ _ _ |- _] => inv H
         | [H: Execution.corw _ _ _ |- _] => inv H
         | [H: Execution.ob _ _ _ |- _] => inv H
         | [H: Execution.obs _ _ _ |- _] => inv H
         | [H: (_ ∪ _) _ _ |- _] => inv H
         end).

Lemma ob_ob'
      ex eid1 eid2:
  Execution.ob ex eid1 eid2 <->
  (Execution.fre ex ∪ ex.(Execution.co) ∪ Execution.fob ex ∪ Execution.pf ex ∪ Execution.fp ex ∪ ob' ex) eid1 eid2.
Proof.
  split; i.
  - des_union.
    + right. left. left. auto.
    + repeat left. auto.
    + left. left. left. left. right. auto.
    + right. left. right. auto.
    + right. right. auto.
    + left. left. left. right. auto.
    + left. left. right. auto.
    + left. right. auto.
  - unfold ob' in *. des_union.
    + left. left. left. left. left. left. right. auto.
    + left. left. left. left. left. right. auto.
    + left. left. right. auto.
    + left. right. auto.
    + right. auto.
    + repeat left. auto.
    + left. left. left. left. right. auto.
    + left. left. left. right. auto.
Qed.

Lemma ob'_persist
      ex eid1 eid2
      (RF2: Valid.rf2 ex)
      (OB': ob' ex eid1 eid2)
      (EID2: ex.(Execution.label_is) Label.is_persist eid2):
  False.
Proof.
  inv OB'; obtac.
  - exploit RF2; eauto. i. des. obtac.
    rewrite EID in EID1. simplify. destruct l1; ss.
  - rewrite EID0 in EID1. simplify. destruct l1; ss.
  - rewrite EID0 in EID1. simplify. destruct l1; ss.
  - rewrite EID3 in EID1. simplify. destruct l1; ss.
Qed.

Lemma nth_error_last A (l: list A) a n
      (N: Nat.eqb n (List.length l) = true):
  List.nth_error (l ++ [a]) n = Some a.
Proof.
  apply Nat.eqb_eq in N. subst.
  rewrite List.nth_error_app2, Nat.sub_diag; ss.
Qed.

Lemma nth_error_not_last A (l: list A) a b n
      (NTH: List.nth_error (l ++ [a]) n = Some b)
      (N: Nat.eqb n (List.length l) = false):
  n < List.length l.
Proof.
  apply nth_error_snoc_inv in NTH. des; ss. subst.
  apply Nat.eqb_neq in N. lia.
Qed.

Definition sim_view (vext: eidT -> Time.t) (view: Time.t) (eids: eidT -> Prop): Prop :=
  forall eid (EID: eids eid), le (vext eid) view.

Inductive sim_view_rev (vext: eidT -> Time.t) (view: Time.t) (eids: eidT -> Prop): Prop :=
| sim_view_rev_bot
    (VIEW: view = bot)
| sim_view_rev_event
    eid
    (EID: eids eid)
    (VIEW: le view (vext eid))
.
Hint Constructors sim_view_rev.

Definition sim_view_eq (vext: eidT -> Time.t) (view: Time.t) (eids: eidT -> Prop): Prop :=
  sim_view vext view eids /\ sim_view_rev vext view eids.

Inductive sim_val (tid:Id.t) (vext:eidT -> Time.t) (vala:ValA.t (A:=unit)) (avala:ValA.t (A:=unit)): Prop :=
| sim_val_intro
    (VAL: vala.(ValA.val) = avala.(ValA.val))
.
Hint Constructors sim_val.

Inductive sim_rmap (tid:Id.t) (vext:eidT -> Time.t) (rmap:RMap.t (A:=unit)) (armap:RMap.t (A:=unit)): Prop :=
| sim_rmap_intro
    (RMAP: IdMap.Forall2 (fun reg => sim_val tid vext) rmap armap)
.
Hint Constructors sim_rmap.

Inductive sim_state (tid:Id.t) (vext:eidT -> Time.t) (state:State.t (A:=unit)) (astate:State.t (A:=unit)): Prop :=
| sim_state_intro
    (STMTS: state.(State.stmts) = astate.(State.stmts))
    (RMAP: sim_rmap tid vext state.(State.rmap) astate.(State.rmap))
.
Hint Constructors sim_state.

Lemma sim_rmap_add
      tid vext rmap armap reg vala avala
      (SIM: sim_rmap tid vext rmap armap)
      (VAL: sim_val tid vext vala avala):
  sim_rmap tid vext (RMap.add reg vala rmap) (RMap.add reg avala armap).
Proof.
  econs. ii. unfold RMap.add. rewrite ? IdMap.add_spec.
  inv SIM. condtac; eauto.
Qed.

Lemma sim_rmap_expr
      tid vext rmap armap e
      (SIM: sim_rmap tid vext rmap armap):
  sim_val tid vext (sem_expr rmap e) (sem_expr armap e).
Proof.
  inv SIM. induction e; s.
  - (* const *)
    econs; ss.
  - (* reg *)
    specialize (RMAP reg). unfold RMap.find. inv RMAP; ss.
  - (* op1 *)
    inv IHe. econs; ss. congr.
  - (* op2 *)
    inv IHe1. inv IHe2. econs; ss. congr.
Qed.

Inductive sim_local (tid:Id.t) (mem: Memory.t) (ex: Execution.t) (vext: eidT -> Time.t) (local:Local.t) (alocal:ALocal.t): Prop := mk_sim_local {
  COH: forall loc,
        sim_view
          vext
          (local.(Local.coh) loc).(View.ts)
          (inverse (sim_local_coh ex loc) (eq (tid, List.length (alocal.(ALocal.labels)))));
  VRN: sim_view
         vext
         local.(Local.vrn).(View.ts)
         (inverse (sim_local_vrn ex) (eq (tid, List.length (alocal.(ALocal.labels)))));
  VWN: exists mloc,
        (forall loc, (local.(Local.coh) loc).(View.ts) <= (local.(Local.coh) mloc).(View.ts)) /\
        sim_view
          vext
          (local.(Local.coh) mloc).(View.ts)
          (inverse (sim_local_vwn ex) (eq (tid, List.length (alocal.(ALocal.labels)))));
  PROMISES: forall view (VIEW: Promises.lookup view local.(Local.promises)),
      exists n,
        <<N: (length alocal.(ALocal.labels)) <= n>> /\
        <<WRITE: ex.(Execution.label_is) Label.is_kinda_write (tid, n)>> /\
        <<VIEW: vext (tid, n) = view>>;
  COH_CL: forall loc,
          exists mloc_cl,
          <<CL: Loc.cl loc mloc_cl>> /\
          <<COH_MAX_CL: forall loc0 (CL: Loc.cl loc0 mloc_cl),
                         (local.(Local.coh) loc0).(View.ts) <= (local.(Local.coh) mloc_cl).(View.ts)>> /\
          <<COH_CL:
              sim_view
                vext
                (local.(Local.coh) mloc_cl).(View.ts)
                (inverse (sim_local_coh_cl ex loc) (eq (tid, List.length (alocal.(ALocal.labels)))))>>;
  VPR: sim_view
         vext
         (local.(Local.vpr)).(View.ts)
         (inverse (sim_local_vpr ex) (eq (tid, List.length (alocal.(ALocal.labels)))));
  VPA: forall loc,
        sim_view
          vext
          (local.(Local.vpa) loc).(View.ts)
          (inverse (sim_local_vpa ex loc) (eq (tid, List.length (alocal.(ALocal.labels)))));
  VPC: forall loc,
        sim_view
          vext
          (local.(Local.vpc) loc).(View.ts)
          (inverse (sim_local_vpc ex loc) (eq (tid, List.length (alocal.(ALocal.labels)))));
}.
Hint Constructors sim_local.

Definition sim_ob_write
           (tid:Id.t) (ex:Execution.t) (vext: eidT -> Time.t)
           (eu:ExecUnit.t) (aeu:AExecUnit.t): Prop :=
  forall eid1 eid2
    (LABEL: eid2 < List.length aeu.(AExecUnit.local).(ALocal.labels))
    (OB: ob' ex eid1 (tid, eid2))
    (EID2: ex.(Execution.label_is) Label.is_kinda_write (tid, eid2)),
    Time.lt (vext eid1) (vext (tid, eid2)).

Definition sim_ob_read
           (tid:Id.t) (ex:Execution.t) (vext: eidT -> Time.t)
           (eu:ExecUnit.t) (aeu:AExecUnit.t): Prop :=
  forall eid1 eid2
    (LABEL: eid2 < List.length aeu.(AExecUnit.local).(ALocal.labels))
    (AOB: ob' ex eid1 (tid, eid2))
    (EID2: ex.(Execution.label_is) Label.is_kinda_read (tid, eid2)),
    Time.le (vext eid1) (vext (tid, eid2)).

Definition sim_fre
           (tid:Id.t) (ex:Execution.t) (vext: eidT -> Time.t)
           (eu:ExecUnit.t) (aeu:AExecUnit.t): Prop :=
  forall eid1 eid2
    (LABEL: eid1 < List.length aeu.(AExecUnit.local).(ALocal.labels))
    (FR: Execution.fre ex (tid, eid1) eid2),
    Time.lt (vext (tid, eid1)) (vext eid2).

Definition sim_fob
           (tid:Id.t) (ex:Execution.t) (vext: eidT -> Time.t)
           (eu:ExecUnit.t) (aeu:AExecUnit.t): Prop :=
  forall eid1 eid2
    (LABEL: eid2 < List.length aeu.(AExecUnit.local).(ALocal.labels))
    (FOB: Execution.fob ex eid1 (tid, eid2)),
    Time.le (vext eid1) (vext (tid, eid2)).

Definition sim_fp
           (tid:Id.t) (ex:Execution.t) (vext: eidT -> Time.t)
           (eu:ExecUnit.t) (aeu:AExecUnit.t): Prop :=
  forall eid1 eid2
    (LABEL: eid1 < List.length aeu.(AExecUnit.local).(ALocal.labels))
    (FP: Execution.fp ex (tid, eid1) eid2),
    Time.lt (vext (tid, eid1)) (vext eid2).

Inductive sim_th'
          (tid:Id.t) (mem:Memory.t) (ex:Execution.t) (vext: eidT -> Time.t)
          (eu:ExecUnit.t) (aeu:AExecUnit.t): Prop := {
  ST: sim_state tid vext eu.(ExecUnit.state) aeu.(AExecUnit.state);
  LC: sim_local tid mem ex vext eu.(ExecUnit.local) aeu.(AExecUnit.local);
  OBW: sim_ob_write tid ex vext eu aeu;
  OBR: sim_ob_read tid ex vext eu aeu;
  FRE: sim_fre tid ex vext eu aeu;
  FOB: sim_fob tid ex vext eu aeu;
  FP: sim_fp tid ex vext eu aeu;
}.
Hint Constructors sim_th'.
