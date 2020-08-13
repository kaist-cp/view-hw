Require Import Relations.
Require Import EquivDec.
Require Import Equality.
Require Import List.
Require Import Bool.
Require Import Lia.
Require Import NArith.
Require Import PArith.
Require Import ZArith.
Require Import FMapPositive.
Require Import FSetPositive.
Require Import sflib.

Require Import PromisingArch.lib.Basic.
Require Import PromisingArch.lib.Order.
Require Import PromisingArch.lib.Time.
Require Import PromisingArch.lib.Lang.
Require Import PromisingArch.promising.CommonPromising.
Require Import PromisingArch.promising.TsoPromising.
Require Import PromisingArch.equiv.TsoPtoPF.

Set Implicit Arguments.


Inductive sim_local (local1 local2:Local.t): Prop :=
| sim_local_intro
    (COH: local1.(Local.coh) = local2.(Local.coh))
    (VRN: local1.(Local.vrn) = local2.(Local.vrn))
.
Hint Constructors sim_local.

Definition last_error A (l:list A): option A := nth_error l (Nat.pred (length l)).

Lemma get_eutr
      tid eu1 eu2
      (STEP: rtc (ExecUnit.state_step tid) eu1 eu2):
  exists (eutr:list ((option (Event.t (A:=unit)) * ExecUnit.t))),
    <<FIRST: hd_error eutr = Some (None, eu1)>> /\
    <<LAST:
      <<ONE: 1 = length eutr -> last_error eutr = Some (None, eu2)>> /\
      <<MORE: 1 < length eutr -> exists e, last_error eutr = Some (Some e, eu2)>>>> /\
    <<STEP:
      forall n eopt e eu1 eu2
             (N: n < length eutr)
             (EU1: nth_error eutr n = Some (eopt, eu1))
             (EU2: nth_error eutr (S n) = Some (Some e, eu2)),
        ExecUnit.state_step0 tid e e eu1 eu2>>.
Proof.
  induction STEP.
  { eexists [(None, x)]. splits; ss; [lia|].
    i. destruct n; ss.
  }
  des. inv H.
  eexists ((None, x) :: (Some e, y) :: (tl eutr)).
  splits; ss.
  - i. destruct (lt_eq_lt_dec 1 (length eutr)); cycle 1.
    { destruct eutr; ss; try lia. }
    inv s.
    + apply MORE in H0. des.
      eexists e0. destruct eutr; ss. destruct eutr; ss.
      inv FIRST. inv H0.
    + destruct eutr; ss. inv FIRST. destruct eutr; ss.
      exploit ONE; try lia. intro HL. inv HL.
      eexists e. ss.
  - i. destruct n; ss.
    { inv EU1. inv EU2. ss. }
    destruct eutr; ss. inv FIRST.
    assert (n < S (length eutr)); try lia.
    destruct n; [inv EU1|]; exploit STEP0; eauto; ss.
Qed.

Lemma get_eutrs
      p m1 m
      (STEP1: rtc (Machine.step ExecUnit.promise_step) (Machine.init p) m1)
      (STEP2: Machine.state_exec m1 m):
  exists eutrs,
    IdMap.Forall3
      (fun tid eu_m1 eu_m eutr =>
        <<FIRST: hd_error eutr = Some (None, ExecUnit.mk (fst eu_m1) (snd eu_m1) m.(Machine.mem))>> /\
        <<LAST:
          <<ONE: 1 = length eutr -> last_error eutr = Some (None, ExecUnit.mk (fst eu_m) (snd eu_m) m.(Machine.mem))>> /\
          <<MORE: 1 < length eutr -> exists e, last_error eutr = Some (Some e, ExecUnit.mk (fst eu_m) (snd eu_m) m.(Machine.mem))>>>> /\
        <<STEP:
            forall n eopt e eu1 eu2
                  (N: n < length eutr)
                  (EU1: nth_error eutr n = Some (eopt, eu1))
                  (EU2: nth_error eutr (S n) = Some (Some e, eu2)),
              ExecUnit.state_step0 tid e e eu1 eu2>>)
      m1.(Machine.tpool) m.(Machine.tpool) eutrs.
Proof.
  inv STEP2.
  destruct m1. ss. induction tpool.
  { eexists (IdMap.empty (list (option Event.t * ExecUnit.t))).
    ii. specialize (TPOOL id). inv TPOOL.
    - rewrite IdMap.gempty. ss.
    - exploit IdMap.gempty. unfold IdMap.empty. intro EMPTY.
      rewrite <- H0 in EMPTY. ss.
  }
  admit.
Qed.

Definition event_is_kinda_write (e:Event.t (A:=unit)) :=
  match e with
  | Event.write _ _ _ _ _
  | Event.rmw _ _ _ _ _ => true
  | _ => false
  end.

Lemma eutrs_unique_write
      eutrs
      tid1 tid2 i1 i2
      l1 l2 e1 e2 eu1 eu2
      mloc1 mloc2
      (L1: Some l1 = IdMap.find tid1 eutrs)
      (L2: Some l2 = IdMap.find tid2 eutrs)
      (EEU1: Some (Some e1, eu1) = nth_error l1 i1)
      (EEU2: Some (Some e2, eu2) = nth_error l2 i2)
      (MLOC1: Local.cohmax mloc1 eu1.(ExecUnit.local))
      (MLOC2: Local.cohmax mloc2 eu2.(ExecUnit.local))
      (COHMEQ: (eu1.(ExecUnit.local).(Local.coh) mloc1).(View.ts) = (eu2.(ExecUnit.local).(Local.coh) mloc2).(View.ts))
      (NEQ: tid1 <> tid2 \/ i1 <> i2)
      (W1: event_is_kinda_write e1)
      (W2: event_is_kinda_write e2):
  False.
Proof.
  admit.
Qed.

Inductive eu_order (ti1 ti2: (Id.t * nat)) (eutrs: IdMap.t (list ((option (Event.t (A:=unit))) * ExecUnit.t))): Prop :=
| eu_order_intro
    tid1 tid2 i1 i2
    l1 l2 eopt1 eopt2 eu1 eu2
    mloc1 mloc2 cohm1 cohm2
    e
    (TID1: tid1 = fst ti1)
    (TID2: tid2 = fst ti2)
    (I1: i1 = snd ti1)
    (I2: i2 = snd ti2)
    (L1: Some l1 = IdMap.find tid1 eutrs)
    (L2: Some l2 = IdMap.find tid2 eutrs)
    (EEU1: Some (eopt1, eu1) = nth_error l1 i1)
    (EEU2: Some (eopt2, eu2) = nth_error l2 i2)
    (MLOC1: Local.cohmax mloc1 eu1.(ExecUnit.local))
    (MLOC2: Local.cohmax mloc2 eu2.(ExecUnit.local))
    (COHM1: cohm1 = (eu1.(ExecUnit.local).(Local.coh) mloc1).(View.ts))
    (COHM2: cohm2 = (eu2.(ExecUnit.local).(Local.coh) mloc2).(View.ts))
    (TH_ORD: tid1 = tid2 -> i1 < i2)
    (COHMAX_ORD: cohm1 <> cohm2 -> cohm1 < cohm2)
    (OTHER_ORD: cohm1 = cohm2 -> (eopt1 = Some e /\ event_is_kinda_write e))
.
Hint Constructors eu_order.

Lemma eu_order_antisym
      tid1 tid2 i1 i2 eutrs
      (ORD1: eu_order (tid1, i1) (tid2, i2) eutrs)
      (ORD2: eu_order (tid2, i2) (tid1, i1) eutrs):
  False.
Proof.
  inv ORD1. inv ORD2. ss.
  rewrite <- L1 in L3. inv L3. rewrite <- L2 in L0. inv L0.
  rewrite <- EEU1 in EEU3. inv EEU3. rewrite <- EEU2 in EEU0. inv EEU0.
  exploit Local.two_cohmax_ts_eq; [exact MLOC1 | exact MLOC3 |]; eauto. intro MLOCEQ. rewrite MLOCEQ in *.
  exploit Local.two_cohmax_ts_eq; [exact MLOC2 | exact MLOC0 |]; eauto. intro MLOCEQ0. rewrite MLOCEQ0 in *.
  destruct (View.ts (Local.coh (ExecUnit.local eu1) mloc3) == View.ts (Local.coh (ExecUnit.local eu2) mloc0)); cycle 1.
  - generalize c. intro c0.
    apply COHMAX_ORD in c. symmetry in c0. apply COHMAX_ORD0 in c0. lia.
  - inv e1. rewrite H0 in *.
    exploit OTHER_ORD; eauto. exploit OTHER_ORD0; eauto. i. des. subst.
    eapply eutrs_unique_write.
    { exact L1. }
    { exact L2. }
    all: eauto.
    destruct (tid1 == tid2); cycle 1.
    { left. ss. }
    inv e1. exploit TH_ORD; ss. exploit TH_ORD0; ss. lia.
Qed.

Theorem promising_pf_to_view
        p m
        (EXEC: Machine.pf_exec p m):
  Machine.view_exec p m.
Proof.
  inv EXEC.
  generalize (Machine.init_wf p). intro WF.
  generalize (Machine.init_no_promise p). intro NOPROMISE0.
  inv STEP2.
  admit.
Qed.

Theorem promising_to_view
        p m
        (EXEC: Machine.exec p m):
  Machine.view_exec p m.
Proof.
  apply promising_to_promising_pf in EXEC.
  apply promising_pf_to_view; auto.
Qed.
