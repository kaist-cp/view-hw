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
Require Import HahnRelationsBasic.

Require Import PromisingArch.lib.Basic.
Require Import PromisingArch.lib.Order.
Require Import PromisingArch.lib.Time.
Require Import PromisingArch.lib.Lang.
Require Import PromisingArch.promising.CommonPromising.
Require Import PromisingArch.promising.TsoPromising.

Set Implicit Arguments.


(* TODO: move *)
Require Import ClassicalChoice.

(* TODO: move *)
Inductive opt_rel3 A B C (rel: A -> B -> C -> Prop): forall (a:option A) (b:option B) (c:option C), Prop :=
| opt_rel3_None:
    opt_rel3 rel None None None
| opt_rel3_Some
    a b c
    (REL: rel a b c):
    opt_rel3 rel (Some a) (Some b) (Some c)
.
Hint Constructors opt_rel3.

(* TODO: move *)
Definition adj A (rel: A -> A -> Prop) (l: list A): Prop :=
  forall i prev next
    (PREV: nth_error l i = Some prev)
    (NEXT: nth_error l (S i) = Some next),
    rel prev next.

Theorem promising_pf_to_view
        p pm
        (EXEC: Machine.pf_exec p pm):
  exists vm,
    <<STEP: Machine.view_exec p vm>> /\
    <<SIM: Machine.equiv pm vm>>.
Proof.
  inv EXEC. rename m1 into mf, pm into mt.

  (* TODO: by STEP2 *)
  (* https://github.com/kaist-cp/promising-hw/issues/46#issuecomment-672911617 1. *)
  assert (TRACES: forall tid, exists traces,
               opt_rel3
                 (fun eu_begin eu_end eus =>
                    <<BEGIN_END: exists l, eus = eu_begin :: l ++ [eu_end]>> /\
                    <<ADJ: adj (fun a b => ExecUnit.state_step
                                          tid
                                          (ExecUnit.mk (fst a) (snd a) mf.(Machine.mem))
                                          (ExecUnit.mk (fst b) (snd b) mt.(Machine.mem)))
                               eus>>)
                 (IdMap.find tid mf.(Machine.tpool))
                 (IdMap.find tid mt.(Machine.tpool))
                 traces).
  { admit.
    (* maybe the following may help: https://github.com/kaist-cp/promising-hw/pull/73/files#diff-aa828713167abebc52916701eb636131R72 *)
  }
  apply choice in TRACES. des. rename f into traces.

  Inductive event_order
            (traces: Id.t -> option (list (State.t (A:=unit) * Local.t)))
            (l r:Id.t * nat)
    : Prop :=
  | event_order_intro
      (* l: lf -> lt in ltrace *)
      (* r: rf -> rt in rtrace *)
      ltrace lf lt
      rtrace rf rt
      (LTRACE: traces (fst l) = Some ltrace)
      (RTRACE: traces (fst r) = Some rtrace)
      (LF: nth_error ltrace (snd l) = Some lf)
      (RF: nth_error rtrace (snd l) = Some rf)
      (LT: nth_error ltrace (S (snd l)) = Some lt)
      (RT: nth_error rtrace (S (snd l)) = Some rt)
  (* TODO: describe https://github.com/kaist-cp/promising-hw/issues/46#issuecomment-672911617 2. *)
  (* consult https://github.com/kaist-cp/promising-hw/pull/73/files#diff-aa828713167abebc52916701eb636131R129 *)
  .

  (* https://github.com/kaist-cp/promising-hw/issues/46#issuecomment-672911617 3. *)
  assert (acyclic (event_order traces)).
  { admit. }

  (* the list of all events *)
  assert (EVENTS: exists events,
             <<SOUND: forall tid n trace t
                        (TRACE: traces tid = Some trace)
                        (TO: nth_error trace (S n) = Some t),
               In (tid, n) events>> /\
             <<COMPLETE: forall tid n (IN: In (tid, n) events),
                 exists trace t,
                   <<TRACE: traces tid = Some trace>> /\
                   <<TO: nth_error trace (S n) = Some t>>>>).
  { admit. }
  des.

  exploit (linearize events); eauto. i. des. rename l' into steps.

  (* TODO: https://github.com/kaist-cp/promising-hw/issues/46#issuecomment-672911617 4. *)
  admit.
Admitted.
