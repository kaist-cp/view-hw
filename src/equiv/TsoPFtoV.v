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


Inductive sim_state (state1 state2:State.t (A:=unit)): Prop :=
| sim_state_intro
    (STMTS: state1.(State.stmts) = state2.(State.stmts))
    (RMAP: state1.(State.rmap) = state2.(State.rmap))
.
Hint Constructors sim_state.

Inductive sim_local (local1 local2:Local.t): Prop :=
| sim_local_intro
    (COH: local1.(Local.coh) = local2.(Local.coh))
    (VRN: local1.(Local.vrn) = local2.(Local.vrn))
.
Hint Constructors sim_local.

(* TODO: describe fulfilled message
  exist M,
    PF 실행 메모리의 프리픽스
    M의 모든 메시지는 L[0..i] 사이에서 fulfill 되어있다.
    L[0..i] 사이에서 fulfill 된 모든 메세지는 M에 있다.
*)
Inductive sim_mem (pmem vmem:Memory.t) (n:Nat.t) (reord: list ((Event.t (A:=unit) * Id.t) * ExecUnit.t))
          : Prop :=
| sim_mem_intro
    (MEM: Memory.prefix vmem pmem)
.

Definition tid_step_cnt (tid:Id.t) (reord: list ((Event.t (A:=unit) * Id.t) * ExecUnit.t)): Nat.t :=
  length (filter (fun ete => tid == (snd (fst ete))) reord).

Inductive sim_machine (eutrs: IdMap.t (list (ExecUnit.t))) (pmem:Memory.t) (vm:Machine.t) (n:Nat.t) (reord: list ((Event.t (A:=unit) * Id.t) * ExecUnit.t)): Prop :=
| sim_machine_intro
    (TPOOL: IdMap.Forall2
            (fun tid eutr sl =>
              forall eu,
                List.nth_error eutr (tid_step_cnt tid reord) = Some eu /\
                sim_state eu.(ExecUnit.state) (fst sl) /\
                sim_local eu.(ExecUnit.local) (snd sl))
             eutrs vm.(Machine.tpool))
    (MEM: sim_mem pmem vm.(Machine.mem) n reord)
.

Inductive insert_eu (new: (Event.t (A:=unit) * Id.t) * ExecUnit.t) (l1 l2: list ((Event.t (A:=unit) * Id.t) * ExecUnit.t)): Prop :=
| insert_eu_empty
    (L1: l1 = [])
    (L2: l2 = [new])
| insert_eu_cohmax_lt
    l
    e1 tid1 eu1
    mloc1 mloc2
    (L1: l1 = (e1, tid1, eu1) :: l)
    (COHMAX1: Local.cohmax mloc1 eu1.(ExecUnit.local))
    (COHMAX2: Local.cohmax mloc2 (snd new).(ExecUnit.local))
    (LT: (eu1.(ExecUnit.local).(Local.coh) mloc1).(View.ts) < ((snd new).(ExecUnit.local).(Local.coh) mloc2).(View.ts))
    (L2: l2 = new :: l1)
| insert_eu_wu
    l
    e1 tid1 eu1
    mloc1 mloc2
    (L1: l1 = (e1, tid1, eu1) :: l)
    (COHMAX1: Local.cohmax mloc1 eu1.(ExecUnit.local))
    (COHMAX2: Local.cohmax mloc2 (snd new).(ExecUnit.local))
    (EQ: (eu1.(ExecUnit.local).(Local.coh) mloc1).(View.ts) = ((snd new).(ExecUnit.local).(Local.coh) mloc2).(View.ts))
    (WU: match (fst (fst new)) with
         | Event.write _ _ _ _ _
         | Event.rmw _ _ _ _ _ => True
         | _ => False
         end)
    (L2: l2 = new :: l1)
| insert_eu_prior
    l recl
    e1 tid1 eu1
    mloc1 mloc2
    (L1: l1 = (e1, tid1, eu1) :: l)
    (COHMAX1: Local.cohmax mloc1 eu1.(ExecUnit.local))
    (COHMAX2: Local.cohmax mloc2 (snd new).(ExecUnit.local))
    (EQ: (eu1.(ExecUnit.local).(Local.coh) mloc1).(View.ts) = ((snd new).(ExecUnit.local).(Local.coh) mloc2).(View.ts))
    (NWU: match (fst (fst new)) with
          | Event.write _ _ _ _ _
          | Event.rmw _ _ _ _ _ => False
          | _ => True
          end)
    (L2: l2 = (e1, tid1, eu1) :: recl)
    (REC: insert_eu new l recl)
| insert_eu_cohmax_gt
    l recl
    e1 tid1 eu1
    mloc1 mloc2
    (L1: l1 = (e1, tid1, eu1) :: l)
    (COHMAX1: Local.cohmax mloc1 eu1.(ExecUnit.local))
    (COHMAX2: Local.cohmax mloc2 (snd new).(ExecUnit.local))
    (GT: (eu1.(ExecUnit.local).(Local.coh) mloc1).(View.ts) > ((snd new).(ExecUnit.local).(Local.coh) mloc2).(View.ts))
    (L2: l2 = (e1, tid1, eu1) :: recl)
    (REC: insert_eu new l recl)
.

Inductive traces (p: program) (mem: Memory.t):
  forall (tr: list (Machine.t)) (eutrs: IdMap.t (list (ExecUnit.t))) (reord: list ((Event.t (A:=unit) * Id.t) * ExecUnit.t)), Prop :=
| traces_init
    eutrs_init
    (INIT: IdMap.Forall2
            (fun _ eutr sl => eutr = [ExecUnit.mk (fst sl) (snd sl) mem])
            eutrs_init (Machine.init_with_promises p mem).(Machine.tpool)):
    traces p mem [Machine.init_with_promises p mem] eutrs_init []
| traces_step
    e tid tr1 m1 m2 eu1 eu2 eutr eutrs1 eutrs2 reord1 reord2
    (STEP: ExecUnit.state_step0 tid e e eu1 eu2)
    (M1: IdMap.find tid m1.(Machine.tpool) = Some (eu1.(ExecUnit.state), eu1.(ExecUnit.local)))
    (M2: IdMap.find tid m2.(Machine.tpool) = Some (eu2.(ExecUnit.state), eu2.(ExecUnit.local)))
    (REORD: insert_eu ((e, tid), eu2) reord1 reord2)
    (EUTRS1: IdMap.find tid eutrs1 = Some eutr)
    (EUTRS2: eutrs2 = IdMap.add tid (eutr++[eu2]) eutrs1)
    (TRACES: traces p mem (tr1++[m1]) eutrs1 reord1):
    traces p mem (tr1++[m1]++[m2]) eutrs2 reord2
.

Lemma sim_eu_init
      p m mem
      tr eutrs reord
      (EXEC: Machine.pf_exec p m)
      (TRACES: traces p mem (tr++[m]) eutrs reord):
  sim_machine eutrs mem (Machine.init p) 0 reord.
Proof.
  admit.
Qed.

Lemma sim_eu_step
      p m mem
      tr eutrs n reord
      vm1
      (EXEC: Machine.pf_exec p m)
      (TRACES: traces p mem (tr++[m]) eutrs reord)
      (SIM: sim_machine eutrs mem vm1 n reord):
  exists vm2,
    <<STEP: Machine.step ExecUnit.view_step vm1 vm2>> /\
    <<SIM: sim_machine eutrs mem vm2 (S n) reord>>.
Proof.
  admit.
Qed.

Lemma sim_eu_final
      p m mem
      tr eutrs reord
      (EXEC: Machine.pf_exec p m)
      (TRACES: traces p mem (tr++[m]) eutrs reord):
  exists vm,
    <<STEP: rtc (Machine.step ExecUnit.view_step) (Machine.init p) vm>> /\
    <<SIM: sim_machine eutrs mem vm (length reord) reord>>.
Proof.
  admit.
Qed.

Theorem promising_pf_to_view
        p pm
        (EXEC: Machine.pf_exec p pm):
  exists vm,
    <<STEP: Machine.view_exec p vm>> /\
    <<SIM: Machine.equiv pm vm>>.
Proof.
  inv EXEC.
  generalize (Machine.init_wf p). intro WF.
  generalize (Machine.init_no_promise p). intro NOPROMISE0.
  inv STEP2.
  admit.
Qed.

Theorem promising_to_view
        p pm
        (EXEC: Machine.exec p pm):
  exists vm,
    <<STEP: Machine.view_exec p vm>> /\
    <<SIM: Machine.equiv pm vm>>.
Proof.
  apply promising_to_promising_pf in EXEC.
  apply promising_pf_to_view; auto.
Qed.
