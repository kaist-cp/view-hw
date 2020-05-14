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
Require Import PromisingArch.promising.TsoStateExecFacts.
Require Import PromisingArch.axiomatic.TsoAxiomatic.
Require Import PromisingArch.axiomatic.TsoCommonAxiomatic.

Set Implicit Arguments.


Inductive sim_trace (p: program) (mem: Memory.t) (tid: Id.t):
  forall (tr: list (ExecUnit.t)) (atr: list AExecUnit.t)
     (wl: list (nat -> option (Loc.t * Time.t))) (rl: list (nat -> option (Loc.t * Time.t)))
     (cov: list (nat -> Time.t)) (vext: list (nat -> Time.t)), Prop :=
| sim_trace_init
    st lc stmts
    (FIND: IdMap.find tid (Machine.init_with_promises p mem).(Machine.tpool) = Some (st, lc))
    (STMT: IdMap.find tid p = Some stmts):
    sim_trace p mem tid [ExecUnit.mk st lc mem] [AExecUnit.mk (State.init stmts) ALocal.init]
              [fun _ => None] [fun _ => None] [fun _ => Time.bot] [fun _ => Time.bot]
| sim_trace_step
    e ae tr eu1 eu2 atr aeu1 aeu2 rl r1 r2 wl w1 w2 covl cov1 cov2 vextl vext1 vext2
    (STEP: ExecUnit.state_step0 tid e e eu1 eu2)
    (ASTATE_STEP: State.step ae aeu1.(AExecUnit.state) aeu2.(AExecUnit.state))
    (ALOCAL_STEP: ALocal.step ae aeu1.(AExecUnit.local) aeu2.(AExecUnit.local))
    (EVENT: sim_event e ae)
    (STATE: sim_state_weak eu2.(ExecUnit.state) aeu2.(AExecUnit.state))
    (LOCAL: sim_local_weak eu2.(ExecUnit.local) aeu2.(AExecUnit.local))
    (W: w2 = match e with
             | Event.write _ _ vloc _ (ValA.mk _ 0 _)
             | Event.rmw _ _ vloc _ _ =>
               (fun eid => if Nat.eqb eid (ALocal.next_eid aeu1.(AExecUnit.local))
                          then Some (vloc.(ValA.val),
                                     Memory.latest_ts
                                       vloc.(ValA.val)
                                       (eu2.(ExecUnit.local).(Local.coh) vloc.(ValA.val)).(View.ts)
                                       mem)
                         else w1 eid)
             | _ => w1
             end)
    (R: r2 = match e with
               | Event.read _ _ _ vloc _ =>
                 (fun eid => if Nat.eqb eid (ALocal.next_eid aeu1.(AExecUnit.local))
                            then Some (vloc.(ValA.val),
                                       Memory.latest_ts
                                         vloc.(ValA.val)
                                         (eu2.(ExecUnit.local).(Local.coh) vloc.(ValA.val)).(View.ts)
                                         mem)
                            else r1 eid)
               (* CHECK: infer rmw read timestamp *)
               | Event.rmw _ _ vloc _ _ =>
                 (fun eid => if Nat.eqb eid (ALocal.next_eid aeu1.(AExecUnit.local))
                            then Some (vloc.(ValA.val),
                                       Memory.latest_ts
                                         vloc.(ValA.val)
                                         (pred ((eu2.(ExecUnit.local).(Local.coh) vloc.(ValA.val)).(View.ts)))
                                         mem)
                            else r1 eid)
               | _ => r1
               end)
    (COV: cov2 = match e with
                 | Event.read _ _ _ vloc _
                 | Event.write _ _ vloc _ (ValA.mk _ 0 _)
                 | Event.rmw _ _ vloc _ _ =>
                   (fun eid => if Nat.eqb eid (ALocal.next_eid aeu1.(AExecUnit.local))
                              then Memory.latest_ts
                                     vloc.(ValA.val)
                                     (eu2.(ExecUnit.local).(Local.coh) vloc.(ValA.val)).(View.ts)
                                     mem
                              else cov1 eid)
                 | _ => cov1
                 end)
    (VEXT: vext2 = match e with
                   | Event.read _ _ _ vloc _ =>
                     (fun eid => if Nat.eqb eid (ALocal.next_eid aeu1.(AExecUnit.local))
                                then (eu2.(ExecUnit.local).(Local.vrn).(View.ts))
                                else vext1 eid)
                   | Event.write _ _ vloc _ (ValA.mk _ 0 _)
                   | Event.rmw _ _ vloc _ _ =>
                     (fun eid => if Nat.eqb eid (ALocal.next_eid aeu1.(AExecUnit.local))
                                then (eu2.(ExecUnit.local).(Local.coh) vloc.(ValA.val)).(View.ts)
                                else vext1 eid)
                   | _ => vext1
                   end)
    (TRACE: sim_trace p mem tid (eu1::tr) (aeu1::atr) (w1::wl) (r1::rl) (cov1::covl) (vext1::vextl)):
    sim_trace p mem tid (eu2::eu1::tr) (aeu2::aeu1::atr) (w2::w1::wl) (r2::r1::rl) (cov2::cov1::covl) (vext2::vext1::vextl)
.

Definition sim_traces
           (p: program) (mem: Memory.t)
           (trs: IdMap.t (list (ExecUnit.t)))
           (atrs: IdMap.t (list AExecUnit.t))
           (ws: IdMap.t (list (nat -> option (Loc.t * Time.t))))
           (rs: IdMap.t (list (nat -> option (Loc.t * Time.t))))
           (covs: IdMap.t (list (nat -> Time.t)))
           (vexts: IdMap.t (list (nat -> Time.t)))
  : Prop :=
  IdMap.Forall6 (sim_trace p mem) trs atrs ws rs covs vexts.

Lemma sim_trace_last
      p mem tid tr atr wl rl covl vextl
      (SIM: sim_trace p mem tid tr atr wl rl covl vextl):
  exists eu tr' aeu atr' w wl' r rl' cov covl' vext vextl',
    <<HDTR: tr = eu :: tr'>> /\
    <<HDATR: atr = aeu :: atr'>> /\
    <<HDWL: wl = w :: wl'>> /\
    <<HDRL: rl = r :: rl'>> /\
    <<HDCOVL: covl = cov :: covl'>> /\
    <<HDVEXTL: vextl = vext :: vextl'>>.
Proof.
  inv SIM; esplits; eauto.
Qed.

Lemma sim_trace_length
      p mem tid tr atr wl rl covl vextl
      (SIM: sim_trace p mem tid tr atr wl rl covl vextl):
  <<LENGTH_ATR: List.length atr = List.length tr>> /\
  <<LENGTH_WL: List.length wl = List.length tr>> /\
  <<LENGTH_RL: List.length rl = List.length tr>> /\
  <<LENGTH_COVL: List.length covl = List.length tr>> /\
  <<LENGTH_VEXTL: List.length vextl = List.length tr>>.
Proof.
  induction SIM; ss. des. splits; congr.
Qed.

Lemma sim_trace_memory
      p mem tid tr atr rl wl covl vextl
      eu tr'
      (SIM: sim_trace p mem tid tr atr rl wl covl vextl)
      (EU: tr = eu :: tr'):
  mem = eu.(ExecUnit.mem).
Proof.
  revert eu tr' EU.
  induction SIM.
  - ii. inv EU. ss.
  - ii. inv EU. exploit IHSIM; try refl. i.
    inv STEP. ss.
Qed.

Lemma sim_traces_memory
      p trs atrs rs ws covs vexts
      m
      ts loc val tid
      (STEP: Machine.pf_exec p m)
      (SIM: sim_traces p m.(Machine.mem) trs atrs ws rs covs vexts)
      (TR: IdMap.Forall2
             (fun tid tr sl => exists l, tr = (ExecUnit.mk (fst sl) (snd sl) m.(Machine.mem)) :: l)
             trs m.(Machine.tpool))
      (GET: Memory.get_msg ts m.(Machine.mem) = Some (Msg.mk loc val tid)):
  exists eu, IdMap.find tid trs = Some eu.
Proof.
  generalize (SIM tid). intro X. inv X; eauto.
  generalize (TR tid). rewrite <- H0. intro X. inv X.
  inv STEP. hexploit state_exec_rtc_state_step; [by eauto|]. i. des.
  exploit Machine.step_get_msg_tpool.
  - etrans.
    + eapply Machine.rtc_step_mon; [|by eauto]. right. ss.
    + eapply Machine.rtc_step_mon; [|by eauto]. left. ss.
  - inv EQUIV. rewrite <- MEM. eauto.
  - s. i. des. inv EQUIV. generalize (TPOOL tid). congr.
Qed.

Ltac simplify :=
  repeat
    (try match goal with
         | [H1: _ = IdMap.find ?id ?m, H2: _ = IdMap.find ?id ?m |- _] =>
           rewrite <- H1 in H2; inv H2
         | [H1: IdMap.find ?id ?m = _, H2: IdMap.find ?id ?m = _ |- _] =>
           rewrite H1 in H2; inv H2
         | [H1: IdMap.find ?id ?m = _, H2: _ = IdMap.find ?id ?m |- _] =>
           rewrite H1 in H2; inv H2
         | [H: Some _ = Some _ |- _] => inv H
         | [H: _::_ = _::_ |- _] => inv H
         end).

Lemma promising_pf_sim_step
      tid e (eu1 eu2:ExecUnit.t) aeu1
      (STATE1: sim_state_weak eu1.(ExecUnit.state) aeu1.(AExecUnit.state))
      (LOCAL1: sim_local_weak eu1.(ExecUnit.local) aeu1.(AExecUnit.local))
      (STEP: ExecUnit.state_step0 tid e e eu1 eu2):
  exists ae aeu2,
    <<ASTATE_STEP: State.step ae aeu1.(AExecUnit.state) aeu2.(AExecUnit.state)>> /\
    <<ALOCAL_STEP: ALocal.step ae aeu1.(AExecUnit.local) aeu2.(AExecUnit.local)>> /\
    <<EVENT: sim_event e ae>> /\
    <<STATE2: sim_state_weak eu2.(ExecUnit.state) aeu2.(AExecUnit.state)>> /\
    <<LOCAL2: sim_local_weak eu2.(ExecUnit.local) aeu2.(AExecUnit.local)>>.
Proof.
  destruct eu1 as [st1 lc1 mem1].
  destruct eu2 as [st2 lc2 mem2].
  destruct aeu1 as [[astmt1 armap1] alc1].
  inv STATE1. inv STEP. ss. subst. inv STATE; inv LOCAL; inv EVENT; ss.
  - eexists _, (AExecUnit.mk (State.mk _ _) _). splits; ss.
    + econs 1.
    + econs; ss.
    + ss.
    + ss.
  - eexists _, (AExecUnit.mk (State.mk _ _) _). splits; ss.
    + econs 2. ss.
    + econs; ss.
    + econs; ss.
    + econs; ss. eauto using sim_rmap_weak_add, sim_rmap_weak_expr.
  - inv STEP.
    eexists _, (AExecUnit.mk (State.mk _ _) _). splits; ss.
    + econs 3; ss.
    + econs 2; ss.
    + econs; ss. eauto using sim_rmap_weak_add, sim_rmap_weak_expr.
    + econs; ss. eauto using sim_rmap_weak_add, sim_rmap_weak_expr.
  - inv STEP.
    eexists _, (AExecUnit.mk (State.mk _ _) _). splits; ss.
    + econs 4; ss.
    + econs 3; ss.
    + econs; ss.
      * eauto using sim_rmap_weak_add, sim_rmap_weak_expr.
      * eauto using sim_rmap_weak_add, sim_rmap_weak_expr.
    + econs; ss. eauto using sim_rmap_weak_add, sim_rmap_weak_expr.
  - inv STEP.
    eexists _, (AExecUnit.mk (State.mk _ _) _). splits; ss.
    + econs 5; ss. admit. (* sem_rmw armap *)
    + econs 4; ss.
    + econs; ss.
      eauto using sim_rmap_weak_add, sim_rmap_weak_expr.
    + econs; ss.
  - inv STEP.
    eexists _, (AExecUnit.mk (State.mk _ _) _). splits; ss.
    + econs 6; ss. admit. (* sem_rmw armap *)
    + econs 2; ss.
    + econs; ss.
      eauto using sim_rmap_weak_add, sim_rmap_weak_expr.
    + econs; ss.
  - inv STEP.
    eexists _, (AExecUnit.mk (State.mk _ _) _). splits; ss.
    + econs 7; ss.
    + econs 5; ss.
    + econs; ss.
    + econs; ss.
  - eexists _, (AExecUnit.mk (State.mk _ _) _). splits; ss.
    + econs 9. ss.
    + econs; ss.
    + ss.
    + ss.
Qed.

Lemma promising_pf_sim_traces
      p m
      (STEP: Machine.pf_exec p m):
  exists trs atrs ws rs covs vexts ex (PRE: Valid.pre_ex p ex),
    <<SIM: sim_traces p m.(Machine.mem) trs atrs ws rs covs vexts>> /\
    <<TR: IdMap.Forall2
            (fun tid tr sl => exists l, tr = (ExecUnit.mk (fst sl) (snd sl) m.(Machine.mem)) :: l)
            trs m.(Machine.tpool)>> /\
    <<ATR: IdMap.Forall2
             (fun tid atr aeu => exists l, atr = aeu :: l)
             atrs PRE.(Valid.aeus)>>.
Proof.
  inv STEP. exploit state_exec_rtc_state_step; eauto. i. des.
  eapply Machine.equiv_no_promise in NOPROMISE; eauto. revert NOPROMISE.
  cut (exists trs atrs ws rs covs vexts ex (PRE: Valid.pre_ex p ex),
    <<SIM: sim_traces p (Machine.mem m2') trs atrs ws rs covs vexts>> /\
    <<TR: forall tid, opt_rel
            (fun tr sl => exists l, tr = (ExecUnit.mk (fst sl) (snd sl) (Machine.mem m2')) :: l)
            (IdMap.find tid trs)
            (IdMap.find tid (Machine.tpool m2'))>> /\
    <<ATR: IdMap.Forall2
             (fun tid atr aeu => exists l, atr = aeu :: l)
             atrs PRE.(Valid.aeus)>>).
  { inv EQUIV. rewrite MEM. i. des. esplits; eauto. ii. rewrite TPOOL. ss. }
  clear m STEP2 EQUIV.
  apply clos_rt_rt1n_iff, clos_rt_rtn1_iff in EXEC. induction EXEC.
  { eexists (IdMap.map (fun x => [x]) (IdMap.mapi (fun _ _ => _) p)).
    eexists (IdMap.map (fun x => [x]) (IdMap.mapi (fun _ _ => _) p)).
    eexists (IdMap.mapi (fun _ _ => [fun _ => None]) p).
    eexists (IdMap.mapi (fun _ _ => [fun _ => None]) p).
    eexists (IdMap.mapi (fun _ _ => [bot]) p).
    eexists (IdMap.mapi (fun _ _ => [bot]) p).
    eexists (Execution.mk (IdMap.mapi (fun _ _ => _) p) bot bot).
    eexists (@Valid.mk_pre_ex _ _ (IdMap.mapi (fun tid stmts => AExecUnit.mk (State.init stmts) ALocal.init) p)  _ _).
    hexploit Machine.rtc_promise_step_spec; eauto. s. intro X.
    s. splits; cycle 1.
    - i. specialize (X tid). rewrite ? IdMap.map_spec, ? IdMap.mapi_spec in *.
      rewrite X. destruct (IdMap.find tid p); ss. econs. eauto.
    - ii. rewrite ? IdMap.map_spec, ? IdMap.mapi_spec. destruct (IdMap.find id p); ss. eauto.
    - ii. rewrite ? IdMap.map_spec, ? IdMap.mapi_spec. destruct (IdMap.find id p) eqn:STMTS; ss. econs.
      econs 1; ss. rewrite IdMap.mapi_spec, STMTS. s. ss.
  }
  des.
  destruct y as [tpool1 mem1].
  destruct z as [tpool2 mem2].
  ss. inv H. ss. subst. inv STEP. inv STEP0. ss. subst.
  generalize (TR tid). rewrite FIND. intro Y. inv Y. des. subst. rename H0 into TRS. symmetry in TRS.
  generalize (SIM tid). intro Y. inv Y; [congr|]. rewrite TRS in H0. inv H0.
  hexploit sim_trace_last; eauto. i. des. subst. simplify.
  exploit promising_pf_sim_step; eauto.
  { inv REL6; eauto. s.
    unfold Machine.init_with_promises in FIND0. ss.
    rewrite IdMap.mapi_spec, STMT in *. inv FIND0.
    apply sim_state_weak_init.
  }
  { instantiate (1 := ExecUnit.mk _ _ _). econs; ss; eauto. }
  i. des.

  eexists (IdMap.add tid _ trs).
  eexists (IdMap.add tid _ atrs).
  eexists (IdMap.add tid _ ws).
  eexists (IdMap.add tid _ rs).
  eexists (IdMap.add tid _ covs).
  eexists (IdMap.add tid _ vexts).
  eexists (Execution.mk _ _ _).
  eexists (@Valid.mk_pre_ex _ _ (IdMap.add tid _ PRE.(Valid.aeus)) _ _).
  s. splits; cycle 1.
  - i. rewrite ? IdMap.add_spec. condtac; eauto.
  - ii. rewrite ? IdMap.add_spec. condtac; eauto.
  - s. ii. rewrite ? IdMap.add_spec. condtac; eauto. inversion e0. subst. clear e0 X. econs.
    econs 2; eauto. econs; eauto.
Grab Existential Variables.
all: ss.
1: { ii. generalize (PRE.(Valid.AEUS) id). intro X.
     rewrite IdMap.add_spec. condtac; ss. inversion e0. subst. clear e0 X0.
     generalize (ATR tid). rewrite <- H. intro Y. inv Y. des. inv REL.
     rewrite <- H6 in X. inv X. econs. etrans; eauto with tso.
}
4: { ii. rewrite IdMap.mapi_spec. destruct (IdMap.find id p); ss. econs. refl. }
3: { unfold IdMap.map. rewrite IdMap.mapi_mapi. f_equal. }
1: { apply bot. (* it's ex's co. *) }
1: { apply bot. (* it's ex's rf. *) }
Qed.

Inductive sim_th
          (p:program) (mem:Memory.t) (tid:Id.t)
          (eu:ExecUnit.t)
          (aeu:AExecUnit.t)
          (w: nat -> option (Loc.t * Time.t))
          (r: nat -> option (Loc.t * Time.t))
          (cov: nat -> Time.t)
          (vext: nat -> Time.t): Prop := mk {
  WPROP1:
    forall ts loc val
      (GET: Memory.get_msg ts mem = Some (Msg.mk loc val tid)),
      ((Promises.lookup ts eu.(ExecUnit.local).(Local.promises) = true /\
        forall eid, w eid <> Some (loc, ts)) \/
       (Promises.lookup ts eu.(ExecUnit.local).(Local.promises) = false /\
        exists eid l,
          w eid = Some (loc, ts) /\
          List.nth_error aeu.(AExecUnit.local).(ALocal.labels) eid = Some l /\
          Label.is_writing_val loc val l));
  WPROP2:
    forall eid loc val l
      (GET: List.nth_error aeu.(AExecUnit.local).(ALocal.labels) eid = Some l /\
            Label.is_writing_val loc val l),
    exists ts,
      w eid = Some (loc, ts) /\
      Memory.get_msg ts mem = Some (Msg.mk loc val tid);
  WPROP2':
    forall eid loc l
      (GET: List.nth_error aeu.(AExecUnit.local).(ALocal.labels) eid = Some l /\
            Label.is_writing loc l),
    exists ts val,
      w eid = Some (loc, ts) /\
      Memory.get_msg ts mem = Some (Msg.mk loc val tid);
  WPROP3:
    forall eid loc ts (GET: w eid = Some (loc, ts)),
      Time.lt Time.bot ts /\
      cov eid = ts /\
      vext eid = ts /\
      le ts (eu.(ExecUnit.local).(Local.coh) loc).(View.ts) /\
      exists val l,
        List.nth_error aeu.(AExecUnit.local).(ALocal.labels) eid = Some l /\
        Label.is_writing_val loc val l /\
        Memory.get_msg ts mem = Some (Msg.mk loc val tid);
  WPROP4:
    forall eid1 loc1 eid2 loc2 ts (W1: w eid1 = Some (loc1, ts)) (W2: w eid2 = Some (loc2, ts)),
      eid1 = eid2;
  RPROP1:
    forall eid loc val l
      (GET: List.nth_error aeu.(AExecUnit.local).(ALocal.labels) eid = Some l /\
            Label.is_reading_val loc val l),
    exists ts tid',
      r eid = Some (loc, ts) /\
      __guard__ ((ts = Time.bot /\ val = Val.default) \/
                 Memory.get_msg ts mem = Some (Msg.mk loc val tid'));
  RPROP2:
    forall eid loc ts (GET: r eid = Some (loc, ts)),
    cov eid = ts /\
    le ts (eu.(ExecUnit.local).(Local.coh) loc).(View.ts) /\
    exists val tid',
      List.nth_error aeu.(AExecUnit.local).(ALocal.labels) eid = Some (Label.read loc val) /\
      __guard__ ((ts = Time.bot /\ val = Val.default) \/
                 Memory.get_msg ts mem = Some (Msg.mk loc val tid'));
  COVPROP:
    forall eid (COV: cov eid > 0),
      AExecUnit.label_is aeu.(AExecUnit.local).(ALocal.labels) Label.is_access eid;
  VEXTPROP:
    forall eid (VEXT: vext eid > 0),
      AExecUnit.label_is aeu.(AExecUnit.local).(ALocal.labels) Label.is_access eid;

  PO: forall iid1 iid2 label1 label2
     (PO: iid1 < iid2)
     (LABEL1: List.nth_error aeu.(AExecUnit.local).(ALocal.labels) iid1 = Some label1)
     (LABEL2: List.nth_error aeu.(AExecUnit.local).(ALocal.labels) iid2 = Some label2)
     (REL: Execution.label_loc label1 label2),
      <<PO_LOC_WRITE:
        Label.is_write label2 ->
        Time.lt (cov iid1) (cov iid2)>> /\
      <<PO_LOC_READ:
        Label.is_read label2 ->
        Time.le (cov iid1) (cov iid2)>>;
  EU_WF: ExecUnit.wf tid eu;
  AEU_WF: AExecUnit.wf aeu;
  MEM: eu.(ExecUnit.mem) = mem;
}.

Lemma sim_trace_sim_state_weak
      p mem tid
      tr eu tr'
      atr aeu atr'
      wl w wl'
      rl r rl'
      covl cov covl'
      vextl vext vextl'
      (SIM: sim_trace p mem tid tr atr wl rl covl vextl)
      (EU: tr = eu :: tr')
      (AEU: atr = aeu :: atr')
      (RL: rl = r :: rl')
      (WL: wl = w :: wl')
      (COV: covl = cov :: covl')
      (VEXT: vextl = vext :: vextl'):
  sim_state_weak eu.(ExecUnit.state) aeu.(AExecUnit.state).
Proof.
  subst. inv SIM; ss.
  rewrite IdMap.mapi_spec, STMT in FIND. inv FIND.
  eapply sim_state_weak_init.
Qed.

Lemma sim_trace_sim_th
      p mem tid
      tr eu tr'
      atr aeu atr'
      wl w wl'
      rl r rl'
      covl cov covl'
      vextl vext vextl'
      (SIM: sim_trace p mem tid tr atr wl rl covl vextl)
      (EU: tr = eu :: tr')
      (AEU: atr = aeu :: atr')
      (RL: rl = r :: rl')
      (WL: wl = w :: wl')
      (COV: covl = cov :: covl')
      (VEXT: vextl = vext :: vextl'):
  sim_th p mem tid eu aeu w r cov vext.
Proof.
  revert r rl' w wl' eu tr' aeu atr' cov covl' vext vextl' RL WL EU AEU COV VEXT. induction SIM.
  { i. simplify. ss. econs; ss.
    - rewrite IdMap.mapi_spec, STMT in FIND. inv FIND. s. i.
      left. splits; ss. destruct ts; ss.
      eapply Machine.promises_from_mem_lookup. eauto.
    - rewrite IdMap.mapi_spec, STMT in FIND. inv FIND. s. i. des.
      destruct eid; ss.
    - rewrite IdMap.mapi_spec, STMT in FIND. inv FIND. s. i. des.
      destruct eid; ss.
    - rewrite IdMap.mapi_spec, STMT in FIND. inv FIND. s. i. des.
      destruct eid; ss.
    - unfold Time.bot. i. lia.
    - unfold Time.bot. i. lia.
    - i. destruct iid1; ss.
    - rewrite IdMap.mapi_spec, STMT in FIND. inv FIND.
      econs; ss.
      econs; ss; i; try by apply bot_spec.
      + destruct ts; ss.
        rewrite Machine.promises_from_mem_spec in IN. des.
        apply lt_le_S. rewrite <- List.nth_error_Some. ii. congr.
      + destruct ts; ss.
        unfold Memory.get_msg in *. ss. destruct msg.
        exploit Machine.promises_from_mem_lookup; eauto. ss. subst. ss.
  }
  clear LOCAL.
  i. simplify.
  destruct eu1 as [st1 lc1 mem1].
  destruct eu as [st2 lc2 mem2].
  destruct aeu1 as [ast1 alc1].
  destruct aeu as [ast2 alc2].
  assert (mem1 = mem); subst.
  { exploit sim_trace_memory; eauto. }
  ss. exploit IHSIM; eauto.
  i. rename x into IH.
  assert (EU_WF2: ExecUnit.wf tid (ExecUnit.mk st2 lc2 mem2)).
  { destruct IH.
    eapply ExecUnit.state_step_wf; eauto. econs; eauto. }
  assert (AEU_WF2: AExecUnit.wf (AExecUnit.mk ast2 alc2)).
  { destruct IH.
    eapply AExecUnit.step_future; eauto with tso. }
  inv STEP. inv ALOCAL_STEP; inv EVENT; ss; eauto.
  { (* internal *)
    inv LOCAL; ss. inv EVENT. econs; ss; try by apply IH.
  }
  { (* read *)
    inv LOCAL; ss.
    { (* pure read *)
      generalize IH.(EU_WF). i. inv H.
      specialize (Local.read_spec LOCAL STEP). intro READ_SPEC. guardH READ_SPEC.
      inv STEP. inv STATE0; inv EVENT; ss.
      exploit sim_trace_sim_state_weak; eauto. s. intro Y. inv Y. ss. inv STMTS.
      exploit sim_rmap_weak_expr; eauto. intro Y. inv Y.
      inv ASTATE_STEP.
      all: econs; ss.
      clear EU_WF2 AEU_WF2.
      - i. exploit IH.(WPROP1); eauto. s. i. des; [left|right]; esplits; eauto.
        eapply nth_error_app_mon. eauto.
      - i. exploit IH.(WPROP2); eauto. des.
        apply nth_error_snoc_inv in GET. des; eauto. split; ss. destruct l; ss.
      - i. exploit IH.(WPROP2'); eauto. des.
        apply nth_error_snoc_inv in GET. des; eauto. split; ss. destruct l; ss.
      - i. exploit IH.(WPROP3); eauto. s. i. des. des_ifs.
        { exfalso. apply Nat.eqb_eq in Heq. subst.
          unfold ALocal.next_eid in *.
          assert (H: List.nth_error (ALocal.labels alc1) (length (ALocal.labels alc1)) <> None) by (ii; congr).
          apply List.nth_error_Some in H. lia.
        }
        esplits; eauto.
        + rewrite fun_add_spec. des_ifs; eauto. inv e.
          ss. etrans; eauto. apply join_l.
        + eapply nth_error_app_mon. eauto.
      - eapply IH.(WPROP4).
      - i. des. apply nth_error_snoc_inv in GET. des.
        + exploit IH.(RPROP1); eauto. i. des. esplits; eauto.
          des_ifs. apply Nat.eqb_eq in Heq. subst. unfold ALocal.next_eid in *. lia.
        + des_ifs; cycle 1.
          { apply Nat.eqb_neq in Heq. unfold ALocal.next_eid in *. congr. }
          rewrite fun_add_spec in *. condtac; [|congr].
          inv VLOC. inv VAL. ss. subst. rewrite VAL1 in *.
          move READ_SPEC at bottom. desH READ_SPEC. rewrite <- COH0.
          des_ifs.
          destruct (equiv_dec (ValA.val (sem_expr rmap0 eloc0)) loc); ss. inv e0.
          destruct (equiv_dec res val0); ss. inv e0.
          exploit Memory.read_get_msg; eauto. i. des; esplits; eauto.
      - i. des_ifs.
        + apply Nat.eqb_eq in Heq. subst.
          rewrite fun_add_spec in *. des_ifs; [|congr].
          inv VLOC. inv VAL. ss. subst. rewrite VAL1 in *.
          move READ_SPEC at bottom. desH READ_SPEC. rewrite <- COH0.
          exploit Memory.read_get_msg; eauto. i. des; esplits; eauto with tso.
          all: try by rewrite COH0 at 1; eapply Memory.latest_ts_spec.
          all: try by rewrite List.nth_error_app2, Nat.sub_diag; [|refl]; ss; eauto with tso.
        + exploit IH.(RPROP2); eauto. s. i. des; esplits; eauto with tso.
          * rewrite fun_add_spec. des_ifs; eauto.
            inv e. etrans; eauto. ss. apply join_l.
          * eapply nth_error_app_mon. eauto.
      - unfold ALocal.next_eid in *. s. i. des_ifs.
        { apply Nat.eqb_eq in Heq. subst. econs; eauto.
          - rewrite List.nth_error_app2, Nat.sub_diag; [|refl]. ss.
          - econs; ss.
        }
        apply AExecUnit.label_is_mon. eapply IH.(COVPROP); eauto.
      - unfold ALocal.next_eid in *. s. i. des_ifs.
        { apply Nat.eqb_eq in Heq. subst. econs; eauto.
          - rewrite List.nth_error_app2, Nat.sub_diag; [|refl]. ss.
          - econs; ss.
        }
        apply AExecUnit.label_is_mon. eapply IH.(VEXTPROP); eauto.
      - i. unfold ALocal.next_eid in *.
        apply nth_error_snoc_inv in LABEL1. apply nth_error_snoc_inv in LABEL2. des.
        + repeat condtac.
          all: try apply Nat.eqb_eq in X; ss; subst; try lia.
          all: try apply Nat.eqb_eq in X0; ss; subst; try lia.
          eapply IH.(PO); eauto.
        + lia.
        + subst. repeat condtac; ss.
          all: try apply Nat.eqb_eq in X; ss; subst; try lia.
          all: try apply Nat.eqb_neq in X0; ss; try lia.
          splits; ss. rewrite fun_add_spec. des_ifs; [|congr].
          inv REL. destruct label1; ss.
          * destruct (equiv_dec loc0 loc); ss. inv e0.
            destruct (equiv_dec (ValA.val (sem_expr rmap0 eloc0)) loc); ss. inv e0.
            exploit IH.(RPROP1); eauto with tso. i. des.
            exploit IH.(RPROP2); eauto. s. i. des. subst.
            exploit sim_rmap_weak_expr; eauto. i. inv x2. rewrite VAL1 in *.
            desH x5.
            { rewrite x5. apply bot_spec. }
            exploit Memory.latest_ts_read_le; try eapply Memory.get_msg_read; eauto. i.
            rewrite x2. apply Memory.latest_ts_mon. apply join_l.
          * destruct (equiv_dec loc0 loc); ss. inv e0.
            destruct (equiv_dec (ValA.val (sem_expr rmap0 eloc0)) loc); ss. inv e0.
            exploit IH.(WPROP2); eauto with tso. i. des.
            exploit IH.(WPROP3); eauto. s. i. des. subst.
            exploit sim_rmap_weak_expr; eauto. i. inv x3. rewrite VAL1 in *.
            exploit Memory.latest_ts_read_le; try eapply Memory.get_msg_read; eauto. i.
            rewrite x3. apply Memory.latest_ts_mon. apply join_l.
          * destruct (equiv_dec loc0 loc); ss. inv e0.
            destruct (equiv_dec (ValA.val (sem_expr rmap0 eloc0)) loc); ss. inv e0.
            exploit IH.(WPROP2); eauto with tso. i. des.
            exploit IH.(WPROP3); eauto. s. i. des. subst.
            exploit sim_rmap_weak_expr; eauto. i. inv x3. rewrite VAL1 in *.
            exploit Memory.latest_ts_read_le; try eapply Memory.get_msg_read; eauto. i.
            rewrite x3. apply Memory.latest_ts_mon. apply join_l.
        + subst. repeat condtac; ss.
          all: try apply Nat.eqb_eq in X; ss; try lia.
    }
    { (* rmw_fail *)
      generalize IH.(EU_WF). i. inv H.
      specialize (Local.rmw_failure_spec LOCAL STEP). intro RMW_FAILURE_SPEC. guardH RMW_FAILURE_SPEC.
      inv STEP. inv STATE0; inv EVENT; ss.
      exploit sim_trace_sim_state_weak; eauto. s. intro Y. inv Y. ss. inv STMTS.
      exploit sim_rmap_weak_expr; eauto. intro Y. inv Y.
      inv ASTATE_STEP.
      all: econs; ss.
      clear EU_WF2 AEU_WF2.
      - i. exploit IH.(WPROP1); eauto. s. i. des; [left|right]; esplits; eauto.
        eapply nth_error_app_mon. eauto.
      - i. exploit IH.(WPROP2); eauto. des.
        apply nth_error_snoc_inv in GET. des; eauto. split; ss. destruct l; ss.
      - i. exploit IH.(WPROP2'); eauto. des.
        apply nth_error_snoc_inv in GET. des; eauto. split; ss. destruct l; ss.
      - i. exploit IH.(WPROP3); eauto. s. i. des. des_ifs.
        { exfalso. apply Nat.eqb_eq in Heq. subst.
          unfold ALocal.next_eid in *.
          assert (H: List.nth_error (ALocal.labels alc1) (length (ALocal.labels alc1)) <> None) by (ii; congr).
          apply List.nth_error_Some in H. lia.
        }
        esplits; eauto.
        + rewrite fun_add_spec. des_ifs; eauto. inv e.
          ss. etrans; eauto. apply join_l.
        + eapply nth_error_app_mon. eauto.
      - eapply IH.(WPROP4).
      - i. des. apply nth_error_snoc_inv in GET. des.
        + exploit IH.(RPROP1); eauto. i. des. esplits; eauto.
          des_ifs. apply Nat.eqb_eq in Heq. subst. unfold ALocal.next_eid in *. lia.
        + des_ifs; cycle 1.
          { apply Nat.eqb_neq in Heq. unfold ALocal.next_eid in *. congr. }
          rewrite fun_add_spec in *. condtac; [|congr].
          inv VLOC. inv VAL. ss. subst. rewrite VAL1 in *.
          move RMW_FAILURE_SPEC at bottom. desH RMW_FAILURE_SPEC. rewrite <- COH0.
          des_ifs.
          destruct (equiv_dec (ValA.val (sem_expr rmap0 eloc0)) loc); ss. inv e0.
          destruct (equiv_dec res val); ss. inv e0.
          exploit Memory.read_get_msg; eauto. i. des; esplits; eauto.
      - i. des_ifs.
        + apply Nat.eqb_eq in Heq. subst.
          rewrite fun_add_spec in *. des_ifs; [|congr].
          inv VLOC. inv VAL. ss. subst. rewrite VAL1 in *.
          move RMW_FAILURE_SPEC at bottom. desH RMW_FAILURE_SPEC. rewrite <- COH0.
          exploit Memory.read_get_msg; eauto. i. des; esplits; eauto with tso.
          all: try by rewrite COH0 at 1; eapply Memory.latest_ts_spec.
          all: try by rewrite List.nth_error_app2, Nat.sub_diag; [|refl]; ss; eauto with tso.
        + exploit IH.(RPROP2); eauto. s. i. des; esplits; eauto with tso.
          * rewrite fun_add_spec. des_ifs; eauto.
            inv e. etrans; eauto. ss. apply join_l.
          * eapply nth_error_app_mon. eauto.
      - unfold ALocal.next_eid in *. s. i. des_ifs.
        { apply Nat.eqb_eq in Heq. subst. econs; eauto.
          - rewrite List.nth_error_app2, Nat.sub_diag; [|refl]. ss.
          - econs; ss.
        }
        apply AExecUnit.label_is_mon. eapply IH.(COVPROP); eauto.
      - unfold ALocal.next_eid in *. s. i. des_ifs.
        { apply Nat.eqb_eq in Heq. subst. econs; eauto.
          - rewrite List.nth_error_app2, Nat.sub_diag; [|refl]. ss.
          - econs; ss.
        }
        apply AExecUnit.label_is_mon. eapply IH.(VEXTPROP); eauto.
      - i. unfold ALocal.next_eid in *.
        apply nth_error_snoc_inv in LABEL1. apply nth_error_snoc_inv in LABEL2. des.
        + repeat condtac.
          all: try apply Nat.eqb_eq in X; ss; subst; try lia.
          all: try apply Nat.eqb_eq in X0; ss; subst; try lia.
          eapply IH.(PO); eauto.
        + lia.
        + subst. repeat condtac; ss.
          all: try apply Nat.eqb_eq in X; ss; subst; try lia.
          all: try apply Nat.eqb_neq in X0; ss; try lia.
          splits; ss. rewrite fun_add_spec. des_ifs; [|congr].
          inv REL. destruct label1; ss.
          * destruct (equiv_dec loc0 loc); ss. inv e0.
            destruct (equiv_dec (ValA.val (sem_expr rmap0 eloc0)) loc); ss. inv e0.
            exploit IH.(RPROP1); eauto with tso. i. des.
            exploit IH.(RPROP2); eauto. s. i. des. subst.
            exploit sim_rmap_weak_expr; eauto. i. inv x2. rewrite VAL1 in *.
            desH x5.
            { rewrite x5. apply bot_spec. }
            exploit Memory.latest_ts_read_le; try eapply Memory.get_msg_read; eauto. i.
            rewrite x2. apply Memory.latest_ts_mon. apply join_l.
          * destruct (equiv_dec loc0 loc); ss. inv e0.
            destruct (equiv_dec (ValA.val (sem_expr rmap0 eloc0)) loc); ss. inv e0.
            exploit IH.(WPROP2); eauto with tso. i. des.
            exploit IH.(WPROP3); eauto. s. i. des. subst.
            exploit sim_rmap_weak_expr; eauto. i. inv x3. rewrite VAL1 in *.
            exploit Memory.latest_ts_read_le; try eapply Memory.get_msg_read; eauto. i.
            rewrite x3. apply Memory.latest_ts_mon. apply join_l.
          * destruct (equiv_dec loc0 loc); ss. inv e0.
            destruct (equiv_dec (ValA.val (sem_expr rmap0 eloc0)) loc); ss. inv e0.
            exploit IH.(WPROP2); eauto with tso. i. des.
            exploit IH.(WPROP3); eauto. s. i. des. subst.
            exploit sim_rmap_weak_expr; eauto. i. inv x3. rewrite VAL1 in *.
            exploit Memory.latest_ts_read_le; try eapply Memory.get_msg_read; eauto. i.
            rewrite x3. apply Memory.latest_ts_mon. apply join_l.
        + subst. repeat condtac; ss.
          all: try apply Nat.eqb_eq in X; ss; try lia.
    }
  }
  { (* write *)
    inv LOCAL; ss; inv EVENT; inv RES; inv STEP; ss. inv STATE. ss.
    destruct IH.(EU_WF).
    econs; ss; clear EU_WF2 AEU_WF2.
    - i. exploit IH.(WPROP1); eauto. s. i. rewrite Promises.unset_o. des_ifs.
      { inv e. right. rewrite MSG in GET. inv GET. esplits; ss.
        - instantiate (1 := ALocal.next_eid alc1). des_ifs; cycle 1.
          { apply Nat.eqb_neq in Heq. congr. }
          rewrite fun_add_spec. des_ifs; ss; try congr.
          repeat f_equal. destruct ts; ss.
          unfold Memory.get_msg in MSG. ss. rewrite MSG. des_ifs.
        - rewrite List.nth_error_app2, Nat.sub_diag; ss.
        - inv VLOC. inv VVAL. rewrite VAL0, VAL1. eauto with tso.
      }
      des; [left|right]; splits; ss.
      + i. des_ifs; eauto. apply Nat.eqb_eq in Heq. subst. ii. inv H.
        rewrite fun_add_spec in *. des_ifs; [|congr]. ss. apply c.
        specialize (Memory.latest_ts_spec (ValA.val vloc0) ts mem). i. des.
        destruct ts; ss. unfold Memory.get_msg in MSG. ss. rewrite MSG. des_ifs.
      + esplits; eauto.
        * des_ifs; eauto. apply Nat.eqb_eq in Heq. subst. unfold ALocal.next_eid in *.
          assert (H: List.nth_error (ALocal.labels alc1) (length (ALocal.labels alc1)) <> None) by (ii; congr).
          apply List.nth_error_Some in H. lia.
        * eapply nth_error_app_mon. eauto.
    - i. des. unfold ALocal.next_eid in *. apply nth_error_snoc_inv in GET. des.
      + des_ifs.
        { apply Nat.eqb_eq in Heq. subst. lia. }
        eapply IH.(WPROP2); eauto.
      + des_ifs; cycle 1.
        { apply Nat.eqb_neq in Heq. lia. }
        inv GET0. destruct (equiv_dec (ValA.val vloc) loc); ss. inv e.
        destruct (equiv_dec (ValA.val vval) val); ss. inv e.
        esplits; eauto.
        * inv VLOC. rewrite VAL0. eauto.
        * rewrite fun_add_spec in *. des_ifs; [|congr]. ss.
          inv VLOC. inv VVAL. rewrite <- VAL0, <- VAL1.
          specialize (Memory.latest_ts_spec (ValA.val vloc0) ts mem). i. des.
          destruct ts; ss. unfold Memory.get_msg in MSG. ss.
          rewrite MSG. ss. des_ifs.
    - i. des. unfold ALocal.next_eid in *. apply nth_error_snoc_inv in GET. des.
      + des_ifs.
        { apply Nat.eqb_eq in Heq. subst. lia. }
        eapply IH.(WPROP2'); eauto.
      + des_ifs; cycle 1.
        { apply Nat.eqb_neq in Heq. lia. }
        inv GET0. destruct (equiv_dec (ValA.val vloc) loc); ss. inv e.
        esplits; eauto.
        * inv VLOC. rewrite VAL0. eauto.
        * rewrite fun_add_spec in *. des_ifs; [|congr]. ss.
          inv VLOC. inv VVAL. rewrite <- VAL0.
          instantiate (1 := ValA.val vval0).
          specialize (Memory.latest_ts_spec (ValA.val vloc0) ts mem). i. des.
          destruct ts; ss. unfold Memory.get_msg in MSG. ss.
          rewrite MSG. ss. des_ifs.
    - i. unfold ALocal.next_eid in *. des_ifs.
      + apply Nat.eqb_eq in Heq. subst. rewrite fun_add_spec. des_ifs; [|congr]. inv e.
        destruct ts; ss. esplits; eauto using Label.write_is_writing_val.
        * unfold Memory.get_msg in MSG. ss. rewrite MSG. des_ifs.
          unfold Time.lt, Time.bot. lia.
        * unfold Memory.get_msg in MSG. ss. rewrite MSG. des_ifs.
        * unfold Memory.get_msg in MSG. ss. rewrite MSG. des_ifs.
        * rewrite List.nth_error_app2, Nat.sub_diag; ss.
          inv VLOC. rewrite VAL0. eauto.
        * generalize MSG. intro X. inv VVAL. rewrite <- VAL0.
          unfold Memory.get_msg in X. ss. rewrite X. des_ifs.
      + exploit IH.(WPROP3); eauto. s. i. des. esplits; eauto.
        * rewrite fun_add_spec. des_ifs; eauto. inv e. etrans; eauto.
          inv WRITABLE. apply Nat.lt_le_incl. ss.
        * eapply nth_error_app_mon. eauto.
    - i. unfold ALocal.next_eid in *.
      specialize (Memory.latest_ts_spec (ValA.val vloc0) ts mem). i. des.
      exploit Memory.latest_ts_read_le; [|refl|i; exploit le_antisym; try eapply LE; eauto; i].
      { eapply Memory.get_msg_read; eauto. }
      des_ifs.
      + apply Nat.eqb_eq in Heq. apply Nat.eqb_eq in Heq0. subst. ss.
      + clear Heq0. rewrite fun_add_spec in *. des_ifs; [|congr].
        exploit IH.(WPROP3); eauto. s. i. des.
        exploit IH.(WPROP1); eauto. s. rewrite x1 in *.
        rewrite PROMISE. i. des; ss.
        rewrite MSG in x8. inv x8. clear - WRITABLE x5. unfold le in x5. inv WRITABLE. lia.
      + rewrite fun_add_spec in *. des_ifs; [|congr].
        exploit IH.(WPROP3); eauto. s. i. des.
        exploit IH.(WPROP1); eauto. s. rewrite x1 in *.
        rewrite PROMISE. i. des; ss.
        rewrite MSG in x8. inv x8. clear -WRITABLE x5. unfold le in x5. inv WRITABLE. lia.
      + eapply IH.(WPROP4); eauto.
    - i. des. exploit IH.(RPROP1); eauto.
      apply nth_error_snoc_inv in GET. des; esplits; eauto.
      rewrite <- GET1 in GET0. ss.
    - i. exploit IH.(RPROP2); eauto. s. i. des. esplits; eauto.
      + des_ifs.
        exfalso. apply Nat.eqb_eq in Heq. subst.
        unfold ALocal.next_eid in *.
        assert (H: List.nth_error (ALocal.labels alc1) (length (ALocal.labels alc1)) <> None) by (ii; congr).
        apply List.nth_error_Some in H. lia.
      + rewrite fun_add_spec. des_ifs; eauto. inv e. etrans; eauto.
        inv WRITABLE. apply Nat.lt_le_incl. ss.
      + eapply nth_error_app_mon in x2. eauto.
    - unfold ALocal.next_eid in *. s. i. des_ifs.
      { apply Nat.eqb_eq in Heq. subst. econs; eauto.
        - rewrite List.nth_error_app2, Nat.sub_diag; [|refl]. ss.
        - econs; ss.
      }
      apply AExecUnit.label_is_mon. eapply IH.(COVPROP); eauto.
    - unfold ALocal.next_eid in *. s. i. des_ifs.
      { apply Nat.eqb_eq in Heq. subst. econs; eauto.
        - rewrite List.nth_error_app2, Nat.sub_diag; [|refl]. ss.
        - econs; ss.
      }
      apply AExecUnit.label_is_mon. eapply IH.(VEXTPROP); eauto.
    - inv ASTATE_STEP; ss; eauto. subst.
      inv VLOC. inv VVAL. rewrite VAL0, VAL1 in *. unfold ALocal.next_eid in *.
      i. apply nth_error_snoc_inv in LABEL1. apply nth_error_snoc_inv in LABEL2. des.
      + repeat condtac; ss.
        all: try apply Nat.eqb_eq in X; ss; subst; try lia.
        all: try apply Nat.eqb_eq in X0; ss; subst; try lia.
        eapply IH.(PO); eauto.
      + lia.
      + subst. repeat condtac; ss.
        all: try apply Nat.eqb_eq in X; ss; subst; try lia.
        all: try apply Nat.eqb_neq in X0; ss; try lia.
        splits; ss. rewrite fun_add_spec. des_ifs; [|congr].
        inv REL. destruct label1; ss.
        * destruct (equiv_dec loc0 loc); ss. inv e0.
          destruct (equiv_dec (ValA.val (sem_expr rmap eloc)) loc); ss. inv e0.
          exploit IH.(RPROP1); eauto with tso. i. des.
          exploit IH.(RPROP2); eauto. s. i. des. subst.
          destruct ts; ss. unfold Memory.get_msg in MSG. ss. rewrite MSG. des_ifs.
          eapply Nat.le_lt_trans; eauto. inv WRITABLE. rewrite VAL0 in *. ss.
        * destruct (equiv_dec loc0 loc); ss. inv e0.
          destruct (equiv_dec (ValA.val (sem_expr rmap eloc)) loc); ss. inv e0.
          exploit IH.(WPROP2); eauto with tso. i. des.
          exploit IH.(WPROP3); eauto. s. i. des. subst.
          destruct ts; ss. unfold Memory.get_msg in MSG. ss. rewrite MSG. des_ifs.
          eapply Nat.le_lt_trans; eauto. inv WRITABLE. rewrite VAL0 in *. ss.
        * destruct (equiv_dec loc0 loc); ss. inv e0.
          destruct (equiv_dec (ValA.val (sem_expr rmap eloc)) loc); ss. inv e0.
          exploit IH.(WPROP2); eauto with tso. i. des.
          exploit IH.(WPROP3); eauto. s. i. des. subst.
          destruct ts; ss. unfold Memory.get_msg in MSG. ss. rewrite MSG. des_ifs.
          eapply Nat.le_lt_trans; eauto. inv WRITABLE. rewrite VAL0 in *. ss.
      + subst. repeat condtac; ss.
        all: try apply Nat.eqb_eq in X; ss; try lia.
  }
  { (* rmw *)
    inv LOCAL; ss.
    generalize IH.(EU_WF). i. inv H.
    specialize (Local.rmw_spec LOCAL STEP). intro RMW_SPEC. guardH RMW_SPEC.
    inv STEP. inv STATE0; inv EVENT; ss.
    inv ASTATE_STEP.
    exploit sim_trace_sim_state_weak; eauto. s. intro Y. inv Y. ss. inv STMTS.
    exploit sim_rmap_weak_expr; eauto. intro Y. inv Y.
    inv VLOC. rewrite VAL0 in *. clear VAL.

    (* inv LOCAL; ss; inv EVENT; inv STEP; ss. inv STATE. ss.
    destruct IH.(EU_WF). *)
    econs; ss; clear EU_WF2 AEU_WF2.
    - i. exploit IH.(WPROP1); eauto. s. i. rewrite Promises.unset_o. des_ifs.
      { inv e. right. rewrite MSG in GET. inv GET. esplits; ss.
        - instantiate (1 := ALocal.next_eid alc1). des_ifs; cycle 1.
          { apply Nat.eqb_neq in Heq. congr. }
          rewrite fun_add_spec. des_ifs; ss; try congr.
          repeat f_equal. destruct ts; ss.
          unfold Memory.get_msg in MSG. ss. rewrite MSG. des_ifs.
        - rewrite List.nth_error_app2, Nat.sub_diag; ss.
        - inv NEW. rewrite VAL. eauto with tso.
      }
      des; [left|right]; splits; ss.
      + i. des_ifs; eauto. apply Nat.eqb_eq in Heq. subst. ii. inv H.
        rewrite fun_add_spec in *. des_ifs; [|congr]. ss. apply c.
        specialize (Memory.latest_ts_spec (ValA.val (sem_expr rmap eloc0)) ts mem). i. des.
        destruct ts; ss. unfold Memory.get_msg in MSG. ss. rewrite MSG. des_ifs.
      + esplits; eauto.
        * des_ifs; eauto. apply Nat.eqb_eq in Heq. subst. unfold ALocal.next_eid in *.
          assert (H: List.nth_error (ALocal.labels alc1) (length (ALocal.labels alc1)) <> None) by (ii; congr).
          apply List.nth_error_Some in H. lia.
        * eapply nth_error_app_mon. eauto.
    - i. des. unfold ALocal.next_eid in *. apply nth_error_snoc_inv in GET. des.
      + des_ifs.
        { apply Nat.eqb_eq in Heq. subst. lia. }
        eapply IH.(WPROP2); eauto.
      + des_ifs; cycle 1.
        { apply Nat.eqb_neq in Heq. lia. }
        inv GET0. destruct (equiv_dec (ValA.val (sem_expr rmap0 eloc0)) loc); ss. inv e.
        destruct (equiv_dec (ValA.val vnewv) val); ss. inv e.
        esplits; eauto.
        rewrite fun_add_spec in *. des_ifs; try congr. ss.
        inv NEW. rewrite <- VAL.
        specialize (Memory.latest_ts_spec (ValA.val (sem_expr rmap eloc0)) ts mem). i. des.
        destruct ts; ss. unfold Memory.get_msg in MSG. ss.
        rewrite MSG. ss. des_ifs.
    - i. des. unfold ALocal.next_eid in *. apply nth_error_snoc_inv in GET. des.
      + des_ifs.
        { apply Nat.eqb_eq in Heq. subst. lia. }
        eapply IH.(WPROP2'); eauto.
      + des_ifs; cycle 1.
        { apply Nat.eqb_neq in Heq. lia. }
        inv GET0. destruct (equiv_dec (ValA.val (sem_expr rmap0 eloc0)) loc); ss. inv e.
        unguardH RMW_SPEC. des.
        rewrite fun_add_spec in *. des_ifs; try congr. ss. rewrite <- COH.
        esplits; eauto.
    - i. unfold ALocal.next_eid in *. des_ifs.
      + apply Nat.eqb_eq in Heq. subst. rewrite fun_add_spec. des_ifs; [|congr]. inv e.
        destruct ts; ss. esplits; eauto using Label.update_is_writing_val.
        * unfold Memory.get_msg in MSG. ss. rewrite MSG. des_ifs.
          unfold Time.lt, Time.bot. lia.
        * unfold Memory.get_msg in MSG. ss. rewrite MSG. des_ifs.
        * unfold Memory.get_msg in MSG. ss. rewrite MSG. des_ifs.
        * rewrite List.nth_error_app2, Nat.sub_diag; ss.
        * generalize MSG. intro X. inv NEW. rewrite <- VAL.
          unfold Memory.get_msg in X. ss. rewrite X. des_ifs.
      + exploit IH.(WPROP3); eauto. s. i. des. esplits; eauto.
        * rewrite fun_add_spec. des_ifs; eauto. inv e. etrans; eauto.
          inv WRITABLE. apply Nat.lt_le_incl. rewrite <- VAL0. ss.
        * eapply nth_error_app_mon. eauto.
    - i. unfold ALocal.next_eid in *.
      specialize (Memory.latest_ts_spec (ValA.val (sem_expr rmap0 eloc0)) ts mem). i. des.
      exploit Memory.latest_ts_read_le; [|refl|i; exploit le_antisym; try eapply LE; eauto; i].
      { eapply Memory.get_msg_read; eauto. }
      des_ifs.
      + apply Nat.eqb_eq in Heq. apply Nat.eqb_eq in Heq0. subst. ss.
      + clear Heq0. rewrite fun_add_spec in *. des_ifs; [|congr].
        exploit IH.(WPROP3); eauto. s. i. des.
        exploit IH.(WPROP1); eauto. s. rewrite x1 in *.
        rewrite PROMISE. i. des; ss.
        rewrite MSG in x8. inv x8. rewrite <- VAL0 in *. clear - WRITABLE x5. unfold le in x5. inv WRITABLE. lia.
      + rewrite fun_add_spec in *. des_ifs; [|congr].
        exploit IH.(WPROP3); eauto. s. i. des.
        exploit IH.(WPROP1); eauto. s. rewrite x1 in *.
        rewrite PROMISE. i. des; ss.
        rewrite MSG in x8. inv x8. rewrite <- VAL0 in *. clear -WRITABLE x5. unfold le in x5. inv WRITABLE. lia.
      + eapply IH.(WPROP4); eauto.
    - i. des. apply nth_error_snoc_inv in GET. des.
      + exploit IH.(RPROP1); eauto. i. des. esplits; eauto.
        des_ifs. apply Nat.eqb_eq in Heq. subst. unfold ALocal.next_eid in *. lia.
      + des_ifs; cycle 1.
        { apply Nat.eqb_neq in Heq. unfold ALocal.next_eid in *. congr. }
        rewrite fun_add_spec in *. condtac; [|congr].
        inv OLD. ss. des_ifs.
        destruct (equiv_dec (ValA.val (sem_expr rmap0 eloc0)) loc); ss. inv e0.
        destruct (equiv_dec (ValA.val voldv) val); ss. inv e0.
        (* subst. rewrite VAL1 in *. *)
        rewrite <- VAL.
        move RMW_SPEC at bottom. desH RMW_SPEC. rewrite <- PRED.
        exploit Memory.read_get_msg; eauto. i. des; esplits; eauto.
    - admit. (* RPROP2: read vs update *)
    - unfold ALocal.next_eid in *. s. i. des_ifs.
      { apply Nat.eqb_eq in Heq. subst. econs; eauto.
        - rewrite List.nth_error_app2, Nat.sub_diag; [|refl]. ss.
        - econs; ss.
      }
      apply AExecUnit.label_is_mon. eapply IH.(COVPROP); eauto.
    - unfold ALocal.next_eid in *. s. i. des_ifs.
      { apply Nat.eqb_eq in Heq. subst. econs; eauto.
        - rewrite List.nth_error_app2, Nat.sub_diag; [|refl]. ss.
        - econs; ss.
      }
      apply AExecUnit.label_is_mon. eapply IH.(VEXTPROP); eauto.
    - inv NEW. rewrite VAL in *. unfold ALocal.next_eid in *.
      i. apply nth_error_snoc_inv in LABEL1. apply nth_error_snoc_inv in LABEL2. des.
      + repeat condtac; ss.
        all: try apply Nat.eqb_eq in X; ss; subst; try lia.
        all: try apply Nat.eqb_eq in X0; ss; subst; try lia.
        eapply IH.(PO); eauto.
      + lia.
      + subst. repeat condtac; ss.
        all: try apply Nat.eqb_eq in X; ss; subst; try lia.
        all: try apply Nat.eqb_neq in X0; ss; try lia.
        rewrite fun_add_spec. des_ifs; [|congr].
        inv REL. ss.
        assert (Time.lt (cov1 iid1) (Memory.latest_ts (ValA.val (sem_expr rmap eloc0)) ts mem)).
        { destruct label1; ss.
          - destruct (equiv_dec loc0 loc); ss. inv e0.
            destruct (equiv_dec (ValA.val (sem_expr rmap0 eloc0)) loc); ss. inv e0.
            exploit IH.(RPROP1); eauto with tso. i. des.
            exploit IH.(RPROP2); eauto. s. i. des. subst.
            destruct ts; ss. unfold Memory.get_msg in MSG. ss. rewrite MSG. des_ifs; try congr.
            eapply Nat.le_lt_trans; eauto. inv WRITABLE. rewrite VAL0 in *. ss.
          - destruct (equiv_dec loc0 loc); ss. inv e0.
            destruct (equiv_dec (ValA.val (sem_expr rmap0 eloc0)) loc); ss. inv e0.
            exploit IH.(WPROP2); eauto with tso. i. des.
            exploit IH.(WPROP3); eauto. s. i. des. subst.
            destruct ts; ss. unfold Memory.get_msg in MSG. ss. rewrite MSG. des_ifs; try congr.
            eapply Nat.le_lt_trans; eauto. inv WRITABLE. rewrite VAL0 in *. ss.
          - destruct (equiv_dec loc0 loc); ss. inv e0.
            destruct (equiv_dec (ValA.val (sem_expr rmap0 eloc0)) loc); ss. inv e0.
            exploit IH.(WPROP2); eauto with tso. i. des.
            exploit IH.(WPROP3); eauto. s. i. des. subst.
            destruct ts; ss. unfold Memory.get_msg in MSG. ss. rewrite MSG. des_ifs; try congr.
            eapply Nat.le_lt_trans; eauto. inv WRITABLE. rewrite VAL0 in *. ss.
        }
        rewrite VAL0 in *.
        split; ss. ii. unfold Time.lt in H. unfold Time.le. lia.
      + subst. repeat condtac; ss.
        all: try apply Nat.eqb_eq in X; ss; try lia.
  }
  { (* barrier *)
    inv LOCAL; ss.
    (* dmb *)
    inv STEP. inv ASTATE_STEP. ss. inv EVENT. econs; ss.
    - i. exploit IH.(WPROP1); eauto. s. i. des; [left|right]; esplits; eauto.
      eapply nth_error_app_mon. eauto.
    - i. des. exploit IH.(WPROP2); eauto.
      apply nth_error_snoc_inv in GET. des; eauto. destruct l; ss.
    - i. des. exploit IH.(WPROP2'); eauto.
      apply nth_error_snoc_inv in GET. des; eauto. destruct l; ss.
    - i. exploit IH.(WPROP3); eauto. s. i. des. esplits; eauto.
      eapply nth_error_app_mon. eauto.
    - eapply IH.(WPROP4).
    - i. des. exploit IH.(RPROP1); eauto.
      apply nth_error_snoc_inv in GET. des.
      + esplits; eauto.
      + rewrite <- GET1 in GET0. ss.
    - i. exploit IH.(RPROP2); eauto. s. i. des. esplits; eauto.
      eapply nth_error_app_mon. eauto.
    - i. apply AExecUnit.label_is_mon. eapply IH.(COVPROP); eauto.
    - i. apply AExecUnit.label_is_mon. eapply IH.(VEXTPROP); eauto.
    - i. apply nth_error_snoc_inv in LABEL1. des; cycle 1.
      { subst. inv REL. inv X. }
      apply nth_error_snoc_inv in LABEL2. des; cycle 1.
      { subst. inv REL. inv Y. }
      eapply IH.(PO); eauto.
  }
  Grab Existential Variables.
  all: auto. (* tid *)
Qed.
