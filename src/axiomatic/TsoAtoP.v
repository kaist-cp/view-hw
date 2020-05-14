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
Require Import PromisingArch.axiomatic.TsoAxiomatic.
Require Import PromisingArch.axiomatic.TsoCommonAxiomatic.

Set Implicit Arguments.


Definition mem_of_ex
           (ex:Execution.t)
           (ob:list eidT):
  Memory.t :=
  filter_map
    (fun eid =>
       match Execution.label eid ex with
       | Some (Label.write loc val) => Some (Msg.mk loc val (fst eid))
       | Some (Label.update loc vold vnew) => Some (Msg.mk loc vnew (fst eid))
       | _ => None
       end)
    ob.

Lemma mem_of_ex_app ex ob1 ob2:
  mem_of_ex ex (ob1 ++ ob2) = mem_of_ex ex ob1 ++ mem_of_ex ex ob2.
Proof. apply filter_map_app. Qed.

Lemma mem_of_ex_in_length
      ex ob eid
      (IN: List.In eid ob)
      (EID: ex.(Execution.label_is) Label.is_write eid):
  length (mem_of_ex ex ob) <> 0.
Proof.
  eapply filter_map_in_length; eauto.
  inv EID. rewrite EID0. destruct l; ss.
Qed.

Inductive sim_mem (ex:Execution.t) (mem: Memory.t): Prop :=
| sim_mem_intro
    ob
    (EIDS: Permutation ob (Execution.eids ex))
    (MEM: mem = mem_of_ex ex ob)
.
Hint Constructors sim_mem.

Definition view_of_eid (ex:Execution.t) (ob: list eidT) (eid:eidT): option Time.t :=
  option_map
    (fun n => length (mem_of_ex ex (List.firstn (S n) ob)))
    (List_find_pos (fun eid' => eid' == eid) ob).

Lemma view_of_eid_inv
      ex ob eid view
      (VIEW: view_of_eid ex ob eid = Some view):
  exists n,
    <<N: List.nth_error ob n = Some eid>> /\
    <<VIEW: view = length (mem_of_ex ex (List.firstn (S n) ob))>>.
Proof.
  unfold view_of_eid in *.
  destruct ((List_find_pos (fun eid' : eidT => equiv_dec eid' eid) ob)) eqn:POS; inv VIEW.
  exploit List_find_pos_inv; eauto. i. des. destruct (equiv_dec a eid); ss. inv e.
  esplits; eauto.
Qed.

Lemma view_of_eid_ob_write_write
      ex ob eid1 eid2 view
      (VIEW1: view_of_eid ex ob eid1 = Some view)
      (VIEW2: view_of_eid ex ob eid2 = Some view)
      (WRITE1: Execution.label_is ex (Label.is_write) eid1)
      (WRITE2: Execution.label_is ex (Label.is_write) eid2):
  eid1 = eid2.
Proof.
  exploit view_of_eid_inv; try exact VIEW1; eauto. i. des.
  exploit view_of_eid_inv; try exact VIEW2; eauto. i. des.
  inv WRITE1. destruct l; try done.
  inv WRITE2. destruct l; try done.
  - destruct (Nat.compare_spec n n0).
    + subst. congr.
    + rewrite (@List_firstn_le (S n) (S n0)) in VIEW0; [|lia].
      rewrite mem_of_ex_app, List.app_length in VIEW0.
      apply plus_minus in VIEW0. rewrite Nat.sub_diag, Nat.sub_succ in VIEW0.
      exploit List_nth_error_skipn; eauto. i.
      exploit @List_nth_error_firstn; [eauto| |i].
      { instantiate (1 := (n0 - n)). lia. }
      exploit List.nth_error_In; eauto. i.
      exfalso. eapply mem_of_ex_in_length; eauto with tso.
    + symmetry in VIEW0.
      rewrite (@List_firstn_le (S n0) (S n)) in VIEW0; [|lia].
      rewrite mem_of_ex_app, List.app_length in VIEW0.
      apply plus_minus in VIEW0. rewrite Nat.sub_diag, Nat.sub_succ in VIEW0.
      exploit List_nth_error_skipn; try exact N; eauto. i.
      exploit @List_nth_error_firstn; [eauto| |i].
      { instantiate (1 := (n - n0)). lia. }
      exploit List.nth_error_In; eauto. i.
      exfalso. eapply mem_of_ex_in_length; eauto with tso.
  - destruct (Nat.compare_spec n n0).
    + subst. congr.
    + rewrite (@List_firstn_le (S n) (S n0)) in VIEW0; [|lia].
      rewrite mem_of_ex_app, List.app_length in VIEW0.
      apply plus_minus in VIEW0. rewrite Nat.sub_diag, Nat.sub_succ in VIEW0.
      exploit List_nth_error_skipn; eauto. i.
      exploit @List_nth_error_firstn; [eauto| |i].
      { instantiate (1 := (n0 - n)). lia. }
      exploit List.nth_error_In; eauto. i.
      exfalso. eapply mem_of_ex_in_length; eauto with tso.
    + symmetry in VIEW0.
      rewrite (@List_firstn_le (S n0) (S n)) in VIEW0; [|lia].
      rewrite mem_of_ex_app, List.app_length in VIEW0.
      apply plus_minus in VIEW0. rewrite Nat.sub_diag, Nat.sub_succ in VIEW0.
      exploit List_nth_error_skipn; try exact N; eauto. i.
      exploit @List_nth_error_firstn; [eauto| |i].
      { instantiate (1 := (n - n0)). lia. }
      exploit List.nth_error_In; eauto. i.
      exfalso. eapply mem_of_ex_in_length; eauto with tso.
  - destruct (Nat.compare_spec n n0).
    + subst. congr.
    + rewrite (@List_firstn_le (S n) (S n0)) in VIEW0; [|lia].
      rewrite mem_of_ex_app, List.app_length in VIEW0.
      apply plus_minus in VIEW0. rewrite Nat.sub_diag, Nat.sub_succ in VIEW0.
      exploit List_nth_error_skipn; eauto. i.
      exploit @List_nth_error_firstn; [eauto| |i].
      { instantiate (1 := (n0 - n)). lia. }
      exploit List.nth_error_In; eauto. i.
      exfalso. eapply mem_of_ex_in_length; eauto with tso.
    + symmetry in VIEW0.
      rewrite (@List_firstn_le (S n0) (S n)) in VIEW0; [|lia].
      rewrite mem_of_ex_app, List.app_length in VIEW0.
      apply plus_minus in VIEW0. rewrite Nat.sub_diag, Nat.sub_succ in VIEW0.
      exploit List_nth_error_skipn; try exact N; eauto. i.
      exploit @List_nth_error_firstn; [eauto| |i].
      { instantiate (1 := (n - n0)). lia. }
      exploit List.nth_error_In; eauto. i.
      exfalso. eapply mem_of_ex_in_length; eauto with tso.
Qed.

Lemma view_of_eid_ob
      ex rel ob eid1 eid2 view1 view2
      (LINEARIZED: linearized rel ob)
      (OB: rel eid1 eid2)
      (VIEW1: view_of_eid ex ob eid1 = Some view1)
      (VIEW2: view_of_eid ex ob eid2 = Some view2):
  le view1 view2.
Proof.
  exploit view_of_eid_inv; try exact VIEW1; eauto. i. des.
  exploit view_of_eid_inv; try exact VIEW2; eauto. i. des.
  subst. exploit LINEARIZED; try exact OB; eauto. i.
  erewrite (@List_firstn_le (S n) (S n0)); [|lia].
  rewrite mem_of_ex_app, List.app_length. unfold le. lia.
Qed.

Lemma view_of_eid_ob_write
      ex rel ob eid1 eid2 view1 view2 loc
      (LINEARIZED: linearized rel ob)
      (OB: rel eid1 eid2)
      (VIEW1: view_of_eid ex ob eid1 = Some view1)
      (VIEW2: view_of_eid ex ob eid2 = Some view2)
      (WRITE2: Execution.label_is ex (Label.is_writing loc) eid2):
  view1 < view2.
Proof.
  exploit view_of_eid_inv; try exact VIEW1; eauto. i. des.
  exploit view_of_eid_inv; try exact VIEW2; eauto. i. des.
  subst. exploit LINEARIZED; try exact OB; eauto. i.
  erewrite (@List_firstn_le (S n) (S n0)); [|lia].
  rewrite mem_of_ex_app, List.app_length. apply Nat.lt_add_pos_r.
  exploit List_nth_error_skipn; eauto. i.
  exploit List_nth_error_firstn; [eauto| |i].
  { instantiate (1 := (S n0 - S n)). lia. }
  exploit List.nth_error_In; eauto. i.
  apply neq_0_lt. ii. eapply mem_of_ex_in_length; eauto.
  inv WRITE2. eauto with tso.
Qed.

Inductive sim_view (ex:Execution.t) (ob: list eidT) (eids:eidT -> Prop) (view:Time.t): Prop :=
| sim_view_bot
    (VIEW: view = bot)
| sim_view_event
    eid v
    (EID: eids eid)
    (VIEW_OF_EID: view_of_eid ex ob eid = Some v)
    (VIEW: le view v)
.
Hint Constructors sim_view.

Lemma sim_view_join ex ob pred v1 v2
      (V1: sim_view ex ob pred v1)
      (V2: sim_view ex ob pred v2):
  sim_view ex ob pred (join v1 v2).
Proof.
  inv V1.
  { rewrite join_comm, bot_join; [|exact Time.order]. ss. }
  inv V2.
  { rewrite bot_join; [|exact Time.order]. econs 2; eauto. }

  generalize (Time.max_spec_le v1 v2). i. des.
  - unfold join, Time.join. rewrite H0. econs 2; try exact VIEW_OF_EID0; eauto.
  - unfold join, Time.join. rewrite H0. econs 2; try exact VIEW_OF_EID; eauto.
Qed.

Lemma sim_view_le ex ob pred1 pred2
      (PRED: pred1 <1= pred2):
  sim_view ex ob pred1 <1= sim_view ex ob pred2.
Proof.
  i. inv PR.
  - econs 1. ss.
  - econs 2; eauto.
Qed.

Lemma sim_view_le2 ex ob pred v1 v2
      (SIM: sim_view ex ob pred v2)
      (LE: v1 <= v2):
  sim_view ex ob pred v1.
Proof.
  inv SIM.
  - inv LE. econs 1. refl.
  - econs 2; eauto. etrans; eauto.
Qed.

Inductive sim_val (tid:Id.t) (ex:Execution.t) (ob: list eidT) (avala:ValA.t (A:=unit)) (vala:ValA.t (A:=unit)): Prop :=
| sim_val_intro
    (VAL: avala.(ValA.val) = vala.(ValA.val))
    (* (VIEW: sim_view ex ob (fun eid => (fst eid) = tid /\ avala.(ValA.annot) (snd eid)) vala.(ValA.annot).(View.ts)) *)
.
Hint Constructors sim_val.

Inductive sim_rmap (tid:Id.t) (ex:Execution.t) (ob: list eidT) (armap:RMap.t (A:=unit)) (rmap:RMap.t (A:=unit)): Prop :=
| sim_rmap_intro
    (RMAP: IdMap.Forall2 (fun reg => sim_val tid ex ob) armap rmap)
.
Hint Constructors sim_rmap.

Inductive sim_state (tid:Id.t) (ex:Execution.t) (ob: list eidT) (astate:State.t (A:=unit)) (state:State.t (A:=unit)): Prop :=
| sim_state_intro
    (STMTS: astate.(State.stmts) = state.(State.stmts))
    (RMAP: astate.(State.rmap) = state.(State.rmap))
.
Hint Constructors sim_state.

Lemma sim_rmap_add
      tid ex ob armap rmap reg avala vala
      (SIM: sim_rmap tid ex ob armap rmap)
      (VAL: sim_val tid ex ob avala vala):
  sim_rmap tid ex ob (RMap.add reg avala armap) (RMap.add reg vala rmap).
Proof.
  econs. ii. unfold RMap.add. rewrite ? IdMap.add_spec.
  inv SIM. condtac; eauto.
Qed.

Inductive sim_local (tid:Id.t) (ex:Execution.t) (ob: list eidT) (alocal:ALocal.t) (local:Local.t): Prop := mk_sim_local {
  COH: forall loc,
        sim_view
          ex ob
          (inverse (sim_local_coh ex loc) (eq (tid, List.length (alocal.(ALocal.labels)))))
          (Memory.latest_ts loc (local.(Local.coh) loc).(View.ts) (mem_of_ex ex ob));
  VRN: sim_view
         ex ob
         (inverse (sim_local_vrn ex) (eq (tid, List.length (alocal.(ALocal.labels)))))
         local.(Local.vrn).(View.ts);
  VWN: sim_view
         ex ob
         (inverse (sim_local_vwn ex) (eq (tid, List.length (alocal.(ALocal.labels)))))
         local.(Local.vwn).(View.ts);
  VRO: sim_view
         ex ob
         (inverse (sim_local_vro ex) (eq (tid, List.length (alocal.(ALocal.labels)))))
         local.(Local.vro).(View.ts);
  VWO: sim_view
         ex ob
         (inverse (sim_local_vwo ex) (eq (tid, List.length (alocal.(ALocal.labels)))))
         local.(Local.vwo).(View.ts);
  PROMISES: forall view,
      Promises.lookup view local.(Local.promises) <->
      (exists n,
          <<N: (length alocal.(ALocal.labels)) <= n>> /\
          <<WRITE: ex.(Execution.label_is) Label.is_write (tid, n)>> /\
          <<VIEW: view_of_eid ex ob (tid, n) = Some view>>);
}.
Hint Constructors sim_local.

Inductive sim_eu (tid:Id.t) (ex:Execution.t) (ob: list eidT) (aeu:AExecUnit.t) (eu:ExecUnit.t): Prop :=
| sim_eu_intro
    (STATE: sim_state tid ex ob aeu.(AExecUnit.state) eu.(ExecUnit.state))
    (LOCAL: sim_local tid ex ob aeu.(AExecUnit.local) eu.(ExecUnit.local))
    (MEM: eu.(ExecUnit.mem) = mem_of_ex ex ob)
.
Hint Constructors sim_eu.

Lemma label_read_mem_of_ex
      eid ex ob l
      (OB: Permutation ob (Execution.eids ex))
      (LABEL: Execution.label eid ex = Some l):
  exists view,
    <<VIEW: view_of_eid ex ob eid = Some view>>.
Proof.
  generalize (Execution.eids_spec ex). i. des. rename NODUP into NODUP0.
  specialize (LABEL0 eid). rewrite LABEL in LABEL0.
  inv LABEL0. clear H0. exploit H; [congr|]. clear H. intro IN0.
  symmetry in OB. exploit Permutation_in; eauto. intro IN.
  exploit HahnList.Permutation_nodup; eauto. intro NODUP.
  generalize (List_in_find_pos _ ob IN). i. des.
  unfold view_of_eid. rewrite H. s. eauto.
Qed.

(* TODO: Lable.write -> writing_val *)
Lemma label_write_mem_of_ex_msg
      eid ex ob loc val
      (OB: Permutation ob (Execution.eids ex))
      (LABEL: Execution.label eid ex = Some (Label.write loc val)):
  exists n,
    <<VIEW: view_of_eid ex ob eid = Some (S n)>> /\
    <<MSG: List.nth_error (mem_of_ex ex ob) n = Some (Msg.mk loc val (fst eid))>>.
Proof.
  generalize (Execution.eids_spec ex). i. des. rename NODUP into NODUP0.
  specialize (LABEL0 eid). rewrite LABEL in LABEL0.
  inv LABEL0. clear H0. exploit H; [congr|]. clear H. intro IN0.
  symmetry in OB. exploit Permutation_in; eauto. intro IN.
  exploit HahnList.Permutation_nodup; eauto. intro NODUP.
  generalize (List_in_find_pos _ ob IN). i. des.
  unfold view_of_eid. rewrite H.
  exploit List_find_pos_inv; eauto. i. des.
  destruct (equiv_dec a eid); [|done]. inversion e. subst.
  esplits.
  - unfold option_map. erewrite List_firstn_S; eauto.
    rewrite mem_of_ex_app, List.app_length.
    unfold mem_of_ex at 2. s. rewrite LABEL. s. rewrite Nat.add_1_r. ss.
  - rewrite <- (List.firstn_skipn n ob) at 1.
    rewrite mem_of_ex_app, List.nth_error_app2; [|lia].
    erewrite Nat.sub_diag, List_skipn_cons; eauto. s.
    unfold mem_of_ex. s. rewrite LABEL. ss.
Qed.

(* TODO: Lable.write -> writing_val *)
Lemma label_write_mem_of_ex
      eid ex ob loc val
      (OB: Permutation ob (Execution.eids ex))
      (LABEL: Execution.label eid ex = Some (Label.write loc val)):
  exists n,
    <<VIEW: view_of_eid ex ob eid = Some (S n)>> /\
    <<READ: Memory.read loc (S n) (mem_of_ex ex ob) = Some val>> /\
    <<MSG: Memory.get_msg (S n) (mem_of_ex ex ob) = Some (Msg.mk loc val (fst eid))>>.
Proof.
  inv LABEL. exploit label_write_mem_of_ex_msg; eauto. i. des.
  esplits; eauto.
  unfold Memory.read. s. rewrite MSG. s. condtac; [|congr]. ss.
Qed.

(* TODO: REMOVE *)
Lemma label_update_mem_of_ex_msg
      eid ex ob loc vold vnew
      (OB: Permutation ob (Execution.eids ex))
      (LABEL: Execution.label eid ex = Some (Label.update loc vold vnew)):
  exists n,
    <<VIEW: view_of_eid ex ob eid = Some (S n)>> /\
    <<MSG: List.nth_error (mem_of_ex ex ob) n = Some (Msg.mk loc vnew (fst eid))>>.
Proof.
  generalize (Execution.eids_spec ex). i. des. rename NODUP into NODUP0.
  specialize (LABEL0 eid). rewrite LABEL in LABEL0.
  inv LABEL0. clear H0. exploit H; [congr|]. clear H. intro IN0.
  symmetry in OB. exploit Permutation_in; eauto. intro IN.
  exploit HahnList.Permutation_nodup; eauto. intro NODUP.
  generalize (List_in_find_pos _ ob IN). i. des.
  unfold view_of_eid. rewrite H.
  exploit List_find_pos_inv; eauto. i. des.
  destruct (equiv_dec a eid); [|done]. inversion e. subst.
  esplits.
  - unfold option_map. erewrite List_firstn_S; eauto.
    rewrite mem_of_ex_app, List.app_length.
    unfold mem_of_ex at 2. s. rewrite LABEL. s. rewrite Nat.add_1_r. ss.
  - rewrite <- (List.firstn_skipn n ob) at 1.
    rewrite mem_of_ex_app, List.nth_error_app2; [|lia].
    erewrite Nat.sub_diag, List_skipn_cons; eauto. s.
    unfold mem_of_ex. s. rewrite LABEL. ss.
Qed.

(* TODO: REMOVE *)
Lemma label_update_mem_of_ex
      eid ex ob loc vold vnew
      (OB: Permutation ob (Execution.eids ex))
      (LABEL: Execution.label eid ex = Some (Label.update loc vold vnew)):
  exists n,
    <<VIEW: view_of_eid ex ob eid = Some (S n)>> /\
    <<READ: Memory.read loc (S n) (mem_of_ex ex ob) = Some vnew>> /\
    <<MSG: Memory.get_msg (S n) (mem_of_ex ex ob) = Some (Msg.mk loc vnew (fst eid))>>.
Proof.
  inv LABEL. exploit label_update_mem_of_ex_msg; eauto. i. des.
  esplits; eauto.
  unfold Memory.read. s. rewrite MSG. s. condtac; [|congr]. ss.
Qed.

Lemma in_mem_of_ex
      ex ob view msg
      (NODUP: List.NoDup ob)
      (IN: List.nth_error (mem_of_ex ex ob) view = Some msg):
  (exists n,
     <<LABEL: Execution.label (msg.(Msg.tid), n) ex = Some (Label.write msg.(Msg.loc) msg.(Msg.val))>> /\
     <<VIEW: view_of_eid ex ob (msg.(Msg.tid), n) = Some (S view)>>) \/
  (exists n vold,
     <<LABEL: Execution.label (msg.(Msg.tid), n) ex = Some (Label.update msg.(Msg.loc) vold msg.(Msg.val))>> /\
     <<VIEW: view_of_eid ex ob (msg.(Msg.tid), n) = Some (S view)>>).
Proof.
  unfold mem_of_ex in IN. exploit nth_error_filter_map_inv; eauto. i. des.
  destruct (Execution.label a ex) eqn:LABEL; ss. destruct t; inv FA; destruct a; ss; [ left | right ].
  - esplits; eauto. unfold view_of_eid.
    erewrite List_nth_error_find_pos; eauto. s. f_equal. ss.
  - esplits; eauto. unfold view_of_eid.
    erewrite List_nth_error_find_pos; eauto. s. f_equal. ss.
Qed.

Lemma sim_eu_step
      p ex ob tid aeu1 eu1 aeu2
      (EX: Valid.ex p ex)
      (OB: Permutation ob (Execution.eids ex))
      (LINEARIZED: linearized (Execution.ob ex) ob)
      (SIM: sim_eu tid ex ob aeu1 eu1)
      (WF: ExecUnit.wf tid eu1)
      (STEP: AExecUnit.step aeu1 aeu2)
      (LABEL: forall n label (LABEL: List.nth_error aeu2.(AExecUnit.local).(ALocal.labels) n = Some label),
          Execution.label (tid, n) ex = Some label):
  exists eu2,
    <<STEP: ExecUnit.state_step tid eu1 eu2>> /\
    <<SIM: sim_eu tid ex ob aeu2 eu2>>.
Proof.
  destruct eu1 as [[stmts1 rmap1] local1].
  destruct aeu1 as [[astmts1 armap1] alocal1].
  destruct aeu2 as [[astmts2 armap2] alocal2].
  inv SIM. inv STATE. ss. subst. rename LOCAL into SIM_LOCAL.
  inv STEP. ss. inv STATE; inv LOCAL; inv EVENT; ss.
  - (* skip *)
    eexists (ExecUnit.mk _ _ _). esplits.
    + econs 1. econs; ss.
      { econs; ss. }
      econs 1; ss.
    + econs; ss.
      inv SIM_LOCAL; econs; eauto.
  - (* assign *)
    eexists (ExecUnit.mk _ _ _). esplits.
    + econs 1. econs; ss.
      { econs; ss. }
      econs 1; ss.
    + econs; ss. inv SIM_LOCAL; econs; eauto.
  - (* read *)
    exploit LABEL.
    { rewrite List.nth_error_app2; [|refl]. rewrite Nat.sub_diag. ss. }
    intro LABEL_LEN.
    exploit label_read_mem_of_ex; eauto. i. des.

    assert (SIM_VRN: sim_view ex ob
                              (eq (tid, ALocal.next_eid alocal1))
                              local1.(Local.vrn).(View.ts)).
    { econs 2; eauto; ss.
      generalize SIM_LOCAL.(VRN). intro VRN.
      inv VRN.
      { rewrite VIEW0. apply bot_spec. }
      rewrite VIEW0. eapply view_of_eid_ob; eauto.
      inv EID. exploit sim_local_vrn_spec; eauto with tso.
    }

    assert (exists n,
               <<READ: Memory.read (ValA.val (sem_expr rmap1 eloc)) n (mem_of_ex ex ob) = Some res0>> /\
               <<MSG: n > 0 ->
                      exists eid2,
                        <<RF: ex.(Execution.rf) eid2 (tid, length (ALocal.labels alocal1))>> /\
                        <<VIEW: view_of_eid ex ob eid2 = Some n>> /\
                        <<MSG: Memory.get_msg n (mem_of_ex ex ob) = Some (Msg.mk (ValA.val (sem_expr rmap1 eloc)) res0 (fst eid2))>>>> /\
               <<UNINIT: n = 0 ->
                      <<RF: ~ codom_rel ex.(Execution.rf) (tid, length (ALocal.labels alocal1))>>>>).
    { exploit EX.(Valid.RF1).
      instantiate (1 := (tid, length (ALocal.labels alocal1))).
      instantiate (1 := res0). instantiate (1 := (ValA.val (sem_expr rmap1 eloc))).
      { econs; eauto with tso. }
      i. des.
      { (* read from uninit *)
        subst. exists 0.
        splits; ss. lia.
      }
      inv LABEL0. destruct l; ss; destruct (equiv_dec loc (ValA.val (sem_expr rmap1 eloc))); ss; inv e.
      - exploit label_write_mem_of_ex; eauto.
        destruct (equiv_dec val res0); ss. inv e.
        i. des.
        esplits; eauto. i. inv H.
      - exploit label_update_mem_of_ex; eauto.
        destruct (equiv_dec vnew res0); ss. inv e.
        i. des.
        esplits; eauto. i. inv H.
    }
    des.

    assert (SIM_EXT1: sim_view ex ob
                               (eq (tid, ALocal.next_eid alocal1))
                               (join (local1.(Local.vrn).(View.ts)) n)).
    { apply sim_view_join; ss. econs 2; try exact VIEW; eauto.
      destruct n; unfold le.
      { lia. }
      exploit MSG; [lia|]. i. des.
      destruct eid2. ss. destruct (t == tid).
      { inv e. subst.
        exploit Valid.rfi_is_po; eauto with tso. i.
        inv x0. ss.
        (* TODO: rfi is ob, so... *)
        admit.
      }
      { exploit view_of_eid_ob; cycle 3.
        { instantiate (1 := view). eauto. }
        all: try eauto.
        left. left. left. left. econs; eauto. econs; eauto.
      }
    }

    assert (READ_STEP: exists res1 local2, Local.read (sem_expr rmap1 eloc) res1 n local1 (mem_of_ex ex ob) local2).
    { esplits. econs; eauto.
      - (* internal *)
        generalize (SIM_LOCAL.(COH) (ValA.val (sem_expr rmap1 eloc))). intro X. inv X.
        { eapply Memory.latest_mon1. eapply Memory.latest_ts_latest; eauto. apply bot_spec. }
        eapply Memory.latest_mon1. eapply Memory.latest_ts_latest; eauto.
        rewrite VIEW0. inv EID. inv REL. inv H. inv H0.
        inv H2.
        inv H1. des. inv H.
        { exploit Valid.coherence_wr; try exact H0; eauto.
          all: try by econs; eauto; eauto with tso.
          i. des.
          destruct n.
          { (* read from uninit *)
            specialize (UNINIT eq_refl). des.
            contradict UNINIT. econs; eauto.
          }
          exploit MSG; [lia|]. i. des.
          exploit EX.(Valid.RF_WF); [exact RF|exact RF0|]. i. subst.
          inv CO.
          - rewrite VIEW_OF_EID in VIEW1. inv VIEW1. refl.
          - eapply view_of_eid_ob; eauto. left. left. right. eauto.
        }
        { inv H1.
          exploit EX.(Valid.RF2); eauto. i. des.
          inv WRITE. inv READ0. rewrite EID in EID0. inv EID0.
          inv LABEL1.
          destruct l0; ss; destruct (equiv_dec loc0 loc); ss; inv e.
          { (* W: write *)
            destruct (equiv_dec val0 val); ss. inv e.
            inv LABEL0.
            destruct (equiv_dec loc (ValA.val (sem_expr rmap1 eloc))); ss. inv e.
            inv LABEL2.
            destruct l1; ss; destruct (equiv_dec loc (ValA.val (sem_expr rmap1 eloc))); ss; inv e.
            { (* W: write -> R: read  *)
              destruct (equiv_dec val0 val); ss. inv e.
              exploit Valid.coherence_rr; try exact H0; eauto with tso.
              i. des.
              destruct n.
              { (* read from uninit *)
                specialize (UNINIT eq_refl). des.
                contradict UNINIT. econs; eauto.
              }
              exploit MSG; [lia|]. i. des.
              exploit EX.(Valid.RF_WF); [exact RF|exact RF0|]. i. subst.
              inv CO.
              - rewrite VIEW_OF_EID in VIEW1. inv VIEW1. refl.
              - eapply view_of_eid_ob; eauto. left. left. right. eauto.
            }
            { (* W: write -> R: update  *)
              destruct (equiv_dec vold val); ss. inv e.
              exploit Valid.coherence_rr; try exact H0; cycle 3.
              instantiate (1 := x).
              instantiate (1 := (ValA.val (sem_expr rmap1 eloc))).
              all: eauto with tso.
              i. des.
              destruct n.
              { (* read from uninit *)
                specialize (UNINIT eq_refl). des.
                contradict UNINIT. econs; eauto.
              }
              exploit MSG; [lia|]. i. des.
              exploit EX.(Valid.RF_WF); [exact RF|exact RF0|]. i. subst.
              inv CO.
              - rewrite VIEW_OF_EID in VIEW1. inv VIEW1. refl.
              - eapply view_of_eid_ob; eauto. left. left. right. eauto.
            }
          }
          { (* W: update *)
            destruct (equiv_dec vnew val); ss. inv e.
            inv LABEL0.
            destruct (equiv_dec loc (ValA.val (sem_expr rmap1 eloc))); ss. inv e.
            inv LABEL2.
            destruct l1; ss; destruct (equiv_dec loc (ValA.val (sem_expr rmap1 eloc))); ss; inv e.
            { (* W: update -> R: read  *)
              destruct (equiv_dec val0 val); ss. inv e.
              exploit Valid.coherence_rr; try exact H0; eauto with tso.
              i. des.
              destruct n.
              { (* read from uninit *)
                specialize (UNINIT eq_refl). des.
                contradict UNINIT. econs; eauto.
              }
              exploit MSG; [lia|]. i. des.
              exploit EX.(Valid.RF_WF); [exact RF|exact RF0|]. i. subst.
              inv CO.
              - rewrite VIEW_OF_EID in VIEW1. inv VIEW1. refl.
              - eapply view_of_eid_ob; eauto. left. left. right. eauto.
            }
            { (* W: update -> R: update  *)
              destruct (equiv_dec vold0 val); ss. inv e.
              exploit Valid.coherence_rr; try exact H0; cycle 3.
              instantiate (1 := x).
              instantiate (1 := (ValA.val (sem_expr rmap1 eloc))).
              all: eauto with tso.
              i. des.
              destruct n.
              { (* read from uninit *)
                specialize (UNINIT eq_refl). des.
                contradict UNINIT. econs; eauto.
              }
              exploit MSG; [lia|]. i. des.
              exploit EX.(Valid.RF_WF); [exact RF|exact RF0|]. i. subst.
              inv CO.
              - rewrite VIEW_OF_EID in VIEW1. inv VIEW1. refl.
              - eapply view_of_eid_ob; eauto. left. left. right. eauto.
            }
          }
        }
      - (* external *)
        ii.
        exploit in_mem_of_ex; swap 1 2; eauto.
        { eapply Permutation_NoDup; [by symmetry; eauto|].
          eapply Execution.eids_spec; eauto.
        }
        i. destruct msg. ss. subst.
        destruct n.
        { (* read from uninit *)
          specialize (UNINIT eq_refl).
          assert (view < S ts).
          { des.
            - eapply view_of_eid_ob_write; eauto.
              + left. left. left. right. right. econs.
                * econs; eauto. econs; eauto with tso.
                * econs; eauto with tso. econs; eauto with tso.
              + econs; eauto with tso.
            - eapply view_of_eid_ob_write; eauto.
              + left. left. left. right. right. econs.
                * econs; eauto. econs; eauto with tso.
                * econs; eauto with tso. econs; eauto with tso.
              + econs; eauto with tso.
          }
          assert (JOIN_ZERO: join (View.ts (Local.vrn local1)) 0 = View.ts (Local.vrn local1)).
          { destruct (View.ts (Local.vrn local1)); ss. }
          inv SIM_EXT1; rewrite JOIN_ZERO in VIEW0.
          { rewrite VIEW0 in TS2. inv TS2. }
          unfold ALocal.next_eid in VIEW_OF_EID. rewrite VIEW_OF_EID in VIEW. inv VIEW.
          unfold le in VIEW0. lia.
        }
        exploit MSG; [lia|]. i. des.
        { (* write_mem_of_ex *)
          exploit EX.(Valid.RF1).
          instantiate (1 := (tid, length (ALocal.labels alocal1))).
          instantiate (1 := res0). instantiate (1 := ValA.val (sem_expr rmap1 eloc)).
          { econs; eauto with tso. }
          i. des.
          { contradict NORF. econs. eauto. }
          exploit EX.(Valid.RF_WF); [exact RF|exact RF0|]. i. subst.
          exploit EX.(Valid.CO1).
          instantiate (1 := eid0).
          instantiate (1 := (tid0, n0)).
          { inv LABEL1. inv LABEL2.
            destruct l; ss; destruct (equiv_dec loc (ValA.val (sem_expr rmap1 eloc))); ss; inv e.
            - destruct (equiv_dec val0 res0); ss; inv e. esplits; eauto with tso.
            - destruct (equiv_dec vnew res0); ss; inv e. esplits; eauto with tso.
          }
          i. des.
          { subst. rewrite VIEW0 in VIEW1. inv VIEW1. lia. }
          { cut (S ts < S n); [lia|].
            eapply view_of_eid_ob_write; eauto.
            { left. left. right. ss. }
            inv LABEL1. inv LABEL2.
            destruct l; ss; destruct (equiv_dec loc (ValA.val (sem_expr rmap1 eloc))); ss; inv e.
            - destruct (equiv_dec val0 res0); ss; inv e. esplits; eauto with tso.
            - destruct (equiv_dec vnew res0); ss; inv e. esplits; eauto with tso.
          }
          assert (view < S ts).
          { eapply view_of_eid_ob_write; eauto.
            - left. left. left. right. left. econs; eauto.
            - econs; eauto with tso.
          }
          assert (JOIN_SN:join (View.ts (Local.vrn local1)) (S n) = View.ts (Local.vrn local1)).
          { destruct (View.ts (Local.vrn local1)).
            - lia.
            - assert (S n < S t).
              { unfold lt. unfold lt in TS1.
                etrans; eauto.
              }
              unfold join. unfold Time.join. lia.
          }
          inv SIM_EXT1; rewrite JOIN_SN in VIEW2.
          { rewrite VIEW2 in TS2. inv TS2. }
          unfold ALocal.next_eid in VIEW_OF_EID. rewrite VIEW_OF_EID in VIEW. inv VIEW.
          unfold le in VIEW2. lia.
        }
        { (* update_mem_of_ex *)
          exploit EX.(Valid.RF1).
          instantiate (1 := (tid, length (ALocal.labels alocal1))).
          instantiate (1 := res0). instantiate (1 := ValA.val (sem_expr rmap1 eloc)).
          { econs; eauto with tso. }
          i. des.
          { contradict NORF. econs. eauto. }
          exploit EX.(Valid.RF_WF); [exact RF|exact RF0|]. i. subst.
          exploit EX.(Valid.CO1).
          instantiate (1 := eid0).
          instantiate (1 := (tid0, n0)).
          { inv LABEL1. inv LABEL2.
            destruct l; ss; destruct (equiv_dec loc (ValA.val (sem_expr rmap1 eloc))); ss; inv e.
            - destruct (equiv_dec val0 res0); ss; inv e. esplits; eauto with tso.
            - destruct (equiv_dec vnew res0); ss; inv e. esplits; eauto with tso.
          }
          i. des.
          { subst. rewrite VIEW0 in VIEW1. inv VIEW1. lia. }
          { cut (S ts < S n); [lia|].
            eapply view_of_eid_ob_write; eauto.
            { left. left. right. ss. }
            inv LABEL1. inv LABEL2.
            destruct l; ss; destruct (equiv_dec loc (ValA.val (sem_expr rmap1 eloc))); ss; inv e.
            - destruct (equiv_dec val0 res0); ss; inv e. esplits; eauto with tso.
            - destruct (equiv_dec vnew res0); ss; inv e. esplits; eauto with tso.
          }
          assert (view < S ts).
          { eapply view_of_eid_ob_write; eauto.
            - left. left. left. right. left. econs; eauto.
            - econs; eauto with tso.
          }
          assert (JOIN_SN:join (View.ts (Local.vrn local1)) (S n) = View.ts (Local.vrn local1)).
          { destruct (View.ts (Local.vrn local1)).
            - lia.
            - assert (S n < S t).
              { unfold lt. unfold lt in TS1.
                etrans; eauto.
              }
              unfold join. unfold Time.join. lia.
          }
          inv SIM_EXT1; rewrite JOIN_SN in VIEW2.
          { rewrite VIEW2 in TS2. inv TS2. }
          unfold ALocal.next_eid in VIEW_OF_EID. rewrite VIEW_OF_EID in VIEW. inv VIEW.
          unfold le in VIEW2. lia.
        }
    }

    des. eexists (ExecUnit.mk _ _ _). esplits.
    + econs. econs; ss.
      { econs; ss. }
      econs 2; eauto.
    + generalize READ_STEP. intro X. inv X.
      rewrite READ in MSG0. inv MSG0.
      econs; ss. econs; ss.
      * (* sim_local coh *)
        i. rewrite List.app_length, Nat.add_1_r.
        rewrite sim_local_coh_step. rewrite inverse_step.
        rewrite inverse_union, fun_add_spec. condtac; cycle 1.
        { eapply sim_view_le; [|exact (SIM_LOCAL.(COH) loc)]. eauto. }
        inversion e. subst. inv WF.
        generalize (Local.read_spec LOCAL READ_STEP). i. des. ss.
        revert COH1. rewrite fun_add_spec. condtac; ss. i.
        rewrite <- COH1. destruct n.
        { econs 1. ss. }
        exploit MSG; [lia|]. i. des.
        exploit EX.(Valid.RF1).
        instantiate (1 := (tid, length (ALocal.labels alocal1))).
        instantiate (1 := val). instantiate (1 := ValA.val (sem_expr rmap1 eloc)).
        eauto with tso.
        i. des.
        { contradict NORF. econs. eauto. }
        exploit EX.(Valid.RF_WF); [exact RF|exact RF0|]. i. subst. inv LABEL0.
        destruct eid0. ss. destruct (t == tid).
        { inversion e1. subst.
          econs 2; try exact VIEW0; ss.
          left. econs; eauto. econs. splits.
          - econs; eauto. econs; eauto with tso.
          - econs. splits; eauto.
            exploit Valid.rfi_is_po; eauto. econs; eauto.
        }
        { econs 2; try exact VIEW0; ss.
          right. econs; eauto. econs. splits.
          - econs; eauto. econs; eauto with tso.
          - econs 2. econs; eauto. econs; eauto.
        }
      * (* sim_local vrn *)
        rewrite List.app_length, Nat.add_1_r.
        rewrite sim_local_vrn_step. rewrite inverse_step.
        rewrite ? inverse_union. apply sim_view_join.
        { eapply sim_view_le; [|exact SIM_LOCAL.(VRN)]. eauto. }
        eapply sim_view_le; [|exact SIM_EXT1].
        i. subst. right. left. econs; eauto. econs; eauto with tso.
      * (* sim_local vwn *)
        rewrite List.app_length, Nat.add_1_r.
        rewrite sim_local_vwn_step. rewrite inverse_step.
        rewrite ? inverse_union. apply sim_view_join.
        { eapply sim_view_le; [|exact SIM_LOCAL.(VWN)]. eauto. }
        eapply sim_view_le; [|exact SIM_EXT1].
        i. subst. right. left. econs; eauto. econs; eauto with tso.
      * (* sim_local vro *)
        rewrite List.app_length, Nat.add_1_r.
        rewrite sim_local_vro_step. rewrite inverse_step.
        rewrite ? inverse_union. apply sim_view_join; eauto.
        { eapply sim_view_le; [|exact SIM_LOCAL.(VRO)]. eauto. }
        eapply sim_view_le; [|exact SIM_EXT1].
        i. subst. right. econs; eauto. econs; eauto with tso.
      * (* sim_local vwo *)
        rewrite List.app_length, Nat.add_1_r.
        rewrite sim_local_vwo_step. rewrite inverse_step.
        rewrite ? inverse_union. eapply sim_view_le; [|exact SIM_LOCAL.(VWO)]. eauto.
      * (* sim_local promises *)
        i. rewrite SIM_LOCAL.(PROMISES), List.app_length. s. econs; i; des.
        { inv N.
          - inv WRITE. destruct l; ss; congr.
          - esplits; cycle 1; eauto. lia.
        }
        { esplits; cycle 1; eauto. lia. }
  - (* write *)
    exploit LABEL.
    { rewrite List.nth_error_app2; [|refl]. rewrite Nat.sub_diag. ss. }
    intro LABEL_LEN.
    exploit label_write_mem_of_ex; eauto. i. des.
    eexists (ExecUnit.mk _ _ _). esplits.
    + econs. econs; ss.
      { econs; ss. }
      econs 3; ss.
      econs; try refl.
      all: cycle 1.
      { eauto. }
      { rewrite SIM_LOCAL.(PROMISES). esplits; eauto with tso. }
      econs; try refl.
      * (* internal *)
        eapply Memory.latest_ts_read_lt; eauto.
        generalize (SIM_LOCAL.(COH) (ValA.val (sem_expr rmap1 eloc))).
        intro X. inv X.
        { rewrite VIEW0. clear. unfold bot. unfold Time.bot. lia. }
        eapply Time.le_lt_trans; eauto. inv EID. inv REL. inv H. inv H0.
        inv H2. destruct l; ss; destruct (equiv_dec loc (ValA.val (sem_expr rmap1 eloc))); ss; inv e.
        { (* write *)
          inv H1. des. inv H.
          { exploit Valid.coherence_ww; try exact H0; eauto with tso.
            i. eapply view_of_eid_ob_write; eauto.
            - left. left. right. ss.
            - econs; eauto. apply Label.write_is_writing.
          }
          { inv H1.
            exploit EX.(Valid.RF2); eauto. i. des.
            inv WRITE. inv READ0. rewrite EID in EID0. inv EID0.
            inv LABEL1.
            destruct (equiv_dec (ValA.val (sem_expr rmap1 eloc)) loc); ss. inv e.
            destruct (equiv_dec val val0); ss. inv e.
            exploit Valid.coherence_rw; try exact H0; eauto with tso.
            i. eapply view_of_eid_ob_write; eauto with tso.
            left. left. right. ss.
          }
        }
        { (* update *)
          inv H1. des. inv H.
          { exploit Valid.coherence_ww; try exact H0; eauto with tso.
            all: try by econs; eauto; eauto with tso.
            i. eapply view_of_eid_ob_write; eauto.
            - left. left. right. ss.
            - econs; eauto. apply Label.write_is_writing.
          }
          { inv H1.
            exploit EX.(Valid.RF2); eauto. i. des.
            inv WRITE. inv READ0. rewrite EID in EID0. inv EID0.
            inv LABEL1.
            destruct (equiv_dec (ValA.val (sem_expr rmap1 eloc)) loc); ss. inv e.
            destruct (equiv_dec vnew val); ss. inv e.
            exploit Valid.coherence_rw; try exact H0; eauto with tso.
            i. eapply view_of_eid_ob_write; eauto with tso.
            left. left. right. ss.
          }
        }
      * (* external *)
        unfold lt. apply le_n_S. s. repeat apply join_spec.
        { generalize SIM_LOCAL.(VWN). intro X. inv X.
          { rewrite VIEW0. apply bot_spec. }
          rewrite VIEW0. inv EID.
          apply lt_n_Sm_le. eapply view_of_eid_ob_write; eauto.
          - eapply sim_local_vwn_spec; eauto with tso.
          - econs; eauto. apply Label.write_is_writing.
        }
    + econs; ss. econs; ss.
      * i. rewrite List.app_length, Nat.add_1_r.
        rewrite sim_local_coh_step. rewrite inverse_step.
        rewrite inverse_union, fun_add_spec. condtac; ss.
        { unfold Memory.get_msg in MSG. ss. rewrite MSG.
          inversion e. subst. condtac; ss.
          econs 2; eauto; [|refl]. right. econs; eauto.
          econs. splits; eauto. econs; eauto. econs; eauto with tso.
        }
        { eapply sim_view_le; [|exact (SIM_LOCAL.(COH) loc)]. eauto. }
      * rewrite List.app_length, Nat.add_1_r.
        rewrite sim_local_vrn_step. rewrite inverse_step.
        rewrite ? inverse_union. eapply sim_view_le; [|exact SIM_LOCAL.(VRN)]. eauto.
      * rewrite List.app_length, Nat.add_1_r.
        rewrite sim_local_vwn_step. rewrite inverse_step.
        rewrite ? inverse_union. apply sim_view_join.
        { eapply sim_view_le; [|exact SIM_LOCAL.(VWN)]. eauto. }
        { eapply sim_view_le; [by right; eauto|]. econs 2; eauto.
          - econs; eauto. econs; eauto with tso.
          - refl.
        }
      * rewrite List.app_length, Nat.add_1_r.
        rewrite sim_local_vro_step. rewrite inverse_step.
        rewrite ? inverse_union. eapply sim_view_le; [|exact SIM_LOCAL.(VRO)]. eauto.
      * rewrite List.app_length, Nat.add_1_r.
        rewrite sim_local_vwo_step. rewrite inverse_step.
        rewrite ? inverse_union. apply sim_view_join.
        { eapply sim_view_le; [|exact SIM_LOCAL.(VWO)]. eauto. }
        { eapply sim_view_le; [by right; eauto|]. econs 2; eauto.
          - econs; eauto. econs; eauto with tso.
          - refl.
        }
      * i. rewrite Promises.unset_o. condtac.
        { econs; ss. i. des. inversion e. subst.
          rewrite List.app_length in *. ss.
          assert ((tid, length (ALocal.labels alocal1)) = (tid, n0)).
          { eapply view_of_eid_ob_write_write; eauto with tso. }
          inv H. lia.
        }
        rewrite SIM_LOCAL.(PROMISES), List.app_length. s. econs; i; des.
        { inv N.
          - inv WRITE. destruct l; ss; congr.
          - esplits; cycle 1; eauto. lia.
        }
        { esplits; cycle 1; eauto. lia. }
  - (* rmw *)
    exploit LABEL.
    { rewrite List.nth_error_app2; [|refl]. rewrite Nat.sub_diag. ss. }
    intro LABEL_LEN.
    exploit label_update_mem_of_ex; eauto. i. des.

    assert (exists old_ts,
               <<READ: Memory.read (ValA.val (sem_expr armap2 eloc)) old_ts (mem_of_ex ex ob) = Some (ValA.val voldv)>> /\
               <<MSG: old_ts > 0 ->
                      exists eid2,
                        <<RF: ex.(Execution.rf) eid2 (tid, length (ALocal.labels alocal1))>> /\
                        <<VIEW: view_of_eid ex ob eid2 = Some old_ts>> /\
                        <<MSG: Memory.get_msg old_ts (mem_of_ex ex ob) = Some (Msg.mk (ValA.val (sem_expr armap2 eloc)) (ValA.val voldv) (fst eid2))>>>> /\
               <<UNINIT: old_ts = 0 ->
                      <<RF: ~ codom_rel ex.(Execution.rf) (tid, length (ALocal.labels alocal1))>>>>).
    { exploit EX.(Valid.RF1).
      instantiate (1 := (tid, length (ALocal.labels alocal1))).
      instantiate (1 := (ValA.val voldv)). instantiate (1 := (ValA.val (sem_expr armap2 eloc))).
      { econs; eauto with tso. }
      i. des.
      { (* read from uninit *)
        subst. exists 0.
        splits; ss.
        - rewrite VAL. ss.
        - lia.
      }
      inv LABEL0. destruct l; ss; destruct (equiv_dec loc (ValA.val (sem_expr armap2 eloc))); ss; inv e.
      - exploit label_write_mem_of_ex; eauto.
        destruct (equiv_dec val (ValA.val voldv)); ss. inv e.
        i. des.
        esplits; eauto. i. inv H.
      - exploit label_update_mem_of_ex; eauto.
        destruct (equiv_dec vnew (ValA.val voldv)); ss. inv e.
        i. des.
        esplits; eauto. i. inv H.
    }
    des.

    assert (SIM_EXT1: sim_view ex ob
                               (eq (tid, ALocal.next_eid alocal1))
                               (S n)).
    { econs 2; try exact VIEW; eauto.
      unfold le. lia.
    }

    assert (SIM_EXT2: sim_view ex ob
                               (eq (tid, ALocal.next_eid alocal1))
                               old_ts).
    { econs 2; try exact VIEW; eauto.
      destruct old_ts; unfold le.
      { lia. }
      exploit MSG0; [lia|]. i. des.
      destruct eid2. ss. destruct (t == tid).
      { inv e. subst.
        exploit Valid.rfi_is_po; eauto with tso. i.
        inv x0. ss.
        (* TODO: rfi is ob, so... *)
        admit.
      }
      { exploit view_of_eid_ob; cycle 3.
        { instantiate (1 := (S n)). eauto. }
        all: try eauto.
        left. left. left. left. econs; eauto. econs; eauto.
      }
    }

    eexists (ExecUnit.mk _ _ _). esplits.
    + econs. econs; ss.
      { econs; ss. instantiate (1 := vnewv). instantiate (1 := voldv). ss. }
      econs 4; ss.
      econs; try refl.
      all: cycle 4.
      { eauto. }
      { rewrite SIM_LOCAL.(PROMISES). esplits; eauto with tso. }
      { instantiate (1 := old_ts).
        admit.
        (* Need a lemma
        "update vold to vnew ->
         uninit vold \/ write vold label \/ update vold label" *)
      }
      { (* latest old_ts *)
        ii.
        exploit in_mem_of_ex; swap 1 2; eauto.
        { eapply Permutation_NoDup; [by symmetry; eauto|].
          eapply Execution.eids_spec; eauto.
        }
        i. destruct msg. ss. subst.
        destruct old_ts.
        { (* read from uninit *)
          specialize (UNINIT eq_refl).
          assert (S n < S ts).
          { des.
            - eapply view_of_eid_ob_write; eauto.
              + left. left. left. right. right. econs.
                * econs; eauto. econs; eauto with tso.
                * econs; eauto with tso. econs; eauto with tso.
              + econs; eauto with tso.
            - eapply view_of_eid_ob_write; eauto.
              + left. left. left. right. right. econs.
                * econs; eauto. econs; eauto with tso.
                * econs; eauto with tso. econs; eauto with tso.
              + econs; eauto with tso.
          }
          inv SIM_EXT1.
          { inv VIEW0. }
          unfold ALocal.next_eid in VIEW_OF_EID. rewrite VIEW_OF_EID in VIEW. inv VIEW.
          unfold le in VIEW0. lia.
        }
        exploit MSG0; [lia|]. i. des.
        { (* write_mem_of_ex *)
          exploit EX.(Valid.RF1).
          instantiate (1 := (tid, length (ALocal.labels alocal1))).
          instantiate (1 := (ValA.val voldv)). instantiate (1 := ValA.val (sem_expr armap2 eloc)).
          { econs; eauto with tso. }
          i. des.
          { contradict NORF. econs. eauto. }
          exploit EX.(Valid.RF_WF); [exact RF|exact RF0|]. i. subst.
          exploit EX.(Valid.CO1).
          instantiate (1 := eid0).
          instantiate (1 := (tid0, n0)).
          { inv LABEL1. inv LABEL2.
            destruct l; ss; destruct (equiv_dec loc (ValA.val (sem_expr armap2 eloc))); ss; inv e.
            - destruct (equiv_dec val0 (ValA.val voldv)); ss; inv e. esplits; eauto with tso.
            - destruct (equiv_dec vnew (ValA.val voldv)); ss; inv e. esplits; eauto with tso.
          }
          i. des.
          { subst. rewrite VIEW0 in VIEW1. inv VIEW1. lia. }
          { cut (S ts < S old_ts); [lia|].
            eapply view_of_eid_ob_write; eauto.
            { left. left. right. ss. }
            inv LABEL1. inv LABEL2.
            destruct l; ss; destruct (equiv_dec loc (ValA.val (sem_expr armap2 eloc))); ss; inv e.
            - destruct (equiv_dec val0 (ValA.val voldv)); ss; inv e. esplits; eauto with tso.
            - destruct (equiv_dec vnew (ValA.val voldv)); ss; inv e. esplits; eauto with tso.
          }
          assert (S n < S ts).
          { eapply view_of_eid_ob_write; eauto.
            - left. left. left. right. left. econs; eauto.
            - econs; eauto with tso.
          }
          inv SIM_EXT1.
          { inv VIEW2. }
          unfold ALocal.next_eid in VIEW_OF_EID. rewrite VIEW_OF_EID in VIEW. inv VIEW.
          unfold le in VIEW2. lia.
        }
        { (* update_mem_of_ex *)
          exploit EX.(Valid.RF1).
          instantiate (1 := (tid, length (ALocal.labels alocal1))).
          instantiate (1 := (ValA.val voldv)). instantiate (1 := ValA.val (sem_expr armap2 eloc)).
          { econs; eauto with tso. }
          i. des.
          { contradict NORF. econs. eauto. }
          exploit EX.(Valid.RF_WF); [exact RF|exact RF0|]. i. subst.
          exploit EX.(Valid.CO1).
          instantiate (1 := eid0).
          instantiate (1 := (tid0, n0)).
          { inv LABEL1. inv LABEL2.
            destruct l; ss; destruct (equiv_dec loc (ValA.val (sem_expr armap2 eloc))); ss; inv e.
            - destruct (equiv_dec val0 (ValA.val voldv)); ss; inv e. esplits; eauto with tso.
            - destruct (equiv_dec vnew (ValA.val voldv)); ss; inv e. esplits; eauto with tso.
          }
          i. des.
          { subst. rewrite VIEW0 in VIEW1. inv VIEW1. lia. }
          { cut (S ts < S old_ts); [lia|].
            eapply view_of_eid_ob_write; eauto.
            { left. left. right. ss. }
            inv LABEL1. inv LABEL2.
            destruct l; ss; destruct (equiv_dec loc (ValA.val (sem_expr armap2 eloc))); ss; inv e.
            - destruct (equiv_dec val0 (ValA.val voldv)); ss; inv e. esplits; eauto with tso.
            - destruct (equiv_dec vnew (ValA.val voldv)); ss; inv e. esplits; eauto with tso.
          }
          assert (S n < S ts).
          { eapply view_of_eid_ob_write; eauto.
            - left. left. left. right. left. econs; eauto.
            - econs; eauto with tso.
          }
          inv SIM_EXT1.
          { inv VIEW2. }
          unfold ALocal.next_eid in VIEW_OF_EID. rewrite VIEW_OF_EID in VIEW. inv VIEW.
          unfold le in VIEW2. lia.
        }
      }
      { ss. }
      econs; try refl.
      * (* internal *)
        eapply Memory.latest_ts_read_lt; eauto.
        generalize (SIM_LOCAL.(COH) (ValA.val (sem_expr armap2 eloc))).
        intro X. inv X.
        { rewrite VIEW0. clear. unfold bot. unfold Time.bot. lia. }
        eapply Time.le_lt_trans; eauto. inv EID. inv REL. inv H. inv H0.
        inv H2. destruct l; ss; destruct (equiv_dec loc (ValA.val (sem_expr armap2 eloc))); ss; inv e.
        { (* write *)
          inv H1. des. inv H.
          { exploit Valid.coherence_ww; try exact H0; eauto with tso.
            i. eapply view_of_eid_ob_write; eauto.
            - left. left. right. ss.
            - econs; eauto with tso.
          }
          { inv H1.
            exploit EX.(Valid.RF2); eauto. i. des.
            inv WRITE. inv READ0. rewrite EID in EID0. inv EID0.
            inv LABEL1.
            destruct (equiv_dec (ValA.val (sem_expr armap2 eloc)) loc); ss. inv e.
            destruct (equiv_dec val val0); ss. inv e.
            inv READ1.
            destruct l; ss.
            - (* read *)
              inv LABEL1.
              destruct (equiv_dec loc (ValA.val (sem_expr armap2 eloc))); ss. inv e.
              destruct (equiv_dec val val0); ss. inv e.
              exploit Valid.coherence_rw; try exact H0; eauto with tso.
              i. eapply view_of_eid_ob_write; eauto with tso.
              left. left. right. ss.
            - (* update *)
              inv LABEL1.
              destruct (equiv_dec loc (ValA.val (sem_expr armap2 eloc))); ss. inv e.
              destruct (equiv_dec vold val0); ss. inv e.
              exploit Valid.coherence_rw; try exact H; try exact H0; eauto with tso.
              i. eapply view_of_eid_ob_write; eauto with tso.
              left. left. right. ss.
          }
        }
        { (* update *)
          inv H1. des. inv H.
          { exploit Valid.coherence_ww; try exact H0; eauto with tso.
            all: try by econs; eauto; eauto with tso.
            i. eapply view_of_eid_ob_write; eauto.
            - left. left. right. ss.
            - econs; eauto with tso.
          }
          { inv H1.
            exploit EX.(Valid.RF2); eauto. i. des.
            inv WRITE. inv READ0. rewrite EID in EID0. inv EID0.
            inv LABEL1.
            destruct (equiv_dec (ValA.val (sem_expr armap2 eloc)) loc); ss. inv e.
            destruct (equiv_dec vnew val); ss. inv e.
            inv READ1.
            destruct l; ss.
            - (* read *)
              inv LABEL1.
              destruct (equiv_dec loc (ValA.val (sem_expr armap2 eloc))); ss. inv e.
              destruct (equiv_dec val0 val); ss. inv e.
              exploit Valid.coherence_rw; try exact H0; eauto with tso.
              i. eapply view_of_eid_ob_write; eauto with tso.
              left. left. right. ss.
            - (* update *)
              inv LABEL1.
              destruct (equiv_dec loc (ValA.val (sem_expr armap2 eloc))); ss. inv e.
              destruct (equiv_dec vold0 val); ss. inv e.
              exploit Valid.coherence_rw; try exact H; try exact H0; eauto with tso.
              i. eapply view_of_eid_ob_write; eauto with tso.
              left. left. right. ss.
          }
        }
      * (* external *)
        unfold lt. apply le_n_S. s. repeat apply join_spec.
        { generalize SIM_LOCAL.(VWN). intro X. inv X.
          { rewrite VIEW0. apply bot_spec. }
          rewrite VIEW0. inv EID.
          apply lt_n_Sm_le. eapply view_of_eid_ob_write; eauto.
          - eapply sim_local_vwn_spec; eauto with tso.
          - econs; eauto with tso.
        }
    + econs; ss. econs; ss.
      * i. rewrite List.app_length, Nat.add_1_r.
        rewrite sim_local_coh_step. rewrite inverse_step.
        rewrite inverse_union, fun_add_spec. condtac; ss.
        { unfold Memory.get_msg in MSG. ss. rewrite MSG.
          inversion e. subst. condtac; ss.
          econs 2; eauto; [|refl]. right. econs; eauto.
          econs. splits; eauto. econs; eauto. econs; eauto with tso.
        }
        { eapply sim_view_le; [|exact (SIM_LOCAL.(COH) loc)]. eauto. }
      * rewrite List.app_length, Nat.add_1_r.
        rewrite sim_local_vrn_step. rewrite inverse_step.
        rewrite ? inverse_union. apply sim_view_join.
        { eapply sim_view_le; [|exact SIM_LOCAL.(VRN)]. eauto. }
        eapply sim_view_le; [|exact SIM_EXT1].
        i. subst. right. left. econs; eauto. econs; eauto with tso.
      * rewrite List.app_length, Nat.add_1_r.
        rewrite sim_local_vwn_step. rewrite inverse_step.
        rewrite ? inverse_union. apply sim_view_join.
        { eapply sim_view_le; [|exact SIM_LOCAL.(VWN)]. eauto. }
        { eapply sim_view_le; [by right; eauto|]. econs 2; eauto.
          - econs; eauto. econs; eauto with tso.
          - refl.
        }
      * rewrite List.app_length, Nat.add_1_r.
        rewrite sim_local_vro_step. rewrite inverse_step.
        rewrite ? inverse_union. apply sim_view_join; eauto.
        { eapply sim_view_le; [|exact SIM_LOCAL.(VRO)]. eauto. }
        eapply sim_view_le; [|exact SIM_EXT1].
        i. subst. right. econs; eauto. econs; eauto with tso.
      * rewrite List.app_length, Nat.add_1_r.
        rewrite sim_local_vwo_step. rewrite inverse_step.
        rewrite ? inverse_union. apply sim_view_join.
        { eapply sim_view_le; [|exact SIM_LOCAL.(VWO)]. eauto. }
        { eapply sim_view_le; [by right; eauto|]. econs 2; eauto.
          - econs; eauto. econs; eauto with tso.
          - refl.
        }
      * i. rewrite Promises.unset_o. condtac.
        { econs; ss. i. des. inversion e. subst.
          rewrite List.app_length in *. ss.
          assert ((tid, length (ALocal.labels alocal1)) = (tid, n0)).
          { eapply view_of_eid_ob_write_write; eauto with tso. }
          inv H. lia.
        }
        rewrite SIM_LOCAL.(PROMISES), List.app_length. s. econs; i; des.
        { inv N.
          - inv WRITE. destruct l; ss; congr.
          - esplits; cycle 1; eauto. lia.
        }
        { esplits; cycle 1; eauto. lia. }
  - exploit LABEL.
    { rewrite List.nth_error_app2; [|refl]. rewrite Nat.sub_diag. ss. }
    intro LABEL_LEN.
    exploit label_read_mem_of_ex; eauto. i. des.

    assert (SIM_VRN: sim_view ex ob
                              (eq (tid, ALocal.next_eid alocal1))
                              local1.(Local.vrn).(View.ts)).
    { econs 2; eauto; ss.
      generalize SIM_LOCAL.(VRN). intro VRN.
      inv VRN.
      { rewrite VIEW0. apply bot_spec. }
      rewrite VIEW0. eapply view_of_eid_ob; eauto.
      inv EID. exploit sim_local_vrn_spec; eauto with tso.
    }

    rename armap2 into rmap1.

    assert (exists n,
               <<READ: Memory.read (ValA.val (sem_expr rmap1 eloc)) n (mem_of_ex ex ob) = Some res0>> /\
               <<MSG: n > 0 ->
                      exists eid2,
                        <<RF: ex.(Execution.rf) eid2 (tid, length (ALocal.labels alocal1))>> /\
                        <<VIEW: view_of_eid ex ob eid2 = Some n>> /\
                        <<MSG: Memory.get_msg n (mem_of_ex ex ob) = Some (Msg.mk (ValA.val (sem_expr rmap1 eloc)) res0 (fst eid2))>>>> /\
               <<UNINIT: n = 0 ->
                      <<RF: ~ codom_rel ex.(Execution.rf) (tid, length (ALocal.labels alocal1))>>>>).
    { exploit EX.(Valid.RF1).
      instantiate (1 := (tid, length (ALocal.labels alocal1))).
      instantiate (1 := res0). instantiate (1 := (ValA.val (sem_expr rmap1 eloc))).
      { econs; eauto with tso. }
      i. des.
      { (* read from uninit *)
        subst. exists 0.
        splits; ss. lia.
      }
      inv LABEL0. destruct l; ss; destruct (equiv_dec loc (ValA.val (sem_expr rmap1 eloc))); ss; inv e.
      - exploit label_write_mem_of_ex; eauto.
        destruct (equiv_dec val res0); ss. inv e.
        i. des.
        esplits; eauto. i. inv H.
      - exploit label_update_mem_of_ex; eauto.
        destruct (equiv_dec vnew res0); ss. inv e.
        i. des.
        esplits; eauto. i. inv H.
    }
    des.

    assert (SIM_EXT1: sim_view ex ob
                               (eq (tid, ALocal.next_eid alocal1))
                               (join (local1.(Local.vrn).(View.ts)) n)).
    { apply sim_view_join; ss. econs 2; try exact VIEW; eauto.
      destruct n; unfold le.
      { lia. }
      exploit MSG; [lia|]. i. des.
      destruct eid2. ss. destruct (t == tid).
      { inv e. subst.
        exploit Valid.rfi_is_po; eauto with tso. i.
        inv x0. ss.
        (* TODO: rfi is ob, so... *)
        admit.
      }
      { exploit view_of_eid_ob; cycle 3.
        { instantiate (1 := view). eauto. }
        all: try eauto.
        left. left. left. left. econs; eauto. econs; eauto.
      }
    }

    inversion RMW. ss.

    assert (RMW_FAIL_STEP: exists vold local2, Local.rmw_failure (sem_expr rmap1 eloc) vold vres n local1 (mem_of_ex ex ob) local2).
    { esplits. econs; eauto.
      - (* internal *)
        generalize (SIM_LOCAL.(COH) (ValA.val (sem_expr rmap1 eloc))). intro X. inv X.
        { eapply Memory.latest_mon1. eapply Memory.latest_ts_latest; eauto. apply bot_spec. }
        eapply Memory.latest_mon1. eapply Memory.latest_ts_latest; eauto.
        rewrite VIEW0. inv EID. inv REL. inv H. inv H0.
        inv H2.
        inv H1. des. inv H.
        { exploit Valid.coherence_wr; try exact H0; eauto.
          all: try by econs; eauto; eauto with tso.
          i. des.
          destruct n.
          { (* read from uninit *)
            specialize (UNINIT eq_refl). des.
            contradict UNINIT. econs; eauto.
          }
          exploit MSG; [lia|]. i. des.
          exploit EX.(Valid.RF_WF); [exact RF|exact RF0|]. i. subst.
          inv CO.
          - rewrite VIEW_OF_EID in VIEW1. inv VIEW1. refl.
          - eapply view_of_eid_ob; eauto. left. left. right. eauto.
        }
        { inv H1.
          exploit EX.(Valid.RF2); eauto. i. des.
          inv WRITE. inv READ0. rewrite EID in EID0. inv EID0.
          inv LABEL1.
          destruct l0; ss; destruct (equiv_dec loc0 loc); ss; inv e.
          { (* W: write *)
            destruct (equiv_dec val0 val); ss. inv e.
            inv LABEL0.
            destruct (equiv_dec loc (ValA.val (sem_expr rmap1 eloc))); ss. inv e.
            inv LABEL2.
            destruct l1; ss; destruct (equiv_dec loc (ValA.val (sem_expr rmap1 eloc))); ss; inv e.
            { (* W: write -> R: read  *)
              destruct (equiv_dec val0 val); ss. inv e.
              exploit Valid.coherence_rr; try exact H0; eauto with tso.
              i. des.
              destruct n.
              { (* read from uninit *)
                specialize (UNINIT eq_refl). des.
                contradict UNINIT. econs; eauto.
              }
              exploit MSG; [lia|]. i. des.
              exploit EX.(Valid.RF_WF); [exact RF|exact RF0|]. i. subst.
              inv CO.
              - rewrite VIEW_OF_EID in VIEW1. inv VIEW1. refl.
              - eapply view_of_eid_ob; eauto. left. left. right. eauto.
            }
            { (* W: write -> R: update  *)
              destruct (equiv_dec vold val); ss. inv e.
              exploit Valid.coherence_rr; try exact H0; cycle 3.
              instantiate (1 := x).
              instantiate (1 := (ValA.val (sem_expr rmap1 eloc))).
              all: eauto with tso.
              i. des.
              destruct n.
              { (* read from uninit *)
                specialize (UNINIT eq_refl). des.
                contradict UNINIT. econs; eauto.
              }
              exploit MSG; [lia|]. i. des.
              exploit EX.(Valid.RF_WF); [exact RF|exact RF0|]. i. subst.
              inv CO.
              - rewrite VIEW_OF_EID in VIEW1. inv VIEW1. refl.
              - eapply view_of_eid_ob; eauto. left. left. right. eauto.
            }
          }
          { (* W: update *)
            destruct (equiv_dec vnew val); ss. inv e.
            inv LABEL0.
            destruct (equiv_dec loc (ValA.val (sem_expr rmap1 eloc))); ss. inv e.
            inv LABEL2.
            destruct l1; ss; destruct (equiv_dec loc (ValA.val (sem_expr rmap1 eloc))); ss; inv e.
            { (* W: update -> R: read  *)
              destruct (equiv_dec val0 val); ss. inv e.
              exploit Valid.coherence_rr; try exact H0; eauto with tso.
              i. des.
              destruct n.
              { (* read from uninit *)
                specialize (UNINIT eq_refl). des.
                contradict UNINIT. econs; eauto.
              }
              exploit MSG; [lia|]. i. des.
              exploit EX.(Valid.RF_WF); [exact RF|exact RF0|]. i. subst.
              inv CO.
              - rewrite VIEW_OF_EID in VIEW1. inv VIEW1. refl.
              - eapply view_of_eid_ob; eauto. left. left. right. eauto.
            }
            { (* W: update -> R: update  *)
              destruct (equiv_dec vold0 val); ss. inv e.
              exploit Valid.coherence_rr; try exact H0; cycle 3.
              instantiate (1 := x).
              instantiate (1 := (ValA.val (sem_expr rmap1 eloc))).
              all: eauto with tso.
              i. des.
              destruct n.
              { (* read from uninit *)
                specialize (UNINIT eq_refl). des.
                contradict UNINIT. econs; eauto.
              }
              exploit MSG; [lia|]. i. des.
              exploit EX.(Valid.RF_WF); [exact RF|exact RF0|]. i. subst.
              inv CO.
              - rewrite VIEW_OF_EID in VIEW1. inv VIEW1. refl.
              - eapply view_of_eid_ob; eauto. left. left. right. eauto.
            }
          }
        }
      - (* external *)
        ii.
        exploit in_mem_of_ex; swap 1 2; eauto.
        { eapply Permutation_NoDup; [by symmetry; eauto|].
          eapply Execution.eids_spec; eauto.
        }
        i. destruct msg. ss. subst.
        destruct n.
        { (* read from uninit *)
          specialize (UNINIT eq_refl).
          assert (view < S ts).
          { des.
            - eapply view_of_eid_ob_write; eauto.
              + left. left. left. right. right. econs.
                * econs; eauto. econs; eauto with tso.
                * econs; eauto with tso. econs; eauto with tso.
              + econs; eauto with tso.
            - eapply view_of_eid_ob_write; eauto.
              + left. left. left. right. right. econs.
                * econs; eauto. econs; eauto with tso.
                * econs; eauto with tso. econs; eauto with tso.
              + econs; eauto with tso.
          }
          assert (JOIN_ZERO: join (View.ts (Local.vrn local1)) 0 = View.ts (Local.vrn local1)).
          { destruct (View.ts (Local.vrn local1)); ss. }
          inv SIM_EXT1; rewrite JOIN_ZERO in VIEW0.
          { rewrite VIEW0 in TS2. inv TS2. }
          unfold ALocal.next_eid in VIEW_OF_EID. rewrite VIEW_OF_EID in VIEW. inv VIEW.
          unfold le in VIEW0. lia.
        }
        exploit MSG; [lia|]. i. des.
        { (* write_mem_of_ex *)
          exploit EX.(Valid.RF1).
          instantiate (1 := (tid, length (ALocal.labels alocal1))).
          instantiate (1 := res0). instantiate (1 := ValA.val (sem_expr rmap1 eloc)).
          { econs; eauto with tso. }
          i. des.
          { contradict NORF. econs. eauto. }
          exploit EX.(Valid.RF_WF); [exact RF|exact RF0|]. i. subst.
          exploit EX.(Valid.CO1).
          instantiate (1 := eid0).
          instantiate (1 := (tid0, n0)).
          { inv LABEL1. inv LABEL2.
            destruct l; ss; destruct (equiv_dec loc (ValA.val (sem_expr rmap1 eloc))); ss; inv e.
            - destruct (equiv_dec val0 res0); ss; inv e. esplits; eauto with tso.
            - destruct (equiv_dec vnew res0); ss; inv e. esplits; eauto with tso.
          }
          i. des.
          { subst. rewrite VIEW0 in VIEW1. inv VIEW1. lia. }
          { cut (S ts < S n); [lia|].
            eapply view_of_eid_ob_write; eauto.
            { left. left. right. ss. }
            inv LABEL1. inv LABEL2.
            destruct l; ss; destruct (equiv_dec loc (ValA.val (sem_expr rmap1 eloc))); ss; inv e.
            - destruct (equiv_dec val0 res0); ss; inv e. esplits; eauto with tso.
            - destruct (equiv_dec vnew res0); ss; inv e. esplits; eauto with tso.
          }
          assert (view < S ts).
          { eapply view_of_eid_ob_write; eauto.
            - left. left. left. right. left. econs; eauto.
            - econs; eauto with tso.
          }
          assert (JOIN_SN:join (View.ts (Local.vrn local1)) (S n) = View.ts (Local.vrn local1)).
          { destruct (View.ts (Local.vrn local1)).
            - lia.
            - assert (S n < S t).
              { unfold lt. unfold lt in TS1.
                etrans; eauto.
              }
              unfold join. unfold Time.join. lia.
          }
          inv SIM_EXT1; rewrite JOIN_SN in VIEW2.
          { rewrite VIEW2 in TS2. inv TS2. }
          unfold ALocal.next_eid in VIEW_OF_EID. rewrite VIEW_OF_EID in VIEW. inv VIEW.
          unfold le in VIEW2. lia.
        }
        { (* update_mem_of_ex *)
          exploit EX.(Valid.RF1).
          instantiate (1 := (tid, length (ALocal.labels alocal1))).
          instantiate (1 := res0). instantiate (1 := ValA.val (sem_expr rmap1 eloc)).
          { econs; eauto with tso. }
          i. des.
          { contradict NORF. econs. eauto. }
          exploit EX.(Valid.RF_WF); [exact RF|exact RF0|]. i. subst.
          exploit EX.(Valid.CO1).
          instantiate (1 := eid0).
          instantiate (1 := (tid0, n0)).
          { inv LABEL1. inv LABEL2.
            destruct l; ss; destruct (equiv_dec loc (ValA.val (sem_expr rmap1 eloc))); ss; inv e.
            - destruct (equiv_dec val0 res0); ss; inv e. esplits; eauto with tso.
            - destruct (equiv_dec vnew res0); ss; inv e. esplits; eauto with tso.
          }
          i. des.
          { subst. rewrite VIEW0 in VIEW1. inv VIEW1. lia. }
          { cut (S ts < S n); [lia|].
            eapply view_of_eid_ob_write; eauto.
            { left. left. right. ss. }
            inv LABEL1. inv LABEL2.
            destruct l; ss; destruct (equiv_dec loc (ValA.val (sem_expr rmap1 eloc))); ss; inv e.
            - destruct (equiv_dec val0 res0); ss; inv e. esplits; eauto with tso.
            - destruct (equiv_dec vnew res0); ss; inv e. esplits; eauto with tso.
          }
          assert (view < S ts).
          { eapply view_of_eid_ob_write; eauto.
            - left. left. left. right. left. econs; eauto.
            - econs; eauto with tso.
          }
          assert (JOIN_SN:join (View.ts (Local.vrn local1)) (S n) = View.ts (Local.vrn local1)).
          { destruct (View.ts (Local.vrn local1)).
            - lia.
            - assert (S n < S t).
              { unfold lt. unfold lt in TS1.
                etrans; eauto.
              }
              unfold join. unfold Time.join. lia.
          }
          inv SIM_EXT1; rewrite JOIN_SN in VIEW2.
          { rewrite VIEW2 in TS2. inv TS2. }
          unfold ALocal.next_eid in VIEW_OF_EID. rewrite VIEW_OF_EID in VIEW. inv VIEW.
          unfold le in VIEW2. lia.
        }
    }

    des. eexists (ExecUnit.mk _ _ _). esplits.
    + econs. econs; ss.
      { inv H. econs 6; try exact RMW; ss. }
      inv H0. econs 5; eauto.
    + generalize RMW_FAIL_STEP. intro X. inv X.
      rewrite READ in OLD_MSG. inv OLD_MSG.
      econs; ss. econs; ss.
      * (* sim_local coh *)
        i. rewrite List.app_length, Nat.add_1_r.
        rewrite sim_local_coh_step. rewrite inverse_step.
        rewrite inverse_union, fun_add_spec. condtac; cycle 1.
        { eapply sim_view_le; [|exact (SIM_LOCAL.(COH) loc)]. eauto. }
        inversion e. subst. inv WF.
        generalize (Local.rmw_failure_spec LOCAL RMW_FAIL_STEP). i. des. ss.
        revert COH1. rewrite fun_add_spec. condtac; ss. i.
        rewrite <- COH1. destruct n.
        { econs 1. ss. }
        exploit MSG; [lia|]. i. des.
        exploit EX.(Valid.RF1).
        instantiate (1 := (tid, length (ALocal.labels alocal1))).
        instantiate (1 := old). instantiate (1 := ValA.val (sem_expr rmap1 eloc)).
        eauto with tso.
        i. des.
        { contradict NORF. econs. eauto. }
        exploit EX.(Valid.RF_WF); [exact RF|exact RF0|]. i. subst. inv LABEL0.
        destruct eid0. ss. destruct (t == tid).
        { inversion e1. subst.
          econs 2; try exact VIEW0; ss.
          left. econs; eauto. econs. splits.
          - econs; eauto. econs; eauto with tso.
          - econs. splits; eauto.
            exploit Valid.rfi_is_po; eauto. econs; eauto.
        }
        { econs 2; try exact VIEW0; ss.
          right. econs; eauto. econs. splits.
          - econs; eauto. econs; eauto with tso.
          - econs 2. econs; eauto. econs; eauto.
        }
      * (* sim_local vrn *)
        rewrite List.app_length, Nat.add_1_r.
        rewrite sim_local_vrn_step. rewrite inverse_step.
        rewrite ? inverse_union. apply sim_view_join.
        { eapply sim_view_le; [|exact SIM_LOCAL.(VRN)]. eauto. }
        eapply sim_view_le; [|exact SIM_EXT1].
        i. subst. right. left. econs; eauto. econs; eauto with tso.
      * (* sim_local vwn *)
        rewrite List.app_length, Nat.add_1_r.
        rewrite sim_local_vwn_step. rewrite inverse_step.
        rewrite ? inverse_union. apply sim_view_join.
        { eapply sim_view_le; [|exact SIM_LOCAL.(VWN)]. eauto. }
        eapply sim_view_le; [|exact SIM_EXT1].
        i. subst. right. left. econs; eauto. econs; eauto with tso.
      * (* sim_local vro *)
        rewrite List.app_length, Nat.add_1_r.
        rewrite sim_local_vro_step. rewrite inverse_step.
        rewrite ? inverse_union. apply sim_view_join; eauto.
        { eapply sim_view_le; [|exact SIM_LOCAL.(VRO)]. eauto. }
        eapply sim_view_le; [|exact SIM_EXT1].
        i. subst. right. econs; eauto. econs; eauto with tso.
      * (* sim_local vwo *)
        rewrite List.app_length, Nat.add_1_r.
        rewrite sim_local_vwo_step. rewrite inverse_step.
        rewrite ? inverse_union. eapply sim_view_le; [|exact SIM_LOCAL.(VWO)]. eauto.
      * (* sim_local promises *)
        i. rewrite SIM_LOCAL.(PROMISES), List.app_length. s. econs; i; des.
        { inv N.
          - inv WRITE. destruct l; ss; congr.
          - esplits; cycle 1; eauto. lia.
        }
        { esplits; cycle 1; eauto. lia. }
  - (* dmb *)
    exploit LABEL.
    { rewrite List.nth_error_app2; ss. rewrite Nat.sub_diag. ss. }
    intro LABEL_LEN. eexists (ExecUnit.mk _ _ _).
    esplits.
    { econs. econs; ss.
      - econs; ss.
      - econs 6; ss.
    }
    econs; ss.
    econs; ss.
    + rewrite List.app_length, Nat.add_1_r. s.
      i. rewrite sim_local_coh_step. rewrite inverse_step.
      rewrite inverse_union. eapply sim_view_le; [by left; eauto|].
      apply SIM_LOCAL.
    + rewrite List.app_length, Nat.add_1_r. s.
      rewrite sim_local_vrn_step. rewrite inverse_step.
      rewrite ? inverse_union. repeat apply sim_view_join; eauto using sim_view_bot.
      { eapply sim_view_le; [|exact SIM_LOCAL.(VRN)]. eauto. }
      { destruct rr; eauto using sim_view_bot.
        eapply sim_view_le; [|exact SIM_LOCAL.(VRO)].
        left.
        inv PR. econs; eauto. econs; eauto.
      }
      { destruct wr; eauto using sim_view_bot.
        eapply sim_view_le; [|exact SIM_LOCAL.(VWO)].
        right. right. rewrite seq_assoc.
        inv PR. econs; eauto. econs; splits; eauto.
        econs; eauto with tso.
      }
    + rewrite List.app_length, Nat.add_1_r. s.
      rewrite sim_local_vwn_step. rewrite inverse_step.
      rewrite ? inverse_union. repeat apply sim_view_join; eauto using sim_view_bot.
      { eapply sim_view_le; [|exact SIM_LOCAL.(VWN)]. eauto. }
      { destruct rw; eauto using sim_view_bot.
        eapply sim_view_le; [|exact SIM_LOCAL.(VRO)].
        left.
        inv PR. econs; eauto. econs; eauto.
      }
      { destruct ww; eauto using sim_view_bot.
        eapply sim_view_le; [|exact SIM_LOCAL.(VWO)].
        left.
        inv PR. econs; eauto. right.
        inv REL. des. inv H. econs; splits; eauto.
        econs; eauto.
      }
    + rewrite List.app_length, Nat.add_1_r. s.
      rewrite sim_local_vro_step. rewrite inverse_step.
      rewrite ? inverse_union. eapply sim_view_le; [|exact SIM_LOCAL.(VRO)]. eauto.
    + rewrite List.app_length, Nat.add_1_r. s.
      rewrite sim_local_vwo_step. rewrite inverse_step.
      rewrite ? inverse_union. eapply sim_view_le; [|exact SIM_LOCAL.(VWO)]. eauto.
    + i. rewrite SIM_LOCAL.(PROMISES), List.app_length. s. econs; i; des.
      { inv N.
        - inv WRITE. destruct l; ss; congr.
        - esplits; cycle 1; eauto. lia.
      }
      { esplits; cycle 1; eauto. lia. }
  - (* dowhile *)
    eexists (ExecUnit.mk _ _ _). esplits.
    + econs. econs; ss; econs; ss.
    + econs; ss.
      inv SIM_LOCAL; econs; eauto.

  Grab Existential Variables.
  eauto. (* vold when rmw_failure*)
Qed.

Lemma sim_eu_rtc_step
      p ex ob tid aeu1 eu1 aeu2
      (EX: Valid.ex p ex)
      (OB: Permutation ob (Execution.eids ex))
      (LINEARIZED: linearized (Execution.ob ex) ob)
      (SIM: sim_eu tid ex ob aeu1 eu1)
      (WF_EU: ExecUnit.wf tid eu1)
      (WF_AEU: AExecUnit.wf aeu1)
      (STEP: rtc AExecUnit.step aeu1 aeu2)
      (LOCAL: IdMap.find tid EX.(Valid.aeus) = Some aeu2):
  exists eu2,
    <<SIM: sim_eu tid ex ob aeu2 eu2>> /\
    <<STEP: rtc (ExecUnit.state_step tid) eu1 eu2>>.
Proof.
  revert eu1 WF_EU SIM. induction STEP.
  { esplits; eauto. }
  i.
  exploit AExecUnit.step_future; eauto. i. des.
  exploit AExecUnit.rtc_step_future; eauto. i. des.
  exploit sim_eu_step; eauto.
  { i. unfold Execution.label. s.
    rewrite EX.(Valid.LABELS), IdMap.map_spec, LOCAL. s.
    inv LE0. des. rewrite LABELS, List.nth_error_app1; ss.
    apply List.nth_error_Some. congr.
  }
  i. des.
  specialize (ExecUnit.state_step_wf STEP0 WF_EU). i.
  exploit IHSTEP; try exact SIM0; eauto. i. des.
  esplits; eauto.
Qed.

Theorem axiomatic_to_promising
      p ex
      (EX: Valid.ex p ex):
  exists m,
    <<STEP: Machine.exec p m>> /\
    <<TERMINAL: Valid.is_terminal EX -> Machine.is_terminal m>> /\
    <<STATE: IdMap.Forall2
               (fun tid sl aeu => sim_state_weak (fst sl) aeu.(AExecUnit.state))
               m.(Machine.tpool) EX.(Valid.aeus)>> /\
    <<MEM: sim_mem ex m.(Machine.mem)>>.
Proof.
  (* Linearize events and construct memory. *)
  exploit (linearize (Execution.eids ex)).
  { eapply EX.(Valid.EXTERNAL). }
  i. des. rename l' into ob.
  remember (mem_of_ex ex ob) as mem eqn:MEM.

  (* Construct promise steps. *)
  exploit (Machine.pf_init_with_promises p mem); eauto.
  { i. subst. unfold mem_of_ex in MSG. rewrite in_filter_map_iff in MSG. des.
    exploit Permutation_in; eauto. intro X.
    generalize (Execution.eids_spec ex). i. des.
    apply LABEL in X. destruct (Execution.label a ex) eqn:Y; ss.
    destruct t; ss.
    - inv MSG0. s. unfold Execution.label in Y.
      rewrite EX.(Valid.LABELS), IdMap.map_spec in Y.
      destruct (IdMap.find (fst a) (Valid.PRE EX).(Valid.aeus)) eqn:Z; ss.
      generalize (EX.(Valid.AEUS) (fst a)). intro W. inv W; ss. congr.
    - inv MSG0. s. unfold Execution.label in Y.
      rewrite EX.(Valid.LABELS), IdMap.map_spec in Y.
      destruct (IdMap.find (fst a) (Valid.PRE EX).(Valid.aeus)) eqn:Z; ss.
      generalize (EX.(Valid.AEUS) (fst a)). intro W. inv W; ss. congr.
  }
  unfold IdMap.Equal, Machine.init_with_promises. s. i. des. subst.
  setoid_rewrite IdMap.mapi_spec in TPOOL.

  (* It's sufficient to construct steps from the promised state. *)
  cut (exists m0,
          <<STEP: rtc (Machine.step ExecUnit.state_step) m m0>> /\
          <<NOPROMISE: Machine.no_promise m0>> /\
          <<TERMINAL: Valid.is_terminal EX -> Machine.is_terminal m0>> /\
          <<STATE: IdMap.Forall2
                     (fun tid sl aeu => sim_state_weak (fst sl) aeu.(AExecUnit.state))
                     m0.(Machine.tpool) EX.(Valid.aeus)>> /\
          <<MEM: sim_mem ex (Machine.mem m0)>>).
  { i. des. esplits; eauto. econs; eauto.
    etrans.
    - eapply rtc_mon; [|by eauto]. apply Machine.step_mon. right. ss.
    - eapply rtc_mon; [|by eauto]. apply Machine.step_mon. left. ss.
  }
  clear STEP.

  (* Execute threads one-by-one (induction). *)
  assert (IN: forall tid stmts
                (FIND1: IdMap.find tid p = Some stmts),
             IdMap.find tid m.(Machine.tpool) =
             Some (State.init stmts,
                   Local.init_with_promises (Machine.promises_from_mem tid (Machine.mem m)))).
  { i. rewrite TPOOL, FIND1, MEM0. ss. }
  assert (OUT: forall tid st lc
                 (FIND1: IdMap.find tid p = None)
                 (FIND2: IdMap.find tid m.(Machine.tpool) = Some (st, lc)),
             exists aeu,
               <<AEU: IdMap.find tid EX.(Valid.aeus) = Some aeu>> /\
               <<STATE: sim_state_weak st aeu.(AExecUnit.state)>> /\
               <<PROMISE: lc.(Local.promises) = bot>>).
  { i. rewrite TPOOL, FIND1 in FIND2. ss. }
  assert (INVALID: forall tid
                     (FIND1: IdMap.find tid p = None)
                     (FIND2: IdMap.find tid m.(Machine.tpool) = None),
             IdMap.find tid EX.(Valid.aeus) = None).
  { i. generalize (EX.(Valid.AEUS) tid). rewrite FIND1. intro X. inv X. ss. }
  assert (P: forall tid stmts
               (FIND1: IdMap.find tid p = Some stmts),
             IdMap.find tid p = Some stmts) by ss.

  clear TPOOL.
  setoid_rewrite IdMap.elements_spec in IN at 1.
  setoid_rewrite IdMap.elements_spec in OUT at 1.
  setoid_rewrite IdMap.elements_spec in INVALID at 1.
  setoid_rewrite IdMap.elements_spec in P at 1.
  generalize (IdMap.elements_3w p). intro NODUP. revert NODUP.
  revert IN OUT INVALID P. generalize (IdMap.elements p). intro ps.
  revert m MEM0. induction ps; ss.
  { i. esplits; eauto.
    - econs. i. exploit OUT; eauto. i. des. eauto.
    - econs. i. exploit OUT; eauto. i. des. splits; ss.
      exploit H; eauto. intro X. inv X. inv STATE.
      unfold State.is_terminal. congr.
    - ii. destruct (IdMap.find id (Machine.tpool m)) as [[]|] eqn:T.
      + exploit OUT; eauto. i. des. rewrite AEU. econs. ss.
      + exploit INVALID; eauto. intro X. rewrite X. ss.
  }
  i.

  destruct a as [tid stmts].
  exploit (IN tid); eauto.
  { destruct (equiv_dec tid tid); [|congr]. ss. }
  intro FIND.
  cut (exists st2 lc2 aeu,
          <<STEP: rtc (ExecUnit.state_step tid)
                      (ExecUnit.mk
                         (State.init stmts)
                         (Local.init_with_promises (Machine.promises_from_mem tid (Machine.mem m)))
                         (Machine.mem m))
                      (ExecUnit.mk st2 lc2 (Machine.mem m))>> /\
          <<TERMINAL: Valid.is_terminal EX -> State.is_terminal st2>> /\
          <<AEU: IdMap.find tid EX.(Valid.aeus) = Some aeu>> /\
          <<STATE: sim_state_weak st2 aeu.(AExecUnit.state)>> /\
          <<NOPROMISE: lc2.(Local.promises) = bot>>).
  { i. des. subst.
    exploit Machine.rtc_eu_step_step; try exact STEP; eauto. i.
    assert (NOTIN: SetoidList.findA (fun id' : IdMap.key => if equiv_dec tid id' then true else false) ps = None).
    { inv NODUP. revert H1. clear. induction ps; ss.
      destruct a. i. destruct (equiv_dec tid k); eauto.
      inv e. contradict H1. left. ss.
    }
    exploit (IHps (Machine.mk
                     (IdMap.add tid (st2, lc2) (Machine.tpool m))
                     (Machine.mem m))); ss.
    { i. rewrite IdMap.add_spec. condtac; ss.
      - inversion e. subst. congr.
      - apply IN. destruct (equiv_dec tid0 tid); ss.
    }
    { i. revert FIND2. rewrite IdMap.add_spec. condtac.
      - i. inv FIND2. inversion e. subst. eauto.
      - apply OUT. destruct (equiv_dec tid0 tid); ss.
    }
    { i. revert FIND2. rewrite IdMap.add_spec. condtac.
      - i. inv FIND2.
      - apply INVALID. destruct (equiv_dec tid0 tid); ss.
    }
    { i. generalize (P tid0 stmts0). destruct (equiv_dec tid0 tid); eauto.
      inv e. congr.
    }
    { inv NODUP. ss. }
    i. des. esplits; cycle 1; eauto. etrans; eauto.
  }
  generalize (P tid stmts). destruct (equiv_dec tid tid); [|congr].
  intro FINDP. specialize (FINDP eq_refl).
  rewrite MEM0 in *.
  clear NODUP IN OUT INVALID P IHps MEM0 FIND ps e m.

  (* Execute a thread `tid`. *)
  generalize (EX.(Valid.AEUS) tid). rewrite FINDP.
  intro X. inv X. des. rename b into aeu, H into AEU. clear FINDP.
  exploit (@sim_eu_rtc_step p ex ob tid); eauto.
  { instantiate (1 := ExecUnit.mk
                        (State.init stmts)
                        (Local.init_with_promises (Machine.promises_from_mem tid (mem_of_ex ex ob)))
                        (mem_of_ex ex ob)).
    econs; ss.
    econs; eauto; ss.
    econs; i.
    { destruct view; ss. apply Machine.promises_from_mem_spec in H. des.
      exploit in_mem_of_ex; swap 1 2; eauto.
      { eapply Permutation_NoDup; [by symmetry; eauto|].
      eapply Execution.eids_spec; eauto.
      }
      s. i. des.
      - esplits; cycle 1; eauto with tso. lia.
      - esplits; cycle 1; eauto with tso. lia.
    }
    { des. inv WRITE.
      destruct l; ss; [ exploit label_write_mem_of_ex | exploit label_update_mem_of_ex ]; eauto.
      - i. des.
        rewrite VIEW in VIEW0. inv VIEW0.
        unfold Memory.get_msg in MSG. ss. apply Machine.promises_from_mem_spec. eauto.
      - i. des.
        rewrite VIEW in VIEW0. inv VIEW0.
        unfold Memory.get_msg in MSG. ss. apply Machine.promises_from_mem_spec. eauto.
    }
  }
  { clear. econs; ss.
    econs; ss; i; try by apply bot_spec.
    - destruct ts; ss.
      rewrite Machine.promises_from_mem_spec in IN. des.
      apply lt_le_S. rewrite <- List.nth_error_Some. ii. congr.
    - destruct ts; ss.
      unfold Memory.get_msg in MSG. ss. destruct msg. ss. subst.
      apply Machine.promises_from_mem_lookup in MSG. auto. }
  { apply AExecUnit.wf_init. }
  i. des. destruct eu2 as [state2 local2 mem2]. inv SIM. ss. subst.
  esplits; eauto.
  - intro X. exploit X; eauto. i. inv STATE. congr.
  - inv STATE. econs; ss.
    inv RMAP. econs. ii.
    destruct (IdMap.find id (State.rmap (AExecUnit.state aeu))); [econs|]; ss.
  - apply Promises.ext. i. rewrite Promises.lookup_bot.
    destruct (Promises.lookup i (Local.promises local2)) eqn:L; ss; cycle 1.
    apply LOCAL.(PROMISES) in L. des.
    exploit view_of_eid_inv; eauto. i. des. subst.
    inv WRITE. unfold Execution.label in EID. ss.
    rewrite EX.(Valid.LABELS), IdMap.map_spec, <- AEU in EID. ss.
    apply List.nth_error_None in N. congr.
Qed.
