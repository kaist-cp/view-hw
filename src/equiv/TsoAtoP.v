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
Require Import PromisingArch.promising.TsoPromising.
Require Import PromisingArch.promising.CommonPromising.
Require Import PromisingArch.axiomatic.TsoAxiomatic.
Require Import PromisingArch.equiv.TsoSimLocal.

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
      (EID: ex.(Execution.label_is) Label.is_kinda_write eid):
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
      (WRITE1: Execution.label_is ex (Label.is_kinda_write) eid1)
      (WRITE2: Execution.label_is ex (Label.is_kinda_write) eid2):
  eid1 = eid2.
Proof.
  exploit view_of_eid_inv; try exact VIEW1; eauto. i. des.
  exploit view_of_eid_inv; try exact VIEW2; eauto. i. des.
  inv WRITE1. inv WRITE2.
  destruct (Nat.compare_spec n n0).
  - subst. congr.
  - rewrite (@List_firstn_le (S n) (S n0)) in VIEW0; [|lia].
    rewrite mem_of_ex_app, List.app_length in VIEW0.
    apply plus_minus in VIEW0. rewrite Nat.sub_diag, Nat.sub_succ in VIEW0.
    exploit List_nth_error_skipn; eauto. i.
    exploit @List_nth_error_firstn; [eauto| |i].
    { instantiate (1 := (n0 - n)). lia. }
    exploit List.nth_error_In; eauto. i.
    exfalso. eapply mem_of_ex_in_length; eauto with tso.
  - symmetry in VIEW0.
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
      (WRITE2: Execution.label_is ex (Label.is_kinda_writing loc) eid2):
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

Lemma view_of_eid_co
      p ex ob eid1 eid2 view1 view2 loc
      (EX: Valid.ex p ex)
      (LINEARIZED: linearized (Execution.ob ex) ob)
      (VIEW1: view_of_eid ex ob eid1 = Some view1)
      (VIEW2: view_of_eid ex ob eid2 = Some view2)
      (WRITE1: Execution.label_is ex (Label.is_kinda_writing loc) eid1)
      (WRITE2: Execution.label_is ex (Label.is_kinda_writing loc) eid2)
      (LT: view1 < view2):
  Execution.co ex eid1 eid2.
Proof.
  exploit EX.(Valid.CO1).
  { esplits; [exact WRITE1 | exact WRITE2]; eauto. }
  i. des; ss.
  { subst. rewrite VIEW1 in VIEW2. inv VIEW2. lia. }
  cut (view2 < view1).
  { i. lia. }
  eapply view_of_eid_ob_write; eauto.
  left. left. left. left. left. right. ss.
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
          (local.(Local.coh) loc).(View.ts);
  VRN: sim_view
         ex ob
         (inverse (sim_local_vrn ex) (eq (tid, List.length (alocal.(ALocal.labels)))))
         local.(Local.vrn).(View.ts);
  VWN: exists mloc,
        (forall loc, (local.(Local.coh) loc).(View.ts) <= (local.(Local.coh) mloc).(View.ts)) /\
         sim_view
           ex ob
           (inverse (sim_local_vwn ex) (eq (tid, List.length (alocal.(ALocal.labels)))))
           (local.(Local.coh) mloc).(View.ts);
  FWDBANK: forall loc,
      (exists eid ts,
          <<TS: view_of_eid ex ob eid = Some ts>> /\
          <<TS_NONZERO: 0 < ts>> /\
          <<WRITE: sim_local_fwd ex loc eid (tid, List.length (alocal.(ALocal.labels)))>> /\
          <<LE_COH: ts <= (local.(Local.coh) loc).(View.ts)>>) \/
      (forall eid, ~ (inverse (sim_local_fwd_none ex loc) (eq (tid, List.length (alocal.(ALocal.labels)))) eid));
  PROMISES: forall view,
      Promises.lookup view local.(Local.promises) <->
      (exists n,
          <<N: (length alocal.(ALocal.labels)) <= n>> /\
          <<WRITE: ex.(Execution.label_is) Label.is_kinda_write (tid, n)>> /\
          <<VIEW: view_of_eid ex ob (tid, n) = Some view>>);
  COH_CL: forall loc,
          exists mloc_cl,
          <<CL: Loc.cl loc mloc_cl>> /\
          <<COH_MAX_CL: forall loc0 (CL: Loc.cl loc0 mloc_cl),
                         (local.(Local.coh) loc0).(View.ts) <= (local.(Local.coh) mloc_cl).(View.ts)>> /\
          <<COH_CL:
              sim_view
                ex ob
                (inverse (sim_local_coh_cl ex loc) (eq (tid, List.length (alocal.(ALocal.labels)))))
                (local.(Local.coh) mloc_cl).(View.ts)>>;
  VPR: sim_view
         ex ob
         (inverse (sim_local_vpr ex) (eq (tid, List.length (alocal.(ALocal.labels)))))
         local.(Local.vpr).(View.ts);
  VPA: forall loc,
        sim_view
          ex ob
          (inverse (sim_local_vpa ex loc) (eq (tid, List.length (alocal.(ALocal.labels)))))
          (local.(Local.vpa) loc).(View.ts);
  VPC: forall loc,
        sim_view
          ex ob
          (inverse (sim_local_vpc ex loc) (eq (tid, List.length (alocal.(ALocal.labels)))))
          (local.(Local.vpc) loc).(View.ts)
}.
Hint Constructors sim_local.

Inductive sim_eu (tid:Id.t) (ex:Execution.t) (ob: list eidT) (aeu:AExecUnit.t) (eu:ExecUnit.t): Prop :=
| sim_eu_intro
    (STATE: sim_state tid ex ob aeu.(AExecUnit.state) eu.(ExecUnit.state))
    (LOCAL: sim_local tid ex ob aeu.(AExecUnit.local) eu.(ExecUnit.local))
    (MEM: eu.(ExecUnit.mem) = mem_of_ex ex ob)
.
Hint Constructors sim_eu.

Inductive persisted_event_view (ex:Execution.t) (ob: list eidT) (loc:Loc.t) (view: Time.t): Prop :=
| persisted_event_view_uninit
  (VIEW: view = bot)
  (NPER: forall eid (PEID: Valid.persisted_event ex loc eid), False)
| persisted_event_view_init
  eid
  (VIEW: view_of_eid ex ob eid = Some view)
  (EID: ex.(Execution.label_is) (Label.is_kinda_writing loc) eid)
  (VPC: forall eid0 (PEID: Valid.persisted_event ex loc eid0), ex.(Execution.co)^? eid0 eid)
.
Hint Constructors persisted_event_view.

Lemma label_mem_of_ex
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

Lemma label_write_mem_of_ex_msg
      eid ex ob loc val
      (OB: Permutation ob (Execution.eids ex))
      (LABEL: Execution.label_is ex (Label.is_kinda_writing_val loc val) eid):
  exists n,
    <<VIEW: view_of_eid ex ob eid = Some (S n)>> /\
    <<MSG: List.nth_error (mem_of_ex ex ob) n = Some (Msg.mk loc val (fst eid))>>.
Proof.
  generalize (Execution.eids_spec ex). i. des. rename NODUP into NODUP0.
  specialize (LABEL0 eid). inv LABEL. rewrite EID in LABEL0.
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
    unfold mem_of_ex at 2. s. rewrite EID.
    destruct l; try rewrite Nat.add_1_r; ss.
  - rewrite <- (List.firstn_skipn n ob) at 1.
    rewrite mem_of_ex_app, List.nth_error_app2; [|lia].
    erewrite Nat.sub_diag, List_skipn_cons; eauto. s.
    unfold mem_of_ex. s. rewrite EID.
    destruct l; ss; eqvtac; ss.
Qed.

Lemma label_write_mem_of_ex
      eid ex ob loc val
      (OB: Permutation ob (Execution.eids ex))
      (LABEL: Execution.label_is ex (Label.is_kinda_writing_val loc val) eid):
  exists n,
    <<VIEW: view_of_eid ex ob eid = Some (S n)>> /\
    <<READ: Memory.read loc (S n) (mem_of_ex ex ob) = Some val>> /\
    <<MSG: Memory.get_msg (S n) (mem_of_ex ex ob) = Some (Msg.mk loc val (fst eid))>>.
Proof.
  inv LABEL. exploit label_write_mem_of_ex_msg; eauto with tso. i. des.
  esplits; eauto.
  unfold Memory.read. s. rewrite MSG. s. condtac; [|congr]. ss.
Qed.

Lemma read_msg_exist_ts
      p ex ob tid local alocal loc val
      (EX: Valid.ex p ex)
      (OB: Permutation ob (Execution.eids ex))
      (LINEARIZED: linearized (Execution.ob ex) ob)
      (SIM_LOCAL: sim_local tid ex ob alocal local)
      (READ: Execution.label_is ex (fun label : Label.t => Label.is_kinda_reading_val loc val label)
             (tid, length (ALocal.labels alocal))):
  exists ts,
    <<READ: Memory.read loc ts (mem_of_ex ex ob) = Some val>> /\
    <<MSG: ts > 0 ->
          exists eid,
            <<RF: ex.(Execution.rf) eid (tid, length (ALocal.labels alocal))>> /\
            <<VIEW: view_of_eid ex ob eid = Some ts>> /\
            <<MSG: Memory.get_msg ts (mem_of_ex ex ob) = Some (Msg.mk loc val (fst eid))>>>> /\
    <<FWD: ts = 0 ->
          <<RF: ~ codom_rel ex.(Execution.rf) (tid, length (ALocal.labels alocal))>> /\
          <<FWD: Local.coh local loc = View.mk bot bot>>>> /\
    <<SIM_FWD: sim_view ex ob
                        (eq (tid, ALocal.next_eid alocal))
                        (Local.read_view (Local.coh local loc) ts).(View.ts)>>.
Proof.
  exploit EX.(Valid.RF1); eauto.
  inv READ. exploit label_mem_of_ex; eauto. i. des.
  { (* read from uninit *)
    subst. exists 0.
    assert (FWD: Local.coh local loc = View.mk bot bot).
    { generalize (SIM_LOCAL.(COH) loc). i. inv H.
      { destruct (Local.coh local loc). destruct annot. rewrite <- VIEW0. ss. }
      inv EID0. inv REL. des. inv H. inv H2.
      inv H0. des. inv H.
      - exfalso. eapply EX.(Valid.COWR).
        econs. esplits; eauto with tso.
        right. repeat econs; eauto with tso.
      - inversion H1. exploit EX.(Valid.RF2); eauto. i. des. inv READ.
        exfalso. eapply EX.(Valid.EXTERNAL). instantiate (1 := x).
        econs 2.
        { (* rfe *)
          econs. repeat left. eauto.
        }
        econs 2.
        { (* dob *)
          econs. left. left. left. left. right. left.
          econs. econs; cycle 1.
          { econs. econs; eauto. econs; eauto with tso. }
          econs; eauto with tso.
        }
        (* fre *)
        econs. left. left. left. left. left. left. right.
        econs; cycle 1.
        { destruct x, x0. inv H0. inv H2. ss. inv TID. econs; eauto. }
        right. repeat econs; eauto with tso.
    }
    splits; ss; [lia |].
    rewrite FWD. econs 1. ss.
  }
  inv LABEL0.
  exploit label_write_mem_of_ex; eauto with tso. i. des.
  esplits; eauto.
  { i. ss. }
  econs 2; try exact VIEW; eauto; ss.
  generalize (SIM_LOCAL.(FWDBANK) loc). i. des.
  - (* fwdbank = Some *)
    destruct (Local.coh local loc) eqn:FWD.
    ss. unfold Local.read_view. s. condtac; [(* forwarded *) apply bot_spec |].
    (* not forwarded *)
    destruct eid2. destruct (t == tid); cycle 1.
    { eapply view_of_eid_ob; eauto. repeat left. econs; ss. }
    inv e.
    (* rfi before coh, so.. *) exfalso.
    exploit rfi_sim_local_fwd; eauto with tso.
    { econs; eauto with tso. }
    i. exploit sim_local_fwd_functional; [exact WRITE|exact x0|]. i. subst.
    rewrite VIEW0 in TS. inv TS.
    generalize (SIM_LOCAL.(COH) loc). i. inv H; rewrite FWD in VIEW1; ss.
    { unfold bot in *. unfold Time.bot in *. lia. }
    inv EID1. inv REL. des. inv H. inv H2.
    exploit EX.(Valid.CO1).
    { esplits; econs; [exact EID1| |exact EID0|]; eauto with tso. }
    i. des.
    + subst. rewrite VIEW0 in VIEW_OF_EID. inv VIEW_OF_EID. exploit le_antisym; eauto.
    + assert (v < S n).
      { eapply view_of_eid_ob_write; eauto with tso. left. left. left. left. left. right. ss. }
      unfold le in *. lia.
    + inv H0. des. inv H.
      * eapply EX.(Valid.COWR). econs. econs; eauto.
        left. econs. econs; eauto.
      * inversion H1. exploit EX.(Valid.RF2); eauto. i. des. inv READ0.
        eapply EX.(Valid.EXTERNAL). instantiate (1 := x).
        econs 2.
        { (* rfe *)
          econs. repeat left. eauto.
        }
        econs 2.
        { (* dob *)
          econs. left. left. left. left. right. left.
          econs. econs; cycle 1.
          { econs. econs; eauto. econs; eauto with tso. }
          econs; eauto with tso.
        }
        (* fre *)
        econs. left. left. left. left. left. left. right.
        econs; cycle 1.
        { destruct x, x0. inv H0. inv H2. ss. inv TID. econs; eauto. }
        left. repeat econs; eauto with tso.
  - (* fwdbank = None *)
    unfold Local.read_view. condtac; ss; [(* forwarded *) apply bot_spec |].
    eapply view_of_eid_ob; eauto.
    destruct eid2. destruct (t == tid); cycle 1.
    { repeat left. econs; ss. }
    inv e. exfalso. eapply H. econs; eauto. econs. splits.
    + econs; eauto. econs; eauto with tso.
    + exploit rfi_sim_local_fwd; eauto with tso.
      { econs; eauto with tso. }
      intro Y. apply Y.
Qed.

Lemma read_msg_latest_coh
      p ex ob tid local alocal loc ts val
      (EX: Valid.ex p ex)
      (LINEARIZED: linearized (Execution.ob ex) ob)
      (SIM_LOCAL: sim_local tid ex ob alocal local)
      (READING: Execution.label_is ex (fun label : Label.t => Label.is_kinda_reading loc label)
             (tid, length (ALocal.labels alocal)))
      (MSG: ts > 0 ->
            exists eid : eidT,
              Execution.rf ex eid (tid, length (ALocal.labels alocal)) /\
              view_of_eid ex ob eid = Some ts /\
              Memory.get_msg ts (mem_of_ex ex ob) = Some (Msg.mk loc val (fst eid)))
      (FWD: ts = 0 ->
            ~ codom_rel (Execution.rf ex) (tid, length (ALocal.labels alocal)) /\
            Local.coh local loc = View.mk bot bot):
  (local.(Local.coh) loc).(View.ts) <= ts.
Proof.
  generalize (SIM_LOCAL.(COH) loc). intro X. inv X.
  { rewrite VIEW. apply bot_spec. }
  rewrite VIEW. inv EID. inv REL. inv H. inv H0.
  inv H2. inv H1. des. inv H.
  - (* W;po;R *)
    exploit Valid.coherence_wr; try exact H0; eauto.
    all: try by econs; eauto; eauto with tso.
    i. des.
    destruct ts.
    { (* read from uninit *)
      specialize (FWD eq_refl). des.
      generalize (SIM_LOCAL.(FWDBANK) loc).
      rewrite FWD0; ss. i. des.
      { unfold bot in *. unfold Time.bot in *. lia. }
      exfalso. eapply H. econs; eauto. econs; eauto.
      econs; eauto. econs; eauto. econs; eauto.
    }
    exploit MSG; [lia|]. i. des.
    exploit EX.(Valid.RF_WF); [exact RF|exact x|]. i. subst.
    inv CO.
    + rewrite VIEW_OF_EID in x1. inv x1. refl.
    + eapply view_of_eid_ob; eauto. left. left. left. left. left. right. eauto.
  - (* W;rfe;po;R *)
    inv H1.
    exploit EX.(Valid.RF2); eauto. i. des.
    inv WRITE. inv READ. rewrite EID in EID0. inv EID0.
    assert (LOC: loc = loc0); eauto with tso. subst.
    exploit Valid.coherence_rr; try exact H0; eauto with tso. i. des.
    destruct ts.
    { (* read from uninit *)
      specialize (FWD eq_refl). des.
      contradict FWD. econs; eauto.
    }
    exploit MSG; [lia|]. i. des.
    exploit EX.(Valid.RF_WF); [exact RF|exact x1|]. i. subst.
    inv CO.
    + rewrite VIEW_OF_EID in x2. inv x2. refl.
    + eapply view_of_eid_ob; eauto. left. left. left. left. left. right. eauto.
Qed.

Lemma in_mem_of_ex
      ex ob view msg
      (NODUP: List.NoDup ob)
      (IN: List.nth_error (mem_of_ex ex ob) view = Some msg):
  (exists n,
     <<WRITING: Execution.label_is ex
                  (fun label : Label.t => Label.is_kinda_writing_val msg.(Msg.loc) msg.(Msg.val) label)
                  (msg.(Msg.tid), n)>> /\
     <<VIEW: view_of_eid ex ob (msg.(Msg.tid), n) = Some (S view)>>).
Proof.
  unfold mem_of_ex in IN. exploit nth_error_filter_map_inv; eauto. i. des.
  destruct (Execution.label a ex) eqn:LABEL; ss. destruct t; inv FA; destruct a; ss.
  - esplits; eauto with tso. unfold view_of_eid.
    erewrite List_nth_error_find_pos; eauto. s. f_equal. ss.
  - esplits; eauto with tso. unfold view_of_eid.
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
    exploit label_mem_of_ex; eauto. i. des.

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

    exploit read_msg_exist_ts; eauto with tso. intro X. destruct X as [n]. des.

    assert (READ_STEP: exists res1 local2, Local.read (sem_expr rmap1 eloc) res1 n local1 (mem_of_ex ex ob) local2).
    { esplits. econs; eauto.
      { eapply read_msg_latest_coh; eauto with tso. }
      ii. exploit in_mem_of_ex; swap 1 2; eauto.
      { eapply Permutation_NoDup; [by symmetry; eauto|].
        eapply Execution.eids_spec; eauto.
      }
      i. destruct msg. ss. subst.
      destruct n.
      { (* read from uninit *)
        specialize (FWD eq_refl).
        assert (view < S ts).
        { des. inv WRITING.
          eapply view_of_eid_ob_write; eauto; cycle 1.
          { econs; eauto with tso. }
          destruct (tid == tid0).
          - inv e. left. left. left. left. right. left. econs. split.
            { econs; eauto with tso. }
            econs. split; cycle 1.
            { econs; eauto with tso. }
            destruct (lt_eq_lt_dec (length (ALocal.labels alocal1)) n).
            { inv s; destruct l; ss; try congr. }
            exfalso. exploit EX.(Valid.COWR); ss. instantiate (1 := (tid0, n)).
            econs. split.
            { instantiate (1 := (tid0, length (ALocal.labels alocal1))). econs; auto. }
            right. econs; eauto with tso. econs; eauto with tso. econs; eauto with tso.
          - left. left. left. left. left. left. right. split; ss. right. econs.
            * econs; eauto. econs; eauto with tso.
            * econs; eauto with tso. econs; eauto with tso.
        }
        inv SIM_VRN.
        { rewrite VIEW0 in TS2. inv TS2. }
        unfold ALocal.next_eid in VIEW_OF_EID. rewrite VIEW_OF_EID in VIEW. inv VIEW.
        unfold le in VIEW0. lia.
      }
      exploit MSG; [lia|]. i. des. inv WRITING.
      exploit EX.(Valid.RF1).
      instantiate (1 := (tid, length (ALocal.labels alocal1))).
      instantiate (1 := res0). instantiate (1 := ValA.val (sem_expr rmap1 eloc)).
      { econs; eauto with tso. }
      i. des.
      { contradict NORF. econs. eauto. }
      exploit EX.(Valid.RF_WF); [exact RF|exact RF0|]. i. subst.
      exploit EX.(Valid.CO1).
      { obtac. esplits; econs; [exact EID| |exact EID0|]; eauto with tso. }
      i. des.
      { subst. rewrite VIEW0 in VIEW1. inv VIEW1. lia. }
      { cut (S ts < S n); [lia|].
        eapply view_of_eid_ob_write; eauto.
        { left. left. left. left. left. right. ss. }
        inv LABEL1. esplits; eauto with tso.
      }
      assert (view < S ts).
      { eapply view_of_eid_ob_write; eauto; cycle 1.
        { econs; eauto with tso. }
        destruct (tid == tid0).
        - inv e. left. left. left. left. right. left. econs. split.
          { econs; eauto with tso. }
          econs. split; cycle 1.
          { econs; eauto with tso. }
          destruct (lt_eq_lt_dec (length (ALocal.labels alocal1)) n0).
          { inv s; destruct l; ss; try congr. }
          exfalso. exploit EX.(Valid.COWR); ss. instantiate (1 := (tid0, n0)).
          econs. split.
          { instantiate (1 := (tid0, length (ALocal.labels alocal1))). econs; auto. }
          left. econs; eauto with tso.
        - left. left. left. left. left. left. right. split; ss. left. econs. econs; eauto.
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
      inv SIM_VRN.
      { rewrite VIEW2 in TS2. inv TS2. }
      unfold ALocal.next_eid in VIEW_OF_EID. rewrite VIEW_OF_EID in VIEW. inv VIEW.
      unfold le in VIEW2. lia.
    }
    des. eexists (ExecUnit.mk _ _ _). esplits.
    + econs. econs; ss.
      { econs; ss. }
      econs 2; eauto.
    + generalize READ_STEP. intro X. inv X. unfold le in *.
      rewrite READ in MSG0. inv MSG0.
      econs; ss. econs; ss.
      * (* sim_local coh *)
        i. rewrite List.app_length, Nat.add_1_r.
        rewrite sim_local_coh_step. rewrite inverse_step.
        rewrite inverse_union, fun_add_spec. condtac; cycle 1.
        { eapply sim_view_le; [|exact (SIM_LOCAL.(COH) loc)]. eauto. }
        inversion e. subst. inv WF.
        generalize (Local.read_spec LOCAL READ_STEP); ss.
        rewrite fun_add_spec. condtac; ss. i. des.
        destruct n.
        { econs 1. ss. }
        exploit MSG; [lia|]. i. des.
        exploit EX.(Valid.RF1); eauto with tso. i. des.
        { contradict NORF. econs. eauto. }
        exploit EX.(Valid.RF_WF); [exact RF|exact RF0|]. i. subst. inv LABEL0.
        destruct eid2. ss. destruct (t == tid).
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
        eapply sim_view_le; [|exact SIM_FWD].
        i. subst. right. left. econs; eauto. econs; eauto with tso.
      * (* sim_local vwn *)
        generalize SIM_LOCAL.(VWN). intro COH_MAX. des.
        destruct (lt_eq_lt_dec n (View.ts (Local.coh local1 mloc))).
        { (* <= *)
          eexists mloc. split.
          - i. repeat rewrite fun_add_spec. repeat condtac; ss.
            + viewtac. inv s; lia.
            + inversion e. subst.
              rewrite COH_MAX. ss.
          - rewrite List.app_length, Nat.add_1_r.
            rewrite sim_local_vwn_step. rewrite inverse_step.
            rewrite inverse_union, fun_add_spec. condtac; cycle 1.
            { eapply sim_view_le; [|exact COH_MAX0]. eauto. }
            inversion e. subst. s. inv s; try lia.
            eapply sim_view_le; [|exact COH_MAX0]. eauto.
        }
        { (* > *)
          inv WF; ss.
          exploit Local.high_ts_spec; eauto.
          { i. eapply le_lt_trans; try exact l; eauto. }
          i. des.
          eexists (ValA.val (sem_expr rmap1 eloc)). split.
          - i. repeat rewrite fun_add_spec. repeat condtac; ss; cycle 2.
            { exfalso. apply c0. ss. }
            { exfalso. apply c. ss. }
            rewrite COH_MAX. lia.
          - rewrite List.app_length, Nat.add_1_r.
            rewrite sim_local_vwn_step. rewrite inverse_step.
            rewrite inverse_union, fun_add_spec. condtac; cycle 1; ss.
            { exfalso. apply c. ss. }
            rewrite JOINS with (ValA.val (sem_expr rmap1 eloc)).
            apply sim_view_join.
            + inv COH_MAX0.
              { econs; eauto. apply le_antisym; [| apply bot_spec].
                rewrite COH_MAX. rewrite VIEW0. ss.
              }
              econs 2; try exact VIEW0; eauto.
              rewrite COH_MAX. ss.
            + eapply sim_view_le; [|exact SIM_FWD].
              i. subst. right. econs; eauto. econs; eauto with tso.
        }
      * (* sim_local fwdbank *)
        rewrite List.app_length, Nat.add_1_r. i.
        generalize (SIM_LOCAL.(FWDBANK) loc). i. des.
        { left. esplits; eauto; cycle 1.
          - funtac. inversion e. subst. lia.
          - rewrite sim_local_fwd_step. econs. instantiate (1 := (_, _)). splits; [|econs; ss].
            left. econs. splits; eauto. econs; eauto with tso.
        }
        { right. ii. inv H0. inv REL. inv H0. rewrite Execution.po_po_adj in H2. inv H2. des.
          inv H2. destruct x0. ss. inv N. inv H0.
          - inv H1. inv H2. rewrite LABEL_LEN in EID. inv EID. ss.
          - eapply H. econs; eauto. econs; eauto.
        }
      * (* sim_local promises *)
        i. rewrite SIM_LOCAL.(PROMISES), List.app_length. s. econs; i; des.
        { inv N.
          - inv WRITE. destruct l; ss; congr.
          - esplits; cycle 1; eauto. lia.
        }
        { esplits; cycle 1; eauto. lia. }
      * (* sim_local coh_cl *)
        i. generalize SIM_LOCAL.(COH_CL). intro X. specialize (X loc). des.
        destruct (Loc.cl (ValA.val (sem_expr rmap1 eloc)) mloc_cl) eqn:H_CL; cycle 1.
        { exists mloc_cl. esplits; ss.
          - i. funtac.
            + inversion e. subst. rewrite H_CL in *. ss.
            + inversion e. subst.
              exploit Loc.cl_refl. rewrite H_CL. ss.
          - funtac.
            + inversion e. subst.
              exploit Loc.cl_refl. rewrite H_CL. ss.
            + rewrite List.app_length, Nat.add_1_r.
              rewrite sim_local_coh_cl_step. rewrite inverse_step.
              rewrite inverse_union. eapply sim_view_le; [| exact COH_CL0]. eauto.
        }
        destruct (lt_eq_lt_dec n (View.ts (Local.coh local1 mloc_cl))).
        { (* <= *)
          eexists mloc_cl. splits; ss.
          - i. funtac.
            { inv s; lia. }
            inversion e. subst.
            rewrite COH_MAX_CL; ss.
          - rewrite List.app_length, Nat.add_1_r.
            rewrite sim_local_coh_cl_step. rewrite inverse_step.
            rewrite inverse_union, fun_add_spec. condtac; cycle 1.
            { eapply sim_view_le; [|exact COH_CL0]. eauto. }
            inversion e. subst. s. inv s; try lia.
            eapply sim_view_le; [|exact COH_CL0]. eauto.
        }
        { (* > *)
          inv WF; ss.
          exploit Local.high_ts_spec_cl; eauto.
          { i. eapply le_lt_trans; try exact l; eauto. }
          i. des.
          eexists (ValA.val (sem_expr rmap1 eloc)). splits; ss.
          - eapply Loc.cl_trans; eauto. eapply Loc.cl_sym. ss.
          - i. repeat rewrite fun_add_spec. repeat condtac; ss; cycle 2.
            { exfalso. apply c0. ss. }
            { exfalso. apply c. ss. }
            rewrite COH_MAX_CL; try lia. eapply Loc.cl_trans; eauto.
          - rewrite List.app_length, Nat.add_1_r.
            rewrite sim_local_coh_cl_step. rewrite inverse_step.
            rewrite inverse_union, fun_add_spec. condtac; cycle 1; ss.
            { exfalso. apply c. ss. }
            rewrite JOINS with (ValA.val (sem_expr rmap1 eloc)); ss.
            apply sim_view_join.
            + inv COH_CL0.
              { econs; eauto. apply le_antisym; [| apply bot_spec].
                rewrite COH_MAX_CL. rewrite VIEW0; ss.
                rewrite H_CL. ss.
              }
              econs 2; try exact VIEW0; eauto. rewrite COH_MAX_CL; ss.
            + rewrite NOFWD; [| apply H_CL]. s.
              destruct n.
              { econs 1. ss. }
              exploit MSG; [lia|]. i. des.
              exploit EX.(Valid.RF1); eauto with tso. i. des.
              { contradict NORF. econs. eauto. }
              exploit EX.(Valid.RF_WF); [exact RF|exact RF0|]. i. subst. inv LABEL0.
              exploit Loc.cl_trans; try exact CL; eauto.
              { rewrite Loc.cl_sym; ss. apply H_CL. }
              intro CL0.
              destruct eid2. destruct (t == tid).
              { inv e0.
                econs 2; try exact VIEW0; ss.
                left. econs; eauto. econs. splits.
                - simtac. econs; eauto. destruct l0; ss; eqvtac.
                - econs. splits; eauto.
                  exploit Valid.rfi_is_po; eauto. econs; eauto.
              }
              { econs 2; try exact VIEW0; ss.
                right. econs; eauto. econs. splits.
                - simtac. econs; eauto. destruct l0; ss; eqvtac.
                - econs 2. econs; eauto. econs; eauto.
              }
        }
      * (* sim_local vpr *)
        i. rewrite List.app_length, Nat.add_1_r.
        rewrite sim_local_vpr_step. rewrite inverse_step.
        rewrite ? inverse_union. apply sim_view_join.
        { eapply sim_view_le; [|exact SIM_LOCAL.(VPR)]. eauto. }
        eapply sim_view_le; [|exact SIM_FWD].
        i. subst. right. left. econs; eauto. simtac.
      * (* sim_local vpa *)
        i. rewrite List.app_length, Nat.add_1_r.
        rewrite sim_local_vpa_step. rewrite inverse_step.
        rewrite inverse_union.
        eapply sim_view_le; [|exact (SIM_LOCAL.(VPA) loc)]. eauto.
      * (* sim_local per *)
        i. rewrite List.app_length, Nat.add_1_r.
        rewrite sim_local_vpc_step. rewrite inverse_step.
        rewrite inverse_union.
        eapply sim_view_le; [|exact (SIM_LOCAL.(VPC) loc)]. eauto.
  - (* write *)
    exploit LABEL.
    { rewrite List.nth_error_app2; [|refl]. rewrite Nat.sub_diag. ss. }
    intro LABEL_LEN.
    exploit label_write_mem_of_ex; eauto with tso. i. des.
    generalize (SIM_LOCAL.(VWN)). intro VWN. des.
    assert (WRITABLE_TS: View.ts (Local.coh local1 mloc) < S n).
    { unfold lt. apply le_n_S.
      inv VWN0.
      { rewrite VIEW0. apply bot_spec. }
      rewrite VIEW0. inv EID.
      apply lt_n_Sm_le. eapply view_of_eid_ob_write; eauto.
      - eapply sim_local_vwn_spec; eauto with tso.
      - econs; eauto with tso.
    }
    eexists (ExecUnit.mk _ _ _). esplits.
    + econs. econs; ss.
      { econs; ss. }
      econs 3; ss.
      econs; try refl.
      all: cycle 1.
      { eauto. }
      { rewrite SIM_LOCAL.(PROMISES). esplits; eauto with tso. }
      econs; eauto. econs; ss. econs; ss.
    + econs; ss. econs; ss.
      * i. rewrite List.app_length, Nat.add_1_r.
        rewrite sim_local_coh_step. rewrite inverse_step.
        rewrite inverse_union, fun_add_spec. condtac; ss.
        { inversion e. subst.
          econs 2; eauto; [|refl]. right. econs; eauto.
          econs. splits; eauto. econs; eauto. econs; eauto with tso.
        }
        { eapply sim_view_le; [|exact (SIM_LOCAL.(COH) loc)]. eauto. }
      * rewrite List.app_length, Nat.add_1_r.
        rewrite sim_local_vrn_step. rewrite inverse_step.
        rewrite ? inverse_union. eapply sim_view_le; [|exact SIM_LOCAL.(VRN)]. eauto.
      * eexists (ValA.val (sem_expr rmap1 eloc)). split.
        { i. repeat rewrite fun_add_spec. repeat condtac; ss; cycle 2.
          { exfalso. apply c0. ss. }
          { exfalso. apply c. ss. }
          rewrite VWN. lia.
        }
        rewrite List.app_length, Nat.add_1_r.
        rewrite sim_local_vwn_step. rewrite inverse_step.
        rewrite ? inverse_union, fun_add_spec. condtac; ss; cycle 1.
        { exfalso. apply c. ss. }
        eapply sim_view_le; [by right; eauto|]. econs 2; eauto; ss.
        econs; eauto. econs; eauto with tso.
      * rewrite List.app_length, Nat.add_1_r. i.
        rewrite fun_add_spec. condtac; s; cycle 1.
        { generalize (SIM_LOCAL.(FWDBANK) loc). i. des.
          - left. esplits; eauto. eapply sim_local_fwd_spec; eauto. econs; eauto.
            ii. ss. eqvtac. apply c. ss.
          - right. splits; ss. eapply sim_local_fwd_none_spec; eauto with tso. econs; eauto.
            ii. ss. eqvtac. apply c. ss.
        }
        { inversion e. subst. left. esplits; eauto; [lia |].
          econs; eauto with tso.
          i. destruct eid. inv PO. inv PO0. ss. subst. lia.
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
      * (* sim_local coh_cl *)
        generalize (SIM_LOCAL.(COH_CL)). i. specialize (H loc). des.
        destruct (Loc.cl (ValA.val (sem_expr rmap1 eloc)) mloc_cl) eqn:H_CL; cycle 1.
        { exists mloc_cl. splits; ss.
          - i. funtac.
            + inversion e. subst. rewrite H_CL in *. ss.
            + inversion e. subst.
              exploit Loc.cl_refl. rewrite H_CL. ss.
          - funtac.
            + inversion e. subst.
              exploit Loc.cl_refl. rewrite H_CL. ss.
            + rewrite List.app_length, Nat.add_1_r.
              rewrite sim_local_coh_cl_step. rewrite inverse_step.
              rewrite inverse_union. eapply sim_view_le; [| exact COH_CL0]. eauto.
        }
        exists (ValA.val (sem_expr rmap1 eloc)). splits; ss.
        { eapply Loc.cl_trans; eauto. eapply Loc.cl_sym. ss. }
        { i. funtac. rewrite VWN. lia. }
        rewrite List.app_length, Nat.add_1_r.
        rewrite sim_local_coh_cl_step. rewrite inverse_step.
        rewrite ? inverse_union, fun_add_spec. condtac; ss; cycle 1.
        { exfalso. apply c. ss. }
        eapply sim_view_le; [by right; eauto|]. econs 2; eauto; ss.
        econs; eauto. simtac. econs; eauto. ss.
        eapply Loc.cl_trans; eauto. eapply Loc.cl_sym. ss.
      * (* sim_local vpr *)
        i. rewrite List.app_length, Nat.add_1_r.
        rewrite sim_local_vpr_step. rewrite inverse_step.
        rewrite ? inverse_union. eapply sim_view_le; [by left; eauto|].
        apply SIM_LOCAL.
      * (* sim_local vpa *)
        i. rewrite List.app_length, Nat.add_1_r.
        rewrite sim_local_vpa_step. rewrite inverse_step.
        rewrite inverse_union.
        eapply sim_view_le; [|exact (SIM_LOCAL.(VPA) loc)]. eauto.
      * (* sim_local per *)
        i. rewrite List.app_length, Nat.add_1_r.
        rewrite sim_local_vpc_step. rewrite inverse_step.
        rewrite inverse_union.
        eapply sim_view_le; [|exact (SIM_LOCAL.(VPC) loc)]. eauto.
  - (* rmw *)
    exploit LABEL.
    { rewrite List.nth_error_app2; [|refl]. rewrite Nat.sub_diag. ss. }
    intro LABEL_LEN.
    exploit label_write_mem_of_ex; eauto with tso. i. des.
    exploit read_msg_exist_ts; eauto with tso. intro X. destruct X as [old_ts]. des.

    assert (SIM_EXT1: sim_view ex ob
                               (eq (tid, ALocal.next_eid alocal1))
                               (S n)).
    { econs 2; try exact VIEW; eauto.
      unfold le. lia.
    }

    generalize (SIM_LOCAL.(VWN)). intro VWN. des.
    assert (WRITABLE_TS: View.ts (Local.coh local1 mloc) < S n).
    { unfold lt. apply le_n_S.
      inv VWN0.
      { rewrite VIEW0. apply bot_spec. }
      rewrite VIEW0. inv EID.
      apply lt_n_Sm_le. eapply view_of_eid_ob_write; eauto.
      - eapply sim_local_vwn_spec; eauto with tso.
      - econs; eauto with tso.
    }

    eexists (ExecUnit.mk _ _ _). esplits.
    + econs. econs; ss.
      { econs; ss. instantiate (1 := vnewv). instantiate (1 := voldv). ss. }
      econs 4; ss. instantiate (3 := old_ts).
      econs; try refl; cycle 5.
      { eauto. }
      { rewrite SIM_LOCAL.(PROMISES). esplits; eauto with tso. }
      { eapply read_msg_latest_coh; eauto with tso. }
      { (* old_ts < ts  *)
        destruct old_ts; try lia.
        exploit MSG0; try lia. i. des.
        eapply view_of_eid_ob_write; eauto with tso.
        destruct eid. destruct (t == tid); cycle 1.
        { repeat left. econs; ss. }
        inv e.
        destruct (lt_eq_lt_dec n0 (length (ALocal.labels alocal1))). inv s.
        - (* < *)
          left. left. left. left. right. right. econs. split; cycle 1.
          { econs. split; cycle 1.
            - econs; eauto with tso.
            - instantiate (1 := (tid, n0)). econs; eauto.
          }
          exploit EX.(Valid.RF2); eauto. i. des.
          inv READ1. rewrite LABEL_LEN in EID. destruct l; ss.
          destruct (equiv_dec loc0 loc); ss. inv e.
          destruct (ValA.val (sem_expr armap2 eloc) == loc); try congr. inv e.
          inv WRITE. econs; eauto with tso.
        - (* = *)
          exfalso. exploit EX.(Valid.CORW); eauto. econs. esplits; try exact RF; eauto.
        - (* > *)
          exfalso. exploit EX.(Valid.CORW); eauto. econs. esplits; try exact RF.
          econs 2. econs; eauto.
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
          specialize (FWD eq_refl).
          assert (S n < S ts).
          { des. subst. inv WRITING.
            eapply view_of_eid_ob_write; eauto; cycle 1.
            { econs; eauto with tso. }
            left. left. left. left. left. left. right. split; cycle 1.
            { econs; eauto. }
            right. econs.
            - econs; eauto. econs; eauto with tso.
            - econs; eauto with tso. econs; eauto with tso.
          }
          inv SIM_EXT1; [inv VIEW0|].
          unfold ALocal.next_eid in VIEW_OF_EID. rewrite VIEW_OF_EID in VIEW. inv VIEW.
          unfold le in VIEW0. lia.
        }
        exploit MSG0; [lia|]. i. des. inv WRITING.
        exploit EX.(Valid.RF1).
        instantiate (1 := (tid, length (ALocal.labels alocal1))).
        instantiate (1 := (ValA.val voldv)). instantiate (1 := ValA.val (sem_expr armap2 eloc)).
        { econs; eauto with tso. }
        i. des.
        { contradict NORF. econs. eauto. }
        exploit EX.(Valid.RF_WF); [exact RF|exact RF0|]. i. subst.
        exploit EX.(Valid.CO1).
        { obtac. esplits; econs; [exact EID| |exact EID0|]; eauto with tso. }
        i. des.
        { subst. rewrite VIEW0 in VIEW1. inv VIEW1. lia. }
        { cut (S ts < S old_ts); [lia|].
          eapply view_of_eid_ob_write; eauto.
          { left. left. left. left. left. right. ss. }
          inv LABEL1. esplits; eauto with tso.
        }
        assert (S n < S ts).
        { eapply view_of_eid_ob_write; eauto; cycle 1.
          { econs; eauto with tso. }
          left. left. left. left. left. left. right. split; cycle 1.
          { econs; eauto. }
          left. econs. econs; eauto.
        }
        inv SIM_EXT1.
        { inv VIEW2. }
        unfold ALocal.next_eid in VIEW_OF_EID. rewrite VIEW_OF_EID in VIEW. inv VIEW.
        unfold le in VIEW2. lia.
      }
      { ss. }
      econs; eauto. econs; ss. i. econs; ss.
    + econs; ss. econs; ss.
      * i. rewrite List.app_length, Nat.add_1_r.
        rewrite sim_local_coh_step. rewrite inverse_step.
        rewrite inverse_union, fun_add_spec. condtac; ss.
        { inversion e. subst.
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
      * eexists (ValA.val (sem_expr armap2 eloc)). split.
        { i. repeat rewrite fun_add_spec. repeat condtac; ss; cycle 2.
          { exfalso. apply c0. ss. }
          { exfalso. apply c. ss. }
          rewrite VWN. lia.
        }
        rewrite List.app_length, Nat.add_1_r.
        rewrite sim_local_vwn_step. rewrite inverse_step.
        rewrite ? inverse_union, fun_add_spec. condtac; ss; cycle 1.
        { exfalso. apply c. ss. }
        eapply sim_view_le; [by right; eauto|]. econs 2; eauto; ss.
        econs; eauto. econs; eauto with tso.
      * rewrite List.app_length, Nat.add_1_r. i.
        rewrite fun_add_spec. condtac; s; cycle 1.
        { generalize (SIM_LOCAL.(FWDBANK) loc). i. des.
          - left. esplits; eauto. eapply sim_local_fwd_spec; eauto. econs; eauto.
            ii. ss. eqvtac. apply c. ss.
          - right. splits; ss. eapply sim_local_fwd_none_spec; eauto with tso. econs; eauto.
            ii. ss. eqvtac. apply c. ss.
        }
        { inversion e. subst. left. esplits; eauto; [lia |].
          econs; eauto with tso.
          i. destruct eid. inv PO. inv PO0. ss. subst. lia.
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
      * (* sim_local coh_cl *)
        generalize (SIM_LOCAL.(COH_CL)). i. specialize (H loc). des.
        destruct (Loc.cl (ValA.val (sem_expr armap2 eloc)) mloc_cl) eqn:H_CL; cycle 1.
        { exists mloc_cl. splits; ss.
          - i. funtac.
            + inversion e. subst. rewrite H_CL in *. ss.
            + inversion e. subst.
              exploit Loc.cl_refl. rewrite H_CL. ss.
          - funtac.
            + inversion e. subst.
              exploit Loc.cl_refl. rewrite H_CL. ss.
            + rewrite List.app_length, Nat.add_1_r.
              rewrite sim_local_coh_cl_step. rewrite inverse_step.
              rewrite inverse_union. eapply sim_view_le; [| exact COH_CL0]. eauto.
        }
        exists (ValA.val (sem_expr armap2 eloc)). splits; ss.
        { eapply Loc.cl_trans; eauto. eapply Loc.cl_sym. ss. }
        { i. funtac. rewrite VWN. lia. }
        rewrite List.app_length, Nat.add_1_r.
        rewrite sim_local_coh_cl_step. rewrite inverse_step.
        rewrite ? inverse_union, fun_add_spec. condtac; ss; cycle 1.
        { exfalso. apply c. ss. }
        eapply sim_view_le; [by right; eauto|]. econs 2; eauto; ss.
        econs; eauto. simtac. econs; eauto. ss.
        eapply Loc.cl_trans; eauto. eapply Loc.cl_sym. ss.
      * i. rewrite List.app_length, Nat.add_1_r.
        rewrite sim_local_vpr_step. rewrite inverse_step.
        rewrite ? inverse_union. apply sim_view_join.
        { eapply sim_view_le; [|exact SIM_LOCAL.(VPR)]. eauto. }
        eapply sim_view_le; [|exact SIM_EXT1].
        i. subst. right. left. econs; eauto. simtac.
      * i. rewrite List.app_length, Nat.add_1_r.
        rewrite sim_local_vpa_step. rewrite inverse_step.
        rewrite inverse_union.
        eapply sim_view_le; [|exact (SIM_LOCAL.(VPA) loc)]. eauto.
      * i. rewrite List.app_length, Nat.add_1_r.
        rewrite sim_local_vpc_step. rewrite inverse_step.
        rewrite inverse_union. apply sim_view_join.
        { eapply sim_view_le; [|exact (SIM_LOCAL.(VPC) loc)]. eauto. }
        eapply sim_view_le; [|exact (SIM_LOCAL.(VPA) loc)]. i.
        right. econs; eauto. right.
        inv PR. simtac. econs; eauto. simtac.
  - (* rmw_failure *)
    exploit LABEL.
    { rewrite List.nth_error_app2; [|refl]. rewrite Nat.sub_diag. ss. }
    intro LABEL_LEN.
    exploit label_mem_of_ex; eauto. i. des.
    exploit read_msg_exist_ts; eauto with tso. intro X. destruct X as [n]. des.

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

    inversion RMW. ss.

    assert (RMW_FAIL_STEP: exists local2, Local.rmw_failure (sem_expr rmap1 eloc) (ValA.mk _ res0 bot)  vres n local1 (mem_of_ex ex ob) local2).
    { esplits. econs; eauto.
      { eapply read_msg_latest_coh; eauto with tso. }
      (* external *)
      ii.
      exploit in_mem_of_ex; swap 1 2; eauto.
      { eapply Permutation_NoDup; [by symmetry; eauto|].
        eapply Execution.eids_spec; eauto.
      }
      i. destruct msg. ss. subst.
      destruct n.
      { (* read from uninit *)
        specialize (FWD eq_refl).
        assert (view < S ts).
        { des. inv WRITING.
          eapply view_of_eid_ob_write; eauto; cycle 1.
          { econs; eauto with tso. }
          destruct (tid == tid0).
          - inv e. left. left. left. left. right. left. econs. split.
            { econs; eauto with tso. }
            econs. split; cycle 1.
            { econs; eauto with tso. }
            destruct (lt_eq_lt_dec (length (ALocal.labels alocal1)) n).
            { inv s; destruct l; ss; try congr. }
            exfalso. exploit EX.(Valid.COWR); ss. instantiate (1 := (tid0, n)).
            econs. split.
            { instantiate (1 := (tid0, length (ALocal.labels alocal1))). econs; auto. }
            right. econs; eauto with tso. econs; eauto with tso. econs; eauto with tso.
          - left. left. left. left. left. left. right. split; ss. right. econs.
            * econs; eauto. econs; eauto with tso.
            * econs; eauto with tso. econs; eauto with tso.
        }
        inv SIM_VRN.
        { rewrite VIEW0 in TS2. inv TS2. }
        unfold ALocal.next_eid in VIEW_OF_EID. rewrite VIEW_OF_EID in VIEW. inv VIEW.
        unfold le in VIEW0. lia.
      }
      exploit MSG; [lia|]. i. des. inv WRITING.
      exploit EX.(Valid.RF1).
      instantiate (1 := (tid, length (ALocal.labels alocal1))).
      instantiate (1 := res0). instantiate (1 := ValA.val (sem_expr rmap1 eloc)).
      { econs; eauto with tso. }
      i. des.
      { contradict NORF. econs. eauto. }
      exploit EX.(Valid.RF_WF); [exact RF|exact RF0|]. i. subst.
      exploit EX.(Valid.CO1).
      { obtac. esplits; econs; [exact EID| |exact EID0|]; eauto with tso. }
      i. des.
      { subst. rewrite VIEW0 in VIEW1. inv VIEW1. lia. }
      { cut (S ts < S n); [lia|].
        eapply view_of_eid_ob_write; eauto.
        { left. left. left. left. left. right. ss. }
        inv LABEL1. esplits; eauto with tso.
      }
      assert (view < S ts).
      { eapply view_of_eid_ob_write; eauto; cycle 1.
        { econs; eauto with tso. }
        destruct (tid == tid0).
        - inv e. left. left. left. left. right. left. econs. split.
          { econs; eauto with tso. }
          econs. split; cycle 1.
          { econs; eauto with tso. }
          destruct (lt_eq_lt_dec (length (ALocal.labels alocal1)) n0).
          { inv s; destruct l; ss; try congr. }
          exfalso. exploit EX.(Valid.COWR); ss. instantiate (1 := (tid0, n0)).
          econs. split.
          { instantiate (1 := (tid0, length (ALocal.labels alocal1))). econs; auto. }
          left. econs; eauto with tso.
        - left. left. left. left. left. left. right. split; ss. left. econs. econs; eauto.
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
      inv SIM_VRN.
      { rewrite VIEW2 in TS2. inv TS2. }
      unfold ALocal.next_eid in VIEW_OF_EID. rewrite VIEW_OF_EID in VIEW. inv VIEW.
      unfold le in VIEW2. lia.
    }

    des. eexists (ExecUnit.mk _ _ _). esplits.
    + econs. econs; ss.
      { inv H. econs 6; try exact RMW; ss. }
      inv H0. econs 5; eauto.
    + generalize RMW_FAIL_STEP. intro X. inv X. unfold le in *.
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
        destruct n.
        { econs 1. ss. }
        exploit MSG; [lia|]. i. des.
        exploit EX.(Valid.RF1); eauto with tso. i. des.
        { contradict NORF. econs. eauto. }
        exploit EX.(Valid.RF_WF); [exact RF|exact RF0|]. i. subst. inv LABEL0.
        destruct eid2. ss. destruct (t == tid).
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
        eapply sim_view_le; [|exact SIM_FWD].
        i. subst. right. left. econs; eauto. econs; eauto with tso.
      * (* sim_local vwn *)
        generalize SIM_LOCAL.(VWN). intro COH_MAX. des.
        destruct (lt_eq_lt_dec n (View.ts (Local.coh local1 mloc))).
        { (* <= *)
          eexists mloc. split.
          - i. repeat rewrite fun_add_spec. repeat condtac; ss.
            + viewtac. inv s; lia.
            + inversion e. subst.
              rewrite COH_MAX. ss.
          - rewrite List.app_length, Nat.add_1_r.
            rewrite sim_local_vwn_step. rewrite inverse_step.
            rewrite inverse_union, fun_add_spec. condtac; cycle 1.
            { eapply sim_view_le; [|exact COH_MAX0]. eauto. }
            inversion e. subst. s. inv s; try lia.
            eapply sim_view_le; [|exact COH_MAX0]. eauto.
        }
        { (* > *)
          inv WF; ss.
          exploit Local.high_ts_spec; eauto.
          { i. eapply le_lt_trans; try exact l; eauto. }
          i. des.
          eexists (ValA.val (sem_expr rmap1 eloc)). split.
          - i. repeat rewrite fun_add_spec. repeat condtac; ss; cycle 2.
            { exfalso. apply c0. ss. }
            { exfalso. apply c. ss. }
            rewrite COH_MAX. lia.
          - rewrite List.app_length, Nat.add_1_r.
            rewrite sim_local_vwn_step. rewrite inverse_step.
            rewrite inverse_union, fun_add_spec. condtac; cycle 1; ss.
            { exfalso. apply c. ss. }
            rewrite JOINS with (ValA.val (sem_expr rmap1 eloc)).
            apply sim_view_join.
            + inv COH_MAX0.
              { econs; eauto. apply le_antisym; [| apply bot_spec].
                rewrite COH_MAX. rewrite VIEW0. ss.
              }
              econs 2; try exact VIEW0; eauto.
              rewrite COH_MAX. ss.
            + eapply sim_view_le; [|exact SIM_FWD].
              i. subst. right. econs; eauto. econs; eauto with tso.
        }
      * (* sim_local fwdbank *)
        rewrite List.app_length, Nat.add_1_r. i.
        generalize (SIM_LOCAL.(FWDBANK) loc). i. des.
        { left. esplits; eauto; cycle 1.
          - funtac. inversion e. subst. lia.
          - rewrite sim_local_fwd_step. econs. instantiate (1 := (_, _)). splits; [|econs; ss].
            left. econs. splits; eauto. econs; eauto with tso.
        }
        { right. ii. inv H0. inv REL. inv H0. rewrite Execution.po_po_adj in H2. inv H2. des.
          inv H2. destruct x0. ss. inv N. inv H0.
          - inv H1. inv H2. rewrite LABEL_LEN in EID. inv EID. ss.
          - eapply H. econs; eauto. econs; eauto.
        }
      * (* sim_local promises *)
        i. rewrite SIM_LOCAL.(PROMISES), List.app_length. s. econs; i; des.
        { inv N.
          - inv WRITE. destruct l; ss; congr.
          - esplits; cycle 1; eauto. lia.
        }
        { esplits; cycle 1; eauto. lia. }
      * (* sim_local coh_cl *)
        i. generalize SIM_LOCAL.(COH_CL). intro X. specialize (X loc). des.
        destruct (Loc.cl (ValA.val (sem_expr rmap1 eloc)) mloc_cl) eqn:H_CL; cycle 1.
        { exists mloc_cl. esplits; ss.
          - i. funtac.
            + inversion e. subst. rewrite H_CL in *. ss.
            + inversion e. subst.
              exploit Loc.cl_refl. rewrite H_CL. ss.
          - funtac.
            + inversion e. subst.
              exploit Loc.cl_refl. rewrite H_CL. ss.
            + rewrite List.app_length, Nat.add_1_r.
              rewrite sim_local_coh_cl_step. rewrite inverse_step.
              rewrite inverse_union. eapply sim_view_le; [| exact COH_CL0]. eauto.
        }
        destruct (lt_eq_lt_dec n (View.ts (Local.coh local1 mloc_cl))).
        { (* <= *)
          eexists mloc_cl. splits; ss.
          - i. funtac.
            { inv s; lia. }
            inversion e. subst.
            rewrite COH_MAX_CL; ss.
          - rewrite List.app_length, Nat.add_1_r.
            rewrite sim_local_coh_cl_step. rewrite inverse_step.
            rewrite inverse_union, fun_add_spec. condtac; cycle 1.
            { eapply sim_view_le; [|exact COH_CL0]. eauto. }
            inversion e. subst. s. inv s; try lia.
            eapply sim_view_le; [|exact COH_CL0]. eauto.
        }
        { (* > *)
          inv WF; ss.
          exploit Local.high_ts_spec_cl; eauto.
          { i. eapply le_lt_trans; try exact l; eauto. }
          i. des.
          eexists (ValA.val (sem_expr rmap1 eloc)). splits; ss.
          - eapply Loc.cl_trans; eauto. eapply Loc.cl_sym. ss.
          - i. repeat rewrite fun_add_spec. repeat condtac; ss; cycle 2.
            { exfalso. apply c0. ss. }
            { exfalso. apply c. ss. }
            rewrite COH_MAX_CL; try lia. eapply Loc.cl_trans; eauto.
          - rewrite List.app_length, Nat.add_1_r.
            rewrite sim_local_coh_cl_step. rewrite inverse_step.
            rewrite inverse_union, fun_add_spec. condtac; cycle 1; ss.
            { exfalso. apply c. ss. }
            rewrite JOINS with (ValA.val (sem_expr rmap1 eloc)); ss.
            apply sim_view_join.
            + inv COH_CL0.
              { econs; eauto. apply le_antisym; [| apply bot_spec].
                rewrite COH_MAX_CL. rewrite VIEW0; ss.
                rewrite H_CL. ss.
              }
              econs 2; try exact VIEW0; eauto. rewrite COH_MAX_CL; ss.
            + rewrite NOFWD; [| apply H_CL]. s.
              destruct n.
              { econs 1. ss. }
              exploit MSG; [lia|]. i. des.
              exploit EX.(Valid.RF1); eauto with tso. i. des.
              { contradict NORF. econs. eauto. }
              exploit EX.(Valid.RF_WF); [exact RF|exact RF0|]. i. subst. inv LABEL0.
              exploit Loc.cl_trans; try exact CL; eauto.
              { rewrite Loc.cl_sym; ss. apply H_CL. }
              intro CL0.
              destruct eid2. destruct (t == tid).
              { inv e0.
                econs 2; try exact VIEW0; ss.
                left. econs; eauto. econs. splits.
                - simtac. econs; eauto. destruct l0; ss; eqvtac.
                - econs. splits; eauto.
                  exploit Valid.rfi_is_po; eauto. econs; eauto.
              }
              { econs 2; try exact VIEW0; ss.
                right. econs; eauto. econs. splits.
                - simtac. econs; eauto. destruct l0; ss; eqvtac.
                - econs 2. econs; eauto. econs; eauto.
              }
        }
      * (* sim_local vpr *)
        i. rewrite List.app_length, Nat.add_1_r.
        rewrite sim_local_vpr_step. rewrite inverse_step.
        rewrite ? inverse_union. apply sim_view_join.
        { eapply sim_view_le; [|exact SIM_LOCAL.(VPR)]. eauto. }
        eapply sim_view_le; [|exact SIM_FWD].
        i. subst. right. left. econs; eauto. simtac.
      * (* sim_local vpa *)
        i. rewrite List.app_length, Nat.add_1_r.
        rewrite sim_local_vpa_step. rewrite inverse_step.
        rewrite inverse_union.
        eapply sim_view_le; [|exact (SIM_LOCAL.(VPA) loc)]. eauto.
      * (* sim_local per *)
        i. rewrite List.app_length, Nat.add_1_r.
        rewrite sim_local_vpc_step. rewrite inverse_step.
        rewrite inverse_union.
        eapply sim_view_le; [|exact (SIM_LOCAL.(VPC) loc)]. eauto.
  - (* mfence *)
    exploit LABEL.
    { rewrite List.nth_error_app2; ss. rewrite Nat.sub_diag. ss. }
    intro LABEL_LEN.
    generalize (SIM_LOCAL.(VWN)). intro VWN. des.
    eexists (ExecUnit.mk _ _ _). splits.
    { econs. econs; ss.
      - econs; ss.
      - econs 6; ss. econs; ss. econs; ss. econs; ss.
    }
    econs; ss. econs; ss.
    + rewrite List.app_length, Nat.add_1_r. s.
      i. rewrite sim_local_coh_step. rewrite inverse_step.
      rewrite inverse_union. eapply sim_view_le; [by left; eauto|].
      apply SIM_LOCAL.
    + rewrite List.app_length, Nat.add_1_r. s.
      rewrite sim_local_vrn_step. rewrite inverse_step.
      rewrite ? inverse_union. repeat apply sim_view_join; eauto using sim_view_bot.
      { eapply sim_view_le; [|exact SIM_LOCAL.(VRN)]. eauto. }
      eapply sim_view_le; [|exact VWN0]. i. inv PR. inv REL. des.
      right. right. rewrite seq_assoc.
      econs; eauto. econs. splits; econs; eauto with tso.
    + eexists mloc. split; ss.
      rewrite List.app_length, Nat.add_1_r. s.
      rewrite sim_local_vwn_step. rewrite inverse_step.
      rewrite ? inverse_union. repeat apply sim_view_join; eauto using sim_view_bot.
      eapply sim_view_le; [|exact VWN0]. eauto.
    + rewrite List.app_length, Nat.add_1_r. i.
      generalize (SIM_LOCAL.(FWDBANK) loc). i. des.
      { left. esplits; eauto. eapply sim_local_fwd_spec; eauto with tso. }
      { right. splits; ss. eapply sim_local_fwd_none_spec; eauto with tso. }
    + i. rewrite SIM_LOCAL.(PROMISES), List.app_length. s. econs; i; des.
      { inv N.
        - inv WRITE. destruct l; ss; congr.
        - esplits; cycle 1; eauto. lia.
      }
      { esplits; cycle 1; eauto. lia. }
    + i. generalize (SIM_LOCAL.(COH_CL)). intro H. specialize (H loc). des.
      exists mloc_cl. splits; ss.
      rewrite List.app_length, Nat.add_1_r. s.
      rewrite sim_local_coh_cl_step. rewrite inverse_step.
      rewrite ? inverse_union. eapply sim_view_le; [|exact COH_CL0]. eauto.
    + i. rewrite List.app_length, Nat.add_1_r.
      rewrite sim_local_vpr_step. rewrite inverse_step.
      rewrite inverse_union. apply sim_view_join.
      { eapply sim_view_le; [|exact SIM_LOCAL.(VPR)]. eauto. }
      eapply sim_view_le; [|exact VWN0]. i.
      right. econs; eauto.
      inv PR. inv REL. obtac.
      right. simtac. left. simtac.
    + i. rewrite List.app_length, Nat.add_1_r.
      rewrite sim_local_vpa_step. rewrite inverse_step.
      rewrite inverse_union.
      eapply sim_view_le; [|exact (SIM_LOCAL.(VPA) loc)]. eauto.
    + i. rewrite List.app_length, Nat.add_1_r.
      rewrite sim_local_vpc_step. rewrite inverse_step.
      rewrite inverse_union. apply sim_view_join.
      { eapply sim_view_le; [|exact (SIM_LOCAL.(VPC) loc)]. eauto. }
      eapply sim_view_le; [|exact (SIM_LOCAL.(VPA) loc)]. i.
      right. econs; eauto. right.
      inv PR. econs. econs; eauto. simtac.
  - (* sfence *)
    exploit LABEL.
    { rewrite List.nth_error_app2; ss. rewrite Nat.sub_diag. ss. }
    intro LABEL_LEN.
    generalize (SIM_LOCAL.(VWN)). intro VWN. des.
    eexists (ExecUnit.mk _ _ _). splits.
    { econs. econs; ss.
      - econs; ss.
      - econs 7; ss. econs; ss. econs; ss. econs; ss.
    }
    econs; ss. econs; ss.
    + rewrite List.app_length, Nat.add_1_r. s.
      i. rewrite sim_local_coh_step. rewrite inverse_step.
      rewrite inverse_union. eapply sim_view_le; [by left; eauto|].
      apply SIM_LOCAL.
    + rewrite List.app_length, Nat.add_1_r. s.
      rewrite sim_local_vrn_step. rewrite inverse_step.
      rewrite inverse_union. eapply sim_view_le; [by left; eauto|].
      apply SIM_LOCAL.
    + eexists mloc. split; ss.
      rewrite List.app_length, Nat.add_1_r. s.
      rewrite sim_local_vwn_step. rewrite inverse_step.
      rewrite ? inverse_union. repeat apply sim_view_join; eauto using sim_view_bot.
      eapply sim_view_le; [|exact VWN0]. eauto.
    + rewrite List.app_length, Nat.add_1_r. i.
      generalize (SIM_LOCAL.(FWDBANK) loc). i. des.
      { left. esplits; eauto. eapply sim_local_fwd_spec; eauto with tso. }
      { right. splits; ss. eapply sim_local_fwd_none_spec; eauto with tso. }
    + i. rewrite SIM_LOCAL.(PROMISES), List.app_length. s. econs; i; des.
      { inv N.
        - inv WRITE. destruct l; ss; congr.
        - esplits; cycle 1; eauto. lia.
      }
      { esplits; cycle 1; eauto. lia. }
    + i. generalize (SIM_LOCAL.(COH_CL)). intro H. specialize (H loc). des.
      exists mloc_cl. splits; ss.
      rewrite List.app_length, Nat.add_1_r. s.
      rewrite sim_local_coh_cl_step. rewrite inverse_step.
      rewrite ? inverse_union. eapply sim_view_le; [|exact COH_CL0]. eauto.
    + i. rewrite List.app_length, Nat.add_1_r.
      rewrite sim_local_vpr_step. rewrite inverse_step.
      rewrite inverse_union. apply sim_view_join.
      { eapply sim_view_le; [|exact SIM_LOCAL.(VPR)]. eauto. }
      eapply sim_view_le; [|exact VWN0]. i.
      right. econs; eauto.
      inv PR. inv REL. obtac.
      right. simtac. right. simtac.
    + i. rewrite List.app_length, Nat.add_1_r.
      rewrite sim_local_vpa_step. rewrite inverse_step.
      rewrite inverse_union.
      eapply sim_view_le; [|exact (SIM_LOCAL.(VPA) loc)]. eauto.
    + i. rewrite List.app_length, Nat.add_1_r.
      rewrite sim_local_vpc_step. rewrite inverse_step.
      rewrite inverse_union. apply sim_view_join.
      { eapply sim_view_le; [|exact (SIM_LOCAL.(VPC) loc)]. eauto. }
      eapply sim_view_le; [|exact (SIM_LOCAL.(VPA) loc)]. i.
      right. econs; eauto. right.
      inv PR. econs. econs; eauto. simtac.
  - (* dowhile *)
    eexists (ExecUnit.mk _ _ _). esplits.
    + econs. econs; ss; econs; ss.
    + econs; ss.
      inv SIM_LOCAL; econs; eauto.
  - (* flushopt *)
    exploit LABEL.
    { rewrite List.nth_error_app2; ss. rewrite Nat.sub_diag. ss. }
    intro LABEL_LEN.
    generalize (SIM_LOCAL.(VWN)). intro VWN. des.
    generalize (SIM_LOCAL.(COH_CL)). intro H. specialize (H (ValA.val (sem_expr armap2 eloc))). des.
    eexists (ExecUnit.mk _ _ _). splits.
    { econs. econs; ss.
      - econs; ss.
      - econs 9; ss. econs; ss. econs; ss. econs; ss.
        unfold ifc. condtac; [| apply bot_spec]. rewrite CL. rewrite COH_MAX_CL; ss.
        eapply Loc.cl_trans; eauto. eapply Loc.cl_sym. ss.
    }
    econs; ss. econs; ss.
    + rewrite List.app_length, Nat.add_1_r. s.
      i. rewrite sim_local_coh_step. rewrite inverse_step.
      rewrite inverse_union. eapply sim_view_le; [by left; eauto|].
      apply SIM_LOCAL.
    + rewrite List.app_length, Nat.add_1_r. s.
      rewrite sim_local_vrn_step. rewrite inverse_step.
      rewrite ? inverse_union. repeat apply sim_view_join; eauto using sim_view_bot.
      eapply sim_view_le; [|exact SIM_LOCAL.(VRN)]. eauto.
    + eexists mloc. split; ss.
      rewrite List.app_length, Nat.add_1_r. s.
      rewrite sim_local_vwn_step. rewrite inverse_step.
      rewrite ? inverse_union. repeat apply sim_view_join; eauto using sim_view_bot.
      eapply sim_view_le; [|exact VWN0]. eauto.
    + rewrite List.app_length, Nat.add_1_r. i.
      generalize (SIM_LOCAL.(FWDBANK) loc). i. des.
      { left. esplits; eauto. eapply sim_local_fwd_spec; eauto with tso. }
      { right. splits; ss. eapply sim_local_fwd_none_spec; eauto with tso. }
    + i. rewrite SIM_LOCAL.(PROMISES), List.app_length. s. econs; i; des.
      { inv N.
        - inv WRITE. destruct l; ss; congr.
        - esplits; cycle 1; eauto. lia.
      }
      { esplits; cycle 1; eauto. lia. }
    + i. generalize (SIM_LOCAL.(COH_CL)). intro H. specialize (H loc). des.
      exists mloc_cl0. splits; ss.
      rewrite List.app_length, Nat.add_1_r. s.
      rewrite sim_local_coh_cl_step. rewrite inverse_step.
      rewrite ? inverse_union. eapply sim_view_le; [|exact COH_CL1]. eauto.
    + i. rewrite List.app_length, Nat.add_1_r.
      rewrite sim_local_vpr_step. rewrite inverse_step.
      rewrite ? inverse_union.
      eapply sim_view_le; [|exact SIM_LOCAL.(VPR)]. eauto.
    + i. rewrite List.app_length, Nat.add_1_r.
      rewrite sim_local_vpa_step. rewrite inverse_step.
      rewrite inverse_union.
      apply sim_view_join.
      { eapply sim_view_le; [|exact (SIM_LOCAL.(VPA) loc)]. eauto. }
      unfold ifc. condtac; [|econs]; ss. condtac; [|econs]; ss.
      apply sim_view_join.
      * hexploit label_mem_of_ex; eauto. i. des.
        econs 2; eauto.
        { right. econs; ss. right. simtac. econs; eauto. ss. apply Loc.cl_sym. ss. }
        inv COH_CL0.
        { rewrite VIEW0. apply bot_spec. }
        etrans; eauto.
        inv EID. inv REL. obtac. inv H1.
        { eapply view_of_eid_ob; eauto. destruct l; ss.
          - left. left. right. right. simtac.
            econs; ss. econs; eauto. econs; eauto with tso. apply Loc.cl_sym. ss.
          - left. left. right. left. right. simtac. split; simtac.
            left. simtac.
        }
        obtac. exploit EX.(Valid.RF2); eauto. i. des. obtac. labtac.
        hexploit label_mem_of_ex; eauto. i. des.
        etrans; eapply view_of_eid_ob; eauto.
        { repeat left. econs; ss. }
        left. left. right. left. right. simtac. split; simtac.
        left. simtac.
      * hexploit label_mem_of_ex; eauto. i. des.
        econs 2; eauto.
        { right. econs; ss. right. simtac. econs; eauto. ss. apply Loc.cl_sym. ss. }
        generalize (SIM_LOCAL.(VPR)). intro Z. inv Z.
        { rewrite VIEW0. apply bot_spec. }
        etrans; eauto. eapply view_of_eid_ob; eauto.
        inv EID. inv REL.
        { obtac. left. left. right. left. right. simtac. split; simtac. left. simtac. }
        inv H. des. inv H1. des. inv H1. des. rename H2 into PBAR. guardH PBAR. obtac.
        destruct (Label.is_kinda_read l) eqn:READ.
        { assert (PO: Execution.po x (tid, length (ALocal.labels alocal1))).
          { rewrite H. inv PBAR; obtac; ss. }
          left. left. right. left. right.
          econs. split; cycle 1.
          { econs. split; simtac. eauto. }
          left. simtac.
        }
        destruct l; ss.
        left. left. right. left. right.
        econs. split; cycle 1.
        { econs. split; simtac. eauto. }
        right. simtac.
    + i. rewrite List.app_length, Nat.add_1_r.
      rewrite sim_local_vpc_step. rewrite inverse_step.
      rewrite inverse_union.
      eapply sim_view_le; [|exact (SIM_LOCAL.(VPC) loc)]. eauto.
  - (* flush *)
    exploit LABEL.
    { rewrite List.nth_error_app2; ss. rewrite Nat.sub_diag. ss. }
    intro LABEL_LEN.
    generalize (SIM_LOCAL.(VWN)). intro VWN. des.
    eexists (ExecUnit.mk _ _ _). splits.
    { econs. econs; ss.
      - econs; ss.
      - econs 8; ss. econs; ss. econs; ss. econs; ss.
    }
    econs; ss. econs; ss.
    + rewrite List.app_length, Nat.add_1_r. s.
      i. rewrite sim_local_coh_step. rewrite inverse_step.
      rewrite inverse_union. eapply sim_view_le; [by left; eauto|].
      apply SIM_LOCAL.
    + rewrite List.app_length, Nat.add_1_r. s.
      rewrite sim_local_vrn_step. rewrite inverse_step.
      rewrite ? inverse_union. repeat apply sim_view_join; eauto using sim_view_bot.
      eapply sim_view_le; [|exact SIM_LOCAL.(VRN)]. eauto.
    + eexists mloc. split; ss.
      rewrite List.app_length, Nat.add_1_r. s.
      rewrite sim_local_vwn_step. rewrite inverse_step.
      rewrite ? inverse_union. repeat apply sim_view_join; eauto using sim_view_bot.
      eapply sim_view_le; [|exact VWN0]. eauto.
    + rewrite List.app_length, Nat.add_1_r. i.
      generalize (SIM_LOCAL.(FWDBANK) loc). i. des.
      { left. esplits; eauto. eapply sim_local_fwd_spec; eauto with tso. }
      { right. splits; ss. eapply sim_local_fwd_none_spec; eauto with tso. }
    + i. rewrite SIM_LOCAL.(PROMISES), List.app_length. s. econs; i; des.
      { inv N.
        - inv WRITE. destruct l; ss; congr.
        - esplits; cycle 1; eauto. lia.
      }
      { esplits; cycle 1; eauto. lia. }
    + i. generalize (SIM_LOCAL.(COH_CL)). intro H. specialize (H loc). des.
      exists mloc_cl. splits; ss.
      rewrite List.app_length, Nat.add_1_r. s.
      rewrite sim_local_coh_cl_step. rewrite inverse_step.
      rewrite ? inverse_union. eapply sim_view_le; [|exact COH_CL0]. eauto.
    + i. rewrite List.app_length, Nat.add_1_r.
      rewrite sim_local_vpr_step. rewrite inverse_step.
      rewrite ? inverse_union.
      eapply sim_view_le; [|exact SIM_LOCAL.(VPR)]. eauto.
    + i. rewrite List.app_length, Nat.add_1_r.
      rewrite sim_local_vpa_step. rewrite inverse_step.
      rewrite inverse_union. apply sim_view_join.
      { eapply sim_view_le; [|exact (SIM_LOCAL.(VPA) loc)]. eauto. }
      unfold ifc. condtac; [|econs]; ss.
      hexploit label_mem_of_ex; eauto. i. des.
      econs 2; eauto.
      { right. econs; ss. left. simtac. econs; eauto. ss. apply Loc.cl_sym. ss. }
      inv VWN0.
      { rewrite VIEW0. apply bot_spec. }
      etrans; eauto. eapply view_of_eid_ob; eauto.
      inv EID. inv REL. obtac.
      left. left. right. repeat left. simtac.
    + i. rewrite List.app_length, Nat.add_1_r.
      rewrite sim_local_vpc_step. rewrite inverse_step.
      rewrite inverse_union. apply sim_view_join.
      { eapply sim_view_le; [|exact (SIM_LOCAL.(VPC) loc)]. eauto. }
      unfold ifc. condtac; [|econs]; ss.
      hexploit label_mem_of_ex; eauto. i. des.
      econs 2; eauto.
      { right. econs; ss. left. simtac. econs; eauto. apply Loc.cl_sym. ss. }
      inv VWN0.
      { rewrite VIEW0. apply bot_spec. }
      rewrite VIEW0. eapply view_of_eid_ob; eauto.
      inv EID. inv REL. obtac.
      left. left. right. repeat left. simtac.
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
      p ex smem
      (EX: Valid.ex p ex)
      (PMEM: Valid.persisted ex smem):
  exists m,
    <<STEP: Machine.exec p m>> /\
    <<TERMINAL: Valid.is_terminal EX -> Machine.is_terminal m>> /\
    <<STATE: IdMap.Forall2
               (fun tid sl aeu => sim_state_weak (fst sl) aeu.(AExecUnit.state))
               m.(Machine.tpool) EX.(Valid.aeus)>> /\
    <<MEM: sim_mem ex m.(Machine.mem)>> /\
    <<PMEM: Machine.persisted m smem>>.
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
          <<MEM: sim_mem ex (Machine.mem m0)>> /\
          <<PMEM: Machine.persisted m0 smem>>).
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
                   Local.init_with_promises (Promises.promises_from_mem tid (Machine.mem m)))).
  { i. rewrite TPOOL, FIND1, MEM0. ss. }
  assert (OUT: forall tid st lc
                 (FIND1: IdMap.find tid p = None)
                 (FIND2: IdMap.find tid m.(Machine.tpool) = Some (st, lc)),
             exists aeu,
               <<AEU: IdMap.find tid EX.(Valid.aeus) = Some aeu>> /\
               <<STATE: sim_state_weak st aeu.(AExecUnit.state)>> /\
               <<PROMISE: lc.(Local.promises) = bot>> /\
               <<PMEM: forall loc view
                              (PVIEW: persisted_event_view ex ob loc view),
                        Memory.latest loc view (lc.(Local.vpc) loc).(View.ts) m.(Machine.mem)>>).
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
    - ii. specialize (PMEM loc). inv PMEM.
      + assert (ZERO: Memory.read loc 0 m.(Machine.mem) = Some (smem loc)).
        { rewrite UNINIT. ss. }
        econs; eauto.
        intros tid [st0 lc0]. i. s. hexploit OUT; eauto. i. des.
        eapply PMEM; eauto.
      + exploit label_write_mem_of_ex; eauto with tso. i. des.
        rewrite <- MEM0 in *. econs; eauto.
        intros tid [st0 lc0]. i. s.
        hexploit OUT; eauto. i. des.
        eapply PMEM; eauto. econs 2; eauto.
        obtac. simtac.
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
                         (Local.init_with_promises (Promises.promises_from_mem tid (Machine.mem m)))
                         (Machine.mem m))
                      (ExecUnit.mk st2 lc2 (Machine.mem m))>> /\
          <<TERMINAL: Valid.is_terminal EX -> State.is_terminal st2>> /\
          <<AEU: IdMap.find tid EX.(Valid.aeus) = Some aeu>> /\
          <<STATE: sim_state_weak st2 aeu.(AExecUnit.state)>> /\
          <<NOPROMISE: lc2.(Local.promises) = bot>> /\
          <<PMEM: forall loc view
                         (PVIEW: persisted_event_view ex ob loc view),
                  Memory.latest loc view (lc2.(Local.vpc) loc).(View.ts) m.(Machine.mem)>>).
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
                        (Local.init_with_promises (Promises.promises_from_mem tid (mem_of_ex ex ob)))
                        (mem_of_ex ex ob)).
    econs; ss. econs; eauto.
    - exists Loc.default. eauto.
    - right. splits; ss. ii. inv H. inv REL1. inv H. inv H1. ss. lia.
    - econs; i.
      { destruct view; ss. apply Promises.promises_from_mem_spec in H. des.
        exploit in_mem_of_ex; swap 1 2; eauto.
        { eapply Permutation_NoDup; [by symmetry; eauto|].
        eapply Execution.eids_spec; eauto.
        }
        s. i. des. inv WRITING.
        esplits; cycle 1; eauto with tso. lia.
      }
      { des. inv WRITE.
        destruct l; ss; exploit label_write_mem_of_ex; eauto with tso.
        - i. des.
          rewrite VIEW in VIEW0. inv VIEW0.
          unfold Memory.get_msg in MSG. ss. apply Promises.promises_from_mem_spec. eauto.
        - i. des.
          rewrite VIEW in VIEW0. inv VIEW0.
          unfold Memory.get_msg in MSG. ss. apply Promises.promises_from_mem_spec. eauto.
      }
    - i. exists loc. splits; eauto. eapply Loc.cl_refl.
  }
  { clear. econs; ss.
    econs; ss; i; try by apply bot_spec.
    - econs; esplits; ss.
    - destruct ts; ss.
      rewrite Promises.promises_from_mem_spec in IN. des.
      apply lt_le_S. rewrite <- List.nth_error_Some. ii. congr.
    - destruct ts; ss.
      unfold Memory.get_msg in MSG. ss. destruct msg. ss. subst.
      apply Promises.promises_from_mem_lookup in MSG. auto.
    - econs; viewtac; try by i; apply bot_spec.
      econs; ss. instantiate (1 := Loc.default). econs; ss.
    - rewrite TS. ss.
    - left. apply bot_spec.
  }
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
  - i. generalize LOCAL.(VPC). intro SIM_VPC. specialize (SIM_VPC loc). inv SIM_VPC.
    { rewrite VIEW. unfold bot. unfold Time.bot. ii. lia. }
    unfold le in *. ii. exploit in_mem_of_ex; try exact MSG.
    { generalize (Execution.eids_spec ex). i. des.
      symmetry in PERM. eapply HahnList.Permutation_nodup; eauto.
    }
    i. des. inv WRITING. destruct msg as [loc val tid0]; ss.

    cut (exists feid fview,
          <<FEID: Execution.label_is ex (fun l => Label.is_persisting_cl loc l) feid>> /\
          <<FVIEW: view_of_eid ex ob feid = Some fview>> /\
          <<SIM2FL: v <= fview>> /\
          <<FLUSHOPT:
              Execution.label_is ex (fun l => Label.is_flushopting_cl loc l) feid ->
              (exists beid,
                <<PO: Execution.po feid beid>> /\
                <<BARRIER: Execution.label_is ex (fun l => Label.is_persist_barrier l) beid>>)>>).
    { i. des. obtac.
      cut (Execution.fp ex feid (tid0, n)).
      { i.
        cut (fview < S ts).
        { i. lia. }
        eapply view_of_eid_ob_write; eauto with tso. right. ss.
      }
      exploit EX.(Valid.PF1); eauto with tso. i. des.
      { right. simtac. }
      cut (view_of_eid ex ob eid2 = Some view).
      { i.
        assert (Execution.co ex eid2 (tid0, n)).
        { eapply view_of_eid_co; eauto with tso. }
        left. econs; eauto.
      }
      assert (PERSISTED: Valid.persisted_event ex loc eid2).
      { econs; eauto. obtac. destruct l0; ss; eqvtac.
        { econs. econs. simtac. left. simtac. }
        exploit FLUSHOPT; eauto with tso. i. des.
        econs. econs. simtac. right. simtac.
      }
      inv PVIEW.
      { exfalso. eapply NPER. eauto. }
      obtac. exploit label_mem_of_ex; try exact EID2; eauto. i. des.
      exploit EX.(Valid.CO1).
      { esplits; econs; [try exact EID3 | | try exact EID2|]; eauto with tso. }
      i. des.
      - subst. ss.
      - hexploit VPC0; eauto. intro Z. inv Z; ss.
        exfalso. eapply EX.(Valid.EXTERNAL).
        econs 2; econs; left; left; left; left; left; right; eauto.
      - cut (fview < view).
        { i. lia. }
        eapply view_of_eid_ob_write; eauto with tso.
        right. left. econs; eauto.
    }

    inv EID. inv REL1; obtac.
    + esplits; eauto with tso.
      i. obtac. labtac. destruct l1; ss.
    + inv H0; obtac; esplits; eauto with tso.
Qed.
