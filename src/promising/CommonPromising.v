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

Set Implicit Arguments.


Module Msg.
  Inductive t := mk {
    loc: Loc.t;
    val: Val.t;
    tid: Id.t;
  }.
  Hint Constructors t.

  Global Program Instance eqdec: EqDec t eq.
  Next Obligation.
    destruct x, y.

    destruct (loc0 == loc1); cycle 1.
    { right. intro X. inv X. intuition. }

    destruct (val0 == val1); cycle 1.
    { right. intro X. inv X. intuition. }

    destruct (tid0 == tid1); cycle 1.
    { right. intro X. inv X. intuition. }

    left. f_equal; intuition.
  Defined.
End Msg.

Module Memory.
  Definition t := list Msg.t.

  Definition empty: t := [].

  Definition read (loc:Loc.t) (ts:Time.t) (mem:t): option Val.t :=
    match Time.pred_opt ts with
    | None => Some Val.default
    | Some ts =>
      match List.nth_error mem ts with
      | None => None
      | Some msg =>
        if msg.(Msg.loc) == loc
        then Some msg.(Msg.val)
        else None
      end
    end.

  Definition get_msg (ts:Time.t) (mem:t): option Msg.t :=
    match Time.pred_opt ts with
    | None => None
    | Some ts => List.nth_error mem ts
    end.

  Definition append (msg:Msg.t) (mem:t): Time.t * t :=
    (S (length mem), mem ++ [msg]).

  Definition no_msgs (from to:nat) (pred:Msg.t -> Prop) (mem:t): Prop :=
    forall ts msg
      (TS1: from < S ts)
      (TS2: S ts <= to)
      (MSG: List.nth_error mem ts = Some msg),
      ~ pred msg.

  Definition latest (loc:Loc.t) (from to:Time.t) (mem:t): Prop :=
    Memory.no_msgs from to (fun msg => msg.(Msg.loc) = loc) mem.

  Fixpoint latest_ts (loc:Loc.t) (to:Time.t) (mem:t): Time.t :=
    match to with
    | O => O
    | S to =>
      match List.nth_error mem to with
      | Some (Msg.mk loc0 _ _) =>
        if (Loc.eq_dec loc0 loc) then S to else latest_ts loc to mem
      | _ => latest_ts loc to mem
      end
    end
  .

  Definition exclusive (tid:Id.t) (loc:Loc.t) (from to:Time.t) (mem:t): Prop :=
    Memory.no_msgs from to (fun msg => msg.(Msg.loc) = loc /\ msg.(Msg.tid) <> tid) mem.

  Lemma read_mon ts loc val mem1 mem2
        (READ: Memory.read loc ts mem1 = Some val):
    Memory.read loc ts (mem1 ++ mem2) = Some val.
  Proof.
    revert READ. unfold Memory.read. destruct (Time.pred_opt ts); ss.
    destruct (nth_error mem1 t0) eqn:NTH; ss.
    rewrite nth_error_app1, NTH; ss.
    apply List.nth_error_Some. congr.
  Qed.

  Lemma get_msg_mon ts msg mem1 mem2
        (READ: Memory.get_msg ts mem1 = Some msg):
    Memory.get_msg ts (mem1 ++ mem2) = Some msg.
  Proof.
    revert READ. unfold Memory.get_msg. destruct (Time.pred_opt ts); ss.
    destruct (nth_error mem1 t0) eqn:NTH; ss.
    rewrite nth_error_app1, NTH; ss.
    apply List.nth_error_Some. congr.
  Qed.

  Lemma get_msg_read ts mem loc val tid
        (GET: get_msg ts mem = Some (Msg.mk loc val tid)):
    read loc ts mem = Some val.
  Proof.
    destruct ts; ss.
    unfold get_msg, read in *. ss.
    rewrite GET. ss. des_ifs. exfalso. apply c. ss.
  Qed.

  Lemma read_get_msg
        loc ts mem val
        (READ: read loc ts mem = Some val):
    (ts = Time.bot /\ val = Val.default) \/
    (exists tid, get_msg ts mem = Some (Msg.mk loc val tid)).
  Proof.
    revert READ. unfold read, get_msg. destruct ts; ss.
    - i. inv READ. left. eauto.
    - destruct (List.nth_error mem ts); ss. des_ifs. i. inv READ. inv e.
      destruct t0. s. right. eauto.
  Qed.

  Lemma get_msg_app_inv
        ts mem1 mem2 m
        (GET: get_msg ts (mem1 ++ mem2) = Some m):
    (ts <= length mem1 /\ get_msg ts mem1 = Some m) \/
    (ts > length mem1 /\ List.nth_error mem2 (ts - (S (length mem1))) = Some m).
  Proof.
    unfold get_msg in *. destruct ts; ss.
    destruct (lt_dec ts (length mem1)).
    - rewrite nth_error_app1 in GET; eauto.
    - rewrite nth_error_app2 in GET; [|lia]. right. splits; ss. lia.
  Qed.

  Lemma get_msg_snoc_inv
        ts mem msg m
        (GET: get_msg ts (mem ++ [msg]) = Some m):
    (ts <= length mem /\ get_msg ts mem = Some m) \/
    (ts = S (length mem) /\ msg = m).
  Proof.
    exploit get_msg_app_inv; eauto. i. des; [left|right]; ss.
    destruct ts; ss.
    destruct (ts - length mem) eqn:SUB; ss.
    - assert (ts = length mem) by lia. inv x1. ss.
    - destruct n; ss.
  Qed.

  Lemma get_latest
        loc mem:
    exists ts val,
      (forall ts' val (READ: read loc ts' mem = Some val), ts' <= ts) /\
      read loc ts mem = Some val.
  Proof.
    induction mem using List.rev_ind.
    { exists 0, Val.default. splits; ss. i. destruct ts'; ss. destruct ts'; ss. }
    destruct (loc == x.(Msg.loc)).
    { inversion e. subst. exists (S (length mem)), x.(Msg.val). splits.
      - i. unfold read in READ. destruct ts'; [lia|]. ss.
        destruct (nth_error (mem ++ [x]) ts') eqn:NTH; ss.
        apply nth_error_snoc_inv in NTH. des; [lia|]. subst. ss.
      - unfold read. ss. rewrite nth_error_app2, Nat.sub_diag; ss. condtac; ss.
    }
    des. exists ts, val. splits.
    - ii. eapply IHmem. rewrite <- READ.
      destruct (read loc ts' mem) eqn:READ'.
      { erewrite read_mon; eauto. }
      unfold read in *. destruct ts'; ss.
      destruct (nth_error (mem ++ [x]) ts') eqn:NTH; ss.
      apply nth_error_snoc_inv in NTH. des; ss.
      { rewrite NTH0 in READ'. ss. }
      subst. revert READ. condtac; ss. inversion e. subst. congr.
    - apply read_mon. ss.
  Qed.

  Lemma latest_lt
        loc ts1 ts2 ts3 mem msg
        (LATEST: Memory.latest loc ts1 ts2 mem)
        (LT: ts1 < ts3)
        (MSG: Memory.get_msg ts3 mem = Some msg)
        (LOC: msg.(Msg.loc) = loc):
    ts2 < ts3.
  Proof.
    destruct ts3; ss.
    destruct (le_lt_dec (S ts3) ts2); ss.
    exfalso. eapply LATEST; eauto.
  Qed.

  Lemma ge_latest loc ts1 ts2 mem
        (GE: ts2 <= ts1):
    Memory.latest loc ts1 ts2 mem.
  Proof. ii. lia. Qed.

  Lemma latest_mon1
        loc ts1 ts2 ts3 mem
        (LATEST: latest loc ts1 ts3 mem)
        (LT: ts1 <= ts2):
    latest loc ts2 ts3 mem.
  Proof.
    ii. eapply LATEST; try eapply MSG; eauto.
    eapply le_lt_trans; eauto.
  Qed.

  Lemma latest_mon2
        loc ts1 ts2 ts3 mem
        (LATEST: latest loc ts1 ts3 mem)
        (LT: ts2 <= ts3):
    latest loc ts1 ts2 mem.
  Proof.
    ii. eapply LATEST; try eapply MSG; eauto.
    eapply lt_le_trans; eauto.
  Qed.

  Lemma latest_join
        loc ts ts1 ts2 mem
        (LATEST1: latest loc ts ts1 mem)
        (LATEST2: latest loc ts ts2 mem):
    latest loc ts (join ts1 ts2) mem.
  Proof.
    destruct (le_dec ts1 ts2).
    - eapply latest_mon2; try exact LATEST2.
      rewrite max_r; auto.
    - eapply latest_mon2; try exact LATEST1.
      rewrite max_l; auto. lia.
  Qed.

  Lemma latest_ts_spec
        loc to mem:
    <<LE: latest_ts loc to mem <= to>> /\
    <<READ: exists val, read loc (latest_ts loc to mem) mem = Some val>>.
  Proof.
    induction to; i.
    - ss. esplits; ss.
    - ss. destruct (nth_error mem to) eqn:NTH.
      + destruct t0. des_ifs.
        * esplits; eauto. unfold read. ss. rewrite NTH.
          ss. des_ifs. exfalso. apply c. refl.
        * des. split; auto. esplits. eauto.
      + des. split; auto. esplits. eauto.
  Qed.

  Lemma latest_ts_mon
        loc to1 to2 mem
        (LE: to1 <= to2):
    latest_ts loc to1 mem <= latest_ts loc to2 mem.
  Proof.
    revert to1 LE. induction to2.
    - i. specialize (latest_ts_spec loc to1 mem). i. des.
      inv LE. inv LE0. auto.
    - i. inv LE; auto. rewrite IHto2; auto.
      clear. unfold latest_ts at 2. des_ifs.
      specialize (latest_ts_spec loc to2 mem). i. des.
      rewrite LE. auto.
  Qed.

  Lemma latest_ts_append
        loc to mem1 mem2:
    latest_ts loc to mem1 <= latest_ts loc to (mem1++mem2).
  Proof.
    induction to; ss.
    destruct (nth_error mem1 to) eqn:NTH.
    - exploit nth_error_app_mon; eauto. i.
      rewrite x0. destruct t0. condtac; ss.
    - destruct (nth_error (mem1++mem2) to); ss.
      destruct t0. condtac; ss.
      exploit latest_ts_spec. i. des. rewrite LE. lia.
  Qed.

  Lemma latest_ts_latest
        loc from to mem
        (LATEST: latest_ts loc to mem = from):
    latest loc from to mem.
  Proof.
    revert from LATEST.
    induction to; ii; try lia.
    ss. destruct (nth_error mem to) eqn:NTH.
    - destruct t0. revert LATEST. condtac.
      + i. subst. lia.
      + i. eapply IHto; eauto.
        destruct (le_lt_dec (S ts) to); auto.
        apply lt_le_S in l. exploit le_antisym; eauto. i.
        inv x0. destruct msg. ss. rewrite NTH in MSG. inv MSG.
        contradiction.
    - eapply IHto; eauto.
      destruct (le_lt_dec (S ts) to); auto.
      apply lt_le_S in l. exploit le_antisym; eauto. i.
      inv x0. rewrite NTH in MSG. inv MSG.
  Qed.

  Lemma latest_latest_ts
        loc from to mem
        (LATEST: latest loc from to mem):
    latest_ts loc to mem <= from.
  Proof.
    revert from LATEST.
    induction to; ii; ss; try lia.
    destruct (nth_error mem to) eqn:NTH.
    - destruct t0. condtac.
      + destruct (le_lt_dec (S to) from); auto.
        exfalso. eapply LATEST; eauto.
      + eapply IHto; eauto. eapply latest_mon2; eauto.
    - eapply IHto; eauto. eapply latest_mon2; eauto.
  Qed.

  Lemma latest_ts_rec
        loc to mem:
    latest_ts loc (latest_ts loc to mem) mem = latest_ts loc to mem.
  Proof.
    induction to; ss.
    destruct (nth_error mem to) eqn:NTH; ss. destruct t0.
    destruct (Loc.eq_dec loc0 loc); ss. rewrite NTH.
    destruct (Loc.eq_dec loc0 loc); ss.
  Qed.

  Lemma latest_ts_read_lt
        loc from to mem v val
        (LATEST: latest_ts loc to mem = from)
        (READ: read loc v mem = Some val)
        (LT: from < v):
    to < v.
  Proof.
    generalize (latest_ts_latest mem LATEST). i.
    destruct (le_dec v to); try lia.
    destruct v; try by inv LT.
    unfold read in *. ss.
    destruct (nth_error mem v) eqn:NTH; ss. des_ifs.
    exfalso. eapply H; eauto.
  Qed.

  Lemma latest_ts_read_le
        loc to mem v val
        (READ: read loc v mem = Some val)
        (LE: v <= to):
    v <= latest_ts loc to mem.
  Proof.
    revert v val LE READ. induction to; ss; i.
    des_ifs.
    - inv LE; eauto.
      unfold read in READ. ss. rewrite Heq in READ.
      des_ifs.
    - inv LE; eauto.
      unfold read in READ. ss. rewrite Heq in READ. inv READ.
  Qed.

  Lemma no_msgs_split
        a b c pred mem
        (AB: a <= b)
        (BC: b <= c):
    no_msgs a c pred mem <->
    no_msgs a b pred mem /\ no_msgs b c pred mem.
  Proof.
    econs; intro X.
    - split; ii; eapply X; try exact MSG; ss.
      + lia.
      + lia.
    - des. ii.  destruct (le_lt_dec (S ts) b).
      + eapply X; eauto.
      + eapply X0; eauto.
  Qed.

  Lemma no_msgs_split'
        a b c pred mem:
    no_msgs a b pred mem /\ no_msgs b c pred mem ->
    no_msgs a c pred mem.
  Proof.
    i. des. ii. destruct (le_lt_dec (S ts) b).
    + eapply H; eauto.
    + eapply H0; eauto.
  Qed.

  Lemma no_msgs_full
        pred from to mem1 mem2
        (TO: to <= length mem1)
        (NOMSGS: no_msgs from to pred mem1):
    no_msgs from to pred (mem1 ++ mem2).
  Proof.
    ii. eapply NOMSGS; eauto.
    apply nth_error_app_inv in MSG. des; subst; ss. lia.
  Qed.

  Lemma no_msgs_weaken
        a b c pred mem1 mem2
        (BC: b <= c)
        (NOMSGS: no_msgs a c pred (mem1 ++ mem2)):
    no_msgs a b pred mem1.
  Proof.
    ii. eapply NOMSGS; eauto.
    - lia.
    - rewrite nth_error_app1; ss. apply nth_error_Some. congr.
  Qed.

  Lemma ge_no_msgs
        ts1 ts2 pred mem
        (GE: ts2 <= ts1):
    no_msgs ts1 ts2 pred mem.
  Proof.
    ii. lia.
  Qed.

  Lemma latest_uniq
        ts1 ts2 ts loc mem val1 val2
        (TS1: ts1 <= ts)
        (TS2: ts2 <= ts)
        (LATEST1: latest loc ts1 ts mem)
        (LATEST2: latest loc ts2 ts mem)
        (MSG1: read loc ts1 mem = Some val1)
        (MSG2: read loc ts2 mem = Some val2):
    ts1 = ts2.
  Proof.
    destruct (Nat.lt_trichotomy ts1 ts2); des; ss.
    - destruct ts2; [lia|]. exfalso.
      revert MSG2. unfold read. s. destruct (nth_error mem ts2) eqn:NTH; ss.
      condtac; ss. inversion e. subst. i. inv MSG2.
      eapply LATEST1; eauto.
    - destruct ts1; [lia|]. exfalso.
      revert MSG1. unfold read. s. destruct (nth_error mem ts1) eqn:NTH; ss.
      condtac; ss. inversion e. subst. i. inv MSG1.
      eapply LATEST2; eauto.
  Qed.

  Lemma read_wf
        ts loc val mem
        (READ: read loc ts mem = Some val):
    ts <= List.length mem.
  Proof.
    revert READ. unfold read. destruct ts; [lia|]. s.
    destruct (nth_error mem ts) eqn:NTH; ss. condtac; ss.
    i. eapply List.nth_error_Some. congr.
  Qed.

  Lemma get_msg_wf
        ts msg mem
        (READ: get_msg ts mem = Some msg):
    ts <= List.length mem.
  Proof.
    revert READ. unfold get_msg. destruct ts; [lia|]. s.
    destruct (nth_error mem ts) eqn:NTH; ss. i. inv READ.
    eapply List.nth_error_Some. congr.
  Qed.
End Memory.

Module View.
Section View.
  Context `{A: Type, _: orderC A eq}.

  Inductive t := mk {
    ts: Time.t;
    annot: A;
  }.
  Hint Constructors t.

  Inductive _le (a b:t): Prop :=
  | _le_intro
      (TS: le a.(ts) b.(ts))
      (ANNOT: le a.(annot) b.(annot))
  .

  Definition _join (a b:t): t :=
    mk (join a.(ts) b.(ts)) (join a.(annot) b.(annot)).

  Definition _bot: t := mk bot bot.

  Global Program Instance preorder: PreOrder _le.
  Next Obligation. ii. econs; refl. Qed.
  Next Obligation. ii. inv H1. inv H2. econs; etrans; eauto. Qed.

  Global Program Instance partialorder: PartialOrder eq _le.
  Next Obligation.
    ii. econs.
    - i. subst. econs; refl.
    - i. destruct x, x0. inv H1. inv H2. inv H3. ss. f_equal.
      + intuition.
      + antisym; ss.
  Qed.

  Global Program Instance order:
    @orderC
      t
      eq
      _le
      _join
      _bot
      _ _ _.
  Next Obligation.
    unfold _join. destruct a, b; ss. econs; s; apply join_l.
  Qed.
  Next Obligation.
    unfold _join. destruct a, b; ss. econs; s; apply join_r.
  Qed.
  Next Obligation.
    unfold _join. destruct a, b, c; ss. f_equal; apply join_assoc.
  Qed.
  Next Obligation.
    unfold _join. destruct a, b; ss. f_equal; apply join_comm.
  Qed.
  Next Obligation.
    inv AC. inv BC. econs; s; apply join_spec; ss.
  Qed.
  Next Obligation.
    econs; apply bot_spec.
  Qed.

  Lemma ts_join a b:
    (join a b).(View.ts) = join (a.(View.ts)) (b.(View.ts)).
  Proof. destruct a, b; ss. Qed.

  Lemma ts_ifc a b:
    (ifc a b).(View.ts) = ifc a b.(View.ts).
  Proof. destruct a; ss. Qed.

  Lemma ts_bot:
    bot.(View.ts) = bot.
  Proof. ss. Qed.

  Lemma eq_time_eq
        (v1 v2:t)
        (EQ: v1 = v2):
    v1.(ts) = v2.(ts).
  Proof.
    subst. ss.
  Qed.
End View.
End View.

Ltac viewtac :=
  repeat
    (try match goal with
         | [|- join _ _ <= _] => apply join_spec
         | [|- bot <= _] => apply bot_spec
         | [|- ifc ?c _ <= _] => destruct c; s

         | [|- Time.join _ _ <= _] => apply join_spec
         | [|- Time.bot <= _] => apply bot_spec

         | [|- context[View.ts (join _ _)]] => rewrite View.ts_join
         | [|- context[View.ts bot]] => rewrite View.ts_bot
         | [|- context[View.ts (ifc _ _)]] => rewrite View.ts_ifc
         end;
     ss; eauto).

Module Promises.
  Definition t := Id.t -> bool.

  Definition id_of_time (ts:Time.t): option positive :=
    option_map Pos.of_succ_nat (Time.pred_opt ts).

  Lemma id_of_time_inj ts ts'
        (EQ: id_of_time ts = id_of_time ts'):
    ts = ts'.
  Proof.
    revert EQ. unfold id_of_time, Time.pred_opt.
    destruct ts, ts'; ss. i. inv EQ.
    f_equal. apply SuccNat2Pos.inj. ss.
  Qed.

  Lemma id_of_time_le ts ts' p p'
        (P: id_of_time ts = Some p)
        (P': id_of_time ts' = Some p')
        (LE: (p <= p')%positive):
    ts <= ts'.
  Proof.
    revert P P' LE. unfold id_of_time, Time.pred_opt.
    destruct ts, ts'; ss. i. inv P. inv P'. lia.
  Qed.

  Lemma id_of_time_lt ts ts' p p'
        (P: id_of_time ts = Some p)
        (P': id_of_time ts' = Some p')
        (LE: (p < p')%positive):
    ts < ts'.
  Proof.
    revert P P' LE. unfold id_of_time, Time.pred_opt.
    destruct ts, ts'; ss. i. inv P. inv P'. lia.
  Qed.

  Definition lookup (ts:Time.t) (promises:t): bool :=
    match id_of_time ts with
    | None => false
    | Some ts => promises ts
    end.

  Definition set (ts:Time.t) (promises:t): t :=
    match id_of_time ts with
    | None => promises
    | Some ts => fun_add ts true promises
    end.

  Lemma set_o ts' ts promises:
    lookup ts' (set ts promises) =
    if ts' == ts
    then ts' <> 0
    else lookup ts' promises.
  Proof.
    unfold lookup, set.
    destruct (id_of_time ts') eqn:X', (id_of_time ts) eqn:X, (equiv_dec ts' ts); ss;
      destruct ts, ts'; ss;
      try rewrite fun_add_spec in *.
    - inv e. rewrite X in X'. inv X'. condtac; ss. congr.
    - condtac; ss. inversion e. subst.
      rewrite <- X' in X. apply id_of_time_inj in X. inv X. intuition.
  Qed.

  Definition unset (ts:Time.t) (promises:t): t :=
    match id_of_time ts with
    | None => promises
    | Some ts => fun_add ts false promises
    end.

  Lemma unset_o ts' ts promises:
    lookup ts' (unset ts promises) =
    if ts' == ts
    then false
    else lookup ts' promises.
  Proof.
    unfold lookup, unset.
    destruct (id_of_time ts') eqn:X', (id_of_time ts) eqn:X, (equiv_dec ts' ts); ss;
      destruct ts, ts'; ss;
      try rewrite fun_add_spec in *.
    - inv e. rewrite X in X'. inv X'. condtac; intuition.
    - condtac; ss. inversion e. subst.
      rewrite <- X' in X. apply id_of_time_inj in X. inv X. intuition.
  Qed.

  Definition clear_below (ts:Time.t) (promises:t): t :=
    match id_of_time ts with
    | None => promises
    | Some ts => fun i =>
                  if Pos.leb i ts
                  then false
                  else promises i
    end.

  Lemma clear_below_o ts' ts promises:
    lookup ts' (clear_below ts promises) = lookup ts' promises && Time.ltb ts ts'.
  Proof.
    unfold lookup, clear_below.
    destruct (id_of_time ts') eqn:X', (id_of_time ts) eqn:X; destruct ts, ts'; ss.
    - destruct (Pos.leb_spec0 p p0); ss.
      + exploit id_of_time_le; try exact l; eauto.
        destruct (promises p), (S ts <? S ts') eqn:CMP; ss.
        apply Time.ltb_lt in CMP. lia.
      + assert ((p0 < p)%positive) by lia.
        exploit id_of_time_lt; try exact H; eauto.
        destruct (promises p), (S ts <? S ts') eqn:CMP; ss.
        apply Time.ltb_ge in CMP. lia.
    - destruct (promises p); ss.
  Qed.

  Lemma set_unset a b promises
        (DIFF: a <> b):
    set a (unset b promises) = unset b (set a promises).
  Proof.
    funext. i. unfold set, unset.
    destruct a, b; ss.
    rewrite ? fun_add_spec. repeat condtac; ss.
    inversion e. inversion e0. subst.
    apply SuccNat2Pos.inj in H0. congr.
  Qed.

  Lemma lookup_bot view:
    lookup view bot = false.
  Proof.
    unfold lookup. destruct (id_of_time view); ss.
  Qed.

  Lemma ext p1 p2
        (EQ: forall i, lookup i p1 = lookup i p2):
    p1 = p2.
  Proof.
    funext. i. specialize (EQ (Pos.to_nat x)).
    unfold lookup, id_of_time in *.
    destruct (Id.eq_dec 1 x).
    { subst. ss. }
    exploit (Pos2Nat.inj_pred x); [lia|].
    destruct (Pos.to_nat x) eqn:NAT; ss.
    - destruct x; ss. destruct x; ss.
    - i. subst. rewrite Pos2SuccNat.id_succ in *.
      generalize (Pos.succ_pred_or x). i. des; [congr|].
      rewrite H in *. ss.
  Qed.

  Definition promises_from_mem
             (tid:Id.t) (mem: Memory.t): t.
  Proof.
    induction mem using list_rev_rect.
    - exact bot.
    - destruct x.
      apply (if tid0 == tid
             then Promises.set (S (List.length (List.rev mem))) IHmem
             else IHmem).
  Defined.

  Lemma promises_from_mem_nil tid:
    promises_from_mem tid Memory.empty = bot.
  Proof.
    unfold promises_from_mem, list_rev_rect, eq_rect. ss.
    match goal with
    | [|- context[match ?c with | eq_refl => _ end]] => destruct c
    end; ss.
  Qed.

  Lemma promises_from_mem_snoc tid mem msg:
    promises_from_mem tid (mem ++ [msg]) =
    if msg.(Msg.tid) == tid
    then set (S (List.length mem)) (promises_from_mem tid mem)
    else promises_from_mem tid mem.
  Proof.
    unfold promises_from_mem at 1, list_rev_rect, eq_rect.
    match goal with
    | [|- context[match ?c with | eq_refl => _ end]] => destruct c
    end; ss.
    rewrite List.rev_involutive, List.rev_app_distr. ss.
    destruct msg. s. condtac.
    - inversion e. subst. rewrite ? List.rev_length.
      f_equal.
      unfold promises_from_mem, list_rev_rect, eq_rect.
      match goal with
      | [|- context[match ?c with | eq_refl => _ end]] => destruct c
      end; ss.
    - unfold promises_from_mem, list_rev_rect, eq_rect.
      match goal with
      | [|- context[match ?c with | eq_refl => _ end]] => destruct c
      end; ss.
  Qed.

  Lemma promises_from_mem_inv
        ts tid mem
        (LOOKUP: lookup (S ts) (promises_from_mem tid mem)):
    exists loc val, List.nth_error mem ts = Some (Msg.mk loc val tid).
  Proof.
    revert LOOKUP. induction mem using List.rev_ind.
    { rewrite promises_from_mem_nil, lookup_bot. ss. }
    rewrite promises_from_mem_snoc. condtac.
    { rewrite set_o. condtac.
      - inversion e. inversion e0. subst.
        rewrite List.nth_error_app2; [|lia].
        rewrite Nat.sub_diag. ss.
        destruct x. esplits; eauto.
      - i. exploit IHmem; eauto.  i. des.
        rewrite List.nth_error_app1; eauto.
        apply List.nth_error_Some. congr.
    }
    i. exploit IHmem; eauto.  i. des.
    rewrite List.nth_error_app1; eauto.
    apply List.nth_error_Some. congr.
  Qed.

  Lemma promises_from_mem_lookup
        mem ts loc val tid
        (GET: List.nth_error mem ts = Some (Msg.mk loc val tid)):
    lookup (S ts) (promises_from_mem tid mem).
  Proof.
    revert GET. induction mem using List.rev_ind.
    { i. apply List.nth_error_In in GET. inv GET. }
    rewrite promises_from_mem_snoc. condtac.
    - rewrite Promises.set_o. condtac.
      + inversion e. inversion e0. subst.
        rewrite List.nth_error_app2; [|lia].
        rewrite Nat.sub_diag. ss.
      + i. apply IHmem.
        erewrite <- List.nth_error_app1; eauto.
        assert (H: ts < List.length (mem ++ [x])).
        { rewrite <- List.nth_error_Some. ii. congr. }
        rewrite List.app_length in H.
        rewrite Nat.add_1_r in H. inv H; try lia.
        exfalso. apply c. ss.
    - i. apply IHmem.
      destruct (Nat.eq_dec ts (List.length mem)) eqn:Heq.
      + inv Heq. rewrite List.nth_error_app2 in GET; try lia.
        rewrite Nat.sub_diag in GET. ss. inv GET. ss.
        exfalso. apply c. ss.
      + rewrite List.nth_error_app1 in GET; auto.
        assert (H: ts < List.length (mem ++ [x])).
        { rewrite <- List.nth_error_Some. ii. congr. }
        rewrite List.app_length in H.
        rewrite Nat.add_1_r in H. inv H; try lia; congr.
  Qed.

  Lemma promises_from_mem_spec
        ts tid mem:
    lookup (S ts) (promises_from_mem tid mem) <->
    exists loc val, List.nth_error mem ts = Some (Msg.mk loc val tid).
  Proof.
    induction mem using List.rev_ind.
    { econs.
      - rewrite promises_from_mem_nil, lookup_bot. ss.
      - i. des. destruct ts; ss.
    }
    rewrite promises_from_mem_snoc. econs.
    - condtac.
      + inversion e. subst. rewrite set_o. condtac.
        * inversion e0. subst. i.
          rewrite List.nth_error_app2, Nat.sub_diag; [|lia]. ss.
          destruct x. ss. eauto.
        * intro Y. apply IHmem in Y. des.
          esplits; eauto. apply nth_error_app_mon. eauto.
      + intro Y. apply IHmem in Y. des.
        esplits; eauto. apply nth_error_app_mon. eauto.
    - i. des. apply nth_error_snoc_inv in H. des; ss.
      { condtac; eauto. rewrite set_o. condtac; eauto. }
      subst. condtac; ss; [|congr]. rewrite set_o. condtac; [|congr]. ss.
  Qed.
End Promises.
