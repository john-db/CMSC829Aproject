Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Import ListNotations.
Require Import Lia.

Require Import Coq.Structures.OrderedTypeEx.
Require Import Coq.FSets.FMapAVL.
Require Import Coq.FSets.FMapFacts.
Require Import Coq.FSets.FSetAVL.
Require Import Coq.FSets.FSetFacts.

Module NatMap := FMapAVL.Make(Nat_as_OT).
Module NatSet := FSetAVL.Make(Nat_as_OT).

Fixpoint duplicateAt (n : nat) (lst : list nat) : list nat :=
  match n, lst with
  | _, [] => []
  | _, [x] => [x; x]
  | O, x :: xs => x :: x :: xs
  | S m, x :: xs => x :: duplicateAt m xs
  end.

Fixpoint insertAt (n x : nat) (lst : list nat) : list nat :=
  match n, lst with
  | _, [] => [x]
  | O, xs => x :: xs
  | S m, y :: ys => y :: insertAt m x ys
  end.

Fixpoint take (n : nat) (l : list nat ) :=
  match l with
  | nil => nil
  | cons x xs =>
    match n with
    | 0 => nil
    | S n => cons x (take n xs)
    end 
  end.  

Fixpoint drop (n : nat) (l : list nat) :=
  match l with
  | nil => nil
  | cons x xs =>
    match n with
    | 0 => cons x xs
    | S n => drop n xs
    end 
  end.

Theorem insertAtTakeDrop : forall n x l, insertAt n x l = app (take n l) (cons x (drop n l)).
Proof.
  intros. generalize dependent n. generalize dependent x. 
  induction l; intros; destruct n; simpl; auto.
  rewrite IHl. auto.
  Qed.
Check last.

Fixpoint targets' (initLen : nat) (v : list nat) : list nat :=
  match initLen, v with
  | O, _ => []
  | S O, _ => [0]
  | S predinitlen, _ =>
    let lastElt := last v 0 in
    let remainingTargets := targets' (predinitlen) (removelast v) in
    let numWaits := lastElt - initLen + 1 in
    if lastElt <? initLen then
      lastElt :: remainingTargets
    else
      duplicateAt (numWaits - 1) remainingTargets
  end.

Definition targets (v : list nat) : list nat :=
  targets' (pred (length v)) v.

Fixpoint joiners' (initLen : nat) (v : list nat) : list nat :=
  match initLen, v with
  | O, _ => []
  | S O, _ => [1]
  | S predinitlen, _ =>
    let lastElt := last v 0 in
    let remainingJoiners := joiners' (predinitlen) (removelast v) in
    let numWaits := lastElt - initLen + 1 in
    if lastElt <? initLen then
      initLen :: remainingJoiners
    else
      insertAt numWaits initLen remainingJoiners
  end.

Definition joiners (v : list nat) : list nat :=
  joiners' (pred (length v)) v.

Definition vecToNaive (v : list nat) : list (nat * nat) :=
  combine (joiners v) (targets v).

Definition numberSmallerThan (n : nat) (seenJoiners : NatMap.t nat) : nat :=
  length (filter (fun x => x <? n) (map fst (NatMap.elements seenJoiners))).


Definition naiveToVecLoop (v : NatMap.t nat) 
                          (jt : nat * nat) 
                          : NatMap.t nat :=
  let (j, t) := jt in
  let waits := numberSmallerThan j v in
  let val :=
    if Nat.eqb waits 0
    then t
    else waits + j - 1 in
  NatMap.add j val v.

Check naiveToVecLoop.

Check fold_left.

Definition naiveToVec' (l : list (nat * nat)) (initial : NatMap.t nat) : NatMap.t nat :=
  NatMap.add 0 0 (fold_left naiveToVecLoop l initial).

#[global] Hint Unfold naiveToVec' : core.

Search fold_left.

Search take.

Definition naiveToVec (l : list (nat * nat)) : list nat :=
 take (S (length l)) (map snd (NatMap.elements (naiveToVec' l (NatMap.empty nat)))).

#[global] Hint Unfold naiveToVec : core.

Lemma filter_cons : forall A (l l' : list A) x p, filter p l = x :: l' ->
  p x = true.
Proof.
  intros. induction l.
  - discriminate.
  - simpl in H. destruct (p a) eqn: E; auto. injection H as H. subst; auto.
  Qed.

Lemma existsb_false_filter_emp : forall A (l : list A) p, existsb p l = false ->
  filter p l = [].
Proof.
  intros A. induction l; intros; simpl in *; auto.
  apply orb_false_elim in H. destruct H.
  rewrite H. apply IHl. auto.
  Qed.

Theorem naiveGreaterIrrel : forall (l : list (nat * nat)) x t init,  
  (*forallb (fun x' => (fst x') <? x) l = true ->*)
  existsb (fun x' => x' <? x) (map fst (NatMap.elements init)) = false ->
  naiveToVec' ((x,t) :: l) init = naiveToVec' l (NatMap.add x t init).
Proof.
  induction l; intros; simpl; unfold naiveToVec'; f_equal; simpl; unfold numberSmallerThan;
  rewrite (existsb_false_filter_emp _ _ _ H); auto.
 Qed.
 (* - auto.
  - simpl in *. auto. apply andb_prop in H. destruct H.
    unfold naiveToVec, naiveToVec'; simpl. unfold naiveToVecLoop.
    destruct a. simpl in *.*)
    



Theorem list_last_destruct : forall A (l : list A), l = [] \/ exists l' x, l = l' ++ [x].
Proof.
  intros. induction l using rev_ind.
  - auto.
  - destruct IHl.
    + subst. right. simpl. exists [], x. auto.
    + right. destruct H as [l' [x' H]]. eexists. eexists. f_equal; auto.
  Qed.

Inductive validVec : list nat -> nat -> Prop := 
  | validVec0 : validVec [0;0] 1
  | validVecS l x n : validVec l n -> x <= 2 * n -> validVec (l ++ [x]) (S n)
.     


Theorem validVec_longerthan1 : forall l n, validVec l n -> length l > 1.
Proof.
  intros. induction H; auto.
  rewrite last_length. constructor. auto.
  Qed.

Theorem validVec_length : forall l n, validVec l n -> length l = S n.
Proof.
  intros. induction H; auto. rewrite last_length. auto.
  Qed.

Theorem validVec_base : forall l, validVec l 1 -> l = [0;0].
Proof.
  intros. inversion H; subst; auto. inversion H1.
  Qed.

Theorem validVec_bound : forall l n d, validVec l n -> last l d <= 2 * (pred n).
Proof. 
  intros. induction H.
  - simpl. auto.
  - rewrite last_last. lia.
  Qed.

(*
Theorem vecToNaiveRoundTrip : forall v i, validVec v i -> naiveToVec (vecToNaive v) = v.
Proof.
  unfold vecToNaive, targets, joiners. intros.
  induction H.
  - compute. auto.
  - rewrite last_length. simpl. unfold joiners'. 
    pose proof (validVec_longerthan1 _ _ H). inversion H1.
    + simpl. rewrite last_last. pose proof (validVec_length _ _ H). rewrite <- H3 in H2.
      injection H2 as H2. rewrite <- H2 in H0. 
      destruct (x <? 2) eqn: E.
      * apply Nat.ltb_lt in E. simpl. unfold naiveToVec. simpl.
        inversion E; subst.
        -- simpl. apply validVec_base in H. subst. auto.
        -- rewrite orb_true_r. apply validVec_base in H. subst; auto.
      * apply Nat.ltb_ge in E. simpl. rewrite <- H3 in IHvalidVec.
        destruct (x - 2 + 1) eqn: E'; try lia.
        simpl. destruct n0 eqn: E''; try lia. simpl. 
        simpl in *. unfold naiveToVec, naiveToVec'; simpl in *. compute in IHvalidVec.
        rewrite <- IHvalidVec. simpl. repeat f_equal. lia.
    + rewrite <- H2 in IHvalidVec. simpl in IHvalidVec.
      pose proof H2.
      rewrite (validVec_length _ _ H) in H2.
      injection H2 as H2. subst. simpl. rewrite last_last. fold joiners'.
      simpl. rewrite removelast_last.
      destruct (Nat.ltb_spec x (S n)).
      * unfold naiveToVec, naiveToVec' in *. inversion H3; subst.
        -- simpl in *. destruct (Nat.ltb_spec (last l 0) 2).
          ++ simpl in *. unfold naiveToVec, naiveToVec' in *.
             simpl in *. repeat rewrite orb_true_r in *.
             rewrite <- IHvalidVec at 2. auto.
          ++ simpl in *.
             destruct ((last l 0 - 2 + 1)) eqn: E; try lia.
             simpl in *. 
             pose proof (validVec_bound _ _ 0 H). simpl in *.
             apply Nat.le_antisymm in H5; auto. repeat rewrite H5 in *.
             simpl in *. injection E as E; subst. simpl in *.
             rewrite orb_true_r. rewrite orb_false_r.
             destruct x; auto.
        -- simpl in *. destruct (Nat.ltb_spec (last l 0) (S m)).
          ++ simpl in *. inversion H5.
            ** repeat rewrite <- H7 in *. simpl in *. rewrite orb_true_r.
               Search (NatSet.mem).
               destruct (Nat.ltb_spec (last (removelast l) 0) 2).
               --- simpl in *. repeat rewrite orb_true_r in *. rewrite <- IHvalidVec. auto.
               --- admit.
            ** admit.
          ++ simpl in *. inversion H5; subst.
            ** admit.
            ** admit.
  Admitted.
*)

Inductive validVec' : list nat -> nat -> Prop := 
  | validVec0' : validVec' [0;0] 1
  | validVecTarget l x n : validVec' l n -> x <= n -> validVec' (l ++ [x]) (S n)
  | validVecWait l w n : validVec' l n -> w <= pred n -> validVec' (l ++ [w + pred n]) (S n)
.

Theorem validVec'_longerthan1 : forall l n, validVec' l n -> length l > 1.
Proof.
  intros; induction H; simpl; auto; rewrite last_length; constructor; apply IHvalidVec'.
  Qed.

Theorem validVec'_length : forall l n, validVec' l n -> length l = S n.
Proof.
  intros. induction H; auto; rewrite last_length; auto.
  Qed.

Theorem validVec'_index_pos : forall l n, validVec' l n -> n > 0.
Proof.
  intros. pose proof (validVec'_length _ _ H). pose proof (validVec'_longerthan1 _ _ H).
  rewrite H0 in H1. apply Arith_prebase.gt_S_n_stt in H1. auto.
  Qed.

Theorem validVec'_base : forall l, validVec' l 1 -> l = [0;0].
Proof.
  intros. inversion H; subst; auto; inversion H1.
  Qed.

Theorem validVec'_bound : forall l n d, validVec' l n -> last l d <= 2 * (pred n).
Proof. 
  intros. induction H.
  - simpl. auto.
  - rewrite last_last. lia.
  - rewrite last_last. lia.
  Qed. 

Theorem lte_ltb : forall x y, x <= y -> x <? S y = true.
Proof.
  intros. destruct (Nat.ltb_spec x (S y)); auto. lia.
  Qed.

Ltac gen x := generalize dependent x.

Lemma ltb_S : forall n, S n <? n = false.
Proof.
  intros. destruct (Nat.ltb_spec (S n) n); auto.
  destruct (Nat.nlt_succ_diag_l _ H).
  Qed.

Theorem unrollNaiveToVec : forall v n x, validVec' v n ->
  x <= n ->
  naiveToVec ((S n, x) :: combine (joiners' n v) (targets' n v)) = v ++ [x].
Proof.
  intros. gen x. induction H; intros.
  - auto.
  - simpl in *. rewrite last_last. rewrite (lte_ltb _ _ H0).
    rewrite removelast_last. 
    pose proof (validVec'_index_pos _ _ H). destruct n eqn: E. { inversion H2. }
    rewrite <- E in *. simpl.
    unfold naiveToVec in*. rewrite naiveGreaterIrrel; auto.
    simpl in IHvalidVec'. 
    rewrite naiveGreaterIrrel; simpl; auto.
    +  simpl. admit.
    + rewrite ltb_S. auto. Admitted. 
    

Lemma vecToNaiveRT_length : forall v i, validVec' v i -> length (naiveToVec (vecToNaive v)) = S i.
Proof.
  intros. induction H.
  - auto.
  - simpl. unfold vecToNaive, joiners, targets. rewrite last_length.
    simpl. pose proof (validVec'_length _ _ H). rewrite H1. simpl.
    rewrite last_last, removelast_last. Admitted.

Theorem vecToNaiveRoundTrip' : forall v i, validVec' v i -> naiveToVec (vecToNaive v) = v.
Proof.
  intros. induction H; unfold vecToNaive in *.
  - auto.
  - simpl in *. unfold joiners, targets in *. 
    rewrite last_length. simpl. 
    pose proof (validVec'_length _ _ H).
    rewrite H1 in *. simpl in *. rewrite last_last. rewrite removelast_last.
    rewrite (lte_ltb _ _ H0).
    pose proof (validVec'_longerthan1 _ _ H). rewrite H1 in H2.
    apply le_S_n in H2. destruct n eqn: E. { inversion H2. }
    rewrite <- E in *. simpl.
    unfold naiveToVec in *. 
    rewrite naiveGreaterIrrel. simpl length. 
    (*Consing a first move that joins (S n) onto any target without a wait should only
      cause its target to append on the end of the vec that would come without that
      consed join. *)
     Admitted.

  


