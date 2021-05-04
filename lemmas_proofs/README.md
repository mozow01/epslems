# Intuitionistic epsilon semantics in Coq

## Lemma 1

````coq
Lemma ref_subst_presupp : forall U : Type, forall A B : U -> Prop, 
forall u : { x : U | {y | A y} -> A x},
B(proj1_sig u) -> 
exists x : U, ({y | A y} -> A x) /\ B x.
Proof.
  intros.
  apply ex_intro with (x:=proj1_sig u).
  split.
  exact (proj2_sig u).
  exact H.
Qed.
````
## Definition 1

````coq
Definition epsinv (A B : nat -> Prop) := forall u v : { x : nat | (exists x, A x) -> A x }, 
B (proj1_sig u) <-> B (proj1_sig v).
````

## Lemma 2

````coq
Lemma ekv_subst_cont : forall U : Type, forall A B : U -> Prop, 
forall u : { x : U | {y | A y} -> A x},
epsinv_type A B ->
{x : U | ({y | A y} -> A x) /\ B x} ->
B(proj1_sig u).
Proof.
  intros.
  assert (L:B (proj1_sig X)).
  assert (K: ({y : U | A y} -> A (proj1_sig X)) /\ B (proj1_sig X)).
  exact (proj2_sig X).
  destruct K as [K1 K2].
  exact K2.
  assert (M:{y : U | A y} -> A (proj1_sig X)).
  assert (K: ({y : U | A y} -> A (proj1_sig X)) /\ B (proj1_sig X)).
  exact (proj2_sig X).  
  destruct K as [K1 K2].
  exact K1. 
  apply H with (u:=u) (v:=exist (fun x0: U => {y : U | A y} -> A x0) (proj1_sig X) M).
  compute. auto.
Qed. 
```` 

## Lemma 3

````coq
Lemma subst_1 : forall A B : nat -> Prop, forall u : { x : nat | (exists x, A x) -> A x },
(((exists x, A x )/\(forall x, A x -> B x))\/((~ exists x, A x)/\ forall x, B x )->
B (proj1_sig u)).
Proof.
  intros.
  destruct H as [K|L].
  destruct K as [K1 K2].
  assert (M0 :(exists x, A x) -> A (proj1_sig u)).
  exact (proj2_sig u). 
  assert (M1 :  A (proj1_sig u)).
  auto.
  auto.
  destruct L as [L1 L2].
  auto.
Qed.
````
## Lemma 4

````coq
Lemma subst_2 : forall A B : nat -> Prop, forall u : { x : nat | (exists x, A x) -> A x },
(exists x, A x ) \/ (~ exists x, A x) -> 
(epsinv A B) -> 
B (proj1_sig u)->((((exists x, A x )/\(forall x, A x -> B x))\/((~ exists x, A x)/\ forall x, B x ))).
Proof.
  intros.
  destruct H as [K|L].
  - left.
  split.
  + auto.
  + intros.
  assert (M:(exists x0 : nat, A x0) -> A x).
  ++ auto.
  ++ assert (L : x = proj1_sig (exist (fun x0:nat => (exists x1 : nat, A x1) -> A x0) x M)). 
  * compute.
  reflexivity.
  * assert (L1 : B (proj1_sig (exist (fun x0 : nat => (exists x1 : nat, A x1) -> A x0) x M))).
  ** apply H0 with (u:=u) (v:=exist (fun x0 : nat => (exists x1 : nat, A x1) -> A x0) x M).
  auto.
  ** rewrite L.
  exact L1.
  - right.
  split.
  + exact L.
  + intros.
  assert (W:(exists x0 : nat, A x0) -> A x).
  * intros.
  contradiction.
  * assert (N : x = proj1_sig (exist (fun x0:nat => (exists x1 : nat, A x1) -> A x0) x W)). 
  compute.
  ** reflexivity.
  ** assert (L2 : B (proj1_sig (exist (fun x0 : nat => (exists x1 : nat, A x1) -> A x0) x W))).
  apply H0 with (u:=u) (v:=exist (fun x0 : nat => (exists x1 : nat, A x1) -> A x0) x W).
  *** auto.
  *** rewrite N.
  exact L2.
Qed.
````
