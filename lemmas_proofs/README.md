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
