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
