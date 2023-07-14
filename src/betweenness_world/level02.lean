import betweenness_world.level01 --hide
open IncidencePlane --hide


/-
# Betweenness World

## Don't try to break a point into two...

In this level, we are asked to show that points cannot be splitted. You may want to use the first axiom of order `different_of_between`. 
You will find it in the list of theorem statements. In case you get stuck, click right below for a hint. 
-/

/- Hint : Click here for a hint, in case you get stuck.
You can add the hypothesis `hAx : A ≠ x ∧ A ≠ A ∧ x ≠ A` and use the theorem statement commented above to prove it. Then, the `tauto` tactic may help you
to close the goal.
-/

variables {Ω : Type} [IncidencePlane Ω] --hide
variables {A B C P Q R : Ω} --hide
variables {ℓ r s t : Line Ω} --hide

@[simp] --hide
/- Lemma :
There are no points between a point and itself.
-/
lemma no_point_between_a_point {A x : Ω} : ¬ (A * x * A) :=
begin
  intro h,
  have hAx : A ≠ x ∧ A ≠ A ∧ x ≠ A,
  {
    apply different_of_between h,
  },
  tauto,




  
end
