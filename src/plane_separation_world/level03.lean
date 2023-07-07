import plane_separation_world.level02 --hide
open IncidencePlane --hide

/-
# Plane Separation World

## Being reflexive

In this level we prove that a point outside a line is on the same side of the line as itself. It seems stupid,
but needs to be proven nevertheless.

-/ 

variables {Ω : Type} [IncidencePlane Ω] --hide
variables {A B C P Q R : Ω} --hide
variables {ℓ r s t : Line Ω} --hide

/- Lemma :
A is at the same side as A of ℓ.
-/
@[simp] -- hide
lemma same_side_reflexive (h : A ∉ ℓ): same_side ℓ A A :=
begin
simp,
exact h,






end
