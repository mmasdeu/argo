import plane_separation_world.level03 --hide
open IncidencePlane --hide

/-
# Plane Separation World

## Who is on the same side?

In this level we prove that being on the same side of a line is a symmetric concept.

-/ 

variables {Ω : Type} [IncidencePlane Ω] --hide
variables {A B C P Q R : Ω} --hide
variables {ℓ r s t : Line Ω} --hide

/- Lemma :
A is at the same side as B of ℓ if and only if B is at the same side of A of ℓ.
-/
lemma same_side_symmetric: same_side ℓ A B ↔ same_side ℓ B A:=
begin
split,
{
  intro h,
  simp at h ⊢,
  simp_rw between_symmetric,
  tauto,
},
{
  intro h,
  simp at h ⊢,
  simp_rw between_symmetric A,
  tauto,
}




end
