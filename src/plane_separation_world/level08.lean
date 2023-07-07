import plane_separation_world.level07 --hide
open IncidencePlane --hide

/-
# Plane Separation World

## On the way to the final level (IV).

This is the fourth and last lemma that we need to prove before jumping into the final level of the game! 
-/


variables {Ω : Type} [IncidencePlane Ω] --hide
variables {A B C P Q R : Ω} --hide
variables {ℓ r s t : Line Ω} --hide

/- Lemma :
If two points A and C are not on the same side of the line ℓ, there exists a point in the segment A·C which is incident with the line ℓ. 
-/
lemma not_same_side_intersection (h : ¬ same_side ℓ A C) : ∃ P , (P = A ∨ P = C ∨ (A * P * C)) ∧ P ∈ ℓ :=
begin
  by_contra hlAC,
  simp at hlAC,
  apply h,
  rw same_side,
  tauto,
  



  
end 
