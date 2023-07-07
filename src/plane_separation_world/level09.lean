import plane_separation_world.level08 --hide
open IncidencePlane --hide


variables {Ω : Type} [IncidencePlane Ω] --hide
variables {A B C P Q R : Ω} --hide
variables {ℓ r s t : Line Ω} --hide
/-
# Plane Separation World

## A reformulation of Pasch axiom

We prove a more useful way of stating Pasch axiom, using the concept of `same_side`. This form will be
the one that we will use in our application. Of course, we need to use Pasch's axiom in the proof!
-/

/- Lemma :
If a line cuts properly the segment AB, of a triangle ABC, then cuts properly either
AC or BC, but not both.
-/
lemma same_side_pasch {A B C : Ω} {ℓ : Line Ω} (hnc: C ∉ line_through A B)
(hnAl: (A ∉ ℓ)) (hnBl: B ∉ ℓ) (hnCl: C ∉ ℓ) (hAB : ¬ same_side ℓ A B) :
(same_side ℓ A C) xor (same_side ℓ B C) :=
begin

  simp at hAB,
  replace hAB := hAB hnAl hnBl,
  rcases hAB with ⟨D,⟨hD1,hD2⟩⟩,
  have H := pasch hnc hnAl hnBl hnCl hD2 hD1,
  simp at H ⊢,
  itauto,





end
