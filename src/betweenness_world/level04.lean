import betweenness_world.level03 --hide
open IncidencePlane --hide


/-
# Betweenness World

## Another version of the previous level...

You can try this variation of the previous lemma on your own. Remember that it's best to have a paper proof before you start typing!
-/

variables {Ω : Type} [IncidencePlane Ω] --hide
variables {A B C P Q R : Ω} --hide
variables {ℓ r s t : Line Ω} --hide

/- Lemma :
Given two different collinear points A and B, there is a third C that shares the same line with them and satisfies A * B * C.
-/
lemma between_points_share_line_v2 (h : A * B * C) (hAr : A ∈ r) (hBr : B ∈ r) : 
	C ∈ r :=
begin
    have h1 : A ≠ B ∧ A ≠ C ∧ B ≠ C,
    {
        exact different_of_between h,
    },
    have h2 : ∃ ℓ, A ∈ ℓ ∧ B ∈ ℓ ∧ C ∈ ℓ,
    { 
        apply collinear_of_between,
        exact h,
    },
    cases h2 with s hs,
    have h3 : r = s,
    {
        exact equal_lines_of_contain_two_points h1.1 hAr hs.1 hBr hs.2.1,
    },
    rw h3,
    exact hs.2.2,
	





end
