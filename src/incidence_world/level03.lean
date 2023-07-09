import incidence_world.level02 --hide
open IncidencePlane --hide

/-
# Incidence World

## Proving useful lemmas (II).

We will see that
a point can help us deciding that two lines are different.

To solve this level, you just need three lines of code. Try to finish it on your own. 
-/

/- Hint : Click here for a hint, in case you get stuck.
Remember that `¬ P` is the same as `P → false`, so `intro` may get you going. 
-/

variables {Ω : Type} [IncidencePlane Ω] --hide
variables {P : Ω} {r s : Line Ω} --hide

/- Lemma :
If two lines `r` and `s` do not share a point, then they are not equal.
-/
lemma ne_line_of_not_share_point (P : Ω) (hPr : P ∈ r)
(hPs : P ∉ s): r ≠ s:=
begin
  
  intro H,
  rw H at hPr,
  tauto,



end
