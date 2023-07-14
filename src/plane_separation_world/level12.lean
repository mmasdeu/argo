import plane_separation_world.level11 --hide
open IncidencePlane --hide


/-
# Plane Separation World

## The Final Level!

After all this hard work, we are left with the final task of assembling the bits and proving transitivity
in the collinear case. We will prove this by applying up to three times the noncollinear case already proven.
For this, we need the auxiliary point from the previous level. Here is a sketch of the proof.

1. First, note that the case $A = B$, $A = C$ or $B = C$ are easy, and they can be proved separately. So we may
  assume for the rest of the proof that $A \neq B$, $A \neq C$ and $B \neq C$.
1. Let $m$ be the line through $A$, $B$, $C$.
1. Consider the point $E$ obtained from the previous level, which is not in $m$ and is on the same side of $\ell$ as $A$.
1. Show that the sets $\{A, B, E\}$, $\{A, C, E\}$ and $\{B, C, E\}$ are all non-collinear (they are all done similarly).
1. Using symmetry, and transitivity for non-collinear points, show that $B$ is on the same side as $E$.
1. Show, using the previous step and a similar argument, that $E$ is on the same side as  $C$.
1. Finally, finish the proof using a third time transitivity for non-collinear points.

![Proof sketch](trans_collinear_diagram.png "Proof of transitivity, collinear case")

-/
variables {Ω : Type} [IncidencePlane Ω] --hide
variables {A B C P Q R : Ω} --hide
variables {ℓ m r s t : Line Ω} --hide


/- Lemma :
Given three collinear points A, B, C and a line ℓ, if A and B are on the same side of 
ℓ and B and C are on the same side of ℓ, then A and C are on the same side of ℓ.
-/
lemma same_side_trans_of_collinear (hCol : collinear A C B):
    same_side ℓ A B → same_side ℓ B C → same_side ℓ A C :=
begin
/- hint
intros hABℓ hBCℓ,
have hAℓ : A ∉ ℓ := not_in_line_of_same_side_left hABℓ,
by_cases hAB : A = B,
{
  sorry
},
by_cases hAC : A = C,
{
  sorry
},
by_cases hBC : B = C,
{
  sorry
},
cases hCol with m hm, -- Let m be the line through A, B, C
rcases hm with ⟨hAm, hCm, hBm⟩,
rcases auxiliary_point hAm hAℓ with ⟨E, ⟨hEm, hAE⟩⟩,
have hABE : ¬ collinear A B E,
{
  sorry
},
have hACE : ¬ collinear A C E,
{
  sorry
},
have hBCE : ¬ collinear B C E,
{
  sorry
},
have hBE : same_side ℓ B E, -- Use transitivity for non-collinear points
{
  sorry
},
have hEC : same_side ℓ E C, -- Use transitivity for non-collinear points
{
  sorry
},
sorry -- And we are done in one line!
-/
intros hABℓ hBCℓ,
have hAℓ : A ∉ ℓ := not_in_line_of_same_side_left hABℓ,
by_cases hAB : A = B,
{
  rw hAB,
  exact hBCℓ,
},
by_cases hAC : A = C,
{
  rw hAC at *,
  exact same_side_reflexive hAℓ,
},
by_cases hBC : B = C,
{
  rw hBC at hABℓ,
  exact hABℓ,
},
cases hCol with m hm,
rcases hm with ⟨hAm, hCm, hBm⟩,
rcases auxiliary_point hAm hAℓ with ⟨E, ⟨hEm, hAE⟩⟩,

have hABE : ¬ collinear A B E,
{
  rw collinear_iff_on_line_through hAB,
  rw incidence hAB hAm hBm at hEm,
  exact hEm,
},
have hACE : ¬ collinear A C E,
{
  rw collinear_iff_on_line_through hAC,
  rw incidence hAC hAm hCm at hEm,
  exact hEm,
},
have hBCE : ¬ collinear B C E,
{
  rw collinear_iff_on_line_through hBC,
  rw incidence hBC hBm hCm at hEm,
  exact hEm,
},
have hBE : same_side ℓ B E,
{
  rw same_side_symmetric at hABℓ,
  rw collinear_of_equal A B E B E A at hABE,
  apply same_side_trans_of_noncollinear hABE hABℓ hAE,
},
have hEC : same_side ℓ E C,
{
  rw same_side_symmetric at hBE,
  rw collinear_of_equal B C E E C B at hBCE,
  apply same_side_trans_of_noncollinear hBCE hBE hBCℓ,
},
exact same_side_trans_of_noncollinear hACE hAE hEC,
end
