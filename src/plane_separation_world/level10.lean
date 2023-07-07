import plane_separation_world.level09 --hide
open IncidencePlane --hide

/-
# Plane Separation World

## The Pasch's Axiom in action!

In this level we prove transitivity of the relation "being in the same side of $ℓ$", provided that the three
points involved are non-collinear. So suppose that we are given three non-collinear points $A$, $B$, $C$, and suppose
that $A$ is on the same side of $ℓ$ as $B$, and $B$ is on the same side of $ℓ$ as $C$. We want to prove that $A$ is on
the same side of $ℓ$ as $C. Here is a sketch of the proof.

1. We argue by contradiction, so assume that the line $AC$ does meet $\ell$.
2. Let $D \in \ell$ be the point of intersection, so $A * D * C$.
3. Use Pasch to prove that either $\ell$ either meets the segment $AB$ or $BC$, thus
  obtaining a contradiction.

![Proof sketch](trans_noncollinear_diagram.png "Proof of transitivity, noncollinear case")

Try to write the structure of this proof in **LEAN** and then fill in the sorries.
-/


variables {Ω : Type} [IncidencePlane Ω] --hide
variables {A B C P Q R : Ω} --hide
variables {ℓ r s t : Line Ω} --hide

/- Lemma :
Given three non-collinear points A, B, C and a line ℓ, if A and B are on the same side of 
ℓ and B and C are on the same side of ℓ, then A and C are on the same side of ℓ.
-/
lemma same_side_trans_of_noncollinear (hCol : ¬ collinear A C B):
    same_side ℓ A B → same_side ℓ B C → same_side ℓ A C :=
begin
intros hAB hBC,
by_contradiction,
have h' := not_same_side_intersection h,
rcases h' with ⟨D, hD1, hD2⟩,
have hkey := same_side_of_noncollinear_ne_line hAB hBC,
have hB : B ∉ line_through A C := notin_line_of_noncollinear hCol,
cases same_side_pasch hB hkey.1 hkey.2.2 hkey.2.1 h with H H,
{
  rw same_side_symmetric at hBC,
  tauto,
},
{
  tauto,
},







end
