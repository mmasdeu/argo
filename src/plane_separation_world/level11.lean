import plane_separation_world.level10 --hide
open IncidencePlane --hide

/-
# Plane Separation World

## Getting ready for the final level!

We are left with proving transitivity for collinear points. The trick in this case is to reduce to the known
case by a quite slick argument. The key step lies in the lemma below: given two lines $m$ and $\ell$, and a point
$A$ on $m$ but not on $ℓ$, the goal is to find a new point $E$ which is not on $m$ and which is on the same side of $\ell$
as $A$.

Here is a sketch of the proof, most of which has been replicated already for you in **LEAN** code.

1. Prove first that $\ell$ and $m$ are distinct.
1. Let $D$ be a point on $\ell$ not lying on $m$ (in particular, $D \neq A$).
1. Using axiom (B2), find a point $E$ such that $D * A * E$. Let $s$ be the line through these points.
1. Prove that $E \notin \ell$ (because $A \notin \ell$ and the intersection of $s$ and $\ell$ already contains $D$). Note that this implies,
  in particular, that $\ell ≠ s$.
1. Prove that $E \notin m$:
    - Suppose it where, and show in that case that m = s.
    - Since $D \in s$ but $D \notin m$ we get a contradiction.
1. Show that $A$ is on the same side as $E$:
    - If the segment $AE$ did meet $\ell$, the intersection point would be $D$.
    - This would mean that $A * D * E$.
    - Since we also have $D * A * E$, we would get a contradiction.

![Proof sketch](trans_collinear_diagram.png "Proof of transitivity, collinear case")

-/
variables {Ω : Type} [IncidencePlane Ω] --hide
variables {A B C P Q R : Ω} --hide
variables {ℓ m r s t : Line Ω} --hide


/- Lemma :
Given lines $m$ and $\ell$ and a point $A$ in $m$ and not in $\ell$, there
exists a point $E$ not in $m$ on the same side of $\ell$ as $A$.
-/
lemma auxiliary_point (hAm : A ∈ m) (hAs : A ∉ ℓ) :
  ∃ E, E ∉ m ∧ same_side ℓ A E :=
begin
/- hint
  have hℓm : ℓ ≠ m, -- Prove that ℓ ≠ m
  {
    sorry
  },
  have hD : ∃ D, D ∈ ℓ ∧ D ∉ m, -- Therefore, there is a point in ℓ not in m.
  {
    sorry
  },
  rcases hD with ⟨D, ⟨hDℓ, hDm⟩⟩,
  have hDA : D ≠ A,
  {
    sorry
  },
  have hE : ∃ E, D * A * E, -- Prove that there is point E such that D * A * E
  {
    sorry
  },
  cases hE with E hDAE,
  use E, -- This is the sought E, prove it!
  split,
  { -- Prove that E ∉ m 
    sorry
  },
  { -- Prove that same_side ℓ A E
    sorry
  }
-/
  sorry
end
