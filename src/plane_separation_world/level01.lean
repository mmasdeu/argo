import incidence_world.hilbertaxioms --hide
import betweenness_world.level05 --hide
open IncidencePlane --hide

/- Axiom : AXIOM B4
pasch (hnc: ¬ C ∈ line_through A B)
  (hnAl: ¬ (A ∈ ℓ)) (hnBl: ¬ B ∈ ℓ)
  (hnCl: ¬ C ∈ ℓ) (hDl: D ∈ ℓ)
  (hADB: A * D * B) :
  (∃ E ,  E ∈ ℓ ∧ (A * E * C)) xor (∃ E, E ∈ ℓ ∧ (B * E * C))
-/

/-
# Plane Separation World

## A new world of possibilities...

The notion of **plane separation** comes from the fourth axiom of order, which is the Pasch's Axiom. 

**B.4) Pasch's Axiom:** Let A, B, C be three non-collinear points and let ℓ be a line lying in the plane ABC
and not passing through any of the points A, B, C. Then, if the line ℓ passes through a point of the segment A·B, 
it will also pass through either a point of the segment B·C or a point of the segment A·C (but not both).

In Lean, the Pasch's Axiom may be useful to complete following levels:

* `lemma pasch {A B C D : Ω} {ℓ : Line Ω} (hnc: C ∉ line_through A B)
(hnAl: A ∉ ℓ) (hnBl: B ∉ ℓ) (hnCl: C ∉ ℓ) (hDl: D ∉ ℓ) (hADB: A * D * B) :
(∃ E ,  E ∈ ℓ ∧ (A * E * C)) xor (∃ E, E ∈ ℓ ∧ (B * E * C))`

![Axiom Pasch](pasch.png "Pasch's Axiom, the fourth axiom of betweenness")

Thanks to this, we can define what "being on the same side" means. 

**Definition:** Given a line ℓ and the points A and B, such that A, B ∉ ℓ, we say that A and B are on the same side if
the segment A·B does not meet ℓ or A = B.

In Lean, the definition of `same_side` is represented as follows: 

* `def same_side (ℓ : Line Ω) (P Q : Ω) :=  P ∉ ℓ ∧ Q ∉ ℓ ∧ (∀ x, (P * x * Q) → x ∉ ℓ)`


[**Rule of thumb:** Whenever you see `same_side` in Lean, you may use the `rw` tactic to "unfold" its definition. In this way, it will be easier to understand what it means. If it is 
located at the hypothesis `h2`, for example, then `rw same_side at h2,` will make progress. If it is located at the goal, then `rw same_side,` will be enough 
to rewrite the goal.
-/

variables {Ω : Type} [IncidencePlane Ω] --hide
variables {A B C P Q R : Ω} --hide
variables {ℓ r s t : Line Ω} --hide

/- Lemma :
If the segment $PQ$ is on the same side of a line $\ell$, then $P \notin ℓ$.
-/
lemma not_in_line_of_same_side_left (h : same_side ℓ A B) : A ∉ ℓ :=
begin
  rw same_side at h,
  tauto,
end

-- begin hide
lemma not_in_line_of_same_side_right (h : same_side ℓ A B) : B ∉ ℓ :=
begin
  rw same_side at h,
  tauto,
end
-- end hide