import incidence_world.level01 --hide
open IncidencePlane --hide

/-
# Incidence World

## Proving useful lemmas (I).

To solve this level, you will need to use the second axiom of incidence.
-/

variables {Ω : Type} [IncidencePlane Ω] --hide
variables  {P Q: Ω} {r : Line Ω}  -- hide

/- Lemma : no-side-bar
Given a line, there exists one point in that line.
-/
lemma exists_point_on_line (ℓ : Line Ω): ∃ A : Ω, A ∈ ℓ :=
begin
	have A2 : ∃ (P Q : Ω), P ≠ Q ∧ ℓ = line_through P Q,
  {
    exact line_contains_two_points ℓ,
  },
  cases A2 with A hA,
  cases hA with B hB,
  cases hB with HAB hl,
  use A,
  rw hl,
  exact line_through_left A B,




  
end
