import incidence_world.level04 --hide
open IncidencePlane --hide

/-
# Incidence World

## Triangles, triangles...

We end this world by proving the existence of triangles.

To give you some hints, remember these Lean tips that might help you to step through the proof. 

**Tip 1:** whenever a hypothesis looks like `h : P ∧ Q`, we can refer to `P` and `Q` as `h.1` and `h.2`, respectively.

**Tip 2:** whenever you have a goal of the form `⊢ ∀ (P : Ω), ...`, the `intros` tactic wil make progress.

If needed, you can go back to the previous levels to remember how to use some tactics. Good luck! Let's do this!
-/

variables {Ω : Type} [IncidencePlane Ω] --hide

/- Lemma :
There exist three lines that do not have a point in common.
-/
lemma three_distinct_lines : ∃ (r s t: Line Ω), (∀ (P : Ω),
¬(P ∈ r ∧ P ∈ s ∧ P ∈ t)) :=
begin
  rcases existence Ω with ⟨A, B, C, ⟨hAB, hAC, hBC, h⟩⟩,
  use line_through A B,
  use line_through A C,
  use line_through B C,
  intros P H,
  have h1 : line_through A C ≠ line_through A B, 
  {
    exact ne_line_of_not_share_point C (line_through_right A C) h,
  },
  by_cases hPA : P = A,
  {
    have hAlBC : A ∈ line_through B C,
    {
      rw ← hPA,
      exact H.2.2,
    },
    have H1 : line_through A C = line_through B C,
    {
      exact equal_lines_of_contain_two_points hAC (line_through_left A C) hAlBC (line_through_right A C) (line_through_right B C),
    },
    have H2 : line_through A C = line_through A B, 
    {
      rw H1,
      exact equal_lines_of_contain_two_points hAB hAlBC (line_through_left A B) (line_through_left B C) (line_through_right A B),
    },
    exact h1 H2,
  },
  {
    have h2 : line_through A C = line_through A B, 
    {
      exact equal_lines_of_contain_two_points hPA H.2.1 H.1 (line_through_left A C) (line_through_left A B),
    },
    tauto,
  },
  
  



end
