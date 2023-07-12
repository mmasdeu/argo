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
  
  use line_through A C,
  use line_through B C,
  use line_through A B,
  simp,
  intros P h1 h2,
  have hkey : line_through A C ≠ line_through B C,
  {
    apply ne_line_of_not_share_point A (line_through_left A C),
    intro hc,
    apply h,
    have lABeqlBC : line_through A B = line_through B C,
    {
      apply equal_lines_of_contain_two_points hAB;
      simp [hc],
    },
    rw lABeqlBC,
    apply line_through_right,
  },
  have hCP : P = C,
  {
    apply equal_points_of_in_two_lines
      hkey h1 h2 (line_through_right A C) (line_through_right B C),
  },
  rw hCP,
  assumption,


end
