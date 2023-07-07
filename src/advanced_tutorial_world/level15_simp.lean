import advanced_tutorial_world.level14_apply --hide
open IncidencePlane --hide

/- Tactic : simp

## Summary
The `simp` tactic is a high-level tactic which tries to prove equalities using facts in its database.

## Details
The `simp` tactic does basic automation. It uses lemmas already proved that have been tagged
with a special label, to simplify either a goal or a hypothesis.
-/

/-
# Advanced Tutorial World

## The `simp` tactic.

In this level, we introduce a high level tactic called `simp`. This is an Artificial Intelligence (AI) tactic which 
can nail some really tedious-for-a-human-to-solve goals. It uses lemmas that are already in our database to make 
the goal simpler. You can simplify an hypothesis `h` by calling `simp at h,`. As the game progresses, this tactic
will become better (we are tagging some of the lemmas as "simp lemmas" along the way).

Just to illustrate, **LEAN** has a lemma  (called `not_not`) that says that double negation is the same as an affirmation:

`@[simp] lemma not_not (p : Prop) : ¬¬ p ↔ p`

The fact that it has `@[simp]` written in front of it instructs the `simp` tactic to replace all occurrences
of `¬¬ p` with `p`. There are lots of lemmas like these in **LEAN**, which makes this tactic really powerful.
-/


variables {Ω : Type} [IncidencePlane Ω] --hide

/- Lemma : no-side-bar
If a point $P$ is on a line $\ell$, then $P$ is not outside of $\ell$.
-/
lemma simp_example (P : Ω) (ℓ : Line Ω) (h : P ∈ ℓ) : ¬ (P ∉ ℓ) :=
begin 

  simp,
  exact h,

end

