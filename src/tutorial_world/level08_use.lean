import tutorial_world.level07_split --hide
open IncidencePlane --hide
open set --hide


/- Symbol:
ℓ : \ell
-/

/- Tactic : use

## Summary
The `use` tactic works on the goal that looks like `⊢ ∃ x, P x`, where the symbol **`∃`** is read as **"there exists"** and
**`P x`** can be understood as **"P is an element of x"**, which could also be written as **`P ∈ x`**.
In this case, the whole goal can be interpreted as **"there exists x such that P is an element of x"**.
Then, the `use` tactic is useful. If we know that an object `a` satisfies the  property `x`, then `use a` 
will simplify the goal into ⊢ P a.

## Example
If your goal is `⊢ ∃ n : natural_numbers, 1 + x = x + n` then `use 1` will 
turn the goal into `⊢ 1 + x = x + 1`, and the rather more unwise `use 0` will 
turn it into the impossible-to-prove `⊢ 1 + x = x + 0`.
-/

/-
# Tutorial World

## The `use` tactic.

In further proofs, we will need to prove that there exists an object satisfying certain properties.
The goal will then look like `⊢ ∃ x, P x`, where the symbol **`∃`** is read as **"there exists"** and
**`P x`** can be understood as **"x satisfies property P"**.
In this case, the whole goal can be interpreted as **"there exists x such that x satisfies P"**.
Then, the `use` tactic is useful. If we know that an object `a` satisfies the  property `P`, then `use a` 
will simplify the goal into ⊢ P a.

In the example below, we are given three points and two lines. We know certain things about the points, and the
goal is to find a line $\ell$ such that $P$ and $Q$ both belong to $\ell$. Think, looking at the hypotheses,
which line could do the trick. Then `use` it, and finish the proof using tactics you already know.
-/


/- Hint : Click here for a hint, in case you get stuck.
Notice that $s$ contains both $P$ and $Q$, so `use s` will take you in the right direction. If you have typed
`use r`, you will have to delete it because that has taken you to a cul-de-sac.
-/

variables {Ω : Type} [IncidencePlane Ω] --hide

/- Lemma : no-side-bar
Fins a line that contains the points $P$ and $Q$ at the same time.
-/
lemma line_containing_point (P Q R: Ω) (r s : Line Ω) (hP1 : P ∈ r) (hP2 : P ∈ s) (hR : R ∈ r) (hQ : Q ∈ s) :
∃ ℓ : Line Ω, P ∈ ℓ ∧ Q ∈ ℓ :=
begin
  use s,
  split;
  assumption,




end
