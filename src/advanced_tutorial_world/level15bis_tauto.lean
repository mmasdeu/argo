import incidence_world.level02 --hide
open IncidencePlane --hide

/- Tactic : tauto

## Summary
The `tauto` tactic is a high-level tactic which tries to prove statements that follow tautologically
from the hypotheses.

## Details
The `tauto` tactic does basic automation. It breaks down assumptions of the form `_ ∧ _`, `_ ∨ _`, `_ ↔ _` and `∃ _, _`,
and splits a goal of the form `_ ∧ _`, `_ ↔ _` or `∃ _, _` until it can be proved using trivialities.

## Example
``example (p q r : Prop) : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (r ∨ p ∨ r) := by tauto``
-/

variables {p q r : Prop} --hide
/-
# Advanced Tutorial World

## The `tauto` tactic.

When the goal follows from the hypotheses directly from the rules of logic, then we say that we are proving a tautology,
and there is a tactic that does this automatically for us. For example, the following is a tautology (if p, q and r are
arbitrary statements).

p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (r ∨ p ∨ r)

You can see that this is true because regardless of whether each of `p`, `q` and `r` is true or false, the statement
above is true.
-/

/- Lemma : no-side-bar
If $p$, $q$ and $r$ are three true-false statements, and we know $p \lor q$ and $r \lor p \lor r$, then
we have $p \lor (q \land r)$.
-/
lemma some_logic (h1 : p ∨ q) (h2 : r ∨ p ∨ r): 
p ∨ (q ∧ r) :=
begin

  tauto,


end
