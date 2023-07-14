import betweenness_world.level04 --hide
open IncidencePlane --hide

variables {Ω : Type} [IncidencePlane Ω] --hide
variables {A B C P Q R : Ω} --hide
variables {ℓ r s t : Line Ω} --hide

/-
# Betweenness World

## The definition of segment.

We've already seen how to define some primitive notions from a given set of axioms, such as **point**, **line**, **incidence** or **betweenness**. In
mathematics, we can also define new concepts by combining those that we've learned so far. In this way, the notion of **segment** joins the party.

**Definition:** the segment $AB$ is the set of points $P$ such that $P=A$, $P=B$ or $A * P * B$.
-/
@[simp] -- hide
def segment (A B : Ω) := {P | P = A ∨ P = B ∨  A * P * B }

/-
We have (secretely) tagged this as a simp definition. Try to prove this level on your own, or see by yourself the power of `simp`.
By the way, if you want to see which lemmas did `simp` use, you can type `squeeze_simp` and it will give you a list.
-/



/- Lemma :
The only point on the segment $AA$ is $A itself.
-/
lemma one_point_segment (A P : Ω) : P ∈ segment A A  ↔ P = A :=
begin
  simp,





end
