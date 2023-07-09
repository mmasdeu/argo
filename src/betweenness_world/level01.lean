import incidence_world.level05 --hide
open IncidencePlane --hide

/- Axiom : AXIOM B1a
between_symmetric :
  (A * B * C) ↔ (C * B * A)
-/

/- Axiom : AXIOM B1b
different_of_between :
  (A * B * C) → (A ≠ B ∧ A ≠ C ∧ B ≠ C)
-/

/- Axiom : AXIOM B1c
collinear_of_between :
  (A * B * C) → ∃ ℓ, A ∈ ℓ ∧ B ∈ ℓ ∧ C ∈ ℓ
-/

/- Axiom : AXIOM B2
point_on_ray :
  A ≠ B → ∃ C, A * B * C
-/

/- Axiom : AXIOM B3
between_of_collinear (A B C : Ω) (collinear {A, B, C}) :
	((A * B * C) ∧ ¬ ( B * A * C ) ∧ ¬ (A * C * B)) ∨
	(¬ (A * B * C) ∧ ( B * A * C ) ∧ ¬ (A * C * B)) ∨
	(¬ (A * B * C) ∧ ¬ ( B * A * C ) ∧ (A * C * B))
-/

/-
# Betweenness World

## The axioms of order

Also called the axioms of betweenness, the axioms of order were formalized by David Hilbert (1862-1943 AD) on the occasion of studying the Euclid's `Elements`.
When it comes to them, there are up to four axioms of order. Their learning involves the definition of **segment**, **betweenness**, **line separation** and
**plane separation**, among others. In written mathematics, the notion of **betweenness** is represented by the **`*`** symbol. Now, let's take a look at the axioms of order.

**B.1)** If $A ∗ B ∗ C$, then $A$, $B$, $C$ are three distinct points all lying on the same line, and $C ∗ B ∗ A$.

**B.2)** Given two distinct collinear points $A$ and $B$, there is a third point $C$ such that $A * B * C$.

**B.3)** Given 3 distinct collinear points $A$, $B$ and $C$, exactly one of them is between the other two. 

**B.4)** [This axiom will be learned in the following world.]

Later on this world we will learn the definition of **segment**, which can be inferred from the first three axioms of order.

## The axioms of order in Lean

To solve the levels of this world, we may need to use the first three axioms of order. Because of this reason, they are presented right below in Lean format. 

The first axiom of order is divided into three statements: 

* `between_symmetric {A B C : Ω} : (A * B * C) ↔ (C * B * A)`

* `different_of_between {A B C : Ω} : (A * B * C) → (A ≠ B ∧ A ≠ C ∧ B ≠ C)`

* `collinear_of_between {A B C : Ω} : (A * B * C) → ∃ ℓ : Line Ω, A ∈ ℓ ∧ B ∈ ℓ ∧ C ∈ ℓ`

The second axiom of order is represented as follows:

* `point_on_ray {A B : Ω} (h: A ≠ B) : ∃ (C : Ω), A * B * C`

To finish with, here it comes the third axiom of order in Lean: 

* `between_of_collinear {A B C : Ω} (h: ∃(ℓ : Line Ω), A ∈ ℓ ∧ B ∈ ℓ ∧ C ∈ ℓ) :
	  ((A * B * C) ∧ ¬ ( B * A * C ) ∧ ¬ (A * C * B)) ∨
	  (¬ (A * B * C) ∧ ( B * A * C ) ∧ ¬ (A * C * B)) ∨
	  (¬ (A * B * C) ∧ ¬ ( B * A * C ) ∧ (A * C * B))`

## Let's solve this level! 

To solve this level, you will need to use two axioms of order. Because of this reason, two theorem statements have been added to the list. Display the
box called "Betweenness World" to take a look at them. Try to think of a mathematical proof in paper before typing your solution in Lean.
-/

variables {Ω : Type} [IncidencePlane Ω] --hide
variables {A B C P Q R : Ω} --hide
variables {ℓ r s t : Line Ω} --hide


/- Lemma :
Given three distinct collinear points A, B and C, if B lies between A and C, then A does not lie between B and C.
-/
lemma not_between_of_between : (A * B * C) → ¬ (B * A * C) :=
begin

  intro h,
  have h2 := between_of_collinear (collinear_of_between h),
  cases h2 with hA hB,
  {
    exact hA.2.1,
  },
  cases hB with hB1 hB2,
  {
    exfalso,
    exact hB1.1 h,
  },
  exact hB2.2.1,
  




end
