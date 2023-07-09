import tactic

noncomputable theory
open_locale classical
open set function

@[protect_proj]
class subset (A : Type*) (B : out_param $ Type*) :=
(mem : B → A → Prop)

namespace subset
-- The following allows us to use the symbol `∈`
instance {A : Type*} {B : Type*} [subset A B] : has_mem B A := ⟨subset.mem⟩

-- This says that two "subset"s are equivalent (written `≈`, type with \approx) when
-- they have the same points.
instance {A : Type*} {B : Type*} [subset A B] : has_equiv A := ⟨λ X Y, ∀ t, t ∈ X ↔ t ∈ Y⟩
@[simp] lemma equiv_iff {A : Type*} {B : Type*} [subset A B] (X Y : A) : X ≈ Y ↔ ∀ t, t ∈ X ↔ t ∈ Y := iff.rfl

-- A "subset" can always be considered as an actual subset, in Lean this is `set B`
instance {A : Type*} {B : Type*} [subset A B] : has_coe_t A (set B) := ⟨λ x p, p ∈ x⟩

@[simp] lemma mem_pts  {A : Type*} {B : Type*} [subset A B] (a : A) (P : B) : P ∈ (a : set B) ↔ P ∈ a
:= iff.rfl

end subset

@[simp] def pts {A : Type*} {B : Type*} [subset A B] : A → set B := λ a, {x : B | x ∈ a}

notation p `xor` q := (p ∧ ¬ q) ∨ (q ∧ ¬ p)

/--
We define an incidence plane as having the undefined terms `Point` and `Line`,
a function `distance` that takes every two points to a real number, and a predicate
`belongs` that relates points and lines.

There are essentially two axioms: existence of two distinct points, and the incidence postulate.
-/
class IncidencePlane (Point : Type*) :=
	(Line : Type*)

	-- Belongs is an undefined concept
  (belongs : Point → Line → Prop)
	(infix  `∈` :100 := belongs)

	-- A1 postulate is divided into 4 statements
	(line_through : Point → Point → Line)
	(line_through_left' (P Q : Point) : P ∈ (line_through P Q))
	(line_through_right' (P Q : Point) : Q ∈ (line_through P Q))
	(incidence' {P Q : Point} {ℓ : Line} : P ≠ Q → P ∈ ℓ → Q ∈ ℓ → ℓ = line_through P Q)

	-- A2 postulate
	(line_contains_two_points' (ℓ : Line) : ∃ P Q : Point, P ≠ Q ∧ ℓ = line_through P Q)

	-- A3 postulate (existence postulate)
	(existence' : ∃ P Q R : Point, P ≠ Q ∧ P ≠ R ∧ Q ≠ R ∧ ¬ R ∈ (line_through P Q))

	-- Betweenness is an undefined concept
	(between : Point → Point → Point → Prop)
	(notation A `*` B `*` C := between A B C)

	/- Betweenness is symmetric -/
	(between_symmetric' {A B C : Point} : (A * B * C) ↔ (C * B * A))

	/- If A * B * C then the three points are distinct and collinear. -/
	(different_of_between' {A B C : Point} : (A * B * C) → (A ≠ B ∧ A ≠ C ∧ B ≠ C))
	(collinear_of_between' {A B C : Point} : (A * B * C) → ∃ ℓ, A ∈ ℓ ∧ B ∈ ℓ ∧ C ∈ ℓ)

	/- Given two distinct points A, B, there is a third point C such that A * B * C.-/
	(point_on_ray' {A B : Point} (h: A ≠ B) : ∃ C, A * B * C)

	/- Given 3 distinct collinear points A B C, exactly one of them is between the other two.-/
	(between_of_collinear' {A B C : Point} (h: ∃ℓ, A ∈ ℓ ∧ B ∈ ℓ ∧ C ∈ ℓ) :
	((A * B * C) ∧ ¬ ( B * A * C ) ∧ ¬ (A * C * B)) ∨
	(¬ (A * B * C) ∧ ( B * A * C ) ∧ ¬ (A * C * B)) ∨
	(¬ (A * B * C) ∧ ¬ ( B * A * C ) ∧ (A * C * B)))

	/- Pasch -/
	(pasch' {A B C D : Point} {ℓ : Line}
		(hnc: ¬ C ∈ line_through A B)
		(hnAl: ¬ (A ∈ ℓ)) (hnBl: ¬ B ∈ ℓ) (hnCl: ¬ C ∈ ℓ)
		(hDl: D ∈ ℓ) (hADB: A * D * B) : (∃ E ,  (A * E * C) ∧ E ∈ ℓ) xor (∃ E, (B * E * C) ∧ E ∈ ℓ))

namespace IncidencePlane
variables {Ω Point : Type*} [IncidencePlane Ω] [IncidencePlane Point]

-- From here on, we can use the symbol `∈` for Lines
instance : subset (Line Ω) Ω := {mem := belongs}

notation A `*` B `*` C := IncidencePlane.between A B C


-- LIST OF ALL AXIOMS

-- A1
@[simp] lemma line_through_left (P Q : Ω) : P ∈ (line_through P Q) := line_through_left' P Q
@[simp] lemma line_through_right (P Q : Ω) : Q ∈ (line_through P Q) := line_through_right' P Q
lemma incidence {P Q : Ω} {ℓ : Line Ω} (hPQ : P ≠ Q) (hPℓ: P ∈ ℓ) (hQℓ : Q ∈ ℓ) :
	ℓ = line_through P Q := incidence' hPQ hPℓ hQℓ

-- A2
lemma line_contains_two_points (ℓ : Line Ω) : ∃ P Q : Ω, P ≠ Q ∧ ℓ = line_through P Q
:= line_contains_two_points' ℓ

-- A3
lemma existence (Ω : Type*) [IncidencePlane Ω] : ∃ P Q R : Ω, P ≠ Q ∧ P ≠ R ∧ Q ≠ R ∧
R ∉ (line_through P Q) := existence'

lemma between_symmetric (A B C : Ω) : (A * B * C) ↔ (C * B * A)  := between_symmetric'
lemma different_of_between {A B C : Ω} : (A * B * C) → (A ≠ B ∧ A ≠ C ∧ B ≠ C) := different_of_between'
lemma different_of_between_12 {A B C : Ω} : (A * B * C) → A ≠ B := λ h, (different_of_between h).1
lemma different_of_between_13 {A B C : Ω} : (A * B * C) → A ≠ C := λ h, (different_of_between h).2.1
lemma different_of_between_23 {A B C : Ω} : (A * B * C) → B ≠ C := λ h, (different_of_between h).2.2
lemma collinear_of_between {A B C : Ω} : (A * B * C) → ∃ ℓ : Line Ω, A ∈ ℓ ∧ B ∈ ℓ ∧ C ∈ ℓ := collinear_of_between'
lemma point_on_ray {A B : Ω} (h: A ≠ B) : ∃ (C : Ω), A * B * C := point_on_ray' h
lemma between_of_collinear {A B C : Ω} (hℓ : ∃ ℓ : Line Ω, A ∈ ℓ ∧ B ∈ ℓ ∧ C ∈ ℓ) : 
	((A * B * C) ∧ ¬ ( B * A * C ) ∧ ¬ (A * C * B)) ∨
	(¬ (A * B * C) ∧ ( B * A * C ) ∧ ¬ (A * C * B)) ∨
	(¬ (A * B * C) ∧ ¬ ( B * A * C ) ∧ (A * C * B)) := between_of_collinear' hℓ

lemma pasch {A B C D : Ω} {ℓ : Line Ω} (hnc: ¬ C ∈ line_through A B)
(hnAl: ¬ (A ∈ ℓ)) (hnBl: ¬ B ∈ ℓ) (hnCl: ¬ C ∈ ℓ) (hDl: D ∈ ℓ) (hADB: A * D * B) :
(∃ E ,  (A * E * C) ∧ E ∈ ℓ) xor (∃ E, (B * E * C) ∧ E ∈ ℓ) := pasch' hnc hnAl hnBl hnCl hDl hADB

-- END OF AXIOMS

/--
A set of points is collinear if they all lie on some line
-/
--@[simp]
--def collinear (S : set Ω) : Prop := ∃ (ℓ : Line Ω), ∀ {P : Ω}, P ∈ S → P ∈ ℓ

def collinear (A B C : Ω) := ∃ (ℓ : Line Ω), A ∈ ℓ ∧ B ∈ ℓ ∧ C ∈ ℓ

/--
This lemma is a rephrasing of the incidence axiom that
doesn't mention `line_through`
-/ 
lemma equal_lines_of_contain_two_points {A B : Ω}	{r s : Line Ω}
(hAB: A ≠ B)	(hAr: A ∈ r) (hAs: A ∈ s) (hBr: B ∈ r) (hBs: B ∈ s) :	r = s :=
by rw [incidence hAB hAr hBr, incidence hAB hAs hBs]

-- The next lemmas allow us to deal with collinearity of sets
meta def extfinish : tactic unit := `[ext, finish]

lemma collinear_of_equal (A B C D E F) (h : ({A, B, C} : set Ω) = {D, E, F} . extfinish) : collinear A B C ↔ collinear D E F
:=
begin
rw collinear,
rw collinear,
split,
{
	intro h1,
	cases h1 with ℓ hℓ,
	rcases hℓ with ⟨hA, hB, hC⟩,
	use ℓ,
	simp at *,
	have HH : D ∈ ({A, B, C} : set Ω) ∧ E ∈ ({A, B, C} : set Ω) ∧ F ∈ ({A, B, C} : set Ω),
	{
		rw h,
		simp,
	},
	simp at HH,
	rcases HH with ⟨H1, H2, H3⟩,
	all_goals {rcases H1 with H | H | H, repeat{subst H}},
	all_goals {rcases H2 with H | H | H, repeat{subst H}},
	all_goals {rcases H3 with H | H | H, repeat{subst H}},
	all_goals {tauto},
},
{
	intro h1,
	cases h1 with ℓ hℓ,
	rcases hℓ with ⟨hE, hF, hG⟩,
	use ℓ,
	simp at *,
	have HH : A ∈ ({D, E, F} : set Ω) ∧ B ∈ ({D, E, F} : set Ω) ∧ C ∈ ({D, E, F} : set Ω),
	{
		rw ←h,
		simp,
	},
	simp at HH,
	rcases HH with ⟨H1, H2, H3⟩,
	all_goals {rcases H1 with H | H | H, repeat{subst H}},
	all_goals {rcases H2 with H | H | H, repeat{subst H}},
	all_goals {rcases H3 with H | H | H, repeat{subst H}},
	all_goals {tauto},
}
end

/--
Two points P and Q lie on the same side of a line ℓ if the segment P⬝Q doesn't intersect ℓ
-/
@[simp]
def same_side (ℓ : Line Ω) (P Q : Ω) :=  P ∉ ℓ ∧ Q ∉ ℓ ∧ (∀ x, (P * x * Q) → x ∉ ℓ) 

@[simp]
lemma different_of_between''
{A B : Ω} : (A * A * B) ↔ false := ⟨λ h, (different_of_between h).1 (eq.refl _),by tauto⟩

@[simp]
lemma different_of_between'''
{A B : Ω} : (A * B * B) ↔ false := ⟨λ h, (different_of_between h).2.2 (eq.refl _),by tauto⟩

end IncidencePlane
