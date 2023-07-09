import incidence_world.hilbertaxioms --hide
open IncidencePlane --hide


/- Symbol:
⊢ : \|-
-/


/- Symbol:
∧ : \and
-/

/- Symbol:
¬ : \not
-/

/- Symbol:
→ : \imp
-/

/- Symbol:

↔ : \iff
-/


/- Symbol:
∀ : \forall
-/

/- Symbol:
∃ : \exists
-/

/- Tactic : assumption

## Summary

If the goal is exactly one of the assumption, then `assumption,` will close
the goal automatically.

### Example
If it looks like this in the top right hand box:
```
A B C : Ω
h1 : A = B
h2 : B = C
⊢ A = B
```

then

`assumption,`

will close the goal.
-/

/-
# Tutorial World

## The setup

Welcome to the Tutorial World! In this world, you're going to prove some geometric facts by using **`tactics`**. 
These *tactics* are just instructions that make progress in a mathematical proof.
During your proofs, your "goal" (i.e. what you're
supposed to be proving) will be displayed in front of a `⊢` symbol on the top
right hand box, so you will need to use *tactics* to close that goals. Once you close all the goals, the top
right hand box will report "Proof complete!", so that you 
can move on to the next level in the world you're in. 

## The language

In **LEAN**, everything (points, lines, a set of points, a theorem, a proof) is a *term*, and each term is of a certain *type*,
and only one. One writes `x : T` to say that the term $x$ is of type $T$ (you can read the ":" as "is an element of"). By the way,
*types* are themselves terms (rembember, **everything** is a term). For example, a point $P$ will be a term of type $\Omega$ (which will
denote the plane). We will write this as `P : Ω`. The plane $\Omega$ is of type `Type` (this is a special type, whose terms are
things like the plane, or the set of the real numbers, for example).

There is also another special type called `Prop`. A term of type `Prop` is a true-false statement, like "it rains", "2 + 2 = 4",
"2 + 3 = 7" (yes, they can be either True or False). A term of type `2 + 2 = 4` would be a proof of this fact.
We will write `h : 2 + 2 = 4` to mean exactly this: `h` is a proof of the fact that `2 + 2 = 4`, and we can use it in our proof.
If we had `h' : 2 + 3 = 7` then we would probably be able to proof crazy things!


## The symbols

You will find a **Symbols** at the top left corner of
the screen. Next to each symbol, there is the instruction that you neeed to type in case you want it to appear on the screen.
Sooner or later, you will come across these symbols during the game, so try to save a space in your brain for them. They will be important!

## The `assumption` tactic

The first tactic that we'll learn is the `assumption` tactic. This can be used
when your goal is exactly one of your hypotheses. In the following example,
there are three hypotheses, namely the fact that $A = B$ (hypothesis `h₁`), the
fact that $C = D$ (hypothesis `h₂`) and the fact that $B = C$ (hypothesis `h₃`).

Since we want to prove that $C = D$, which is one of our hypotheses, we should be able to
win by typing `assumption,` (**don't forget the comma**). Delete the `sorry` and try it.

**Pro tip:** If the hypothesis to be used is called, say `hb`, you can also close the goal
by using `exact hb,` instead. Sometimes it is more efficient to do so, especially if we believe
that assumption should work and we don't know why. The `exact` tactic will give us information
about why that does not work.

-/
open set IncidencePlane --hide

variables {Ω : Type} [IncidencePlane Ω] --hide

/- Lemma : no-side-bar
If $A = B$, $C = D$ and $B = C$, then $C = D$.
-/
lemma l0 (A B C D : Ω) (h₁ : A = B) (h₂ : C = D) (h₃ : B = C) : B = C :=
begin
  assumption,

  
end
