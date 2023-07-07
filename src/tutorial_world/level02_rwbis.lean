import incidence_world.hilbertaxioms --hide
open IncidencePlane --hide

/-
# Tutorial World 

## The rewrite (`rw`) tactic (II).

In the previous level, we learned that `rw h` changes A's into B's when the goal contains one or more A's 
and we have the hypothesis `h : A = B` in the local context. You may be wondering if the opposite case is 
also possible. That is to say: could we change B's into A's when the goal contains one or more B's and we have 
the hypothesis `h : A = B` in the local context?

So the answer is... Yes! The hypotheses in this level are a bit different than before, 
so you should use **`rw ←`** instead. To do so, you can type the little left-arrow by typing **\l** 
and then a space, so the system will change it automatically.

-/

/- Hint : Click here for a hint, in case you get stuck.
You may want to use *`rw ←`* first. Use it only with one of the hypotheses.
-/
open set IncidencePlane --hide

variables {Ω : Type} [IncidencePlane Ω] --hide

/- Lemma : no-side-bar
If A, B and C are points with B = A and B = C, then A = C.
-/
lemma example_exact (A B C: Ω) (h1 : B = A) (h2 : B = C) : A = C :=
begin
  rw ← h1,
  rw h2,

  
end

