import Mathlib.Tactic
set_option linter.all false

/-
Complementing the guide in
https://b-mehta.github.io/formalising-mathematics-notes/Part_2/Part_2.html
-/

/-
## `trivial`

**Summary.** `trivial` tries a list of simple tactics, one after another, and
succeeds as soon as one of them closes the goal. In Lean 4.34.1 the list is:
* `assumption`: the goal is one of the hypotheses,
* `rfl`: the goal is an equality whose two sides are the same,
* `contradiction`: the hypotheses contradict each other, e.g. `h : False`,
* `decide`: the goal is a statement Lean can decide by computing, e.g. `2 + 2 = 4`,
* `apply True.intro`: the goal is `True`,
* `apply And.intro <;> trivial`: the goal is `P ∧ Q`, and `trivial` proves both `P` and `Q`.
If none of them works, `trivial` fails.

**Official source.** The documentation and the list are in Lean's file
`src/Init/Tactics.lean` (search for `"trivial"` and for `macro_rules | `(tactic| trivial)`).
See also the Tactic Reference of the Lean manual:
https://lean-lang.org/doc/reference/latest/Tactic-Proofs/Tactic-Reference/#trivial

-/

example : ¬True → False := by
  trivial

/-

## `suffices`

**Summary.** `suffices` is the Lean version of "it suffices to show ...".
If the goal is `R`, then `suffices hQ : Q by tac` works in two parts:
* first, the tactic proof `tac` proves `R`, and it may use the new hypothesis `hQ : Q`,
* after that, the goal becomes `Q`, and we prove `Q` next.
So we first explain why `Q` is enough, and then we prove `Q`.
(With `have hQ : Q` it is the other way round: we first prove `Q`, and then use it.)

Variants:
* `suffices hQ : Q from e`: the term `e` proves `R`, using `hQ`,
* `suffices Q by tac`: without a name, the new hypothesis is called `this`,
* `suffices hQ : Q` (from Mathlib): nothing is attached; we get two goals,
  first `R` with the hypothesis `hQ : Q`, then `Q`.

**Official source.** Lean's file `src/Init/Tactics.lean` (search for `macro "suffices "`):
"Given a main goal `ctx ⊢ t`, `suffices h : t' from e` replaces the main goal with
`ctx ⊢ t'`, `e` must have type `t` in the context `ctx, h : t'`."
The variant without `by` or `from` comes from Mathlib, file `Mathlib/Tactic/Have.lean`.
See also the Tactic Reference of the Lean manual:
https://lean-lang.org/doc/reference/latest/Tactic-Proofs/Tactic-Reference/#suffices
-/

example (P Q R : Prop) (hPQ : P → Q) (hQR : Q → R) (hP : P) : R := by
  suffices hQ : Q by
    exact hQR hQ
  exact hPQ hP

/-
## `congr`

**Summary.** `congr` turns a goal of the form `f a = f b` into the goal `a = b`.
If several arguments differ, as in `f a c = f b d`, we get one goal for each of them.
`congr` goes as deep as it can, and it tries to close each new goal by itself,
with `rfl` and `assumption`. So `congr` may finish the proof, and then no further tactic
is needed.

`congr n` goes only `n` levels deep. This helps when `congr` goes too deep:
for `f (g (x + y)) = f (g (y + x))`, `congr` gives the goals `x = y` and `y = x`,
which may be false, while `congr 2` gives the goal `x + y = y + x`.

**Official source.** Lean's file `src/Init/Tactics.lean` (search for `syntax (name := congr)`):
"Apply congruence (recursively) to goals of the form `⊢ f as = f bs` and `⊢ f as ≍ f bs`.
The optional parameter is the depth of the recursive applications."
That it tries `rfl` and `assumption` on the new goals is in `src/Lean/Meta/Tactic/Congr.lean`.
See also the Tactic Reference of the Lean manual:
https://lean-lang.org/doc/reference/latest/Tactic-Proofs/Tactic-Reference/#congr
-/

example (f : ℕ → ℕ) (a b : ℕ) (h : a = b) : f a = f b := by
  congr
