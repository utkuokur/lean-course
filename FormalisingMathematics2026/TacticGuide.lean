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
## `positivity`

**Summary.** `positivity` proves goals of exactly three forms: `0 ≤ e`, `0 < e` and
`e ≠ 0` (also written `e ≥ 0`, `e > 0`). It either proves the goal completely or fails.

It works by taking the expression `e` apart, following how `e` is built:
for `e = a + b`, `a * b`, `a ^ n`, `a / b`, `|a|`, ..., it first proves that the pieces
`a` and `b` are nonnegative, positive or nonzero, and then combines these facts with
rules such as "positive + nonnegative is positive" or "a square is nonnegative".
For the smallest pieces (numbers and variables) it uses:
* `norm_num` for numbers, e.g. `0 < 37`,
* the type, e.g. every natural number `n : ℕ` satisfies `0 ≤ n`,
* hypotheses about the piece, e.g. `hx : 0 < x`, `hy : y ≠ 0`, or also `hx : x > 37`.

What `positivity` does **not** do: it does not reason with inequalities in general.
For example, from `-1 < x` and `2 < y` it cannot show `0 < x + y`, although this is true
(use `linarith` for such goals). And it fails on goals of other forms, e.g. `a ≤ b`.

`positivity [h₁, h₂]` first adds the facts `h₁`, `h₂` as hypotheses and then runs
`positivity`.

**Official source.** Mathlib's file `Mathlib/Tactic/Positivity/Core.lean`
(search for `syntax (name := positivity)`): "`positivity` solves goals of the form `0 ≤ x`,
`0 < x` and `x ≠ 0`. The tactic works recursively according to the syntax of the expression
`x`, by attempting to prove subexpressions are positive/nonnegative/nonzero and combining
this into a final proof. This tactic either closes the goal or fails."
Documentation page:
https://leanprover-community.github.io/mathlib4_docs/Mathlib/Tactic/Positivity/Core.html#Mathlib.Tactic.Positivity.positivity
-/

example (x : ℝ) : 0 < x ^ 2 + 1 := by
  positivity    -- `x ^ 2` is nonnegative, `1` is positive, so the sum is positive
