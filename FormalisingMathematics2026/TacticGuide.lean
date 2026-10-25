import Mathlib.Tactic
set_option linter.all false

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


https://b-mehta.github.io/formalising-mathematics-notes/Part_2/Part_2.html

-/
