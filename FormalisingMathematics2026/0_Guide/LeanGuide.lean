import Mathlib.Tactic
-- import Mathlib.Order.BourbakiWitt

set_option linter.all false

/-
TACTICS
-/

/-
Complementing the guide in
https://b-mehta.github.io/formalising-mathematics-notes/Part_2/Part_2.html
-/

/-
## `sorry`

**Summary.** `sorry` closes the current goal without proving it: a placeholder for a part
of the proof that we have not done yet. Lean then shows the warning
"declaration uses `sorry`", and `#print axioms` lists the axiom `sorryAx`
for the theorem: it is not proved yet.

**Official source.** Lean's file `src/Init/Tactics.lean` (search for `macro "sorry"`):
"The `sorry` tactic is a temporary placeholder for an incomplete tactic proof,
closing the main goal using `exact sorry`."
See also the Tactic Reference of the Lean manual:
https://lean-lang.org/doc/reference/latest/Tactic-Proofs/Tactic-Reference/#sorry
-/

example (P Q : Prop) (hP : P) : P ∧ Q := by
  constructor
  · exact hP
  · sorry    -- the goal `Q` is left for later; Lean shows a warning

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

/-
## `exact?`

**Summary.** `exact?` searches Mathlib (and the hypotheses) for a lemma that proves
the goal, and suggests it: click the suggestion "Try this: ..." in the Infoview to
replace `exact?` by it.

**Official source.** Lean's file `src/Init/Tactics.lean` (search for `syntax (name := exact?)`):
"Searches environment for definitions or theorems that can solve the goal using `exact`
with conditions resolved by `solve_by_elim`."
See also the Tactic Reference of the Lean manual:
https://lean-lang.org/doc/reference/latest/Tactic-Proofs/Tactic-Reference/#exact___
-/

example (x : ℝ) : 0 ≤ x ^ 2 := by
  exact?    -- suggests `exact sq_nonneg x`

/-
## `simp?`

**Summary.** `simp?` works like `simp`, and it also tells us which lemmas `simp`
actually used, as a suggestion `simp only [...]`. Replacing `simp` by this
`simp only [...]` makes the proof faster and more robust: it no longer searches through the
whole list of `simp` lemmas.

**Official source.** Lean's file `src/Init/Tactics.lean` (search for `syntax (name := simpTrace)`):
"`simp?` takes the same arguments as `simp`, but reports an equivalent call to `simp only`
that would be sufficient to close the goal."
See also the Tactic Reference of the Lean manual:
https://lean-lang.org/doc/reference/latest/Tactic-Proofs/Tactic-Reference/#simp___
-/

example (a b : ℕ) (h : a = b) : a + 0 = b := by
  simp? [h]    -- suggests `simp only [h, add_zero]`

/-
## `let`

**Summary.** `let x : t := e` introduces a new name `x` for the value `e`, inside a proof.
Unlike `have`, Lean remembers the value: `x` can be unfolded to `e` later
(e.g. by `rfl`, `simp` or `dsimp`). Use `let` for data (numbers, functions, ...),
and `have` for proofs of statements.

**Official source.** Lean's file `src/Init/Tactics.lean` (search for `macro "let"`):
"The `let` tactic is for adding definitions to the local context of the main goal.
The definition can be unfolded, unlike definitions introduced by `have`."
-/

example : ∃ n : ℕ, n + n = 10 := by
  let m : ℕ := 5
  use m
  rfl      -- the goal `m + m = 10` holds, because `m` unfolds to `5`

/-
## `dsimp`

**Summary.** `dsimp` simplifies the goal like `simp`, but only with simplifications
that hold *by definition* (by `rfl`), for example applying a `fun` to its argument,
or unfolding a definition. So the new goal is definitionally equal to the old one.
`dsimp` uses the built-in basic steps plus all @[simp] lemmas that hold by rfl,
such as x + 0 = x on ℕ or 2 + 2 = 4.

`dsimp only` uses only the built-in basic steps, but no lemmas;
except those we list ourselves.
`dsimp only [f]` also unfolds the definition `f`.
`dsimp only [Nat.add_zero]` also applies `Nat.add_zero`

**Official source.** Lean's file `src/Init/Tactics.lean` (search for `syntax (name := dsimp)`):
"The `dsimp` tactic is the definitional simplifier. It is similar to `simp` but only
applies theorems that hold by reflexivity. Thus, the result is guaranteed to be
definitionally equal to the input."
See also the Tactic Reference of the Lean manual:
https://lean-lang.org/doc/reference/latest/Tactic-Proofs/Tactic-Reference/#dsimp
-/

example (f : ℕ → ℕ) (hf : ∀ x, f x = 2 * x) : (fun x => f x) 3 = 6 := by
  dsimp only    -- the goal becomes `f 3 = 6`
  rw [hf]       -- the goal becomes `2 * 3 = 6`, which `rw` closes

/-
## `symm`

**Summary.** `symm` swaps the two sides of the goal: `a = b` becomes `b = a`.
It works for every symmetric relation, e.g. also `a ≠ b`.
`symm at h` swaps the two sides of the hypothesis `h`.

**Official source.** Lean's file `src/Init/Tactics.lean` (search for `syntax (name := symm)`):
"`symm` applies to a goal whose target has the form `t ~ u` where `~` is a symmetric relation
[...]. It replaces the target with `u ~ t`."
See also the Tactic Reference of the Lean manual:
https://lean-lang.org/doc/reference/latest/Tactic-Proofs/Tactic-Reference/#symm
-/

example (a b : ℕ) (h : a = b) : b = a := by
  symm       -- the goal becomes `a = b`
  exact h

/-
## `trans`

**Summary.** `trans b` splits the goal `a ~ c` into the two goals `a ~ b` and `b ~ c`.
It works for every transitive relation, e.g. `=`, `≤`, `<`, `⊆`, `↔`, and also `→`.
If `b` is omitted, Lean tries to find it later from how you close the first goal.
`trans` comes from Batteries, a library that Mathlib builds on.

**Official source.** Batteries' file `Batteries/Tactic/Trans.lean`
(search for `elab "trans"`):
https://leanprover-community.github.io/mathlib4_docs/Batteries/Tactic/Trans.html#Batteries.Tactic.tacticTrans___
-/

example (a b c : ℕ) (hab : a ≤ b) (hbc : b ≤ c) : a ≤ c := by
  trans b
  · exact hab
  · exact hbc

/-
## `subst_vars`

**Summary.** `subst_vars` uses every hypothesis of the form `x = t` or `t = x`,
where `x` is a variable, to replace `x` by `t` everywhere, and then removes
the hypothesis. `subst h` does this for one hypothesis `h`.

**Official source.** Lean's file `src/Init/Tactics.lean`
(search for `syntax (name := substVars)`):
"Applies `subst` to all hypotheses of the form `h : x = t` or `h : t = x`."
See also the Tactic Reference of the Lean manual:
https://lean-lang.org/doc/reference/latest/Tactic-Proofs/Tactic-Reference/#subst_vars
-/

example (a b c : ℕ) (h1 : a = b) (h2 : b = c) : a + b = c + c := by
  subst_vars    -- `a` and `b` are replaced by `c`: the goal becomes `c + c = c + c`
  rfl

/-
## `show_term`

**Summary.** `show_term tac` runs the tactic (or tactics) `tac` as usual,
and also prints the proof term that `tac` built, as a suggestion
"Try this: exact ..." in the Infoview.
This shows what a tactic does behind the scenes, e.g. which lemma it used.
If goals are still open after `tac`, the suggestion has the form `refine ...`,
with a hole `?_` for each open goal. To see the proof term of a finished theorem
`my_theorem`, use `#print my_theorem` instead.

**Official source.** Lean's file `src/Init/Tactics.lean`
(search for `syntax (name := showTerm)`):
"`show_term tac` runs `tac`, then prints the generated term in the form
"exact X Y Z" or "refine X ?_ Z" [...] if there are remaining subgoals."
See also the Tactic Reference of the Lean manual:
https://lean-lang.org/doc/reference/latest/Tactic-Proofs/Tactic-Reference/#show_term
-/

#min_imports in
example (x : ℝ) : 0 < x ^ 2 + 1 := by
  show_term positivity

/-
## `choose`

This item extends the explanation of `choose` in the course notes:
https://b-mehta.github.io/formalising-mathematics-notes/Part_2/tactics/choose.html

**What `choose` builds.**
From `h : ∀ x, ∃ y, P x y`, the line `choose g hg using h`
builds the following:
```
g  := fun x => Classical.choose (h x)
hg := fun x => Classical.choose_spec (h x)
```
`Classical.choose` is defined using the axiom of choice `Classical.choice`,
so `#print axioms` lists `Classical.choice` for every theorem proved with `choose`.
-/

theorem choose_example (X Y : Type) (P : X → Y → Prop) (h : ∀ x, ∃ y, P x y) :
    ∃ g : X → Y, ∀ x, P x (g x) := by
  choose g hg using h
  exact ⟨g, hg⟩

-- #print choose_example
-- #print axioms choose_example

/-
COMMANDS
-/

/-
## `#min_imports in`

**Summary.** `#min_imports in` placed before a theorem prints, in the Infoview,
a short list of imports that should be enough for this theorem. Replacing
`import Mathlib` by such a list makes a file load faster.
It reads the text of the theorem (tactic names, notation, names you typed)
and its finished proof term (the lemmas used). For an `example` it reads only
the text, since Lean discards an `example` after checking it.
The list is a best guess, not a guarantee.
For the `positivity` example above, it suggests only
`Mathlib.Basic.Real.Basic`, but with that import
`positivity` fails until `Mathlib.Tactic.Positivity` is added.
(Tactics may use code that leaves no trace in the final proof term,
so `#min_imports` can miss it.)
For further discussion:
https://leanprover-community.github.io/archive/stream/287929-mathlib4/topic/How.20to.20replace.20.60induction%27.60.20and.20.60norm_num.60.3F.html
https://leanprover-community.github.io/archive/stream/513188-CSLib/topic/min_import.20bug.3F.html


**Official source.** Mathlib's file `Mathlib/Tactic/MinImports.lean`
(search for `syntax (name := minImpsStx)`):
"`#min_imports in cmd` scans the syntax `cmd` and the declaration obtained by
elaborating `cmd` to find a collection of minimal imports that should be sufficient
for `cmd` to work."
https://leanprover-community.github.io/mathlib4_docs/Mathlib/Tactic/MinImports.html#Mathlib.Command.MinImports.minImpsStx
-/

#min_imports in
theorem my_trans (X : Type) (s t u : Set X) (hst : s ⊆ t) (htu : t ⊆ u) : s ⊆ u := by
  trans t
  · exact hst
  · exact htu
