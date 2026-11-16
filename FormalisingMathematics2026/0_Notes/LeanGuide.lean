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
## `fun_prop`

**Summary.** `fun_prop` proves that a function has a property such as
`Continuous`, `Differentiable` or `Measurable`. It splits the function into
simple pieces (sums, products, powers, compositions, ...) and uses lemmas
tagged `@[fun_prop]` for each piece, e.g. "a sum of continuous functions is
continuous". If it fails with "No theorems found", the needed lemma is not
imported or not tagged.

**Official source.** Mathlib's file `Mathlib/Tactic/FunProp/Elab.lean`
(search for `syntax (name := funPropTacStx)`):
"`fun_prop` solves a goal of the form `P f`, where `P` is a predicate and `f` is
a function, by decomposing `f` into a composition of elementary functions, and
proving `P` on each of those by matching against a set of `@[fun_prop]` lemmas."
https://leanprover-community.github.io/mathlib4_docs/Mathlib/Tactic/FunProp/Elab.html#Mathlib.Meta.FunProp.funPropTacStx
-/

example : Continuous (fun x : ℝ => x ^ 3 - x - 1) := by
  fun_prop

/-
## `push_cast`

**Summary.** A *coercion* (or *cast*) is a function that Lean inserts
automatically to turn, e.g., a natural number `n : ℕ` into an integer or a real
number; the Infoview shows it as `↑n`. The tactic `push_cast` moves casts inward, towards
the variables: `↑(a + b)` becomes `↑a + ↑b`. This often makes the goal match
the hypotheses. `push_cast at h` does the same in the hypothesis `h`.
`norm_cast` does the opposite: it moves casts outward.

**Official source.** Lean's file `src/Init/Tactics.lean`
(search for `syntax (name := pushCast)`):
"`push_cast` rewrites the goal to move certain coercions (*casts*) inward,
toward the leaf nodes. [...] For example, `↑(a + b)` will be written to
`↑a + ↑b`."
See also the Tactic Reference of the Lean manual:
https://lean-lang.org/doc/reference/latest/Tactic-Proofs/Tactic-Reference/#push_cast
-/

example (n : ℕ) (h : (n : ℤ) = 3) : ((n + 1 : ℕ) : ℤ) = 4 := by
  push_cast
  rw [h]
  norm_num

/-
## `grw`

**Summary.** `grw [h]` is `rw` for inequalities.
Given `h : a ≤ b`, the line `grw [h]` replaces `a` with the larger
`b`, and `grw [← h]` replaces `b` with the smaller `a`. Unlike `rw` with an
equality, it cannot do this everywhere. As for any other tactic, the new goal
must imply the old goal.

For a goal with `≤`, this means that `grw` may only make the left-hand side
larger or the right-hand side smaller. For example:
- goal `a + c ≤ 5`: `grw [h]` changes the goal to `b + c ≤ 5`
- goal `5 ≤ b + c`: `grw [← h]` changes the goal to `5 ≤ a + c`
- goal `5 ≤ a + c`: `grw [h]` fails

A minus sign swaps the two cases: for the goal `c - b ≤ 5`, replacing `b` with
the smaller `a` makes the left-hand side larger, so `grw [← h]` works, whereas
`grw [h]` fails.

The new goal can be strictly stronger than the old goal. In fact, the new goal
could even be false. Hence, just like the `apply` tactic, the generalized
rewrite `grw` must be used with caution.

If `h' : x = y`, then `grw [h']` works exactly like `rw [h']`. It replaces
`x` everywhere, with no restriction on the place and no side conditions.
Therefore, equalities and inequalities can be mixed in one call, as in
`grw [h, h']`.

**Extra features.**
- Hypotheses: `grw [h] at hc` rewrites in a hypothesis `hc`. Here the new `hc`
  must follow from the old one, so `grw` may only make the left-hand side
  smaller or the right-hand side larger. For example, `grw [h] at hc` turns
  `hc : 5 ≤ a + c` into `hc : 5 ≤ b + c`, and `grw [← h] at hc` turns
  `hc : b + c ≤ 5` into `hc : a + c ≤ 5`.
- Other relations: the rule can also be a strict inequality `a < b`, or
  another relation such as `⊆`, divisibility `∣` or congruence
  `≡ [ZMOD n]`. For example, with `h : a ≡ b [ZMOD n]`, `grw [h]` closes
  the goal `a ^ 2 + 1 ≡ b ^ 2 + 1 [ZMOD n]`, where `rw [h]` fails.
- Side conditions: for the goal `a * c ≤ 5`, `grw [h]` needs the step
  `a * c ≤ b * c`, which holds only for `0 ≤ c`. Lean tries to prove `0 ≤ c`
  by itself (for example from a hypothesis `0 ≤ c`); if it cannot, `grw` asks
  us to prove `0 ≤ c` as an extra goal.
- Closing the goal: at the end, `grw` tries `rfl`, just like `rw`.

**Official source.** Mathlib's file `Mathlib/Tactic/GRewrite/Elab.lean`
(search for `macro (name := grwSeq)`):
"`grw [e₁, ..., eₙ]` uses each expression `eᵢ : Rᵢ aᵢ bᵢ` (where `Rᵢ` is any
two-argument relation) as a generalized rewrite rule on the main goal, replacing
occurrences of `aᵢ` with `bᵢ`, then tries to close the main goal by "cheap"
(reducible) `rfl`."
https://leanprover-community.github.io/mathlib4_docs/Mathlib/Tactic/GRewrite/Elab.html#Mathlib.Tactic.GRewrite.grwSeq
-/

example (a b c : ℝ) (h : a ≤ b) (hy : b ≤ 2) (hb : b + c ≤ 5) : a + c ≤ 5 := by
  grw [h]
  /- here, Lean proves the intermediary step `a + c ≤ b + c` using Mathlib lemmas. -/
  exact hb

/-
## `grind`

**Summary.** `grind` is a strong automatic tactic. It argues by contradiction:
it assumes the negation of the goal and collects facts until it reaches `False`.
It combines several methods: from `a = b` it concludes `f a = f b`
(congruence closure), it applies lemmas tagged `@[grind]`, it splits into cases,
and it solves linear arithmetic and ring equations.
Its arithmetic is linear: it treats e.g. `x ^ 2` as an unknown number, so it
fails on `0 ≤ x ^ 2`. If `grind` fails, its error message ("Goal diagnostics")
lists what it found; the "assignment" lines give values for which it could not reach `False`.

`grind?` is to `grind` what `simp?` is to `simp`. On success it suggests a call
`grind only [...]` with only the lemmas it needed.

**Official source.** Lean's file `src/Init/Grind/Tactics.lean`
(search for `syntax (name := grind)`):
"`grind` is a tactic inspired by modern SMT solvers. [...] These engines work
together to handle equality reasoning, apply known theorems, propagate new
facts, perform case analysis, and run specialized solvers for domains like
linear arithmetic and commutative rings."
See also the Tactic Reference of the Lean manual:
https://lean-lang.org/doc/reference/latest/Tactic-Proofs/Tactic-Reference/#grind
-/

example (f : ℝ → ℝ) (x y : ℝ) (h₁ : x + y = 5) (h₂ : x - y = 1) : f x = f 3 := by
  grind

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

/-
NOTATION
-/

/-
## `▸`

**The macro `▸`.**  In term-mode, the macro `▸` works similarly to `rw`.
We can produce this symbol by typing `\t`.

In particular, if `h : a = b` and `e : P a`, then it follows that `h ▸ e : P b`.

Unlike `rw`, which needs `←` for the other direction, `▸` tries both `h` and
its reverse `b = a`.

**Official source.** Lean's file `src/Lean/Parser/Term.lean` writes:
"`h ▸ e` is a macro built on top of `Eq.rec` and `Eq.symm` definitions.
Given `h : a = b` and `e : p a`, the term `h ▸ e` has type `p b`.
You can also view `h ▸ e` as a "type casting" operation
where you change the type of `e` by using `h`.

The macro tries both orientations of `h`. If the context provides an
expected type, it rewrites the expected type, else it rewrites the type of e`."
https://leanprover-community.github.io/mathlib4_docs/Lean/Parser/Term.html#Lean.Parser.Term.subst
-/

/- The proof-term of each of the following examples is built from `Eq.rec`,
either directly or through definitions. Note that the recursor `.rec`
exists for any inductive type, including `Eq`.
-/
example (a b : ℕ) (P : ℕ → Prop) (h : a = b) (ha : P a) : P b := by
  rw [← h]
  exact ha

example (a b : ℕ) (P : ℕ → Prop) (h : a = b) (ha : P a) : P b := Eq.subst h ha

example (a b : ℕ) (P : ℕ → Prop) (h : a = b) (ha : P a) : P b := h ▸ ha

example (a b : ℕ) (P : ℕ → Prop) (h : a = b) : P a = P b := congrArg P h

example (a b : ℕ) (P : ℕ → Prop) (h : a = b) (ha : P a) : P b := by
  have h_prop : P a = P b := congrArg P h
  exact h_prop.rec ha

example (a b : ℕ) (P : ℕ → Prop) (h : a = b) (ha : P a) : P b := by
  have h_prop : P a = P b := congrArg P h
  exact cast h_prop ha
