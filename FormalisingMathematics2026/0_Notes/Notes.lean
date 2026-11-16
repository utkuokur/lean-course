import Mathlib

set_option linter.all false

/-
NOTES
-/

/-
## Cross-reference tags: `@[wikidata ...]`, `@[stacks ...]`, ...

**Summary.** Some Mathlib declarations carry a tag that links them to an entry
in an external database, for example the definition of `IsOpen`:
```
@[wikidata Q213363]
def IsOpen : Set X → Prop := TopologicalSpace.IsOpen
```
Wikidata (https://www.wikidata.org) is a free online database run by the
Wikimedia Foundation, the organisation behind Wikipedia. It gives every concept
a fixed ID: `Q213363` is "open set" (https://www.wikidata.org/wiki/Q213363).
Such a tag links the Lean declaration to that entry, so that tools and websites
can connect Mathlib to other sources. It is only a label: it changes nothing in
the definition or in proofs.

Each database has its own tag and a command that lists all Mathlib declarations
carrying it:
* `@[wikidata ...]`: Wikidata, https://www.wikidata.org
  (`#wikidata_tags`, about 160 declarations)
* `@[stacks ...]`: Stacks Project (algebraic geometry),
  https://stacks.math.columbia.edu (`#stacks_tags`, about 575 declarations)
* `@[kerodon ...]`: Kerodon (higher category theory), https://kerodon.net
  (`#kerodon_tags`, 16 declarations)
* `@[dlmf ...]`: Digital Library of Mathematical Functions,
  https://dlmf.nist.gov (`#dlmf_tags`, 14 declarations)
* `@[lmfdb ...]` (LMFDB, https://www.lmfdb.org) and `@[pibase ...]`
  (π-Base, https://pi-base.org) exist too, but no declaration uses them yet.

**Official source.** Mathlib's file `Mathlib/Tactic/CrossRefAttribute.lean`:
"This file provides attributes for tagging Mathlib results with cross-references
to entries in external mathematical databases".
-/

-- uncomment to see a long list
-- #stacks_tags
-- #wikidata_tags

/-
## `irreducible_def`

**Summary.** `irreducible_def` works like `def`, but Lean does not unfold the new
definition by itself; for example, `rfl` cannot see inside it. To use the
definition, rewrite with the lemma that the command creates automatically,
named with `_def` at the end. Mathlib uses this for definitions that should only
be used through their lemmas, e.g. the neighbourhood filter `nhds` with its
lemma `nhds_def`.

**Official source.** Mathlib's file `Mathlib/Tactic/IrreducibleDef.lean`:
"This file defines an `irreducible_def` command, which works almost like the
`def` command except that the introduced definition does not reduce to the value.
Instead, the command adds a `_def` lemma which can be used for rewriting."
https://leanprover-community.github.io/mathlib4_docs/Mathlib/Tactic/IrreducibleDef.html#Lean.Elab.Command.command_Irreducible_def____
-/

irreducible_def double (n : ℕ) : ℕ := n + n

#check double_def   -- double_def (n : ℕ) : double n = n + n

example : double 2 = 4 := by
  -- rfl            -- fails: `rfl` cannot see inside `double`
  rw [double_def]   -- the goal becomes `2 + 2 = 4`, which `rw` closes by itself

#check nhds_def     -- the `_def` lemma of `nhds`
