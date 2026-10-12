## What changed

The existing signature of `Algebra.exists_smooth_quotient_factorization` is byte-for-byte
unchanged. Its proof now carries out the square-zero lift, nilpotent Nakayama argument,
finitely generated kernel calculation, containment in the extended base ideal, and
quotient factorization. Mathlib's `Algebra.FormallySmooth.comp_surjective`,
`Algebra.FinitePresentation.ker_fG_of_surjective`, and
`Ideal.quotientKerAlgEquivOfSurjective` provide the lifting, kernel and isomorphism steps.
The existing `RingTheory.surjective_of_surjective_mod_nilpotent` supplies Nakayama.

The new module `Sheaf.RingTheory.PopescuLiftOnceCore` states only the preceding
presentation construction, `Algebra.exists_smooth_reduction_factorization`: obtain a
finitely presented intermediary and a smooth algebra with isomorphic reductions.
It does not assert a lift, surjectivity, a kernel bound, a finitely generated kernel,
or the final quotient factorization. Its statement does not need `I² = 0`.

## Proved and sorry left

Hole closed: `Algebra.exists_smooth_quotient_factorization`
(node `lem-weil-pbc-popescu-lift-once`), by a reduction from the presentation construction
and the existing nilpotent Nakayama theorem. The item's module contains no `sorry`.

Hole added: `Algebra.exists_smooth_reduction_factorization`
(node `lem-weil-pbc-popescu-lift-once-core`) in `Sheaf.RingTheory.PopescuLiftOnceCore`.
This named theorem is exactly `:= by sorry` and has a complete source-based docstring
proof. The previous sandbox theorem `Algebra.exists_smooth_quotient_core` is removed;
it was not an existing repository declaration.

This delivery is a decomposition: one upper hole closed and one new lower hole added,
for net zero in the holes directly changed. It is not a sorry-free proof. The existing
`RingTheory.surjective_of_surjective_mod_nilpotent` and
`Algebra.ind_isStandardSmooth_of_ind_smooth` remain open dependencies; their files are
unchanged. No definition, arbitrary witness definition, or axiom is added.

## No longer needed

Removed the direct proof-only import `Sheaf.RingTheory.IndStandardSmooth` from the
item; it remains a proof-dependency import of the presentation construction.
Removed the unnecessary public `Mathlib.RingTheory.Ideal.Quotient.Operations` import
from the first worker's new module. Existing public imports are unchanged.
No library module is claimed globally pruned.

The following old `proof_deps` are no longer directly used by the item, but belong to
the presentation construction's route and remain in its node:

- `lem-weil-pbc-colimit-standard-smooth-algebras`
- `def-weil-pbc-filtered-colimit-smooth-algebras`
- `def-weil-pbc-standard-smooth-algebra`
- `lem-weil-pbc-filtered-colimit-algebras-elementwise`
- `lem-weil-pbc-finite-presentation-algebra-factors-filtered-colimit`
- `def-weil-pbc-finite-type-algebra`
- `lem-weil-pbc-finite-presentation-over-finite-type-algebra`
- `lem-weil-pbc-finite-presentation-base-change-composition`
- `def-weil-pbc-polynomial-partial-derivative`
- `lem-weil-pbc-standard-smooth-is-smooth`

The item's retained dependencies are square-zero lifting, nilpotent Nakayama,
finitely presented algebras, smooth ring maps, and finite-generation of the
surjection kernel, together with the new presentation construction node.

## Where the brief, the DAG or earlier work was wrong

The first worker's core included essentially the entire desired quotient factorization
and its node cited the item itself, creating a circular proof dependency. It also
lacked the required complete natural-language proof, used unverified search records,
did not update the original node's proof route, and reported a decomposition as a proof.
The second reading repairs all of these. The original twelve-step argument agrees
with Stacks Tag 07CK; its last four steps are now formalized rather than repackaged.
No statement change or forced adaptation of another module is needed.

## New nodes

`lem-weil-pbc-popescu-lift-once-core`, file
`dag/nodes/sec-proper-base-change/lem-weil-pbc-popescu-lift-once-core.json`, records
only original steps 1--8, the presentation construction before square-zero lifting.
Its statement is self-contained, its Lean signature is verbatim, its proof dependencies
are the union of the steps' uses, and it has real searches recorded in `searches.jsonl`.
LeanSearch returned HTTP 500 and is recorded as unavailable; LeanFinder and grep
provided no exact match. No change record is needed because no existing statement
or definition changes.

## Second reading by R2

1. Compared the delivered item against the repository with `diff` and separately
   asserted byte-for-byte equality of the original theorem signature. All existing
   signatures, definitions, public imports, and visibility are unchanged. No relevant
   statement-change records were found in `coord/changes`. Verdict: passes.
2. Compiled both modules through `lcompile.py` in dependency order with no errors or
   warnings. Inspected every proof and searched for prohibited declarations: the only
   new direct hole is the named presentation theorem; there are no definitions.
   Scratch `#print axioms` checks show only `propext`, `Classical.choice`, `Quot.sound`,
   and the expected transitive `sorryAx`. Verdict: passes as a decomposition.
3. Read the complete proof of Stacks Tag 07CK from the local Stacks source. Checked
   the construction for `I = 0`, `I = top`, zero rings, and empty generator/relation
   families (the empty Jacobian determinant is 1). The construction preceding lifting
   works for arbitrary I; square-zero is used in the delivered lift. Searched Mathlib,
   upstream and Sheaf under alternative presentation/reduction terminology. Found and
   used the stronger Mathlib surjective-kernel theorem instead of adding another hole.
   The one new theorem is only the presentation portion of the argument, with a full
   docstring proof and matching node. Verdict: passes after replacing the near-restatement.
4. Followed original steps 1--8 in the new node and checked steps 9--12 in Lean.
   Removed the unnecessary new public import and relocated the standard-smooth
   dependency import to the construction module. All ten old dependencies no longer
   used directly are named above. Checked `dag/units/sk-thm-p1.json`: this node is
   not a realization of a unit statement or step; the unit route is unchanged.
   No whole-module pruning or net proof progress is claimed. Verdict: passes.
5. Updated the original node's `proof`, `proof_deps`, and `proof_origin` to match the
   implemented reduction. Replaced the new node's circular dependency by the original
   first eight steps, with their cited prerequisites. Its Lean record matches the
   replacement theorem verbatim, and searches record actual results. Verdict: passes.

Changed during second reading: replaced the nearly complete core conclusion by the
presentation-only statement; implemented lifting, Nakayama transport, kernel FG and
containment; preserved the final composition calculation; repaired docstring, searches,
DAG and report; removed the unnecessary new public import. All changes are in the sandbox.
