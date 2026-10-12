## What changed

Replaced the target's `sorry` with a reduction to a local matrix characteristic-polynomial
identification, Mathlib's monicity and degree lemmas, and localization injectivity.
The existing declaration `Matrix.isIdempotentElem_idempotentCharpoly_leadingCoeff` has
exactly its original signature, hypotheses, conclusion, and definition dependencies.
Its original copyright header, module documentation, and theorem docstring were restored.

Added `Sheaf.LinearAlgebra.IdempotentCharpolyLocalCharpoly`, stating the local determinant
identification with a complete proof in words. The new module publicly imports the summand
polynomial definition and localization API needed by its statement. The main module imports
it, `Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff`, and
`Mathlib.RingTheory.LocalProperties.Submodule` only for the proof.
The finite-projective cover and image-base-change imports moved to the new module,
where they supply the remaining hole's proof plan.

## Proved and sorry left

Hole closed: `Matrix.isIdempotentElem_idempotentCharpoly_leadingCoeff`
(node `lem-weil-pbc-idempotent-charpoly-leading-coeff`).

Hole added and left: `Matrix.exists_standardCover_idempotentCharpoly_eq_charpoly`
(node `lem-weil-pbc-idempotent-charpoly-local-charpoly`). Its proof is exactly `by sorry`,
in its own module, with a source and complete natural-language proof.

This delivery is a decomposition: one existing hole closed, one strictly intermediate
hole added; net hole reduction is zero. The target's coefficient comparison and gluing
steps are fully proved; the finite-free cover and determinant identification remain open.
The target is not axiom-complete: its axiom set still includes `sorryAx` through this
intermediate statement. No definitions or data constructions are added.

The first worker's unpublished `Matrix.idempotentCharpoly_leadingCoeff_local` hole and
`Matrix.isIdempotentElem_of_localized_span` helper were removed. The latter's correct
Mathlib injectivity argument is preserved directly inside the target's proof.

## No longer needed

Removed first-worker-only imports `Mathlib.GroupTheory.MonoidLocalization.Away` and
`Sheaf.RingTheory.CoverModuleExact`; neither supplies a declaration used by the proof.
`Mathlib.RingTheory.Localization.Away.Basic` is public only in the new module, whose
statement mentions localization and its algebra map; it is no longer a public addition
to the main module. The original public import and the existing signature are preserved.

The old direct proof dependencies
`lem-weil-pbc-idempotent-endomorphism-image-base-change`,
`lem-weil-pbc-finite-projective-standard-free-cover`, and
`def-weil-pbc-idempotent-charpoly` now belong to the new local-identification node's plan.
They remain reachable through it (and the definition remains a statement dependency).
The old characteristic-polynomial and localized-span dependencies are used directly.
No old node or module is made unreachable globally; pruned modules: none.

Removed the two unpublished split nodes
`lem-weil-pbc-idempotent-charpoly-leading-coeff-local` and
`lem-weil-pbc-idempotent-charpoly-leading-coeff-glue` from the proposed delivery.

## Where the brief, the DAG or earlier work was wrong

The first worker's local-idempotence statement was equivalent to the target: a singleton
cover with element 1 proves it from the target, and injectivity proves the target from it.
It therefore postponed the whole argument. Its docstring also failed to distinguish the
leading coefficient of a mapped polynomial from the mapped original leading coefficient.
That distinction matters when localization lowers the degree.

The replacement gap is exactly the first two steps of the original node's argument:
construct a standard cover and identify the determinant on each member with a matrix
characteristic polynomial. It contains no leading-coefficient claim. The main module now
proves the separate degree-loss and gluing steps, including zero localizations.
The old target node did not describe the first worker's actual reduction; it now agrees
with the code. The new node has an explicit dependency plan, replacing generic placeholders.

The local source checkout has no `literature/stacks-project/more-algebra.tex`; the cited
paragraph was read from the official Stacks page https://stacks.math.columbia.edu/tag/09XI.
LeanSearch returned Internal Server Error and is recorded as unavailable. LeanFinder,
Loogle, Mathlib grep, and searches in both Lean roots found no exact existing local
identification. The private determinant-map/conjugation/block calculations in
`Sheaf.RingTheory.AdjoinRootIdempotentCharpolyMap` cover portions of a future proof,
but do not construct the standard cover or identify an arbitrary idempotent image.

## New nodes

`lem-weil-pbc-idempotent-charpoly-local-charpoly` is the remaining local determinant
identification, in `Sheaf.LinearAlgebra.IdempotentCharpolyLocalCharpoly`. It realizes
steps 1 and 2 of the old node's plan and records the existing image-base-change and
finite-projective standard-free-cover dependencies. Its `lean.statement` is copied
verbatim from its new declaration. No change records are needed: no existing statement
or definition was changed.

## Second reading by R2

1. Compared the delivered main module with the repository version. PASS: the only existing
   declaration has its byte-for-byte original signature. The existing definition and
   original public import are unchanged; all new imports in this module are proof-only.
   The original documentation and copyright header were restored.
2. Compiled both modules individually in import order through `lcompile.py`. PASS: no errors
   or warnings. There is exactly one direct `sorry`, in the reported named intermediate
   theorem, and none in a definition. Scratch-copy `#print axioms` checks show only
   `propext`, `Classical.choice`, `Quot.sound`, and the expected `sorryAx`; no forbidden
   declarations or implementation escape mechanisms occur.
3. Checked the replacement statement against the split decomposition argument and searched
   the library and Mathlib independently. PASS: its hypotheses are the original idempotence
   and commutation hypotheses, and its conclusion is the local determinant identification,
   a genuine earlier portion of the argument. Cases checked: P=0 gives the empty matrix
   characteristic polynomial 1; P=1 gives T.charpoly; an empty ambient index set gives 1;
   the zero ring admits the singleton cover with d=0; a product ring with different local
   image ranks is allowed because d varies by cover member. For example, over Z×Z the
   rank-one projector (1,0) gives local polynomials X and 1 and global leading coefficient
   (1,0), exactly the degree-drop case handled by the new proof. The remaining hole has
   a complete proof in words, including refinement, base change, and basis invariance.
4. Read top-down and checked the old proof dependencies and the unit's `realized` record.
   PASS after repair: the degree and glue steps use proved Mathlib declarations; the only
   remaining hole is the finite-cover determinant realization. No step realizing the
   unit statement or its route is bypassed. All removed direct proof dependencies are
   listed above, and those transferred to the new lemma remain transitively reachable.
5. Compared both node records with their Lean declarations and actual/planned proofs.
   PASS after repair: the target's proof dependencies name the local identification,
   the characteristic-polynomial Mathlib leaf, and localization injectivity. The new node
   has complete creation/source/search/blueprint/Lean metadata and the union of its steps'
   dependencies. No stale local-idempotence or gluing node remains in the delivery.

Second reading changes: removed the equivalent local-idempotence hole; added the genuine
local matrix-charpoly identification in its own module; proved the coefficient comparison
and preserved the gluing proof inline; removed redundant imports and helpers; restored
original documentation; repaired node records and this report. This is a decomposition,
not a claim of one net theorem hole eliminated.
