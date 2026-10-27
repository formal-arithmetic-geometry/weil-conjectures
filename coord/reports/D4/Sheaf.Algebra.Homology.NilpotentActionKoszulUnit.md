## What changed

Reduced `CategoryTheory.nilpotentActionKoszulUnit` to two strictly separate parts:
`nilpotentKoszulCoordinates` supplies the algebraic short exact sequence and its
canonical tensor coordinates; `roosNilpotentExactAugmentation` proves the generic
Roos augmentation result for an extension of a constant tower by a nilpotent tower.
The original theorem constructs its natural transformation explicitly, proves strict
naturality, proves that scalar nilpotence implies nilpotence of the quotient product
shift by induction on its powers, and applies the generic result level by level.
Its signature is unchanged.

The five existing concrete definitions moved verbatim to
`Sheaf.Algebra.Homology.NilpotentKoszulCoordinates`, publicly reexported by the
original module. There are no hollow definitions or chosen witnesses from an
unproved existence assertion in a definition. The existential coordinate theorem
is eliminated only in the proof of the existential original theorem.

## Proved and sorry left

Original hole closed by decomposition: `CategoryTheory.nilpotentActionKoszulUnit`
(node `lem-sp-nilpotent-action-koszul-unit`). Its proof is complete from the two
following new statements. This is a decomposition, not an unconditional proof and
not a positive net hole reduction: one upper hole closed, two lower holes added.

Two holes remain, both new public theorems with complete source proofs in their
docstrings:

- `CategoryTheory.nilpotentKoszulCoordinates`, node
  `lem-sp-nilpotent-koszul-coordinates`, new module
  `Sheaf.Algebra.Homology.NilpotentKoszulCoordinates`.
- `CategoryTheory.roosNilpotentExactAugmentation`, node
  `lem-sp-roos-nilpotent-exact-augmentation`, new module
  `Sheaf.CategoryTheory.RoosExactAugmentation`.

The original module has zero `sorry`. The three constant-tower construction helpers, the private naturality lemma,
and the two private nilpotence calculation helpers are complete. The scalar power
lemma covers exponent zero as well as positive exponents; the generic augmentation
lemma assumes exponent at least one. Zero complexes and the zero section satisfy
both statements. No cohomological boundedness is used.

## No longer needed

Removed the original proof imports `Sheaf.CategoryTheory.StrictRoosComparison`,
`Mathlib.Algebra.Homology.HomotopyCategory.DegreewiseSplit`, and
`Mathlib.CategoryTheory.Triangulated.Pretriangulated`. The new coordinate module
also omits the unused `StrictRoosModel` and
`RingedStrictTowerHomotopyLimitIndependentCoefficients` imports. The original theorem does
not need a derived-triangle splitting interface: the generic short exact Roos
argument subsumes that step. Removed the original node's tool-use approval for
`strictRoosComparison`, because the proof does not call it.

The original node's direct dependencies `lem-weil-strict-roos-comparison`,
`lem-weil-pbc-degreewise-split-derived-triangle`, and `lem-pc-derived-zero-third-split` are
not used by the new proof. No module is withdrawn, and no adopted source-library
declaration is removed. The abstract derived-category and tensor/tower definition
nodes remain needed through the new lemmas. The blueprint unit route is preserved.

## Where the brief, the DAG or earlier work was wrong

The tensor-coordinate step requires a substantial canonical direct-sum calculation;
it is now stated as its own item rather than hidden in the upper theorem. The
existing strict Roos comparison is specialized to a coefficient universe tied to
the site universes, whereas this theorem permits the independent coefficient
universe `r`. Consequently it cannot directly discharge the generic independent
universe assertion. The new generic Roos lemma states precisely the short exact
sequence and nilpotent product-shift argument needed here. No original statement
is marked disputed or weakened.

## New nodes

`lem-sp-nilpotent-koszul-coordinates` is the algebraic part of steps 1--2 of the
original node: canonical two-summand coordinates, the short exact tower sequence,
and its scalar transitions. It has no augmentation, nilpotence, or derived-limit
conclusion. Existing concrete definitions are owned by its module without changes.

`lem-sp-roos-nilpotent-exact-augmentation` is steps 3--6 abstracted to a
Grothendieck abelian category with exact countable products. Its assumption is
nilpotence of the product-shift endomorphism, not scalar nilpotence. It has no
Koszul tensor, canonical coordinate, scalar, or natural-family construction.
The original theorem supplies the connection by its proved product-shift formula.

Change record: `coord/changes/D4-nilpotent-koszul-coordinate-definitions.md`.

## Second reading by D4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
