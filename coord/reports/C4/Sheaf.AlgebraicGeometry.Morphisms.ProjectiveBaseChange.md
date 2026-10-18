## What changed

Proved `AlgebraicGeometry.projective_base_change` in
`Sheaf.AlgebraicGeometry.Morphisms.ProjectiveBaseChange`, with its exact original
signature. Extract the finite-coordinate closed immersion, construct its base-changed
map by `ProjectiveSpace.liftBaseChange`, and prove the embedding square cartesian
by `ProjectiveSpace.isPullback_liftBaseChange`. Mathlib’s
`MorphismProperty.of_isPullback` transfers closed immersion; the map’s structural
projection equation and Mathlib’s quasi-compact pullback instance construct the
projectivity class. This is the original two-step geometric argument with the
already-proved projective-space API, without new intermediate statements.

Reduced imports to `Mathlib.AlgebraicGeometry.Pullbacks` and the canonical
`WeilConjectures.AlgebraicGeometry.Morphisms.Projective`, both public because the
statement uses them. Updated the node’s proof and dependencies to the actual
argument. Import-interface change record:
`coord/changes/C4-projective-base-change-import-pruning.md`.

Validation: the item compiles cleanly through `lcompile.py`. All six unchanged
direct consumers are checked against the new module; delivery preflight checks
the theorem’s axioms. No target statement or definition changes.

## Proved and sorry left

Closed the single original hole:
`AlgebraicGeometry.projective_base_change`
(node `lem-pc-projective-base-change`). Proved 1 of 1 original sorries.
Added 0 holes; split off 0 statements. No sorry remains in the delivered module.

## No longer needed

Removed imports:

- `WeilConjectures.AlgebraicGeometry.Modules.VeryAmple`: its very-ample field-extension
  theorem is unnecessary; the generic projective-space lift API handles arbitrary bases.
- `WeilConjectures.AlgebraicGeometry.Curve.SmoothProjective`: replaced with the canonical
  lower module `WeilConjectures.AlgebraicGeometry.Morphisms.Projective` defining projectivity.
- `Sheaf.AlgebraicGeometry.BaseChangeConventions` and
  `WeilConjectures.AlgebraicGeometry.BaseChangeConventions`: no module, fibre, or section
  comparison is needed; Mathlib’s pullback object and equations suffice.

Removed proof dependency `def-pc-base-change`: the proof uses fibre-product equations
from `def-pc-fibre-product` directly. Removed `lem-pc-closed-imm-base-change` as an
input: its recorded declaration is only a very-ampleness field-extension specialization,
whereas Mathlib’s generic stability instance (the existing leaf
`lem-weil-pbc-closed-immersion-base-change`) gives exactly the required fact.
The ideal-sheaf and flatness assertions of the former node are unnecessary here.
Retained the projective definition, fibre-product node, and quasi-compact base-change
leaf. Explicitly recorded the already-proved generic projective-space square
`lemma-nagata-projective-space-base-change-pullback`, which the original proof used
implicitly. No unit statement or unit step is bypassed. These are removed import
edges and proof dependencies; no claim is made that their modules are globally unreachable.

## Where the brief, the DAG or earlier work was wrong

The attachment of `lem-pc-closed-imm-base-change` names
`IsVeryAmple.pullback_of_field`, which only treats very ample modules under field
extension and cannot directly prove the arbitrary scheme-morphism step here.
The already-existing Mathlib leaf supplies the needed generic closed-immersion
base-change result. The projective-space cartesian-square API is already proved
upstream and makes the general factorization argument short.

The proof does not assume separatedness or flatness of the base-change morphism.
The cartesian-square argument, rather than cancellation of a closed immersion
along a separated map, is essential for this generality. Identity base changes,
empty schemes, and an empty finite coordinate type require no extra cases or
hypotheses: every construction and Mathlib stability lemma used applies to them.

## Second reading by C4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
