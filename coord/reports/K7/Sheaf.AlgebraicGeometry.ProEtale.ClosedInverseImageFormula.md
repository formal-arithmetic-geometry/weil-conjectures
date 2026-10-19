## What changed

Proved `AlgebraicGeometry.Scheme.AffineProEt.closed_inverseImage_sheafification` in
`Sheaf.AlgebraicGeometry.ProEtale.ClosedInverseImageFormula`, with its signature unchanged.
The proof uses the opposite closed-site adjunction, precomposition, module sheafification,
and restriction through the fully faithful inclusion of sheaves to construct the basis
adjunction. The direct-image base-change square gives a natural isomorphism. Its inverse
mate is invertible across the affine-basis equivalences; evaluation on the inverse
coefficient realization gives the stated isomorphism.

This implements the current blueprint's Hom-adjunction argument directly in `ModuleCat Λ`.
Linearity, including all module operations and noncommutative scalars, is built into the
category, so the separate set-operation and coefficient-tensor arguments are unnecessary.
No definitions, signatures, public imports, visibility, or consumer modules changed.

Added proof imports of
`WeilConjectures.AlgebraicGeometry.ProEtale.AffineClosedSiteFunctorProperties` and
`WeilConjectures.CategoryTheory.InverseMateEquivalence`. The former supplies cocontinuity
needed to make the basis direct image; the latter is the existing proved categorical tool
for transporting this adjunction across equivalences. Their source declarations and DAG
nodes were read. Neither import creates a cycle, as checked with `import_direction.py may`.
These are tool uses from other units, rather than replacements for this unit's route;
the existing top-level `tool_uses` list was only pruned, not extended by the worker.

Updated the existing node's proof, proof dependencies and proof origin to match the Lean.
The unit's statement and route are retained. The three requested searches ran through
msearch.py (LeanFinder, Loogle, grep); local searches found the same categorical construction
in `AffineClosedInverseImageEvaluation` and `ClosedInverseImageLimits`. No imported theorem
already stated this module-valued formula.

Validation: the final proof compiled through lcompile.py without warnings (21.8 seconds
before adding explanatory comments). It handles the zero coefficient ring and the empty
closed fibre (I = top) without any nontriviality, commutativity or nonemptiness hypothesis.
No new assertion needs an edge-case qualification. Delivery preflight performs the final
compile and axiom probe. Existing imported results may themselves still depend on sorry,
as intended by stage 3; no claim of a sorry-free target import closure is made.

## Proved and sorry left

Closed 1 original hole:
`AlgebraicGeometry.Scheme.AffineProEt.closed_inverseImage_sheafification`
(node `lem-exc-closed-inverse-image-formula`).

The item's actual remaining hole count is 0. Added holes: 0. Split-off statements: 0.
No new declaration, axiom or holed definition was introduced.

## No longer needed

Removed these five redundant proof imports:

- `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`.
- `Sheaf.AlgebraicGeometry.ProEtaleConstantRingMap`.
- `Mathlib.CategoryTheory.Adjunction.Mates` (available through the inverse-mate tool).
- `Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations`.
- `Sheaf.AlgebraicGeometry.ProEtaleFiniteModules` (already available through the unchanged
  public realization import).

Removed the following node dependencies and their old top-level tool approvals:

- `lem-weil-pbc-conjugate-iso-unit-equation`: the proved inverse-mate equivalence tool
  handles the comparison across the two basis equivalences directly.
- `lem-weil-pbc-sheafification-sets-exact`: no lifting of set-level operations is needed
  when constructing the adjunction in ModuleCat.
- `prop-weil-pbc-proetale-constant-ring-map`: the actual statement is already in the
  canonical fixed-scalar presentation, so no separate coefficient comparison is applied.

The associated proof modules are not needed directly for this theorem. Public reexports
and other consumers can still reach them; no claim that these modules become globally
unreachable is made. No module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

No false statement or definition repair was found. The planned set-level algebraic
operation transport and tensor comparison are longer than necessary for the existing
Lean statement. The previously planned affine-basis and adjoint-uniqueness argument
works directly for left modules over an arbitrary ring, without passing through sets.
The mixed-size limits needed for the basis equivalence must be supplied explicitly via
`Limits.hasLimitsOfSizeShrink`; inference alone did not find them. All existing statement
hypotheses and the sheafification conclusion remain exactly as written.

## Second reading by K7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
