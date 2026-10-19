## What changed

Partial proof pass for `Sheaf.AlgebraicGeometry.FiniteOpenExchangeScalars`.
Coefficient naturality reuses
`Scheme.proEtaleConstantInverseImageMap_naturality` from
`Sheaf.AlgebraicGeometry.ProfiniteCoefficientInverseImage` through a proof-only import.
The pullback comparison is identified with its direct-image mate; the standard mate
unit and counit equations prove the two adjunction compatibility assertions.
Identity and compatible ambient restriction comparisons are constructed sectionwise
using Mathlib's module restriction isomorphisms, with uniqueness proved by extensionality.
Coefficient composition is functoriality. The inverse-unit formula is proved by
reducing to the recorded singleBetaInv component.
Semilinear transition squares follow from scalar compatibility, exchange naturality,
and cancellation by the exchange isomorphism. These squares assemble the strict
abelian and ambient module towers using NatTrans.ofOpSequence, with the specified
isomorphisms and their inverses as components.
All existing declaration signatures and definitions are retained.
Validation: the retained complete item compiles with lcompile.py against the current
published library in 36.5 seconds, with no errors or warnings.

## Proved and sorry left

All names below belong to
`AlgebraicGeometry.ProEtale.StrictTower.FiniteOpenScalars`.
Closed 12 of the original 16 holes: `coefficientSquare`, `open_unit_counit`,
`pull_unit_counit`, `resId_existsUnique`,
`ambientRes_existsUnique`, `coefficientMap_comp`, `inverse_unit_transpose`,
`exchange_transition`, `exchange_strict_towers`, `exchange_ambient_towers`, `scalar_identity`, `pull_identity`.
No holes added and no statements split off.

The 4 original holes remain in `openResMap_isIso`, `exchange_restrictScalars`,
`scalar_composition`, and `pull_composition`.
Each belongs to node `lem-cbc-finite-open-exchange-scalars` and retains its original
source and complete proof docstring. The scalar exchange and coherence arguments
still need their normalized mate calculations. The tower assertions are now
assembled from the proved transition equalities using NatTrans.ofOpSequence
and naturality of the action-forgetting comparisons.

## No longer needed

All original public imports remain required by unchanged statements and definitions.
The following direct proof imports, added to the shared source since the retained
sandbox was written, are absent from this delivery:

- `Sheaf.AlgebraicGeometry.ProEtaleConstantExact`
- `Sheaf.AlgebraicGeometry.ProEtaleDerivedExtensionZeroBaseChange`
- `Sheaf.AlgebraicGeometry.ProEtaleExtensionZero`
- `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`
- `Sheaf.CategoryTheory.SiteMorphismComposition`
- `WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf`

The completed proofs use the normalized constant-ring module constructions from the
unchanged public imports and the proved constant-coefficient naturality theorem.
They do not use the separate ModuleCat-valued extension and base-change assertions.
The remaining original holes retain their proof plans and dependency nodes; no
whole module or DAG dependency is claimed pruned from the targets' closure.

## Where the brief, the DAG or earlier work was wrong

The previous attempt repaired several uncompiled proofs and removed a global diagnostic
heartbeat limit. This session retained its compiling six-hole proof pass and report,
then closed the inverse-unit transpose, semilinear transition, tower and identity
coherence obligations.
The planned dependencies now expose some extension-by-zero statements in ordinary
ModuleCat-valued sheaf coordinates, whereas this module uses constant ring-sheaf
module coordinates. Their scalar compatibility cannot be applied here without a bridge.
No statement has been weakened or changed.

The previous attempt did not deliver because its worktree checkout timed out.
This session resumed the required dry run and checked the retained proof against
the current published library. No launcher files were changed or worked around.

Local proof commands flagged by preflight are documented in
`coord/changes/FiniteOpenExchangeScalarsProofCommands.md`; no consumer changes are needed.

## Second reading by B9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
