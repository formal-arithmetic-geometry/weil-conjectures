## What changed

The retained theorem proves naturality, representative normalization, and the finite
projection equations. Its two remaining inputs are the isomorphism sub-result and a
strictly smaller K-flat/finite-balancing result. The latter assumes neither a derived
object C nor completeness, and contains none of the normalized Roos or projection
equations now proved in the retained module. All ten existing definitions moved unchanged
to a publicly re-exported dependency module to avoid an import cycle. The existing theorem
signature is unchanged. The DAG follows this argument.

## Proved and sorry left

Closed the original syntactic hole in `WeilConjectures.integralLineTensorComparison`
by a decomposition, adding the two holes
`WeilConjectures.integralLineTensorComparison_iso`
(node `lem-sf-integral-line-tensor-comparison-iso`) and
`WeilConjectures.integralLineTensorComparison_representative`
(node `lem-sf-integral-line-tensor-comparison-representative`). This is one hole closed
and two added, net -1; it is a decomposition, not a complete proof of the original
mathematics. The private lemmas `normalization` and `roosUnit_projection` are fully proved,
as are their uses to establish every normalized projection equation. No definition
contains a hole. All four modules compile without errors or non-sorry warnings.

## No longer needed

The following original proof-only imports were removed; the retained proof and moved
constructors compile without them:

- `Sheaf.NumberTheory.Padics.ExtensionIntegersDvr`
- `Sheaf.Paper.CompletedConstantSheafReduction`
- `Sheaf.CategoryTheory.LocalizedModuleExactIndependent`
- `Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact`
- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`
- `Sheaf.Algebra.Homology.ChangeOfRingsKFlat`
- `Sheaf.Paper.EtaleDerivedScalarTensor`
- `Sheaf.Paper.FiniteFreeCompletedScalarComparison`
- `Sheaf.Paper.IntegralOperationsWellDefined`
- `Sheaf.Algebra.Homology.AcyclicKFlatTensor`
- `Sheaf.Algebra.Homology.SheafRingDerivedCoefficientAdjunction`
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`
- `Sheaf.CategoryTheory.LocalizedModuleExactForSystems`

The retained theorem directly needs only the two new sub-results and
`def-pur-integral-derived-operations`. In particular, the projection equation needs no
separate derived coefficient adjunction, derived change-of-rings, or K-flat descent:
it follows from normalization and the actual mapping-cocone projection. Those original
proof steps are replaced, while the finite balancing and invertibility work remains
recorded in the two new nodes. No whole original module is withdrawn; other nodes may
still use those imports. The original unit statement and route remain.

## Where the brief, the DAG or earlier work was wrong

The original plan proposed an adjunction/descent argument for naturality and the
projection square. Both follow directly from the existing completion-unit
characterization and the actual cone projection. The missing K-flat witnesses and
finite balancing isomorphism are independent of completeness and of the choice of a
derived representative isomorphism.

## New nodes

`def-sf-integral-line-tensor-comparison-constructors` records the ten existing
constructors in their new dependency module, with unchanged signatures and bodies.

`lem-sf-integral-line-tensor-comparison-iso` states only invertibility of the prescribed
comparison and carries its source and proof in words.

`lem-sf-integral-line-tensor-comparison-representative` states only the K-flat models
and finite balancing maps with their pure-tensor formula; it omits the Roos and
projection equations proved here and does not assume completeness.

Change record: `coord/changes/integral-line-tensor-comparison-definitions.md`.

## Second reading by H2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
