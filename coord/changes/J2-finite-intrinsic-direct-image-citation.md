# def-sp-finite-intrinsic-direct-adjunction: finite direct-image citation

## Reason

The node `def-sp-finite-intrinsic-direct-adjunction` incorrectly cites the bundled
integral/common-stage direct-image construction for the ordinary uncompleted
K-injective direct image on finite constant coefficients. This introduces an
artificial dependency back to the scalar cone normalization item.

## Old

Let $A$ be a finite commutative ring and $f:X\to Y$ a scheme morphism. Use intrinsic inverse image [def-sp-finite-intrinsic-pullback] and the actual constant-coefficient module direct image [def-weil-proetale-inverse-image]. Transport the fixed-scalar inverse-image/direct-image adjunction through the canonical realization equivalences, then conjugate its right adjoint by the direct-image comparison uniquely fixed to be identity on constant-scalar unit sections. This defines the existing sfIntrinsicConstantModuleAdjunction. Its right-derived adjunction uses the specified K-injective direct image [def-weil-derived-direct-image], and its derived realization comparison is the localization of that same section-normalized map on K-injective representatives.

The statement, proof dependencies and proof steps 3–4 cite
`def-weil-derived-direct-image`.

## New

Let $A$ be a finite commutative ring and $f:X\to Y$ a scheme morphism. Use intrinsic inverse image [def-sp-finite-intrinsic-pullback] and the actual constant-coefficient module direct image [def-weil-proetale-inverse-image]. Transport the fixed-scalar inverse-image/direct-image adjunction through the canonical realization equivalences, then conjugate its right adjoint by the direct-image comparison uniquely fixed to be identity on constant-scalar unit sections. This defines the existing sfIntrinsicConstantModuleAdjunction. Its right-derived adjunction uses the specified K-injective direct image [def-weil-pbc-proetale-operations], and its derived realization comparison is the localization of that same section-normalized map on K-injective representatives.

Replace these citations by `def-weil-pbc-proetale-operations`. No mathematical
statement, construction, or Lean source changes. In
`Sheaf.AlgebraicGeometry.SfIntrinsicRealizationTransport`, lines 447–475,
`sfIntrinsicDerivedDirectImageComparison_existsUnique` uses
`proEtaleConstantDerivedDirectImage f A` and ordinary fixed-scalar lower star.
The former is defined in `ProEtaleConstantDerivedDirectImage`, lines 47–49, as
`(proEtaleConstantModuleDirectImage f A).rightDerivedFunctor`; both its docstring
and its module docstring explicitly identify
`def-weil-pbc-proetale-operations`. This is exactly the uncompleted K-injective
construction described by that node. The intrinsic adjunction itself at lines
485–498 is the same transported underived adjunction as before.

## Users

Only the node metadata changes; no Lean source, declaration signature, instance,
attribute or public import changes. Its attached module
`Sheaf.AlgebraicGeometry.SfIntrinsicRealizationTransport` is unclaimed.
All existing DAG citers are also recorded individually, with `holds: true`, in
`statement_change.citers`. Their attached modules are listed below; their
interfaces and proofs still apply verbatim, so no adaptation or importer
compilation against changed Lean code is necessary.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.SfIntrinsicRealizationTransport | unclaimed | Node citation only; no Lean change. |
| Sheaf.AlgebraicGeometry.IdentityFullCohomologicalDimension | unclaimed | Cited finite construction unchanged. |
| Sheaf.AlgebraicGeometry.ProEtaleConstantOpenSquareExchange | unclaimed | Cited finite construction unchanged. |
| Sheaf.Paper.DiagonalTraceFiniteChernComparison | unclaimed | Cited finite construction unchanged. |
| Sheaf.Paper.DiagonalTraceFiniteUnitCohomology | unclaimed | Cited finite construction unchanged. |
| Sheaf.Paper.DiagonalTraceUnitArrowComparison | unclaimed | Cited finite construction unchanged. |
| Sheaf.Paper.ExceptionalFiniteIntrinsicBounds | unclaimed | Cited finite construction unchanged. |
| Sheaf.Paper.ExceptionalFiniteOperations | unclaimed | Cited finite construction unchanged. |
| Sheaf.Paper.ExceptionalFiniteRestrictionAdjunction | K9 | Cited finite construction unchanged. |
| Sheaf.Paper.ExceptionalProEtaleRealization | unclaimed | Cited finite construction unchanged. |
| Sheaf.Paper.FiniteCoefficientSmoothPurity | unclaimed | Cited finite construction unchanged. |
| Sheaf.Paper.FiniteExceptionalSiteNormalization | unclaimed | Cited finite construction unchanged. |
| Sheaf.Paper.FiniteKernelConstructibleLocalization | unclaimed | Cited finite construction unchanged. |
| Sheaf.Paper.FiniteP1CoefficientAdjunctionCoordinates | F9 | Cited finite construction unchanged. |
| Sheaf.Paper.IntegralCompactSupportCoefficientComparison | P7 | Cited finite construction unchanged. |
| Sheaf.Paper.IntegralOpenSupportNormalization | unclaimed | Cited finite construction unchanged. |
| Sheaf.Paper.PointIdentitySupportNormalization | unclaimed | Cited finite construction unchanged. |
| Sheaf.Paper.ProperCompactCoincidence | unclaimed | Cited finite construction unchanged. |
| Sheaf.Paper.SfDirectImageCTFEtaleOrigin | unclaimed | Cited finite construction unchanged. |
| Sheaf.SecSmoothPurity.MixedBaseChangeOperations | unclaimed | Cited finite construction unchanged. |
| Sheaf.SixFunctors.AmbientAdjunctionCompositorNormalization | unclaimed | Cited finite construction unchanged. |
| Sheaf.SixFunctors.FiniteReturnFrobeniusCancellation | unclaimed | Cited finite construction unchanged. |
| Sheaf.SixFunctors.OpenClosedWeilMateCoefficient | unclaimed | Cited finite construction unchanged. |
| Sheaf.SixFunctors.OpenClosedWeilMateCompletion | unclaimed | Cited finite construction unchanged. |
| Sheaf.SixFunctors.OpenClosedWeilMateData | unclaimed | Cited finite construction unchanged. |
| Sheaf.SixFunctors.OpenClosedWeilMateDescent | unclaimed | Cited finite construction unchanged. |
| Sheaf.SixFunctors.OpenClosedWeilMateFinite | unclaimed | Cited finite construction unchanged. |
| Sheaf.SixFunctors.OpenClosedWeilMateIntegral | unclaimed | Cited finite construction unchanged. |
| Sheaf.SixFunctors.OpenClosedWeilMateStructures | unclaimed | Cited finite construction unchanged. |
| Sheaf.SixFunctors.OrdinaryProEtaleDirectImagePlusComparison | unclaimed | Cited finite construction unchanged. |
| Sheaf.SixFunctors.ProjectionRefinementInputs | unclaimed | Cited finite construction unchanged. |
| Sheaf.SixFunctors.ProperSupportStepBounds | unclaimed | Cited finite construction unchanged. |

## Status

landed 20261027T103435-L-1078680 2026-10-27 (merge of deliver/J2/Sheaf.Paper.ExplicitScalarConeWordCoordinates)
