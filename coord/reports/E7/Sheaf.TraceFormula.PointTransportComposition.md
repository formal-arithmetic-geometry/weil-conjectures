## What changed

Proved `WeilConjectures.pointPowerFiniteSigma_existsUnique` in
`Sheaf.TraceFormula.PointTransportComposition`, without changing its statement,
the existing definitions, or any other existing declaration signature.

The proof generalizes the already proved finite sigma construction in
`Sheaf.SixFunctors.FrobeniusPointTransport` from the first Frobenius power to
arbitrary powers. Three proved private helpers establish constant-scalar
normalization, turn restriction into a linear map for the transported action,
and supply the degreewise map. Naturality of a module-sheaf differential
proves the chain-map condition, and extensionality proves uniqueness.
Elaboration options and instance suppression are scoped to the new helpers and
the proved theorem; no file-level options or global instances are changed.
The scalar argument uses the existing
`AlgebraicGeometry.Scheme.isoSectionwiseConstantMap_existsUnique` and the
naturality of the sheafification unit. It applies to all `r,n : ℕ`, including
`r = 0` and the first positive coefficient exponent `n = 0`; it uses neither
boundedness nor constructibility. No arbitrary object is selected from a mere
existence theorem: the existing sigma definition still selects the uniquely
sectionwise characterized chain map.

This is a partial delivery with one of the two original holes closed. No new
public declarations or modules are added. The original composition theorem and
its proof plan remain unchanged. The two public imports remain unchanged.

Searches: launcher `msearch.py` LeanFinder queried natural transformations of
point sections under powers of an automorphism; results concerned general
scheme section functoriality, not this module construction. Loogle
`SheafOfModules.pullbackComp` found the generic pullback compositor and its
coherence lemmas, not sigma existence. Mathlib grep for the specialized sigma
and composition names found no matches. Local `rg` found the proved finite
sigma construction in `FrobeniusPointTransport.lean`, which supplied the shorter
route used here. The two stated proof dependencies
`Sheaf.AlgebraicGeometry.PointSheafInsertionCalculus` and
`Sheaf.Paper.PointExactDerivedModel` were read: they use the ordinary tensor
pullback presentation, whereas this file's maps use the intrinsic pullback and
its explicit representative comparisons. Their assembly is still needed for
the untouched composition theorem.

Validation: remote `lcompile.py` checked the proved sigma construction. The final
import cleanup is checked again by the required delivery compile and preflight.
All edited Lean lines have at most 100 characters. Only the sandbox is written;
no source-library declarations, target statements, or launcher tools are edited.

## Proved and sorry left

Closed one original hole:
`WeilConjectures.pointPowerFiniteSigma_existsUnique`
(node `lem-trf-point-transport-composition`).

One original hole remains, unchanged:
`WeilConjectures.point_transport_composition`
(node `lem-trf-point-transport-composition`). This is the full composition and
derived-naturality assertion; the delivery does not claim to prove it.

Added holes: zero. Split-off statements: zero. The three new private helpers
are proved, and every existing definition retains its original body.

## No longer needed

Removed the following redundant direct private imports:

- `Sheaf.AlgebraicGeometry.ProEtaleConstantRingMap`
- `Sheaf.AlgebraicGeometry.ProEtaleConstantExact`
- `Sheaf.AlgebraicGeometry.ProEtaleObjectInverseImageRestriction`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctoriality`
- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`
- `Sheaf.AlgebraicGeometry.ProEtale.IsoSectionwiseInverseImage`
- `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`
- `Sheaf.Paper.FiniteCoefficientPoint`
- `Sheaf.Paper.InverseImagePullbackComparisonDerived`
- `Sheaf.Paper.IsomorphismDerivedPullback`
- `Sheaf.Paper.PointProEtaleSectionsExact`

Their declarations needed by the existing data and the proved sigma theorem are
already supplied by the two unchanged public imports. This is direct-import
cleanup, not withdrawal of any module or mathematical node. In particular,
no node or module is asserted to be globally unreachable, and no dependency of
the unchanged composition proof plan is removed from the DAG. No unit route
is changed.

## Where the brief, the DAG or earlier work was wrong

No mathematical error found. The module has two original holes, not just the
main theorem. The existing first-power sigma proof gives a direct proof of the
auxiliary hole without needing the derived composition machinery. The remaining
main theorem still requires relating its explicitly chosen intrinsic-model maps
to the normalized tensor-model insertion and localization comparisons.

## Second reading by E7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
