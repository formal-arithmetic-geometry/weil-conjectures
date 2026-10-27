## What changed

Proved `WeilConjectures.integralCompactSupport_prescribedReductions` from the recorded
normalized compact-support realization, normalized DVR effectivity, and the finite-level
uniform Tor theorem. The specified Roos triangle is transported through the realization's
evaluation isomorphisms. Adjunction naturality identifies each effectivity counit with the
prescribed coefficient comparison. The Roos projection equation gives the successive
reduction square by adjunction. The tensor-unit test converts the Tor interval to a
uniform cohomological support interval, and the legacy completeness comparison supplies
the exact constructibility predicate in the unchanged statement.

All public statements and data definitions are unchanged. Added only proved private
helpers for restriction comparison, Roos transport, adjunction naturality and Tor support.
Updated the item's proof description to match the Lean argument. No new node, statement
repair, data choice, or consumer adaptation is made.

## Proved and sorry left

Closed: `WeilConjectures.integralCompactSupport_prescribedReductions`
(`lem-coef-integral-compact-support`), the original module's one hole.
Added: zero holes. Left in the delivered module: zero holes. No split-off theorem. The complete module compiled successfully through `lcompile.py`;
the delivery reruns compilation and the required packet checks.
The recorded dependency theorems are used with their published signatures, including
any existing holes in those dependencies; they are not claimed as closed here.

## No longer needed

Removed these direct proof imports:

- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients`
- `Sheaf.Algebra.Homology.KFlat`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses`
- `WeilConjectures.Compactification.BoundaryPreparation`
- `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`
- `Mathlib.AlgebraicGeometry.Morphisms.Immersion`
- `Sheaf.AlgebraicGeometry.DimensionExtension`
- `Sheaf.Paper.OpenExtensionFiniteTor`
- `Sheaf.Paper.ProEtaleFiniteCoefficientDirectImage`
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`
- `Sheaf.Paper.IntrinsicFiniteTorsionConstructibility`
- `Sheaf.Paper.SfDerivedDirectImage`
- `Sheaf.AlgebraicGeometry.ProEtaleConstantDerivedDirectImage`
- `Sheaf.Paper.SfIntegralReductionTower`
- `Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction`
- `WeilConjectures.CategoryTheory.Triangulated.DerivedLimit`
- `Sheaf.Paper.ProEtaleConstructibleOrigin`
- `Sheaf.Paper.SfCompactSupportRestrictionOfScalars`
- `Sheaf.Paper.NormalizedDVRTower`
- `Mathlib.Algebra.Homology.DerivedCategory.Fractions`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`
- `Sheaf.Paper.CompactificationCoherence`
- `Sheaf.Paper.EtaleCompactSupportCoefficientChange`
- `Sheaf.Paper.QcqsCompactSupportRealization`
- `Sheaf.Paper.SfIntegralConstructible`
- `Sheaf.SecSmoothPurity.IntrinsicCompactSupportRestriction`
- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`

The assembly no longer performs the dense-refinement geometry, K-flat quotient
normalization, roof strictification, or coefficient-change proof internally: those
arguments belong to `lem-coef-finite-compact-support-uniform-tor` and
`lem-coef-compact-support-normalized-realization`. Their dependencies remain needed by
those modules; this delivery withdraws no module and claims no global removal of them.
The node's existing four-step assembly and six proof dependencies are retained.
Added explicit edges for `lem-sf-derived-complete-legacy-comparison` and
`lem-weil-proetale-dbc-triangulated`, the completeness translation and closure under
isomorphism used in the final membership step.
No unit realization is bypassed.

## Where the brief, the DAG or earlier work was wrong

The saved interrupted proof did not yet compile. Its attempted direct equality of the
normalized and adjacent restriction associators was ill-typed before identifying the
actual quotient maps. The completed proof compares the ordinary sectionwise identity
associators and derives the corresponding comparison. The latest blueprint describes
compact support as proper image after open extension and uses the scalar-six comparison;
the delivered assembly proves the unchanged completed-sheaf Roos presentation through
its recorded normalized realization. The finite Tor bound uses exactly its dense
compactification argument. No mathematical hypothesis or conclusion was changed.

## Second reading by G1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
