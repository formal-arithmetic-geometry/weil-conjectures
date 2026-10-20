## What changed

Completed `CategoryTheory.CoefficientBidual.scalar_compatibility`, preserving its
entire signature. Restrict the ambient signed exact structure through the full
inclusion; descend the restricted functor and evaluation through the categorical
localization of the raw tensor-Hom category. The comparison with rationalization
is constructed using the existing `Rationalization.tensorHomEquiv`, as in the
proof of `exists_triangulated_scalarLocalization`. All integer-shift equations,
triangle squares, and shift/two-out-of-three invertibility conclusions are proved.
All new helpers are private and fully proved. The ambient and slice theorems are
untouched. The node's Steps 12–13 now describe the categorical descent argument.

Added private imports of
`WeilConjectures.CategoryTheory.DerivedCategory.Complete.RationalizationHom`
and `WeilConjectures.Mathlib.CategoryTheory.Shift.CommShift`.
The local proof settings are recorded in
`coord/changes/W4-coefficient-bidual-scalar-proof-scopes.md`.

## Proved and sorry left

Closed one of the original three holes:
`CategoryTheory.CoefficientBidual.scalar_compatibility`.
No holes added and no statements split off. This is a proof from the existing
ambient compatibility declaration, as intended by the stage-3 dependency policy.
The already proved `subcategory_linearity` stays unchanged.

The two remaining holes, both on
`lem-coef-rational-bidual-triangle-compatibility`, are:

- `CategoryTheory.CoefficientBidual.compatibility`;
- `CategoryTheory.CoefficientBidual.slice_compatibility`.

The item compiles through lcompile.py. The exact supplied shift structure on Q
is used throughout; no faithfulness of Q or invertibility of an arbitrary bidual
component is assumed. No target, source-library declaration, or public interface
changes.

## No longer needed

Removed these unused private proof imports:

- `Sheaf.Algebra.Homology.SignedDoubleHomCone`;
- `Mathlib.Algebra.Homology.BifunctorShift`;
- `Mathlib.Algebra.Homology.HomotopyCategory.KInjective`;
- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`;
- `Sheaf.Algebra.Homology.HomComplexGlobalHomotopyOfUniverses`;
- `Sheaf.Algebra.Homology.KInjectiveHomComplex`;
- `WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMap`;
- `WeilConjectures.Algebra.Homology.HomComplex`;
- `WeilConjectures.Algebra.Homology.HomTensorTotal`;
- `Mathlib.Algebra.Homology.DerivedCategory.KInjective`;
- `Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients`;
- `Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses`.

These are unnecessary as direct imports for the definitions or current proofs.
Their DAG dependencies remain where the unfinished ambient and slice proof plans
still need them. No mathematical node or module is withdrawn; no source-library
declaration is removed. Public imports remain unchanged.

## Where the brief, the DAG or earlier work was wrong

No disputed or corrected statement. Step 12 can use the categorical localization
universal property rather than repeat balancing and naturality on fractions.
The existing raw-scalar/rationalization comparison provides that property without
idempotent completion. The degree-one hshift and hQ assumptions are not needed
by this proof, but their original binders are retained unchanged. The node's
ambient signed calculation and slice comparison are not claimed proved here.

## Second reading by W4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
