## What changed

Proved `WeilConjectures.pointSectionsTensorShift` in
`Sheaf.Paper.PointSectionsTensorShift`, with every existing signature and definition
unchanged. Added the proof-only import
`WeilConjectures.CategoryTheory.DerivedCategory.Shift.ExactFunctor` for the already
proved compatibility of induced natural isomorphisms and composition comparisons
with shifts. The balanced formula comes from the chosen specification of
`pointSectionsTensor`. Naturality, inverse cancellation, and
`Functor.mapDerivedCategoryNatIso_fac` prove the representative identity.
Updated the node proof and proof dependencies to this route.
Removed two unused public imports; the change is recorded in
`coord/changes/Q1-point-sections-tensor-shift-imports.md`.
Validation: the item and unchanged sole direct consumer
`Sheaf.Paper.PointFibreEquivalence` compiled together against the delivered imports
in 13.3 and 11.0 seconds, respectively, with no compiler warnings or errors.
The consumer source was used only for validation and is not part of the delivery.

## Proved and sorry left

Closed the one original hole: `WeilConjectures.pointSectionsTensorShift`
(node `lem-weil-point-sections-tensor-shift`). Proved 1 of 1 original sorries;
added 0 holes and 0 split-offs. No sorry remains in the delivered module.
The proof uses the existing statements in `PointSectionsScalarExtension`, including
its exactness and uniquely specified balanced comparison; these dependencies still
contain their own holes and are not claimed proved by this delivery.

## No longer needed

Removed these two unused public imports:

- `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses`
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`

Removed these six proof-only imports:

- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctoriality`
- `Sheaf.Paper.EtaleDerivedScalarTensor`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`
- `Sheaf.Paper.PointProEtaleSectionsExact`

The proof no longer directly uses the planned nodes
`lem-pc-kflat-resolution`, `lem-pur-derived-change-of-rings`,
`def-pur-sheaf-tensor-product`, or `lem-weil-point-proetale-sections-exact`.
Their statement dependencies remain unchanged: K-flatness, flatness and the
specified derived scalar extension still occur in the unchanged statement and
existing constructions. Removed the obsolete tool approvals for
`lem-pc-kflat-resolution` and `lem-pur-derived-change-of-rings`, preserving the
approval for `lem-weil-point-sections-scalar-extension`.
No claim is made that these modules leave the whole targets import closure:
other modules, including the scalar-extension dependency, still import some of them.
The unit record has no realized statement or proof steps to bypass.

## Where the brief, the DAG or earlier work was wrong

No false statement was found. The planned reconstruction using resolutions and
common refinements is unnecessary for the comparison already defined here:
it is the exact-functor localization of the termwise natural isomorphism.
The existing source-library shift compatibility instances and localization
factorization lemma establish every clause, even for arbitrary complex
representatives. The K-flatness and flat-term hypotheses can consequently remain
unused without changing the statement. The local instance in the proof explicitly
selects the already defined `pointCompletedScalarCommShift`; no new shift structure
or altered definition is introduced.

## Second reading by Q1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
