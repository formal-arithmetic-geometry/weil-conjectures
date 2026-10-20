## What changed

Proved all fourteen original holes in
`lean/Sheaf/Paper/PointSectionsScalarExtension.lean`. All existing declaration signatures,
public imports, definitions and docstrings are preserved. Added only proved private helpers
and private proof imports. No other Lean module is changed.

At the algebraically closed geometric point every covering sieve of the final object
contains its identity. Thus sheafification preserves sections there. This gives the actual
sections-tensor comparison without choosing a global finite-free basis. The coefficient
section identification follows from finite quotient sections and the existing profinite
coefficient-integers tower theorem. It respects all coefficient inclusions.

Exact scalar extension descends to the derived category, and uniqueness of left derived
functors identifies that descent with the existing chosen functor and its specified counit.
The ordinary sheaf associator is transported from the existing normalized associator in
`ScalarExtensionComposition`. Tensor-generator calculations give the ordinary unit and
composition squares. Localization factorization identities carry these squares to derived
categories; naturality and cancellation of the completion comparisons give the integral
identities. The rationalization comparison is the composite of the standard module tensor
associators, with its own unit and tower identities checked on tensor generators.

Updated the item's DAG proof, proof dependencies and proof origin to this route.
Preflight requested a proof-context change record for the new section/variable/open and
local attribute commands: `coord/changes/point-sections-scalar-extension-proof-context.md`.
It lists the unchanged consumer interfaces and all transitive users. Removed
four obsolete entries from its top-level tool-use list, preserving all remaining entries
in order. New dependencies in the proof are existing nodes, not new declarations with holes.

Validation: the complete integrated proof compiled in 49.5 seconds; the cleaned item path compiled
without warnings in 47.4 seconds. Declaration-header comparison against
the shared source found no changed existing signature. The final delivery command performs
the required compile and independent preflight checks.

## Proved and sorry left

Closed all 14 original holes, by declaration name:

- `WeilConjectures.pointCompletedSections_exact`
- `WeilConjectures.pointCoefficientTensors_exact`
- `WeilConjectures.pointSectionsTensor_existsUnique`
- `WeilConjectures.pointCompletedOrdinary_exact`
- `WeilConjectures.pointOrdinaryDerivedComparison_existsUnique`
- `WeilConjectures.pointOrdinaryTensorUnit_existsUnique`
- `WeilConjectures.pointOrdinaryTensorAssoc_existsUnique`
- `WeilConjectures.pointIntegralModuleUnit_existsUnique`
- `WeilConjectures.pointIntegralModuleAssoc_existsUnique`
- `WeilConjectures.pointCoefficientFieldTensor_exact`
- `WeilConjectures.pointTensorRationalization_existsUnique`
- `WeilConjectures.pointIntegralConstructible_iff`
- `WeilConjectures.pointConstructibleCompletionComparison_isIso`
- `WeilConjectures.pointSectionsScalarExtension`

Zero holes remain in the item. Zero holes were added, and zero statements were split off.
Every private helper is proved. Existing dependency theorems are used as published;
this delivery does not claim to close their holes.

## No longer needed

Removed these eight private proof imports:

- `Sheaf.AlgebraicGeometry.ContinuousCoefficientImmersionRestriction`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses`
- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients`
- `Sheaf.Algebra.Homology.ChangeOfRingsKFlat`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`
- `Sheaf.Paper.IntegralScalarExtensionConstructibleIntrinsic`

The point-cover/sheafification argument removes the direct proof dependency and tool use
`lem-weil-pbc-continuous-coefficients-immersion-restriction`. Exact-functor localization
and the published ordinary associator remove the direct proof dependencies/tool uses
`lem-pc-kflat-resolution`, `lem-pur-derived-change-of-rings` and
`lem-pur-kflat-change-of-rings`. Their modules may still be imported transitively by retained
dependencies; no source declaration or module is withdrawn, and no global pruning count
is asserted. The sheaf tensor definitions themselves remain necessary and are available
through the retained imports. The ordinary derived-completeness definition remains in
the statement dependencies; the new proof uses its existing comparison with the intrinsic
predicate instead of directly computing K-flat reductions.

The newly used existing nodes are `lem-sfb-integers-profinite-tower`,
`lem-sf-derived-complete-legacy-comparison`, and
`lem-weil-scalar-extension-composition`. The latter is used only for its published ordinary
sheaf associator, not for its rational composition theorem.

## Where the brief, the DAG or earlier work was wrong

No statement is disputed or weakened. The DAG's finite-free-basis and repeated K-flat
resolution arguments are unnecessary for this point-specific proof. The unit's route and
the specified canonical maps are retained.

The legacy finite-free comparison's completeness hypothesis existentially packages an
auxiliary finite-field datum. Since the intrinsic completeness predicate is independent
of that datum, the proof supplies one of characteristic a prime strictly greater than
ell and transports completeness through `sfDerivedComplete_iff_legacy`. This introduces
no new assumption on the original finite-field datum.

Large definitional conversions between the commutative and ordinary completed coefficient
presentations required an explicit bundled counit/universal-property helper. Local
irreducibility attributes keep elaboration from unfolding the chosen scalar-extension
witnesses. No definition was changed and no time or heartbeat limit was raised.

## Second reading by G2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
