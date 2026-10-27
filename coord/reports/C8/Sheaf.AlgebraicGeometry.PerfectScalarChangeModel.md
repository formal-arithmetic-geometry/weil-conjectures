## What changed

Filled both theorem bodies in `Sheaf.AlgebraicGeometry.PerfectScalarChangeModel`.
The finite-projective argument maps the given splittings through additive scalar
extension, identifies extended finite free modules using the regular-extension
isomorphism, and obtains flatness by closure under finite biproducts and retracts.
The source library's bounded-flat criterion then proves K-flatness directly in
the categorical predicate used by the statement.

The chart argument reuses the existing general
`FreeParameterEvaluation.scalarPullComparison_isIso`, applies derived extension
to the supplied chart isomorphism, and evaluates the derived counit on the K-flat
model. The second isomorphism is constructed at the ordinary functor level from
the constant-sheaf adjunction, naturality of its counit, and extension-of-scalars
composition; it is then mapped to complexes and the derived category.

Validation: the delivered module compiled cleanly through `lcompile.py` in
30.5 seconds, with no errors or warnings. Local priorities select the existing
public monoidal instances directly and avoid failed generic preorder/lattice
instance searches. Local irreducibility keeps implementation definitions from
being unfolded by unrelated inference. No time limit was raised. No private
data helper appears in a public signature or public definition body.
An `--all` consumer check also compiled the unchanged direct importer
`Sheaf.SixFunctors.LocallyPerfectScalarModel` against this module (40.5 seconds).
The unchanged consumer is not part of the delivery.

All existing declaration signatures and definition bodies stay unchanged.
Three unused public imports are removed, with the consumer audit and import
change recorded in `coord/changes/perfect-scalar-change-model-import-pruning.md`. Added helpers are private and completely proved. The node proof and
its dependency list now describe this implementation.

The new cross-unit proof dependency
`def-sfb-free-parameter-scalar-maps` is used only for its already stated general
scalar/pullback comparison, not for any constructibility or local-model result.
Its dependency closure has no path back to this item. The existing regular-module
extension comparison is also reused. These are existing declarations, with no
new statements or new nodes introduced by this delivery.

## Proved and sorry left

Closed the two original holes:

- `AlgebraicGeometry.ProEtale.sfbPerfectScalarChangeModels`.
- `AlgebraicGeometry.ProEtale.sfbPerfectScalarChangeModel`.

Zero holes remain in the delivered module; zero holes are added elsewhere and
zero statements are split off. The existing dependency
`AlgebraicGeometry.ProEtale.FreeParameterEvaluation.scalarPullComparison_isIso`
still has its own named proof obligation; this delivery uses that existing
statement as permitted by stage 3. This is not a claim that the full target
closure is sorry-free.

The constructions cover rank zero, zero complexes, arbitrary strict bounds, and
nonflat coefficient maps: no nonzero-rank hypothesis or scalar-flatness
assumption is used.

## No longer needed

Removed the unused public imports `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`,
`Sheaf.Algebra.Homology.KFlatIndependentCoefficients`, and
`Sheaf.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral`. Their APIs do
not occur in the preserved statements or definitions. The direct importer uses
only the preserved local-model API, and the relevant higher consumer explicitly
imports the ordinary-perfect-complex API itself.

Removed these eight unused proof imports:

- `Sheaf.AlgebraicGeometry.CoefficientSectionsLocalization`.
- `Mathlib.Algebra.Module.Projective`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`.
- `Sheaf.Algebra.Homology.BoundedAboveFlatSheafKFlat`.
- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`.
- `Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings`.
- `Sheaf.Algebra.Homology.RingedSiteRestrictionKFlat`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.LocalizedSiteTensorRestriction`.

The node no longer depends on the explicit localized-site proof:
`lem-sfb-coefficient-sections-localization`,
`def-sfb-pullback-from-point-comp-iso`, `lem-pc-kflat-resolution`,
`lem-sfb-ringed-site-restriction-kflat`, and
`lem-sfb-localized-site-tensor-restriction`. Its chart compatibility is supplied
by the existing general scalar/pullback comparison instead.

The node also no longer uses `def-weil-pbc-projective-module`: the hypothesis
already supplies the finite-free retract, so no projective lifting argument is
needed. The ordinary internal-module adjunction API supplies tensor
associativity directly, without invoking `def-pur-sheaf-tensor-product`.
The site-specific bounded-flat and derived-change-of-rings nodes
`lem-pc-bounded-above-flat-kflat-site` and `lem-pur-derived-change-of-rings`
are replaced by the source categorical bounded-flat theorem and the existing
K-flat derived-functor counit, respectively.

Withdrawn the five obsolete top-level `tool_uses` approvals:
`lem-pc-bounded-above-flat-kflat-site`, `lem-pc-kflat-resolution`,
`lem-pur-derived-change-of-rings`, `lem-sfb-ringed-site-restriction-kflat`, and
`lem-sfb-localized-site-tensor-restriction`.
No module is withdrawn; the above are dependencies this proof no longer needs,
not assertions that no other target needs their modules.

## Where the brief, the DAG or earlier work was wrong

No statement repair was needed. The planned finite-projective splitting is
already a hypothesis in Lean, so constructing generators and a projective lift
would duplicate supplied data. The categorical K-flat criterion and the existing
scalar/pullback comparison avoid a separate intrinsic sheaf-tensor conversion
and a second chart-restriction resolution argument. The unit's scalar-change
local-model step remains exactly the statement proved here.

## Second reading by C8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
