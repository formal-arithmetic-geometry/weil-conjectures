# Fixed coherent comparison and additive action: native construction APIs

## Reason

Repair the returned Frobenius packet without undoing B2's landed comparison proof.
Specialized conversions between inherited additive structures repeatedly made the
kernel expand the derived cohomology construction. Fix native bundled instances
at the generic sheaf and functor levels before specializing to schemes.

## Old

`moduleAbelianCohomologyLarge` composed the fixed resolution-isomorphism component
with the canonical `coherentExtUniverseEquiv`. The additive action returned an
endomorphism of the additive group obtained by forgetting scalars on the actual
derived module object, and conjugated the large sheaf-cohomology map by this
large comparison.

## New

The large comparison has exactly its original signature and component formula.
Its body composes the same resolution and universe maps through generic native
bundled-group APIs. `coherentSheafUniverseEquiv_apply` evaluates the bundled
universe map as the original Ext map, and the module comparison evaluation API
therefore proves the unchanged `moduleAbelianCohomologyLarge_component` statement.
The underlying Ext universe equivalence remains Mathlib's `Ext.chgUniv`.

`coherentAdditiveEndomorphism` now acts directly on the actual derived module
object through the small fixed-resolution comparison. Generic module conjugation
fixes its additive structures before specialization; its evaluation theorem
expresses the action by the forward and inverse resolution components. The
private general theorem `coherentAdditiveEndomorphism_large` in the adapted
Frobenius-comparison consumer proves equality with the original large action on
every class: the large component formula is universe change after the small
component, and universe change commutes with coefficient postcomposition.
Thus extensionality identifies the old and new additive maps. This includes
degree zero, zero modules and empty schemes.

The existing module-group cache and all target signatures are unchanged.
The scalar comparison is rebundled through `coherentScalarEquiv`, whose generic
body is the input additive equivalence itself; its value is unchanged. No adopted source-library declaration is edited. Definition users
in the targets' dependency closure require the usual statement-meaning review;
the component formula and general old/new action certificate provide that review's
explicit equality evidence.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.CanonicalCoherentEtaleComparison | unclaimed | Packages universe change, resolution composition and conjugation generically, with proved evaluation APIs. The fixed native-component and coefficient-naturality statements are preserved. |
| Sheaf.AlgebraicGeometry.CoherentFrobeniusPullback | A2 | Uses native-component evaluation, coefficient transport and the fixed resolution comparison to close the assigned hole. |
| Sheaf.AlgebraicGeometry.CoherentFrobeniusComparison | unclaimed, restored from quarantine | Mentions `moduleAbelianCohomologyLarge` and `coherentAdditiveEndomorphism`; both active and archived consumers are accounted for. The active proof adds the general certificate equating small and large actions, then uses it in the original conjugation argument. |
| Sheaf.AlgebraicGeometry.CoherentEtaleComparisonPullback | unclaimed | The same scalar and canonical comparisons are retained; the structural comparison statement is unchanged. |
| Sheaf.AlgebraicGeometry.CoherentPowerComparison | unclaimed | Uses the same structure-coefficient action; no source edit. |
| Sheaf.AlgebraicGeometry.QcoherentComparisonDegreeZero | unclaimed | The fixed comparison and native-component theorem it uses are unchanged. |
| Sheaf.AlgebraicGeometry.QcoherentNormalizedComparison | unclaimed | Its landed proof and the large-comparison naturality API are preserved. |
| Sheaf.AlgebraicGeometry.QcoherentNormalizedPullbackSquare | F4 | The comparison interface it uses is preserved. |
| Sheaf.AlgebraicGeometry.QcoherentCohomologyComparisonPullback | unclaimed | The comparison interface it uses is preserved. |

## Status

landed 20261021T014657-L-2442192 2026-10-21 (merge of deliver/A2/Sheaf.AlgebraicGeometry.CoherentFrobeniusPullback)
