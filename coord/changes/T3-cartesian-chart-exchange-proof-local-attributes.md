# Proof-local commands for CartesianChartExchangeNaturality

## Reason

Prove the specified exchange identity against the original chart definitions.
Local irreducibility attributes prevent unnecessary expansion of derived
constructions during elaboration. The static visibility check flags changes to
attribute commands, so this record documents their local scope and purpose.

## Old

Sheaf.AlgebraicGeometry.CartesianChartExchangeNaturality (held by T3) imported
the general comparison API, contained the unused private
cartesianChartAdjunct_spec, and left cartesianChartCohomologyLift_exchange open.
The four definition modules identified by the reviewer have their repository
bodies: Over.post followed by Over.pullback, the mapped cone, the literal
cohomology and map constructions, and the original inverse-comparison lift.

## New

The same public theorem signature is proved from the existing
chartRawAdj_classPullback compatibility and the proved restricted-map evaluation
identity. The unused original private helper is removed. The second reader
removed the new private chartClassPullback_exchange duplicate in favor of the
existing library theorem. Local irreducibility
attributes and declaration-local elaboration options control expansion only
inside this module; additional imports are proof-only. The public import stays.
The two new helper modules and their signatures have DAG nodes. Their data are
explicit raw pullback and the uniquely specified inverse evaluation comparison.
The second reader proved the evaluation property as well; no new hole or
unspecified data remains.

## Users

No existing definition, theorem signature, global attribute, notation, namespace,
or exported instance changes. Importers use the identical exchange statement.
No module held by another group is adapted. CartesianChartClassPullback,
CartesianHigherImageChartSystem, RawAffineRestrictedCohomology, and
RestrictedOverAbelianComplexData are excluded from the packet and used unchanged.
The local attributes end with this module or its helper section and do not
change the importers' elaboration environment.

## Status

landed 20261015T081231-L-3876910 2026-10-15 (merge of deliver/T3/Sheaf.AlgebraicGeometry.CartesianChartExchangeNaturality)
removed the duplicate private helper, checked all public signatures unchanged,
and recorded the five review points in report.md. No forced adaptation is
claimed and no other library module is changed. Delivery checks follow.
