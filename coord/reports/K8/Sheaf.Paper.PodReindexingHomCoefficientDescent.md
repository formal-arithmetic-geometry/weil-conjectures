## What changed

Proved `WeilConjectures.PodCoefficientDescent.rational_comparison_existsUnique` in the
assigned module. A fully proved generic lemma in
`Sheaf.CategoryTheory.ScalarLocalizationRestrictedPairIso` transports the localized integral natural
isomorphism through the prescribed object equalities. Its naturality proof inducts
on both tensor Hom groups; pure tensors reduce to integral naturality multiplied
by the product of their scalar coefficients. The normalized rational pullback and
internal-Hom interfaces supply the two separately additive actions. Both component
and inverse have exactly the required localized integral formulas. Componentwise
extensionality proves uniqueness. All existing statements, definitions and public imports
are preserved. The node records this realization of Steps 10--11.

Three fully proved auxiliary modules keep each file within the compilation limit.
The restricted-pair lemma proves naturality and uniqueness by double tensor induction.
The pullback-pair lemma proves the composite object and separately additive arrow
formulas from the normalized operation and pullback formulas. The item specializes
that generic theorem to its recorded functors. The previously proved
`ambient_coordinates` argument is retained in full in the coordinate realization
module, with the original declaration applying it unchanged. These modules add no
unfinished obligation or additional claimed hole closure. Two old private proof
imports move to the coordinate realization; all original public imports remain.

## Proved and sorry left

Closed one of the 18 holes present at the worker base:
`WeilConjectures.PodCoefficientDescent.rational_comparison_existsUnique`.
No holes or unfinished split statements are added. The 17 remaining holes are the following
unchanged declarations, all owned by
`lem-pod-reindexing-hom-coefficient-descent` in
`dag/nodes/sec-poincare-duality/lem-pod-reindexing-hom-coefficient-descent.json`:

- `WeilConjectures.PodCoefficientDescent.ambient_reindex_scalar`
- `WeilConjectures.PodCoefficientDescent.ambient_scalar_chain`
- `WeilConjectures.PodCoefficientDescent.rational_transpose_existsUnique`
- `WeilConjectures.PodCoefficientDescent.rational_signedShift_existsUnique`
- `WeilConjectures.PodCoefficientDescent.integral_existsUnique`
- `WeilConjectures.PodCoefficientDescent.integral_scalar`
- `WeilConjectures.PodCoefficientDescent.rational_scalar`
- `WeilConjectures.PodCoefficientDescent.integral_evaluation_transposition`
- `WeilConjectures.PodCoefficientDescent.rational_evaluation_transposition`
- `WeilConjectures.PodCoefficientDescent.rational_composition`
- `WeilConjectures.PodCoefficientDescent.rational_pullbackShift_existsUnique`
- `WeilConjectures.PodCoefficientDescent.rational_signed_shifts`
- `WeilConjectures.PodCoefficientDescent.common_evaluation_existsUnique`
- `WeilConjectures.PodCoefficientDescent.common_comparison_existsUnique`
- `WeilConjectures.PodCoefficientDescent.common_evaluation`
- `WeilConjectures.PodCoefficientDescent.common_transpose_existsUnique`
- `WeilConjectures.PodCoefficientDescent.common_composition`

## No longer needed

Removed direct private proof imports `Sheaf.Paper.PodFiniteScalarTensorNormalization`
and `Sheaf.Algebra.Homology.ExactScalarDerivedPair` from the item. The new coordinate
realization imports and uses them, so these modules and nodes remain required.
No declaration, node or module is pruned. All broader dependencies remain needed
by the outstanding obligations or the fully proved coordinate realization.

## Where the brief, the DAG or earlier work was wrong

The queue snapshot says 20 holes; the current source already contains K1's proofs
of `ambient_coordinates` and `common_compositor_existsUnique`, leaving 18 at this
worker's base. The delivered proof retains the DAG's raw localization route and
the fixed unit route. Finite sums of pure tensors are handled explicitly, so the
proof does not assume that rational arrows have integral lifts or that integral
localization is faithful. Zero objects, zero morphisms and arbitrary coefficients
are included by the induction.

## New nodes

`lem-pod-restricted-pair-localization-iso` owns the fully proved
`CategoryTheory.ScalarLocalization.restrictedPairIso_existsUnique` in
`Sheaf.CategoryTheory.ScalarLocalizationRestrictedPairIso`. It is the generic
naturality and uniqueness step on restricted contravariant/direct pairs, proved by
double tensor induction. The fully proved pullback-pair lemma verifies the composite bilinear hypotheses.
There is no `sorry` in this module.

`lem-pod-finite-scalar-coordinates-realization` owns the fully proved
`WeilConjectures.PodCoefficientDescent.finiteScalarCoordinatesRealization` in
`Sheaf.Paper.PodFiniteScalarCoordinatesRealization`. It retains the complete
previously proved finite-scalar specialization and exact scalar-derived-pair
assembly, separated after profiling for the single-file runtime limit. It does not
contribute a new claimed hole closure or defer any part of that proof. Its public imports retain the canonical coefficient categories and site instances
of the original; unrelated private proof imports and helpers are omitted.
There is no `sorry` in this module.

`lem-pod-localized-pullback-pair-comparison` owns the fully proved
`CategoryTheory.ScalarLocalization.pullbackPairIso_existsUnique` in
`Sheaf.CategoryTheory.ScalarLocalizationPullbackPairIso`. It composes the object
and bilinear action formulas, transports the permitted-pair endpoints, and applies
the restricted-pair natural-isomorphism theorem. There is no `sorry` in this module.
No other existing module or node is changed, and no change record is needed.

## Related modules compiled before delivery

5 related module(s) compiled against this delivery by deliver3.py: 1 INFRA, 4 OK.

```json
{"capped": false, "direct": 5, "left_out": 0, "own": {"Sheaf.CategoryTheory.ScalarLocalizationPullbackPairIso": "97d1d1be080f916ba62308570967eed3039a5baf", "Sheaf.CategoryTheory.ScalarLocalizationRestrictedPairIso": "27b38750f9f7ab04629cf477032fd4938db5a466", "Sheaf.Paper.PodFiniteScalarCoordinatesRealization": "7582083d7816a0bb9ee698e7a8b1002dabd28792", "Sheaf.Paper.PodReindexingHomCoefficientDescent": "33b6d15e8d7ad35abb5ce543b565bad41916304b"}, "results": {"Sheaf.Paper.AdicCommonPullbackIdentityUnit": {"hash": "e2ff305df123d20c4af44687b4a1c387f6da6347", "status": "INFRA"}, "Sheaf.Paper.DerivedAutomorphismHomEvaluation": {"hash": "d9b824a9ef213fa3e1d5aa65989f86a8ff078cf4", "status": "OK"}, "Sheaf.Paper.DerivedAutomorphismHomEvaluationContinuationA": {"hash": "2e9552db49b2b434602492555058e2dfefccf892", "status": "OK"}, "Sheaf.Paper.DerivedAutomorphismHomEvaluationContinuationABase": {"hash": "67bf1829cd9c42d3e1b9c245695d0b88c464d133", "status": "OK"}, "Sheaf.Paper.DerivedAutomorphismHomEvaluationContinuationB": {"hash": "26f1682872233b77da7f63ae8496a94cdfdecb31", "status": "OK"}}, "seconds": 131, "time": "2026-10-28T11:20:28+0800", "transitive": 0, "version": 1}
```

## Second reading by K8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
