## What changed

`Sheaf.WeilSheaf.SmoothDualizingCohomology` now proves
`AlgebraicGeometry.WeilComplex.nonempty_smooth_dualizing_cohomology_iso` from a
coefficient cohomology comparison and the already published canonical smooth purity
isomorphism and constant-purity Frobenius square. Its public statement and public
imports are preserved. The new imports are private proof imports.

The private helper `coefficient_smooth_purity_iso` constructs the isomorphism of
coefficient Frobenius pairs: its underlying map is
`RationalSmoothPurityCanonical.commonIso`, and its algebra-morphism equation is
clause three of `constant_purity_frobenius_square`. The final proof applies a
cohomology functor to the inverse pair isomorphism and composes the exceptional and
Tate endpoint identifications. It also constructs the finite-field/coefficient
setting and obtains the existing exceptional coefficient system.

The new module `Sheaf.WeilSheaf.CoefficientCohomologyComparison` constructs the
exceptional constant and shifted Tate constant pairs with their actual prescribed
structure maps. Its one remaining theorem isolates exact realization, cohomology,
and the two endpoint normalizations. It assumes no smoothness and does not assert
an isomorphism between those two pairs. The geometric purity isomorphism and its
Frobenius intertwining equation are proved in the parent, rather than included in
the new obligation. In particular this does not identify native derived Weil
categories with fixed pairs in ordinary derived categories.

## Proved and sorry left

Closed the one original hole in
`AlgebraicGeometry.WeilComplex.nonempty_smooth_dualizing_cohomology_iso`
(node `lem-sf-weil-smooth-dualizing-cohomology`). The item's module has zero
remaining `sorry`s. The private coefficient-pair isomorphism is proved completely.

Added one hole:
`WeilConjectures.NativeCoefficientCohomology.coefficient_cohomology_comparison`
(node `lem-sf-native-coefficient-cohomology-comparison`). It is a public theorem in
its own new module, with its source and complete proof in words in its docstring.
There are no holes in definitions or private declarations. Thus this delivery is
a decomposition, one original hole closed and one comparison hole added, not a
net reduction in the number of holes. The unproved comparison contains no smooth
purity assertion; the remaining work is the actual coefficient/cohomology bridge.
Its statements cover degree zero, arbitrary cohomology degree, d=0, and the empty
scheme without introducing geometric hypotheses.

## No longer needed

No modules are withdrawn and no original imports are removed. No unit statement
or realized proof step is pruned or replaced.

The parent's direct use of
`lem-sf-weil-native-exceptional-forgetful`,
`lem-sf-adic-qbar-constructible-realization`, and
`lem-sf-native-weil-scalar-frobenius-counit` is moved into the proof plan of the
new comparison node. These dependencies remain needed there and are not claimed
as globally pruned.

The parent does not directly apply
`cor-pur-adic-and-rational-smooth-dualizing-complexes`
(`Sheaf.Paper.AdicSmoothDualizingComplexes`): it uses the already constructed
`RationalSmoothPurityCanonical.commonIso`, whose construction retains the
coefficient purity route. Thus the direct parent proof dependency is replaced by
`def-pur-canonical-rational-purity-realization`; the corollary is not withdrawn.

## Where the brief, the DAG or earlier work was wrong

No disputed mathematical statement was found. The planned passage from ordinary
coefficient Frobenius pairs to native cohomology sheaves was not an available
single Lean declaration: the existing native exceptional-forgetting package has
ordinary realization comparisons and counit normalizations, while the purity
square has a common-stage Frobenius pair. The new node isolates their exact
cohomological comparison. A derived-category fixed-pair equivalence would be an
incorrect replacement for this comparison and is not asserted.

The two possible scheme-over-itself instances (the identity and Spec of the
identity algebra map) must be kept consistent. The new module locally prefers
the identity structure, matching the original item's native point category.
No global instance priority is changed. The existential cohomology functors are
eliminated only inside the proof of the original proposition; no definition
chooses data from the unproved comparison.

## New nodes

`lem-sf-native-coefficient-cohomology-comparison`, at
`dag/nodes/sec-smooth-purity/lem-sf-native-coefficient-cohomology-comparison.json`,
is the comparison step above. Its provenance is the exceptional-adjunction
paragraph of `cor-coef-verdier-weil-equivariance`, the constant-unit specialization
of smooth dualizing purity, and the canonical root/Tate-source conventions of the
constant-purity Frobenius square. The node records LeanFinder, Loogle, grep and
LeanSearch checks; none supplies this native comparison. Its exceptional and
Tate endpoints are defined concretely in the module. The original node's proof,
proof dependencies and proof origin are updated to the implemented assembly.
No other existing module or node is changed; no change record is needed.

Validation: the server compiled the new comparison module in 11.7 seconds and
the final item module in 21.9 seconds. The original target signature was checked
verbatim against the shared source. All Lean lines are at most 100 characters.
The item contains zero holes; the new module contains exactly the named hole
reported above. Delivery performs the independent mechanical checks.

## Related modules compiled before delivery

7 related module(s) compiled against this delivery by deliver3.py: 6 OK, 1 SLOW.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.WeilSheaf.CoefficientCohomologyComparison": "7d02ddb89844c6902f17aa643a8e1775dc7d7b51", "Sheaf.WeilSheaf.SmoothDualizingCohomology": "f887bbab45224fe64565d4796d2cef05765ec652"}, "results": {"WeilConjectures.DeligneLaumon.AffineLine.LocalDuality": {"hash": "362511fd1ec8ffac6035ff8ce532c2e19daa78d9", "status": "SLOW"}, "WeilConjectures.DeligneLaumon.Reduction.FiniteMiddleExtension": {"hash": "540ce6b39bccc3c943bd009279b59bf301d7a606", "status": "OK"}, "WeilConjectures.WeilSheaf.CohomologicalRange": {"hash": "6ca2482878f1da28c25673e03e74340fbf93acdd", "status": "OK"}, "WeilConjectures.WeilSheaf.CohomologicalRangeAffine": {"hash": "7841feb68e94c3373f511da11e24c3b2b5c8dc3c", "status": "OK"}, "WeilConjectures.WeilSheaf.CurveEndpoints": {"hash": "a34bf6b1522712199f815703144df1c0e606f3ab", "status": "OK"}, "WeilConjectures.WeilSheaf.VerdierDual": {"hash": "cbd782ced4a4ed0d3932076da1a163a61a8db8c5", "status": "OK"}, "WeilConjectures.WeilSheaf.VerdierDualLocalization": {"hash": "8d0fd3ed2a48117c97e67305db2be09cdb6189b4", "status": "OK"}}, "seconds": 241, "time": "2026-10-28T04:21:20+0800", "transitive": 6, "version": 1}
```

## Second reading by H8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
