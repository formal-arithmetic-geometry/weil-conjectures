## What changed

Filled `AlgebraicGeometry.ProEtale.RationalP1.scalar_q_chern_left_inverse` without
changing its signature. Its proof descends the existing second-projection splitting
instead of repeating completion and coefficient transport.

The two component equations in `scalar_chern_base_change` identify the pulled-back Q
splitting, followed by the exchange, with the P2 splitting, up to the canonical
biproduct and unit/line isomorphisms. The private categorical helper proves this
identification by biproduct hom-ext and cancels the isomorphisms. The exchange is
invertible by the proved `unit_exchange_isIso` helper behind `unitInversions`, applied
to the shifted positive line; membership of that line follows from
`line_localizing_of_preservation` and the existing `localizingPreservation` theorem. The
section at infinity and the derived pullback compositor show that pullback by Q reflects
isomorphisms. Taking the inverse of the reflected isomorphism proves the displayed
inverse equation.

All new imports are private proof imports. The public import is unchanged. The
additional definition repair in `RationalP1SecondPretraceData` makes
`secondTraceExchange` compose the existing `secondPretraceExchangeMap` wrapper with the
same pushed-forward line comparison. It avoids expanding the entire native
derived-functor construction at coefficient specialization. All existing signatures,
visibility, attributes, imports, and mathematical maps are preserved; no public
declaration is added or removed. The change record is
`coord/changes/Y2-scalar-q-left-inverse-exchange-cache.md`. The node's proof and
dependencies record this argument. Its new dependencies were checked for paths back to
the item in both the Lean import graph and the DAG; none exists.

The categorical arguments apply to zero objects and to the empty base: the section
identity holds over every scheme, and no nonemptiness or nonzero coefficient hypothesis
is used. Both finite-extension and closure coefficients are handled by the existing
uniform scalar declarations. The unit route retains the actual unit/Chern generators,
the proper exchange, and their component compatibilities.

Searches: local `rg` located the P2 splitting, component equations, public exchange
inversion, and section at infinity. LeanFinder returned `biprod.mapBiprod_inv_map_desc`,
used in the private helper. Loogle had no hit for the queried namespaced reflection
lemma; reading Mathlib found `CategoryTheory.reflectsIsomorphisms_of_comp` and
`CategoryTheory.reflectsIsomorphisms_of_iso`.

Validation: `lcompile.py --all` passed for the two edited modules and all
three unchanged direct importers of `RationalP1SecondPretraceData`. Times were
2.5 seconds for the data module, 27.3 seconds for the completed item, 11.3 seconds
for `RationalP1SecondExchangeProjection`, 14.0 seconds for
`RationalP1SecondProjectionInterchange`, and 31.4 seconds for
`RationalP1SecondPretrace`. The unchanged consumer copies were removed after
verification. No consumer adaptation is needed.

## Proved and sorry left

Closed one existing hole:
`AlgebraicGeometry.ProEtale.RationalP1.scalar_q_chern_left_inverse` (node
`lem-sfb-rational-p1-scalar-q-left-inverse`). No holes are left in the item, and no
holes or split-off statements are added. The additional definition repair in
`RationalP1SecondPretraceData` also has zero remaining holes. The private categorical,
additivity, and exchange helpers are fully proved. Existing imported obligations remain
with their existing nodes; this is a proof from the project's stated declarations, not a
claim that every transitive dependency is already free of `sorry`.

## No longer needed

The direct use of `lem-sfb-diagonal-trace-twisted-splitting-components` in this item's
old plan is unnecessary: the already stated P2 splitting and base-change component
equations suffice. This does not withdraw that node or its module; other arguments still
need them. No existing import was removed and no module is withdrawn. No global pruning
is claimed.

## Where the brief, the DAG or earlier work was wrong

The old plan repeated the entire strict-system-to-scalar transport for one inverse
equation. The existing second-projection splitting can instead be descended through the
already stated invertible proper exchange. Reflection of isomorphisms uses the actual
section at infinity, so it requires no new geometric or cohomological assertion. This
closes the assigned hole without an eighth split of the same obligation. No statement or
definition was found false. The inline scalar exchange was unusable within the kernel
time limit when proving its invertibility; its existing fixed-endpoint exchange wrapper
provides the compatible cached route.

## Related modules compiled before delivery

10 related module(s) compiled against this delivery by deliver3.py: 10 OK.

```json
{"capped": false, "direct": 4, "left_out": 0, "own": {"Sheaf.Paper.RationalP1ScalarChernQLeftInverse": "aa2059b8b92e36fc883bb0997a59ed308c06d007", "Sheaf.Paper.RationalP1SecondPretraceData": "eb2caaf414d47839708f8e7e66584f0205e464b5"}, "results": {"Sheaf.Paper.RationalP1ScalarChernBaseChange": {"hash": "2e619fb96d918c194ac32aef46d40e4abed4efe6", "status": "OK"}, "Sheaf.Paper.RationalP1ScalarChernBaseChangeChern": {"hash": "c43c3ddc9dcdcff5f854b753ce5547cc66dd917d", "status": "OK"}, "Sheaf.Paper.RationalP1ScalarChernBaseChangeUnit": {"hash": "08f873cd81d0f4854a29e0778513a4bcf04f613b", "status": "OK"}, "Sheaf.Paper.RationalP1ScalarChernQSplitting": {"hash": "317550e29fa825425c4a0cc98ef061193ff9af7d", "status": "OK"}, "Sheaf.Paper.RationalP1SecondExchangeProjection": {"hash": "2e9428f85207001c26b285a862a098a716963e58", "status": "OK"}, "Sheaf.Paper.RationalP1SecondPretrace": {"hash": "c2619b530724f0ccbe373a2265c00f84f7f1d1d4", "status": "OK"}, "Sheaf.Paper.RationalP1SecondProjectionInterchange": {"hash": "19ef39bf3d6eb67179e17feaa0d225adbf01bd6e", "status": "OK"}, "Sheaf.Paper.RationalP1SecondScalarTrace": {"hash": "70acd7b00b358a93fcf8c88dc8ac321dc76dfd70", "status": "OK"}, "Sheaf.Paper.RationalP1SecondTraceReordering": {"hash": "4a6f4051c3cff28e9722fccb6b968c09956606f6", "status": "OK"}, "Sheaf.Paper.ScalarP1UnitMateComponent": {"hash": "01049f6d42cbead1b480ec1a4a02f1ad4aecda67", "status": "OK"}}, "seconds": 75, "time": "2026-10-28T07:03:13+0800", "transitive": 6, "version": 1}
```

## Second reading by Y2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
