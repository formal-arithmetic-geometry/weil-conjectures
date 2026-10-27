## What changed

Proved `WeilConjectures.sfOrientedPerfectDuality` by the unit's existing evaluation,
coefficient dual-pair, twist-interchange and double-Hom cancellation route, at all
four recorded coefficient stages. The proof constructs the exact theta, proves its
inverse and naturality, identifies the canonical cancellation arrow, transports
coefficient biduality to relative biduality and explicitly builds the restriction
of relative internal Hom to an anti-equivalence on dualizable objects.

Added `Sheaf.Paper.OrientationPerfectLines`, whose proved theorem transports the
standard shifted Tate line's invertibility and finite-Tor membership to the actual
orientation single-complex representatives. Added a proved public wrapper for the
existing generic private cancellation proof in
`Sheaf.Paper.OrientedDoubleHomCancellation`; no existing signatures or data change.
The change record is `coord/changes/H9-oriented-cancellation-proof-api.md`.

All three Lean modules compiled remotely. The final two whitespace lint warnings
were removed before delivery. Validation uses
`lcompile.py` for the single files and the sandbox import order; `deliver3.py` runs
the final compile, preflight, signature and axiom checks before pushing.

## Proved and sorry left

Closed the item's one hole: `WeilConjectures.sfOrientedPerfectDuality`
(node `sk-thm-sf-dual-perfect`). Added zero holes. There is no `sorry` in any
of the three delivered Lean modules. This is a proof from the declared dependencies;
`sfCoefficientEvaluationNaturality` and `sfPerfectDualPairAndTateStability` remain
existing upstream tasks, not new holes of this delivery.

Also proved `WeilConjectures.sfOrientationPerfectLines`
(node `lem-sf-orientation-perfect-lines`) and
`WeilConjectures.sfOrientedCancellation_of_evaluationLaws`
(node `lem-sf-oriented-double-hom-cancellation`).

## No longer needed

The proof does not need the private imports `Sheaf.Paper.SitePerfectCoefficientDual`,
`WeilConjectures.SixFunctors.Etale.Derived.Perfect.TateTwist`,
`Sheaf.Paper.SitePerfectComplex`, or
`Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted` in the item itself.
Their required interfaces are exposed by the actual dependency modules.
No declared unit dependency is pruned: evaluation, dual-pair/Tate stability,
cancellation, twist interchange, orientation and operations all remain used.
No module is withdrawn. The new line bridge uses only coefficient evaluation,
so it does not import PerfectDualPairAndTateStability.

## Where the brief, the DAG or earlier work was wrong

The mathematical route is unchanged. The canonical orientation line is a shifted
single complex, whereas the evaluation lemma uses the shift of its degree-zero
coefficient. Their canonical single-functor shift isomorphism and the inherited
full-subcategory inclusion's shift comparison must both be inserted. Analogous
localization and base-stage inclusion shift comparisons are required in the field
cases. The generic cancellation argument was already proved privately and needs
only a public wrapper to apply to these isomorphic line presentations.

Edge cases: d=0 uses the zero shift comparisons; the empty scheme and zero object
need no nonzero/rank assumptions. The general tensor inverse transport works for
arbitrary inverse-line contractions. All signed symmetries and evaluation maps
are those of the recorded closed structures. No unsigned cohomological substitute
or geometric biduality theorem is used.

## New nodes

`lem-sf-orientation-perfect-lines` records the strictly smaller coefficient-line
bridge, proved in `Sheaf.Paper.OrientationPerfectLines`, with explicit finite and
integral Tor-isomorphism transport and scalar-stage shift comparisons. Its helper
predicate contains actual membership and tensor-invertibility propositions only.
It has no postponed proof. The unit's statement and route remain intact.

## Second reading by H9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
