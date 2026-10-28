## What changed

Closed the `finiteScalarPullback_representative_factors_core` hole in the item
module.  Its proof rewrites the derived counit using the exact factorization and
then applies a new factorized representative equation, simplifying functorial
composition and associativity.  Added the proof-only module
`Sheaf.Paper.FiniteScalarPullbackRepresentativeFactorsFactorized`; the existing
public statements and definitions are unchanged.  The module chain compiles in
import order, with no new definition holes.

## Proved and sorry left

Proved:

- `WeilConjectures.finiteScalarPullback_representative_factors_core`.

The wrapper theorem `WeilConjectures.finiteScalarPullback_representative_factors`
was already proved and remains proved.  Added one strictly simpler split-off
`sorry`:

- `WeilConjectures.finiteScalarPullback_representative_factors_factorized` in
  `Sheaf.Paper.FiniteScalarPullbackRepresentativeFactorsFactorized`, node
  `lem-sf-finite-scalar-pullback-representative-factors-factorized`.

## No longer needed

No existing imports, modules, or nodes are withdrawn.  The completed proof uses
only the ordinary comparison module, the derived-counit API, and the new
factorized intermediate; no planned dependency was removed beyond the unused
`MapDerivedCategoryMate` proof import.

## Where the brief, the DAG or earlier work was wrong

The original proof plan presented the counit-form equation as one large mate
calculation but did not expose the exact-derived factorization as a Lean-level
intermediate.  The factorized form is a strict syntactic substep: it separates
the left-derived isomorphism from `mapDerivedCategoryFactors`, and the item proof
then performs the counit rewrite explicitly.  No target statement or existing
definition was changed.

## New nodes

- `lem-sf-finite-scalar-pullback-representative-factors-factorized`: the
  factorized derived inverse-mate equation before the standard exact-counit
  factorization; its remaining proof is recorded as a named theorem with the
  Stacks source and proof plan in its docstring.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.FiniteScalarPullbackRepresentativeFactors": "798964148f769d4cc5229bae38cf9f0a320cd023", "Sheaf.Paper.FiniteScalarPullbackRepresentativeFactorsFactorized": "5976ad0ceb5ab0acf327dd9960b169d20cab1396"}, "results": {}, "time": "2026-10-28T08:27:35+0800", "transitive": 0, "version": 1}
```

## Second reading by T2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
