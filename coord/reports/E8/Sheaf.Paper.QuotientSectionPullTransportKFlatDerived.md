## What changed

Corrected `section_pull_transport_kflat_derived` to require the realization equation
relating its supplied `barLam` to the internal `lam`. Proved the computation equation
by pasting the normalized endpoint scalar equations, the fixed geometric equations,
the ordinary square, and `PullNormalized`. The argument gives the equation on all
section complexes; the original flat-term K-flat conclusion is preserved.

The categorical pasting is reused from the already proved private helpers of
`SectionPullComputationOfRealization` through a proof-only `import all`. No data are
chosen from a new existence assertion. The scalar and geometric models and their
counits remain the specified constructions.

Adapted `QuotientSectionPullTransportKFlat` by proving the realization equation for
its existing conjugation construction and passing it to the corrected theorem.
Its existing definitions, theorem signatures, visibility and imports are preserved.
Updated the two corresponding DAG proof descriptions and the corrected Lean record.

The corrected item compiles without warnings in 49.5 seconds; its adapted caller
compiles without warnings in 12.5 seconds. Its unchanged direct importers
`QuotientSectionPullTransportLocalization` and `QuotientSectionPullTransportExtension`
compile against the adapted chain in 6.6 and 6.4 seconds, respectively. Their temporary
source copies were removed. All checks are below the per-file limit.

Change record: `coord/changes/E8-quotient-section-pull-derived-realization.md`.

## Proved and sorry left

Closed the one hole of the item, in the corrected theorem
`AlgebraicGeometry.ProEtale.QuotientSectionTensor.section_pull_transport_kflat_derived`
(node `lem-sfb-quotient-section-pull-transport-kflat-derived`). The omitted realization
hypothesis in the old statement was false in general; this delivery records that
repair explicitly rather than claiming a proof of the unrestricted old statement.

Added zero holes; split off zero statements. No `sorry` remains in either delivered
Lean file. The caller's new private realization lemma is completely proved.
The separate existing ordinary-comparison obligation
`section_pull_transport_kflat_ordinary` is unchanged and is still needed by the parent.

## No longer needed

Removed the item's private import `Sheaf.Paper.IntegralResidueDerivedMonoidal`;
the calculation uses the scoped existing-instance cache instead. The module itself
is still used elsewhere and is not withdrawn. No DAG node or module is pruned.
No K-flat preservation or new representative-resolution lemma is needed by this
all-complex categorical pasting argument. The parent's ordinary-comparison and
localization-extension obligations remain needed.

Searches were run with the required `msearch.py` Lean Finder, Loogle and Mathlib grep,
plus local searches of `lean/Sheaf` and `lean/WeilConjectures`. These found generic
naturality/derived-functor tools and the existing proved project pasting argument.

## Where the brief, the DAG or earlier work was wrong

STATEMENT-DISPUTED (old statement, repaired here): `barLam` was unrestricted and
never related to `lam`. Negating it preserves all the old hypotheses but changes
only the left side of the proposed computation equality. For the identity scalar
and geometric maps over integer coefficients, the positive and negative maps on
the regular module in degree zero cannot both give the same computation square.
The original docstring already called `barLam` the conjugated comparison, and the
parent constructs it by conjugation; the missing equation makes that requirement
explicit. The new private caller lemma proves it from `map_preimage` and inverse
cancellation. No unit statement, unit route, target or adopted source declaration
is changed.

The old DAG had no proof dependencies despite requiring the endpoint and geometric
computation equations. The updated proof records the actual equations used.
The naturality and equivalence argument is categorical and does not require the
flatness assumptions to establish this particular equality. Empty schemes and
zero coefficients require no exceptions.

## Forced adaptations

`Sheaf.Paper.QuotientSectionPullTransportKFlat` is unclaimed in the shared
snapshot. Its original call fails against the corrected theorem at line 123: the
argument `e` has the ordinary-comparison isomorphism type, while the newly inserted
argument expects the realization equation (a `Prop`). The complete private
`sectionPullTransportDerived_realization` proof supplies that equation; the last
call passes it before `e`. Local reducibility settings support the isomorphism
cancellation proof. No existing public signature, visibility, import or definition
body is changed.

## Related modules compiled before delivery

2 related module(s) compiled against this delivery by deliver3.py: 1 INFRA, 1 OK.

```json
{"capped": false, "direct": 2, "left_out": 0, "own": {"Sheaf.Paper.QuotientSectionPullTransportKFlat": "bc9394c60fb4f8468b4f8adbcbc83671e1d0931e", "Sheaf.Paper.QuotientSectionPullTransportKFlatDerived": "3fcf90c1855cd0f2af5d399bbc454efd5646e8e8"}, "results": {"Sheaf.Paper.QuotientSectionPullTransportExtension": {"hash": "3e53cea4a261930ca9e16d8af3e71d959cb32f83", "status": "INFRA"}, "Sheaf.Paper.QuotientSectionPullTransportLocalization": {"hash": "f34e948891cd6e2dda24d63d3817c3360a19ffa4", "status": "OK"}}, "seconds": 83, "time": "2026-10-28T08:09:31+0800", "transitive": 0, "version": 1}
```

## Second reading by E8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
