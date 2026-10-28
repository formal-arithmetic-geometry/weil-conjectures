## What changed

Proved `WeilConjectures.AmbientPullbackTensor.derived_pullback_compositionLaws` in
`Sheaf.Paper.AmbientPullbackDerivedCompositionLaws`, with its signature unchanged.
Added proof-only imports of `Sheaf.Paper.AmbientPullbackOrdinaryCompositionLaws`
and `WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate`.
No public imports, definitions, attributes, instances, or other modules changed.

Associativity specializes the existing proved
`Functor.mapDerivedCategoryCompNatIso_cocycle` to the specified pullbacks.
Four proved private helpers handle postcomposition, equality transport, and the
two unit calculations. The unit helpers apply exact-functor whiskering coherence
and cancel composition isomorphisms; they introduce no additional assumptions.
Endpoint transports are preserved explicitly by equality induction, rather than
by identifying the two bracketings or identity composites definitionally.

The node proof now records these calculations. Its three proof dependencies
remain the ordinary composition laws, exact-functor derived factorization, and
the localization universal property. The unit record has no realized statement
or steps attached to this node, and its route is unchanged.

Read Stacks Tag 015F in `derived.tex`, lemma-right-derived-exact-functor, and
Tag 04VG in `categories.tex`, lemma-properties-left-localization. The existing
source-library coherence lemmas implement the natural-transformation
localization argument specified by the DAG.

Validation: the complete module compiled without errors or warnings through
`lcompile.py` in 6.4 seconds. The delivery tool performs the final compilation
and axiom probe.

## Proved and sorry left

Closed 1 of 1 holes:
`WeilConjectures.AmbientPullbackTensor.derived_pullback_compositionLaws`
(node `new-lem-sf-ambient-pullback-derived-composition-laws`).

Zero holes remain in the item, zero holes were added, and no statements were
split off. The proof uses the already stated
`WeilConjectures.AmbientPullbackTensor.ordinary_pullback_compositionLaws`,
whose existing proof obligation remains in its own module; this delivery proves
the derived localization step from that declaration, as assigned.

## No longer needed

None. No imports were removed. Each original stated proof dependency remains
part of the exact-localization argument. No modules or DAG nodes are withdrawn.
The existing proved cocycle and unit API avoids creating any further
intermediate obligations.

## Where the brief, the DAG or earlier work was wrong

No statement correction was necessary. The planned localization step already
has proved cocycle, whiskering, and unit lemmas in the adopted source library;
instantiating them closes the item without another decomposition.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.AmbientPullbackDerivedCompositionLaws": "b386cbb58546039dfe7650451e079041616aa8d0"}, "results": {"Sheaf.Paper.AmbientPullbackCompositionLaws": {"hash": "7f16387c2823c52b71d11566fc319662f47ef068", "status": "OK"}}, "seconds": 12, "time": "2026-10-28T09:19:54+0800", "transitive": 0, "version": 1}
```

## Second reading by C4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
