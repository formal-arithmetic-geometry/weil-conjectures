## What changed

Retired `Sheaf.AlgebraicGeometry.IntegralClosureDedekindSurjectiveFibres` completely:
its path is in `deleted.txt`, and its DAG node
`lem-sc-integral-closure-dedekind-surjective-fibres` points at the proved
`WeilConjectures.AlgebraicGeometry.IntegralClosureDedekindSurjectiveFibres` twin.
The node's statement and proof plan are unchanged.

Both remaining consumers, `Sheaf.RingTheory.FiniteAlgebraExtremallyDisconnected`
and `Sheaf.TraceFormula.CurveNormalizationCompletion`, now import the twin.
The first consumer used `AlgebraicGeometry.finite_spec_residueFieldMap`, which is
private upstream. Its existing complete proof is retained as the consumer's private
`finite_spec_residueFieldMap` helper, and the one call is updated. Existing consumer
signatures and definitions are unchanged. No upstream file or target is edited.

The other listed consumers, `Sheaf.AlgebraicGeometry.PlurinodalAlteration` and
`Sheaf.RingTheory.SemilocalNormalizationDimOne`, are already absent from the current
repository. They are not recreated. A current whole-library search finds only the
two import sites adapted here and the withdrawn module's own declaration/call.

Validation: both remaining consumers compiled through `lcompile.py --all` against
the upstream twin (6.3 s and 3.8 s, respectively). A source import-closure scan of
both consumers finds neither the withdrawn module nor any Sheaf/upstream twin pair
in either environment.

Change record: `coord/changes/F8-integral-closure-upstream-reexport.md`.

## Proved and sorry left

Assigned module: zero original holes; retired. Holes closed: none. Holes added:
none. Split off: none. This is retirement of one duplicate module, not new proof work.

The retained private affine residue-field transport helper is fully proved.
`extremallyDisconnected_spectrum_of_finite_finitePresentation` remains fully proved.
The pre-existing `RingTheory.curve_normalization_completion` sorry
(node `lem-trf-curve-normalization-completion`) is unchanged; this delivery adds no
sorry and replaces no proof with sorry.

## No longer needed

Withdrawn module:
`Sheaf.AlgebraicGeometry.IntegralClosureDedekindSurjectiveFibres`.
Its import is removed from both remaining consumers and replaced by the official
upstream twin. The duplicate main theorem and three private proof helpers disappear
with the copy. The affine residue-field transport proof stays private in its sole
consumer, without retaining a public compatibility module.

The five mathematical proof dependencies in the node remain needed by the upstream
proof; no mathematical lemma or DAG node is pruned. The source-library declarations
and imports remain untouched.

## Where the brief, the DAG or earlier work was wrong

The earlier packet retained a re-export module and was rejected by the ordinary
proof-progress gate because the assigned module already had zero holes. The current
human instruction requires full retirement, which this packet implements using
`deleted.txt` and consumer adaptations. The earlier claim that no consumer edits were
needed applied only to its retained re-export and does not apply to full withdrawal.

The retirement inventory lists four consumers, but two have already disappeared from
the current library; all remaining consumers are included here. The upstream twin's
main theorem has the same signature and proof; its affine residue-field helper has
private visibility, requiring the one consumer-local proof adaptation above.

## Second reading by F8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
