## What changed

Implemented the scalar/pullback calculation through the L-pullback normalization
on the ordinary scalar extension of P. The proof transports the source quotient
presentation, identifies the resulting strict comparison with the given q,
computes the inverse system scalar/pullback comparison on C, and assembles the
Roos coordinate using naturality and the existing ordinary comparison
normalization. In particular it writes out the transport along eP rather than
postponing the completed-comparison identity under another name.

Added the source-side presentation theorem
`WeilConjectures.ScalarExtensionTower.scalarCompletionQuotientPresentation` as a
strictly smaller obligation. It involves only Y, the source good complex and its
quotient presentation; it has no f, constructible K, derived-pullback completeness,
system scalar/pullback comparison, or Roos coordinate conclusion.

Factored the entire-system coordinate equation into the proved module
`Sheaf.Paper.ScalarPullbackRoosCoordinateSystem`. Profiling identified costly
coefficient-functor elaboration and kernel checking in the combined proof; after
sharing the scalar presentation and avoiding substitution through the whole proof,
this self-contained calculation was compiled separately to keep each file below
the unchanged 60-second limit.

Added `WeilConjectures.ScalarExtensionTower.scalarPullbackQuotient_ext`, with a
proof using the existing ordinary scalar, quotient and inverse-image adjunctions.
Local surjectivity of the completed-to-finite projection permits the intermediate
maps to be regarded as finite-linear. Equality on the nested unit generators then
detects equality. This closes the strict uniqueness part of the original plan.

Validation: the full sandbox compiles through `lcompile.py --all`, with every
file below 60 seconds (the upper file took 47.5 seconds). Its original theorem
signature was also compared verbatim with the assigned source.

## Proved and sorry left

Original hole closed:
`WeilConjectures.ScalarExtensionTower.scalarPullbackLeftRoos`.

New theorems proved:
`WeilConjectures.ScalarExtensionTower.scalarPullbackQuotient_ext` and
`WeilConjectures.ScalarExtensionTower.scalarPullbackRoosCoordinate_system`.

New hole added, and the only explicit sorry remaining in this packet:
`WeilConjectures.ScalarExtensionTower.scalarCompletionQuotientPresentation`.

The remaining hole is recorded by
`lem-pur-scalar-completion-quotient-presentation`.

The original hole is therefore reduced to one source-side presentation obligation;
this is a decomposition with net zero holes, not a claim of a sorry-free proof of
the completed comparison. The upper naturality and normalization assembly and the
strict generator uniqueness argument are complete Lean proofs.

## No longer needed

The proof no longer needs these original proof dependencies:

- `lem-pur-integral-operations-scalar-extension-pullback-clause`: this is a
  different scalar-tower/pullback clause. The present calculation uses the
  ordinary scalar/pullback normalization directly.
- `def-pod-scalar-completion-tensor-comparisons`: its tensor comparison is unused;
  scalar completion and ordinary pullback normalization come from
  `lem-pur-integral-operations-scalar-extension` instead.

No existing Lean import was removed and no module was withdrawn. The above are
removed from this node's proof dependencies, not assertions that every other
consumer in the project can discard them. The supplied coordinate definitions,
realization models, whole-system comparison and good-quotient detection helpers
remain needed. The coherent primitive presentation construction remains a dependency
of the new source-side transport node, since it supplies the ordinary quotient
presentation of scalar P. No source-library declaration is removed or changed.

## Where the brief, the DAG or earlier work was wrong

The original plan described transporting the quotient presentation and identifying
strict maps on generators, but none of its listed declarations stated precisely
those two facts. In particular scalar normalization alone supplies a strict
comparison to the scalar tower, whereas pullback normalization expects a coherent
presentation of ordinary scalar P. The new source-side theorem states that missing
bridge without repeating the completed scalar/pullback statement. The second
missing fact is proved here by ordinary adjunctions.

The original item signature is preserved verbatim. The edge cases for the new
statements were checked mathematically: zero complexes, n=0 (the project's first
quotient), empty schemes, identity embeddings and ramified coefficient inclusions
use balanced tensor association and ordinary adjunctions; no finite-quotient
flatness or faithfulness of derived evaluation is assumed.

## New nodes

- `lem-pur-scalar-completion-quotient-presentation`: coherent source-side scalar
  presentation and its completion/reduction equation; one named sorry.
- `lem-pur-scalar-pullback-quotient-ext`: uniqueness of strict scalar/pullback
  coordinates on nested tensor-unit generators; proved.

- `lem-pur-scalar-pullback-roos-coordinate-system`: the entire-system coordinate
  transport by inverse comparison naturality; proved.

All three inherit the item's chapter and unit. Sources are Stacks 03D3, 06YY, 07A4
and 0941, with the specialized project formulas explicitly identified as an agent
expansion of the original proof steps. The node records include the actual
LeanSearch, LeanFinder/Loogle and source-grep searches.

Change records:
`coord/changes/G6-ScalarCompletionQuotientPresentation.md`,
`coord/changes/G6-ScalarPullbackQuotientExt.md`, and
`coord/changes/G6-ScalarPullbackRoosCoordinateSystem.md`.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.ScalarCompletionQuotientPresentation": "a38d2381e0c0d26e4ba85ebe0d7914087ca94e94", "Sheaf.Paper.ScalarPullbackLeftRoos": "79711afd3ab5cc39b3c6872fd3792cf84939fd9f", "Sheaf.Paper.ScalarPullbackQuotientExt": "378e5578f51af965fe6742c3c9bdca41662b564a", "Sheaf.Paper.ScalarPullbackRoosCoordinateSystem": "c6748187a2781ce968904104aa16cca612203892"}, "results": {"Sheaf.Paper.ScalarTowerPullbackLimitBridge": {"hash": "aa700c326d8cf77ed021154486d5837e117ea91d", "status": "OK"}}, "seconds": 27, "time": "2026-10-28T08:27:33+0800", "transitive": 0, "version": 1}
```

## Second reading by G6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
