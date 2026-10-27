## What changed

Replaced the sole sorry in Sheaf.Paper.IntegralTensorPullbackAugmentation by a complete
Lean derivation from three independent coefficient statements. The private generic
limit_tensor_augmentation lemma proves the adjunction calculation: transpose the
forward tensor map, transpose the two forward pullback maps, cancel the effective
counits, and use the coherent monoidal square. The final proof transports through
the existing pullback/tensor realizations, expands the prescribed canonical completed
comparison, and uses naturality to recover the exact original equation.

Moved tensorModel and TensorAugmentationNormalized, with unchanged signatures and
bodies, into IntegralTensorReductionAugmentation and publicly re-exported them from
the item. No target statement or mathematical definition changed. This extraction
lets the three lower modules avoid an import cycle. Their comparison data are chosen
only from proved unique specifications: uniqueness follows in Lean from the actual
reduction/limit Hom bijections. The remaining existence statements do not choose
arbitrary nonunique data.

All four delivered modules compiled separately in final import order: pullback
reduction 5.4 seconds, tensor reduction 16.1 seconds, coherent square 3.9 seconds,
and the item 14.1 seconds. The unchanged direct caller
Sheaf.Paper.IntegralOrdinaryTensorPullbackNormalization compiled against these files
in 27.9 seconds. Its temporary source copy was removed after verification, so it is
not part of the delivery. Every final file is below the 60-second limit.

## Proved and sorry left

Closed the original textual hole in
WeilConjectures.IntegralOrdinary.tensorPullback_augmentation by decomposition.
It has a complete proof combining the three strictly smaller statements below.
This is a decomposition, not a net proof of the original mathematical obligation:
1 original hole removed, 3 lower holes added, net -2 holes. The item itself has zero holes.

Also proved, without additional holes, the private limit_tensor_augmentation lemma and
WeilConjectures.IntegralOrdinary.tensorReductionAugmentation_existsUnique and
WeilConjectures.IntegralOrdinary.pullbackReductionAugmentation_existsUnique.

Every remaining hole is exactly the full proof of one public theorem:

- WeilConjectures.IntegralOrdinary.tensorReductionAugmentation_exists
  (lem-sf-tensor-reduction-augmentation): one scheme, no geometric pullback.
- WeilConjectures.IntegralOrdinary.pullbackReductionAugmentation_exists
  (lem-sf-pullback-reduction-augmentation): one geometric pullback, no tensor.
- WeilConjectures.IntegralOrdinary.reductionTensorPullback
  (lem-sf-reduction-tensor-pullback): ordinary and coherent system tensor comparisons,
  on arbitrary derived inputs, before the total limit, with no completion augmentation
  and no inverse effective counits.

Each module has one named sorry theorem, its own DAG node, source and proof in words.
None restates the original completed tensor/pullback square. No sorry occurs inside a
definition, private theorem or combining proof.

## No longer needed

No mathematical module is withdrawn, and no import-closure pruning is claimed.
The item's direct public ConstructibleTensorCompletionChain import is replaced by
IntegralTensorReductionAugmentation, which publicly re-exports it. The three lower
statements still use the original representative, chain, ordinary-pullback and
coherent-system ingredients, now assigned to the separate normalization calculations.
The item proof itself uses the three new nodes, the existing coherent adjunction
calculus and the definition of the canonical completed comparison. The original
ambient-model proof dependencies are retained in the lower nodes where needed.

The new pre-limit square module imports ProEtaleCanonicalTensorPullback rather than
the completed tensor comparison module: its statement has no completed comparison.

## Where the brief, the DAG or earlier work was wrong

The current server queue row is a one-hole proof item. The rework file also contains
an older quarantined-dependency entry and the saved build-error file names a bad
IntegralOrdinaryPullbackComparison import. The current item exists, and the unchanged
baseline compiled, so that historical failure is not an assigned zero-hole repair.

The original two proof steps compressed three separate normalized comparisons and the
subsequent categorical argument. The delivery makes their mathematical boundaries
explicit and proves the categorical argument, including the specified counit factors.
The original statement and unit route are preserved. In particular, it never tries to
detect equality of derived system maps by equality of finite derived evaluations.

The DAG already contains unrelated cycles below existing dependencies; the delivery
adds no cycle through any delivered node. No existing unrelated node is changed.
Existing operation-model and coherent-system results from the smooth-purity chapter
are used as general normalization/localization tools, as in the original node, not as
a replacement for the unit's route.

## New nodes

lem-sf-tensor-reduction-augmentation: the strong reduction comparison for ordinary
tensor, normalized by the entire strict augmentation. Its adjunct uniqueness is proved.

lem-sf-pullback-reduction-augmentation: ordinary inverse image commutes with coherent
reduction, with its adjunct equal to the fixed forward pullback augmentation. Its
adjunct uniqueness is proved.

lem-sf-reduction-tensor-pullback: monoidal compatibility of those normalized comparisons
in the coherent system category itself, before applying the derived limit.

Change record: coord/changes/integral-tensor-reduction-augmentation-extraction.md.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.IntegralPullbackReductionAugmentation": "0db06dceb3ac3e3845573ee72b625885de3109bb", "Sheaf.Paper.IntegralReductionTensorPullback": "ec50c031e51891d8b934a3a937859dc78eb882a9", "Sheaf.Paper.IntegralTensorPullbackAugmentation": "460d419d690ace16bd39462050cf1a9224aff152", "Sheaf.Paper.IntegralTensorReductionAugmentation": "3e6238625abc1ed81f92b13c9d5ae4565fcb94ad"}, "results": {"Sheaf.Paper.IntegralOrdinaryTensorPullbackNormalization": {"hash": "5a532ddeaf8fb0e312e07ba92fb3429c9b541b81", "status": "OK"}}, "seconds": 84, "time": "2026-10-28T00:54:57+0800", "transitive": 0, "version": 1}
```

## Second reading by F1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
