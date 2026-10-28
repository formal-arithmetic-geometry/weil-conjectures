## What changed

Replaced the sorry in `WeilConjectures.IntegralVerdier.reductionPairing_delta_uncurried`
with a complete adjunction calculation, using one new proof-only import,
`Sheaf.SixFunctors.IntegralVerdierReductionTensorSymmetry`.
The existing theorem signature, definitions and public imports are unchanged.
Four proved private helpers establish first-variable Hom uncurrying, postcomposition
of transposes, naturality of reduced transposes and cancellation through the finite swap.
The item's DAG proof now records these steps and the remaining tensor-only square.

## Proved and sorry left

Closed the one original hole:
`WeilConjectures.IntegralVerdier.reductionPairing_delta_uncurried`
(node `lem-sf-integral-verdier-reduction-pairing-delta-uncurried`).
No sorry remains in the item module.

Added one hole:
`WeilConjectures.IntegralVerdier.reduction_tensor_symmetry`
(node `lem-sf-integral-verdier-reduction-tensor-symmetry`), in its own new module.
Its proof is exactly `by sorry`, with source and a full representative proof in words.
This is a decomposition: one upper hole closed, one strictly smaller tensor-only hole
added, net hole reduction zero. The new lemma mentions neither delta, dualizing objects,
Hom comparisons nor evaluation; the combination of it with the supplied data is proved here.
The helper proofs are complete and introduce no holes. Server single-file checks passed
for the new tensor module (9.8 s), the item (15.5 s), and its unchanged immediate
consumer `Sheaf.SixFunctors.IntegralVerdierReductionPairingDelta` (10.9 s), with no
warnings in the final versions. The unchanged consumer copy was removed after validation.
The expected unused-binder
lint for the retained `he` is disabled only for this theorem, preserving its binder name.

## No longer needed

No existing import, module or node is pruned. The original model dependency remains.
No source-library declaration is removed or changed.
The ambient evaluation-naturality argument `he` is unnecessary for the formal calculation:
the defining adjunction transpose already supplies the needed ambient evaluation equation.
Its binder is retained verbatim for compatibility. The finite equation `het` is used.

## Where the brief, the DAG or earlier work was wrong

The existing one-step DAG plan hides a separate nonformal requirement: the reduction
tensor comparison must preserve the supplied normalized signed symmetries. Naturality
of the two symmetries alone does not state this square. The new tensor-only node isolates
precisely that representative calculation; the remaining mate calculation is implemented.
The normalized chain formulas give the same Koszul sign in every bidegree and also
cover zero complexes, empty schemes and n = 0 (the first positive quotient).
The unit's route through evaluation and coefficient reduction is unchanged.

The snapshot rework row records a transitive quarantine caused by
`IntegralNormalizedFamily`; the item source was restored and compiles against the
published artifacts. It contained one sorry, so this is proof work, not a zero-hole no-op.
The three earlier splits are not repeated: the new obligation is solely a tensor square,
and this delivery supplies the actual Hom/evaluation/inverse-comparison calculation.

## New nodes

`lem-sf-integral-verdier-reduction-tensor-symmetry` states preservation of signed
interchange by the normalized reduction tensor comparison, for arbitrary derived pairs.
It records the homogeneous-generator calculation and transport by naturality, with
Mathlib and project-library searches. The new module is
`lean/Sheaf/SixFunctors/IntegralVerdierReductionTensorSymmetry.lean`.
The change record is `coord/changes/B6-integral-reduction-tensor-symmetry.md`.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.SixFunctors.IntegralVerdierReductionPairingDeltaUncurried": "7f8952df455e47ea9cd107f9511f01981c74d410", "Sheaf.SixFunctors.IntegralVerdierReductionTensorSymmetry": "30e4a129531948987ccde3e8122aea08c423dc8b"}, "results": {"Sheaf.SixFunctors.IntegralVerdierReductionPairingDelta": {"hash": "e3b727db22e8a97ccf4811eb97e53087f353632a", "status": "OK"}}, "seconds": 21, "time": "2026-10-28T09:49:04+0800", "transitive": 0, "version": 1}
```

## Second reading by B6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
