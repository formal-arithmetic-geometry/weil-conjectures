## What changed

Prove `WeilConjectures.AdicQbarRealization.reindexing_tensor_unit_contraction`
without changing its statement or `unitTensorSquare`. The proof uses a private,
general categorical cancellation argument and the ordinary reindexing left-unitor
law, imported privately from the new module
`Sheaf.Paper.AdicReindexingLeftUnitor`.

The new modules prove the left-unitor law from the recorded homogeneous pure
section equation, coefficient-unit section equation, K-flat representative
normalization, and tensor model coherence. They use the existing proved private
representative and cancellation helpers from the three ringed-forget tensor
modules through proof-only imports. The cochain calculation also reuses the
proved private `CategoryTheory.tensorGenerator_map` from
`Sheaf.Algebra.Homology.RingedSliceScalarUnit`, avoiding a duplicate proof of
naturality on total tensor generators. No existing dependency module is changed.

Validation: `lcompile.py --all` compiled the cochain module, derived unitor and
assigned contraction in import order, in 50.2 s, 38.6 s and 14.9 s respectively.
The remaining two proof-local `letI` style suggestions were then changed to
`let`; the declaration statements and the original definition are unchanged.

## Proved and sorry left

Closed one original hole:
`WeilConjectures.AdicQbarRealization.reindexing_tensor_unit_contraction`
(`lem-sf-adic-reindexing-unit-contraction`).

The new theorem
`WeilConjectures.AdicQbarRealization.reindexing_left_unitor`
(`lem-sf-adic-reindexing-left-unitor`) and
`WeilConjectures.AdicQbarRealization.reindexing_left_unitor_chain`
(`lem-sf-adic-reindexing-unit-complex`) and all private helpers are proved.
No holes are added or split off. None of the three delivered modules contains a `sorry`.
This is a proof of one of one original holes, not a decomposition.

## No longer needed

The theorem of `lem-sf-adic-reindexing-tensor-compatibility`
(`Sheaf.Paper.AdicReindexingTensorCompatibility`) is not needed to prove this
conditional contraction: its specialized tensor square is already the explicit
hypothesis. The own node's proof dependencies now record only the realization
data and the proved ordinary left-unitor calculation. Its statement dependencies
are preserved. No public import is removed, and no module is withdrawn: tensor
compatibility is still used to supply the hypothesis in the parent argument.

The right-unit compatibility equations are unnecessary here. Left-unit
compatibility and cancellation by an object isomorphic to the unit suffice.
The unit's declared route through realization tensor compatibility is preserved.

## Where the brief, the DAG or earlier work was wrong

The plan's instruction to expand the coefficient unit hides a derived-category
step: left unitality is not a field of `ReindexTensor`. Prove it using its
existing pure-section and representative normalization fields. The new lemma
isolates and proves this step rather than postponing the contraction again.

On sections, reindexed modules use the inverse coefficient-ring map for scalar
multiplication. Thus after the unit-section map applies the forward coefficient
isomorphism, the transported action cancels it. No faithfulness of global
sections, global generation by pure tensors, or nonzero coefficient assumption
is needed: the existing sheaf tensor and totalization extensionality lemmas
perform the local generator checks. The argument also covers zero rings and
empty schemes.

## New nodes

`lem-sf-adic-reindexing-left-unitor`, in
`dag/nodes/sec-six-functors/lem-sf-adic-reindexing-left-unitor.json`, records the
fully proved ordinary left-unitor equation for the already normalized
`ReindexTensor`. This is strictly below the contraction: it makes no assertion
about realization comparisons or the common-stage tensor square. Its proof is
by K-flat representatives, degreewise pure sections, localization and naturality.
The proved cochain calculation is in its own module to keep each compile under
the project's file limit.

`lem-sf-adic-reindexing-unit-complex`, in
`dag/nodes/sec-six-functors/lem-sf-adic-reindexing-unit-complex.json`, records the
fully proved cochain equation for any two multiplication-normalized chain
left-unitors. Its module is `Sheaf.Paper.AdicReindexingUnitComplex`. It asserts
neither the derived unitor equation nor the common-stage contraction. Both new
statements are proved, with no split-off holes. No change records are needed:
only the assigned module and its node, and the two new modules and nodes, change.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.AdicReindexingLeftUnitor": "c5b3f39298a353acbb750511d5908aa922d6dc5a", "Sheaf.Paper.AdicReindexingUnitComplex": "50502e1d512abfd9c872f8ceb710277c0d29c391", "Sheaf.Paper.AdicReindexingUnitContraction": "abf4fedfed39d21452eb84ab0faa4d9345c1d0e1"}, "results": {"Sheaf.Paper.AdicReindexingUnitCompatibility": {"hash": "163bcae68c8ec6e3b31e024fe6687d7e9dcbda16", "status": "OK"}}, "seconds": 15, "time": "2026-10-28T08:22:49+0800", "transitive": 0, "version": 1}
```

## Second reading by Q8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
