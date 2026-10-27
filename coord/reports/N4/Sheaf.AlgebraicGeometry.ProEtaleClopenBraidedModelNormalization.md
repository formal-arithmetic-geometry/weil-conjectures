## What changed

Filled `AlgebraicGeometry.Scheme.ProEt.ClopenMonoidalDescent.clopen_braided_model_normalization`
using the existing `CategoryTheory.normalizedBraidedLocalization` and its monoidal
factorization conclusion. The assigned theorem keeps its signature and public import.

Added four support modules, with the native cancellation step split as one named theorem:
`Sheaf.Algebra.Homology.BraidedCochainNormalization` proves the generic additive braided
cochain lift with its summand characterization and single-complex unit;
`Sheaf.AlgebraicGeometry.ProEtaleClopenBraidedCochainNormalization` constructs the concrete
braided cochain lift and proves its summand and unit equations;
`Sheaf.AlgebraicGeometry.ProEtaleClopenBraidedLocalization` supplies K-flat models and
specializes normalized braided localization to the specified exact restriction. The main
proof keeps the cochain structure abstract and cancels the monoidal factorization equations
to obtain the native model square and degree-zero unit equation. Explicit native structures
and tensor-isomorphism equations avoid repeated inference and unfolding of large data.

The generic cochain and localization helpers are proved. The native cancellation theorem is
the one strictly simpler split-off statement below and remains the sole sorry. The cochain braiding and K-flat criterion follow the existing
private proof patterns in `Sheaf.Algebra.Homology.RingIsomorphismTensorTransport`, without
importing its scalar-transport infrastructure. Proof imports of the cochain monoidal
construction, normalized localization and independent-coefficient K-flat resolutions are
confined to the modules that use them. The new support theorems package genuine cochain and
localization steps after profiling; none is the assigned normalization theorem renamed.
Updated the item's DAG proof and added the four support nodes. No other existing module or
node is changed.

## Proved and sorry left

Closed the one original hole in
`AlgebraicGeometry.Scheme.ProEt.ClopenMonoidalDescent.clopen_braided_model_normalization`
(node `lem-pur-clopen-braided-model-normalization`). Also proved the new support theorems
`AlgebraicGeometry.Scheme.ProEt.ClopenMonoidalDescent.clopen_braided_cochain_normalization`
and `AlgebraicGeometry.Scheme.ProEt.ClopenMonoidalDescent.clopen_braided_localization`,
and `CategoryTheory.Functor.OplaxMonoidal.braided_cochain_normalization`.
One original hole is closed and one strictly simpler cancellation theorem is split off.
The split theorem `clopen_braided_model_squares` is the only remaining `sorry`; all other
delivered declarations are proved. Every added private helper has a complete proof.

## No longer needed

Pruned none. No original import, module or node is withdrawn. The generic localization,
K-flat resolution and total-tensor dependencies remain needed through the support modules.
The construction needs only the coproducts defining total tensor, transported from the
hypothesized coefficient-sized coproducts by ULift. The cancellation step does not need
flatness of individual terms; every existing hypothesis is retained.

## Where the brief, the DAG or earlier work was wrong

The current server queue confirmed this was a one-hole proof item, not a zero-hole repair.
No mathematical defect or statement change was needed. The current blueprint places
`sk-def-purity-conv` under `sec-six-functors-basics`; its unit statement and route are kept.
The proof uses no nonzero-ring or nonempty-scheme assumption.

Profiling found expensive comparisons of concrete monoidal structures. The construction
is kept folded behind proved tensor/unit equations, and the derived argument uses the
proved existential cochain interface instead of unfolding its construction. The four
self-contained support modules implement the brief's profiling and splitting procedure;
they introduce no unproved data or unresolved obligation.

## New nodes

`lem-pur-braided-cochain-normalization`, at
`dag/nodes/sec-smooth-purity/lem-pur-braided-cochain-normalization.json`, records the fully
proved signed cochain lift for a general additive braided functor. It has no sheaf,
K-flatness or derived-localization data.

`lem-pur-clopen-braided-cochain-normalization`, at
`dag/nodes/sec-smooth-purity/lem-pur-clopen-braided-cochain-normalization.json`, records the
fully proved ordinary-to-cochain braided lift with prescribed inverse tensorator and unit.
It has no K-flat hypothesis or derived-localization conclusion.

`lem-pur-clopen-braided-localization`, at
`dag/nodes/sec-smooth-purity/lem-pur-clopen-braided-localization.json`, records the fully
proved specialization of normalized localization. It gives a braided derived restriction
with monoidal canonical factors from any braided cochain restriction preserving K-flat
models. It asserts neither the summand identification nor the model and unit normalization
of the assigned theorem. No change record is needed: only the assigned module, new modules
and their nodes are delivered.

`lem-pur-clopen-braided-model-squares`, at
`dag/nodes/sec-smooth-purity/lem-pur-clopen-braided-model-squares.json`, records the
strictly simpler native tensor and unit cancellation step. Its proof is the cancellation
argument described in the theorem docstring; it takes the already constructed braided
cochain and derived functors as inputs and asserts no existence result.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Algebra.Homology.BraidedCochainNormalization": "5a2dddef00743dac3c5fce260adac1ce79ebda31", "Sheaf.AlgebraicGeometry.ProEtaleClopenBraidedCochainNormalization": "2257d64e7a674643859d8f01928ca75e9dd81067", "Sheaf.AlgebraicGeometry.ProEtaleClopenBraidedLocalization": "889a7d7a8170ae9536cba84e544481121036dadd", "Sheaf.AlgebraicGeometry.ProEtaleClopenBraidedModelNormalization": "2b4af1150c2260d9943ecf64ac9b3a4578e5b72d", "Sheaf.AlgebraicGeometry.ProEtaleClopenBraidedModelSquares": "118d68f7de0d7f42f27a75626134a9544d947bfd"}, "results": {"Sheaf.AlgebraicGeometry.ProEtaleClopenKFlatMonoidalDescent": {"hash": "fd83ac868cedd059f98c6b389b496a5bfd7c3883", "status": "OK"}}, "seconds": 121, "time": "2026-10-28T05:16:53+0800", "transitive": 0, "version": 1}
```

## Second reading by N4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
