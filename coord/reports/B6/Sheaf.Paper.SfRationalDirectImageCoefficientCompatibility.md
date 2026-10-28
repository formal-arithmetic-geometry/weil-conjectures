## What changed

Replaced the body of `WeilConjectures.sfRationalDirectImageCoefficientCompatibility`
with a complete Lean reduction. Its statement and all three public imports are unchanged.
The construction reuses `commonStagePullback_comparison_data`: its coherent comparisons
and hom-component equations give the stage morphism and its full isomorphism-component
normalization. For each extension, component extensionality identifies its comparison
with `rationalPullbackStageComparison`. The proved private helper `rightMate_transport`
transports invertibility through both recorded transition equalities, by equality
induction, keeping the supplied adjunctions unchanged. Equality of functor families,
comparison components, and finally proof irrelevance prove uniqueness of the whole
stage morphism.

Added proof imports of `RationalPullbackStageCoherence`,
`RationalPullbackScalarRightMate`, and `all Mathlib.Logic.Small.Defs`. The last exposes
`Shrink` for tactic conversion between the recorded stage categories and their literal
rational coefficient categories. Local reducibility attributes keep large scalar and
pullback constructions folded while exposing the stage adapters; both respectTransparency
options are true. These local attributes change no exported API or global instance.

The new module `Sheaf.Paper.RationalPullbackScalarRightMate` states only the right-mate
calculation for ONE finite coefficient extension and TWO already supplied adjunctions.
It has no algebraic closure, directed index, stage morphism, coherence data, stage
normalization or uniqueness conclusion. The main module performs all those constructions
and the transition-equality transport itself. No data are chosen from the new theorem:
it proves a proposition about the existing named comparison.

Validation: the new module compiled in 5.1 seconds (and a subsequent set compile in
1.6 seconds); the final assigned-module source compiled without warnings in 23.5 seconds.
Only `lcompile.py` was used. The unchanged public signature and public imports preserve
all existing callers; no other existing Lean module is changed. `import_direction.py may`
confirms the proof import of `RationalPullbackStageCoherence` is acyclic.

## Proved and sorry left

Original holes: 1, in
`WeilConjectures.sfRationalDirectImageCoefficientCompatibility`
(node `lem-sf-rational-direct-image-coefficient-compatibility`). Its proof body is now
complete. The stage-family construction, normalization, equality transport of the
literal mate, and uniqueness are checked Lean proofs.

Added holes: 1, exactly
`WeilConjectures.rationalPullbackScalar_rightMate_isIso`
(node `lem-sf-rational-pullback-scalar-right-mate`). Its proof is exactly `by sorry`.
The declaration docstring and node give the finite-free/trace argument, including the
normalization of the mate and the passage through raw rationalization. The adjoints
remain supplied hypotheses. Identity extensions, zero complexes, and empty schemes
are included; no geometric preservation hypothesis has been added.

There are no holes left in the assigned module and no other added holes. This is a
strict decomposition, not a net proof gain: one upper hole closed, one lower hole
added, net zero. The new statement is precisely the coefficient-level part of proof
step 2, not the original bundled existence-and-uniqueness theorem under another name.

## No longer needed

No original public import is removed and no module is withdrawn. The proof uses the
existing completed comparison-data and stage-coherence theorems, so it does not redo
scalar-tower construction from its original low-level dependencies.

The old parent proof-dependency list is replaced by the three actual direct inputs:
`lem-weil-common-stage-pullback-comparison-data`,
`lem-weil-rational-pullback-stage-coherence`, and the new single-extension lemma.
The following old entries are no longer DIRECT proof obligations of this parent:

- `lem-pur-integral-operations-scalar-extension`
  (`Sheaf.Paper.IntegralOperationsScalarComparisons`) and
  `lem-weil-scalar-extension-composition` (`Sheaf.Paper.ScalarExtensionComposition`):
  the proved stage-comparison coherence already supplies the needed tower identity.
- `def-weil-derived-pullback-tensor-hom` (`Sheaf.Paper.DerivedPullbackTensorHom`):
  retained as a statement dependency and public import; it need not be reproved here.
- `prop-weil-pbc-descent-functors` (`Sheaf.Paper.PbcDescentFunctors`): no quotient descent
  is performed here; the StageSystem.Morphism record and its coherence suffice.
- `lem-weil-finite-free-completed-scalar-comparison`
  (`Sheaf.Paper.FiniteFreeCompletedScalarComparison`): moved to the single-extension
  calculation's proof dependencies, rather than used by the stage assembly.
- `prop-weil-pbc-scalar-extension` (`Sheaf.Paper.PbcScalarExtension`): the parent does
  not use its scheme-specific scalar/exchange package. The already normalized
  pullback comparisons and the single-extension calculation suffice.
- `lem-pur-completed-coefficient-pushforward-comparison`
  (`Sheaf.Paper.CompletedCoefficientPushforwardComparison`): the coefficient-local
  trace/restriction argument uses the supplied adjoints, without constructing geometric
  direct-image functors or proving their preservation for arbitrary scheme maps.

The integral comparison and rationalization dependencies remain in the graph through
other users, stage coherence, and the new calculation. These are direct dependency
simplifications only, not claims that the listed modules are globally unused. No
whole-library module pruning is claimed.

## Where the brief, the DAG or earlier work was wrong

The DAG's first step is already implemented by the newer normalized comparison-data
and stage-coherence declarations. Reconstructing that theory here would duplicate
proved work. The old second step describes geometric right-adjoint transport, but the
statement deliberately permits arbitrary scheme maps and only supplies pointwise
right adjoints. In particular `PbcScalarExtension` has stronger scheme hypotheses,
so its package cannot be applied directly to this statement. The existing declaration
docstring already gives the alternative finite-free trace/restriction argument that
uses only the supplied adjunctions. The new local node records that argument rather
than claiming geometric adjoints exist or preserve constructibility in this generality.

The current queue row says `proof / route`, with one hole. No rework row, current return
entry, or assigned-module build-error file was present in the shared snapshot. No
statement or definition repair and no target change was needed.

Read the current blueprint via `literature/blueprint/latest`: the direct-image and
pullback nodes now live in `sec-proetale-coefficients/sk-prop-sf-open-closed-triangle`.
The item's existing chapter/unit attachment is retained, and no unit route is changed.
Read Bhatt--Scholze 6.7.2, 6.8.14(2), and 6.8.15 in the local PDF. The single-extension
trace argument is explicitly marked as written out by an agent in its proof_origin.
The Mathlib searches found generic sheaf adjunctions and the iterated-mates identity,
but no theorem for this recorded raw rational comparison. Existing normalized scalar
and finite-free declarations were read before making the new statement.

## New nodes

`lem-sf-rational-pullback-scalar-right-mate`, in
`dag/nodes/sec-smooth-purity/`, is attached to
`WeilConjectures.rationalPullbackScalar_rightMate_isIso` in the new module
`Sheaf.Paper.RationalPullbackScalarRightMate`. It isolates the finite coefficient
calculation before any common-stage construction. Its full statement, source,
three-step proof, actual Mathlib search records, blueprint provenance, and exact Lean
signature are recorded. Edge checks include repeated fields (trace pairing has rank
one), ramified extensions (the trace dual basis is used only after rationalization),
empty schemes and zero complexes. No nonempty or positive-dimensional hypothesis
is required. No change record is needed: no existing statement, definition, exported
attribute, instance, or public import changed.

## Related modules compiled before delivery

4 related module(s) compiled against this delivery by deliver3.py: 2 OK, 2 SLOW.

```json
{"capped": false, "direct": 4, "left_out": 0, "own": {"Sheaf.Paper.RationalPullbackScalarRightMate": "91fccd3bfb775acf488823074bf0b9bf6352dbc7", "Sheaf.Paper.SfRationalDirectImageCoefficientCompatibility": "0a4b2a9b1d067286f873348ca5a47a804c6eed83"}, "results": {"Sheaf.Paper.CommonStageFiniteHomLifting": {"hash": "4fefb4a2f2c06ea9d5b15afdd21d4a6b5ea712f0", "status": "SLOW"}, "Sheaf.Paper.CommonStageOpenHeartAdjunction": {"hash": "9c5fc8eee1c11e239dcc5d8b35671125e5703e3e", "status": "SLOW"}, "Sheaf.Paper.GeometricCommonStageDirectImage": {"hash": "a46ce4a21d9734fd72d52a785f9b44ef32b52a0c", "status": "OK"}, "Sheaf.Paper.SfRationalDirectImageAdjunction": {"hash": "f0c4a504a21d004cc05e74b303718d7ee6e719b1", "status": "OK"}}, "seconds": 276, "time": "2026-10-28T12:04:43+0800", "transitive": 0, "version": 1}
```

## Second reading by B6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
