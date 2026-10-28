## What changed

Proved `WeilConjectures.coefficientDerivedSystemGammaProjectionTransport_finite` in
`Sheaf.Paper.CoefficientDerivedSystemGammaProjectionTransportFinite`, with its
statement, universes, binders and public import unchanged. Added two proved private
categorical helpers in the same module: `enriched_target_adjunct` transports internal
Hom along an ordinary scalar adjunct, and `adjunct_projection` transports an adjunct
through a natural projection using its unit equation.

The proof uses the already supplied `S.beta_evaluation`, `S.fiber_naturality`,
`S.unit_projection`, `S.counit_projection`, and `S.finite_compatible.naturality`.
At `X = limit N`, fiber naturality is applied to the system counit; beta evaluation
then cancels the internal-Hom reduction identification. The finite scalar
adjunction and counit projection identify the remaining composite with the right
side. The resolution-coherence parameter `D` remains in the unchanged statement;
this identity before sections does not need its fields.

Updated the item's DAG proof and proof dependencies to this calculation. No other
existing module or node changes, no definitions or interfaces change, and no new
public declaration is introduced.

Validation: the final single-file `lcompile.py` run compiled cleanly in 7.2 seconds,
with no warnings. The theorem signature and public imports were compared verbatim
with the original and are unchanged; the delivered Lean contains no `sorry`.

## Proved and sorry left

Closed the one original hole in
`WeilConjectures.coefficientDerivedSystemGammaProjectionTransport_finite`
(node `lem-coef-derived-system-gamma-projection-transport-finite`).
Holes closed: 1. Holes added: 0. Remaining holes in the item: 0.
Both private helpers are completely proved. No split-off statements were added.

## No longer needed

No import was removed or added: the existing public import of
`Sheaf.Paper.CoefficientDerivedSystemEvaluationData` supplies the entire proof API.
The following planned proof dependencies are unnecessary for this item:

- `lem-coef-enriched-sequence-projection-formula`
  (`Sheaf.CategoryTheory.EnrichedSequenceProjectionFormula`): its representative,
  sections and global-limit comparison package is unnecessary for this identity
  from the supplied calculus fields.
- `lem-coef-semilinear-derived-sections`
  (`Sheaf.Paper.SemilinearDerivedSections`): no new construction of the system
  operations is needed; the relevant fiber naturality equation is supplied by `S`.
- `lem-weil-pbc-ringed-topoi-derived-tensor-pullback`
  (`Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`): no new tensor
  pullback comparison is constructed; beta evaluation is already a calculus field.

These are removed from this node's proof dependencies. Their use elsewhere,
including in the construction of the calculus, is unaffected. No module is
withdrawn, and the unit's route is preserved.

## Where the brief, the DAG or earlier work was wrong

The existing proof plan suggests a specialization of the general enriched sequence
projection theorem, but the calculus already includes enough coherence equations
to prove this finite identity directly. No additional split is necessary.
The original docstring's blueprint tag points to the parent
`lem-coef-derived-system-gamma-projection-transport-final`; the item's actual Lean
attachment is correctly recorded on
`lem-coef-derived-system-gamma-projection-transport-finite`.
The current server queue was checked: this is a one-hole stage-3 proof item,
with no rework entry or build-error file.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.CoefficientDerivedSystemGammaProjectionTransportFinite": "65caf28bf93f15a2d5d0d9f80696639b13487900"}, "results": {"Sheaf.Paper.CoefficientDerivedSystemGammaProjectionTransportFinal": {"hash": "c0c2fd46ff7f1417630d40b768fb408452e1a22d", "status": "OK"}}, "seconds": 73, "time": "2026-10-28T10:22:29+0800", "transitive": 0, "version": 1}
```

## Second reading by V1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
