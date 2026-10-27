## What changed

Proved `AlgebraicGeometry.ProEtale.SpTowerClasses.restrictedScalarAdjunction_exists`
without changing its statement. The proof constructs the normalized direct-image
comparison level by level, proves horizontal compatibility by finite transposition
of the system counit and the normalized unit-transition equation, and assembles the
natural isomorphism of whole towers. It then composes the scalar, integral-forgetful
and abelian adjunction Hom equivalences, proves their two naturality equations, and
constructs the requested adjunction with its exact normalization.

Private proof imports reuse the existing Forget evaluation, integral full-faithfulness,
finite adjoint evaluation and unit-transition proofs. All new helpers are private and
fully proved. The item's DAG proof and dependencies follow these constructions.

## Proved and sorry left

Closed the original one hole in
`AlgebraicGeometry.ProEtale.SpTowerClasses.restrictedScalarAdjunction_exists`
(node `lem-sp-tower-restricted-scalar-adjunction`). No holes added, no split-off
statements, and no `sorry` remains in the delivered Lean file.

Validation: the complete module compiles cleanly in 42.5 seconds through
`lcompile.py`. A separate importing probe's `#print axioms` reports exactly
`propext`, `Classical.choice` and `Quot.sound` for the proved theorem. The probe
was removed before delivery.

## No longer needed

None. The proof follows all three steps of the original plan. No original import,
node or module is withdrawn. The integral coefficient pullback existence module's
already proved private lifting API supplies full faithfulness directly.

## Where the brief, the DAG or earlier work was wrong

The original proof plan is valid. Horizontal compatibility of push-evaluation
requires the normalized unit-transition equation in addition to levelwise section
identities; the proof makes this step explicit via the system counit and the proved
finite adjoint evaluation theorem. The recorded Forget functors need not be
judgmentally equal to the canonical forgetful functor, so the proof uses their
evaluation isomorphisms and section/morphism equations throughout.

The integral full-faithfulness helpers were present in current source but absent
from the initially published build; verification waited for published artifacts
rather than duplicating those declarations. Empty charts and zero modules require
no additional hypotheses; the proof uses morphism naturality and the existing
constant-residue-ring linearity result.

To avoid expensive kernel conversions between a scalar-restricted transition
section and a native evaluation section, the internal horizontal lemma uses native
section variables with the interface's heterogeneous equalities. This is only a
private proof API: no public definition, signature, instance or attribute changes.

The additive horizontal maps use the existing underlying presheaf's maps. Their
explicit source and target groups avoid unfolding the concrete coefficient maps
when the kernel checks composition. Isomorphism cancellation uses the given
isomorphism directly, avoiding an unnecessary monomorphism instance search.

## Related modules compiled before delivery

2 related module(s) compiled against this delivery by deliver3.py: 2 OK.

```json
{"capped": false, "direct": 2, "left_out": 0, "own": {"Sheaf.Paper.TowerRestrictedScalarAdjunction": "64a28abb14d1843eab49d17dee2d137af703bf96"}, "results": {"Sheaf.Paper.TowerScalarRootAbelianTranspose": {"hash": "39715a9399f9b458307ba4e3429761c9ce7bf5ad", "status": "OK"}, "Sheaf.Paper.TowerScalarUnitAbelianTranspose": {"hash": "7197dfee19bd058a4a0ce77e680028f70fa6645c", "status": "OK"}}, "seconds": 21, "time": "2026-10-28T04:06:26+0800", "transitive": 0, "version": 1}
```

## Second reading by J6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
