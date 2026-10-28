## What changed

The signature and structure of
`completed_tensor_common_lift_tensor_unit` are unchanged. Its proof now constructs
`tensor` using `NatIso.ofComponents` and constructs `unit` by composing
`coherence.unitIso` with the separately proved ordinary coefficient-unit comparison.
The two added imports in the item are proof imports.

`Sheaf.Paper.AdicCompletedTensorCommonComponent` constructs explicit invertible
components. On integral representatives the composite uses the two specified
`R.integral` maps, the inverse of the finite model's ordinary tensor comparison,
its invertible quotient-completion comparison, and the integral-to-rational tensor
identification. At arbitrary objects it uses the prescribed coefficient compositum
and actual `isoToStage` isomorphisms, the normalized inclusion tensor comparison
`stageTensor`, and the common-stage tensor of the inverse transports. The
definitions contain no unproved data.
The new definitions are irreducible to retain their constructed comparison maps
without repeated elaborator expansion; local transparency annotations keep the
large ordinary realization and rational tensor functors folded during assembly.

`Sheaf.Paper.AdicCompletedTensorOrdinaryUnit` proves
`completedTensorOrdinaryUnit`. Fully faithful coherent reduction identifies the
integral tensor unit with the regular coefficient object. The regular single
complex is K-flat, and the prescribed derived extension counit, the single-complex
comparison, and multiplication-normalized `scalarExtensionUnitIso` identify its
scalar extension with the native regular coefficient. At the least coefficient
field the inverse `R.integral` comparison gives the required common-stage unit.
This part needs no assumption about the finite tensor models.

`Sheaf.Paper.AdicCompletedTensorCommonComponentNaturality` states the remaining
compatibility of these specified maps with morphisms. Its docstring details the
fixed-field naturality, normalized pure-section coefficient-extension square,
localization, and common-field representative argument. Its edge cases include
zero objects, zero arrows, equal coefficient stages, and the empty scheme: none
requires nonzero rank or a nonempty space.

Validation: `lcompile.py --all` compiled all four delivered Lean modules in
import order, without warnings or errors. Each was below the 60-second limit.

## Proved and sorry left

The item's one original hole, in
`WeilConjectures.AdicQbarRealization.completed_tensor_common_lift_tensor_unit`, is
closed by a complete assembly proof. The two explicit component definitions and
`WeilConjectures.AdicQbarRealization.completedTensorOrdinaryUnit` have no holes.

One hole is added:
`WeilConjectures.AdicQbarRealization.completedTensorCommonComponent_naturality`,
node `lem-sf-adic-completed-tensor-common-component-naturality`.
It states equality of the two composites for the already constructed maps; it
asserts neither existence nor invertibility of tensor comparison data and contains
no unit assertion. It is a strict part of the argument, not the original existence
statement under another name. One upper hole is closed and one lower hole is added;
this is a decomposition, with net zero holes closed, not a completed tensor proof.
There are no other `sorry`s in this delivery.

## No longer needed

None. No existing public import is removed, and no existing module or dependency
node is withdrawn. The original finite models, native realization, and closed
coherence definitions are still needed through the component and unit proofs.
No unit route is bypassed. In particular, naturality under coefficient extension
remains explicit work rather than an assertion that follows merely from pointwise
invertibility.

## Where the brief, the DAG or earlier work was wrong

The old second proof step compressed the entire coefficient-extension and
localization naturality argument into "the finite comparisons agree". It did not
name a declaration supplying that square. The new equality isolates precisely
that missing argument after the components have been constructed.

The original reference to "coefficient multiplication gives the unit" also left
unwritten the identification of the reconstructed integral tensor unit with the
regular module. This delivery proves that identification using fully faithful
coherent reduction and the existing regular-coefficient reduction theorem.
No existing statement or definition is changed, weakened, or disputed.

## New nodes

`def-sf-adic-completed-tensor-common-components` records the two explicit
invertible tensor component constructions in
`Sheaf.Paper.AdicCompletedTensorCommonComponent`.

`lem-sf-adic-completed-tensor-ordinary-unit` records the proved ordinary
coefficient-unit comparison in `Sheaf.Paper.AdicCompletedTensorOrdinaryUnit`.

`lem-sf-adic-completed-tensor-common-component-naturality` records the remaining
morphism equality in `Sheaf.Paper.AdicCompletedTensorCommonComponentNaturality`.
The original node's proof and proof dependencies now follow the assembly proof.
No other existing module or node is changed and no change record is needed.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.AdicCompletedTensorCommonComponent": "7dd88f1e04ebef34c4c46d72df61b7ccdec7dbac", "Sheaf.Paper.AdicCompletedTensorCommonComponentNaturality": "a0575e1827719110023afddff9440192094969c8", "Sheaf.Paper.AdicCompletedTensorCommonLiftTensorUnit": "25a7a8461dc37dc61806529e6accea3fd35ab7e9", "Sheaf.Paper.AdicCompletedTensorOrdinaryUnit": "5b5c965cff8a397b4e6c2bfd0fc5bd8d6a965070"}, "results": {}, "time": "2026-10-28T08:09:30+0800", "transitive": 0, "version": 1}
```

## Second reading by Y7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
