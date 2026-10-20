## What changed

Retired `Sheaf.AlgebraicGeometry.CommonFieldFibreComparison` via `deleted.txt` and redirected
`lem-sbc-common-field-fibre-comparison` to the proved declaration
`AlgebraicGeometry.exists_common_field_fibre_comparison` in
`WeilConjectures.AlgebraicGeometry.CommonFieldFibreComparison`.

The upstream theorem has precisely the same hypotheses and additionally returns the map
`k : Spec E ⟶ Spec K`, its compatibility equation `heq`, and its surjectivity. The old
conclusion follows by choosing the canonical composite
`(commonFieldFibreIso f g t s z k y heq).hom ≫
pullback.fst (pullback.snd (f.fiberToSpecResidueField s) y) k` as `p` and using its supplied
surjectivity. No restriction on the schemes, the characteristic, or finite type is introduced.
This remains valid when the family has empty fibres: the theorem imposes no nonemptiness
hypothesis on `X`.

Validation through `lcompile.py`:

- A scratch theorem with the exact old signature is proved from the upstream theorem by
  unpacking its witnesses and taking the composite above. It compiles cleanly.
- `#print axioms` for that implication and for the upstream theorem, `commonFieldFibreIso`,
  and `commonFieldFibreIso_hom_snd` lists only `propext`, `Classical.choice`, and `Quot.sound`.
- An unchanged sandbox copy of the current upstream consumer
  `WeilConjectures.AlgebraicGeometry.GeometricGenericCoverSpread` compiles cleanly in 1.9 s.
- `tools/downstream.py` reports zero direct or transitive consumers of the retired module;
  a source search confirms there are no remaining imports to adapt.

The scratch checks are under `scratchpad/` and are not delivery modules. No upstream file
is changed. The node's statement and proof plan are unchanged; its Lean attachment now
records the stronger upstream signature and explains how it implies the node's statement.

Change record: `coord/changes/retire-common-field-fibre-comparison-W2.md`.

## Proved and sorry left

The item has **zero holes before and zero after**. Its only theorem,
`AlgebraicGeometry.exists_common_field_fibre_comparison`
(node `lem-sbc-common-field-fibre-comparison`), was already completely proved in both trees.
Holes closed: 0. Holes added: 0. Holes remaining: 0. No statements are split off.
This delivery completes a retirement item, not a new mathematical proof.

## No longer needed

Pruned module: `Sheaf.AlgebraicGeometry.CommonFieldFibreComparison`, including its duplicate
comparison theorem and its `public import Mathlib.AlgebraicGeometry.Fiber` line. Mathlib's
fibre API remains used by the upstream module. No dependency nodes become unnecessary;
`lem-sbc-common-field-fibre-comparison` stays attached to the upstream theorem. There were
no Sheaf proof imports in the retired module.

The queue's recorded consumer `Sheaf.AlgebraicGeometry.GeometricGenericCoverSpread` is
already absent from the current tree. Its upstream replacement already imports
`WeilConjectures.AlgebraicGeometry.CommonFieldFibreComparison` and unpacks the stronger
witnesses. No consumer adaptation is necessary in this packet.

## Where the brief, the DAG or earlier work was wrong

The generic proof brief describes an item with holes, but the queue marks this item
`retire`, and the human's 2026-10-20 instruction in
`coord/changes/retire-sheaf-twins-20261020.md` requires withdrawing the duplicate. The
recorded consumer list is stale: the listed Sheaf consumer has already been retired.
The old DAG attachment still named the unused Sheaf copy and had the weaker signature;
this packet repairs that attachment without changing the node's mathematical statement.

The required searches were run through `msearch.py`: LeanFinder for common field fibre
comparisons returned scheme fibre APIs and `Scheme.Pullback.exists_preimage_pullback`;
Loogle for `CategoryTheory.Limits.pullbackLeftPullbackSndIso` returned the pullback-pasting
API; grep for `exists_preimage_pullback|pullbackLeftPullbackSndIso` found the corresponding
Mathlib uses. Direct searches of both library roots found the stronger upstream theorem,
which supplies the shortest route and makes the duplicate unnecessary.

## Second reading by W2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
