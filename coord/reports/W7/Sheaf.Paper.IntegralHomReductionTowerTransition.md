## What changed

Replaced the hole in `Sheaf.Paper.IntegralHomReductionTowerTransition` by a
complete assembly proof, with its original declaration and statement unchanged.
The proof chooses common coefficient tensor models, composes a natural signed
Hom--tensor map, applies the existing two-term free component criterion,
localizes, inverts and conjugates by the two model isomorphisms. The transition
square is then a naturality equation.

Added `Sheaf.Paper.SignedHomTensorComparisonConstruction`, with a proved generic
braided naturality theorem and private constructions, and
`Sheaf.Paper.SignedHomTensorComparison`, with the signed natural comparison.
The comparison is constructed by currying evaluation after associating,
braiding and reassociating. Its sign is checked on the actual sheafified tensor
generators using the existing normalized evaluation and complex constraints.
Private typed wrappers avoid repeatedly unfolding the total tensor construction.

Added `Sheaf.Paper.IntegralHomReductionTowerTensorModels` for the remaining
representation step. It identifies the two towers separately; it neither
compares their Hom--tensor expressions nor asserts comparison invertibility.
The three new nodes and the item's revised proof dependencies follow this route.
No existing declaration outside the item, target, definition or unit route changes.

Validation: `lcompile.py --all` compiles all four files in import order.
The last uncached timings were 4.3 s for the tensor-model statement, 37.1 s for
the comparison construction, 37.6 s for its signed section formula and 5.0 s for
the item. The four Lean declarations match their node attachments, and the
original item signature is unchanged. There is exactly one `sorry` in the
changed/new Lean files.

## Proved and sorry left

The original hole in
`WeilConjectures.IntegralHom.reductionTower_components_transition`
(node `lem-sf-integral-hom-tower-components-transition`) is replaced by a complete
Lean proof from the stated dependencies.

Also proved, with no holes in their modules:

- `WeilConjectures.IntegralHom.braidedTensorExchange_naturality`
  (`lem-sf-braided-hom-tensor-exchange-naturality`).
- `WeilConjectures.IntegralHom.signedHomTensorComparison_exists`
  (`lem-sf-signed-hom-tensor-comparison`).

One new hole remains:
`WeilConjectures.IntegralHom.reductionTower_tensor_models`
(`lem-sf-integral-hom-tower-tensor-models`). Its entire proof is `by sorry`;
its docstring and node give the quotient Koszul tower, K-flat/K-injective
representatives and compatible scalar-extension comparisons needed to prove it.

Thus one original hole is closed and one lower hole is added: this is a
strict decomposition with net zero holes closed in these files, not a claim that the whole
mathematical obligation is finished. The signed comparison and finite-free
invertibility assembly are real intervening proofs, not a renaming of the item.
The already stated imported component criterion
`WeilConjectures.IntegralHom.twoTermFreeHomTensor_component_isIso`
(`lem-sf-two-term-free-hom-tensor-components`) is used unchanged; its existing
hole is not added by this delivery.

## No longer needed

No original import is removed, and no existing module is withdrawn.
The new proof does not use either of these original direct proof dependencies:

- `lem-sf-integral-hom-models-exist`, module
  `Sheaf.Paper.IntegralHomModelsExist`, declaration `models_exist`.
- `lem-sf-integral-hom-comparison-is-iso`, module
  `Sheaf.Paper.IntegralHomComparisonIsIso`, declaration `comparison_isIso`.

Separate finite-level existence and invertibility do not supply naturality
across n. The replacement uses a natural transformation before localization
and the two-term free component criterion directly. Resolution independence
remains needed by the tensor-model statement. Other parents may still need the
two old modules, so this delivery does not withdraw them or claim that they are
absent from the targets' entire import closure.

## Where the brief, the DAG or earlier work was wrong

The old dependency list supplied finite-level models and isomorphisms but no
statement ensuring that their chosen comparisons commute with quotient
transitions. The revised route isolates the missing representation step and
uses naturality before inverting the comparison. The old node's source pointer
names paragraph 3 of an older blueprint; the current blueprint's first paragraph
contains the finite-free quotient construction used here. The node's original
statement and attachment are preserved, and its proof origin points to that
current source.

Separately, `reductionTower_components_augmentation` in
`Sheaf.Paper.IntegralHomReductionTowerAugmentation` is STATEMENT-DISPUTED:
it assumes only a family of isomorphisms commuting with transitions and
concludes that this arbitrary family respects a fixed augmentation. Negating
a compatible family preserves its transition equations and changes its
augmentation when that augmentation is nonzero and 2 is invertible (for example
l=3 and the nonzero coefficient unit). Augmentation compatibility requires a
normalization hypothesis. This unrelated module is neither imported nor changed
here; the issue is reported for its owner.

## New nodes

`lem-sf-integral-hom-tower-tensor-models` records common two-term coefficient
models and two separate natural model isomorphisms. Its proof is the quotient
Koszul tower, K-flat/K-injective representatives and resolution-independent
scalar extension. It does not compare the two Hom--tensor expressions. This is
the only new node with a hole.

`lem-sf-signed-hom-tensor-comparison` records the proved generic signed map,
natural in every coefficient complex. It uses evaluation, braiding,
associators and currying. It has no reduction tower or invertibility assertion.

`lem-sf-braided-hom-tensor-exchange-naturality` records the proved categorical
naturality identity used by the construction. Its module also holds the private
construction and instance caches, separating that calculation from the section
calculation to keep individual compiles within the prescribed limit. All three
nodes record actual Mathlib searches, their source and complete proofs in words.
No change records are needed: only the item and new modules/nodes are changed.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.IntegralHomReductionTowerTensorModels": "68fb48cf37dc8c6481fcad7fa9f0a237c50aa1db", "Sheaf.Paper.IntegralHomReductionTowerTransition": "e78be063cd943a7cb4f81fcc2f8506a60ce1c9fe", "Sheaf.Paper.SignedHomTensorComparison": "fee569892066482bd8e8654c667f8cf0eaef8ac0", "Sheaf.Paper.SignedHomTensorComparisonConstruction": "a25eb564c112226233740dea6c8c189d0ff8ab14"}, "results": {}, "time": "2026-10-28T08:54:42+0800", "transitive": 0, "version": 1}
```

## Second reading by W7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
