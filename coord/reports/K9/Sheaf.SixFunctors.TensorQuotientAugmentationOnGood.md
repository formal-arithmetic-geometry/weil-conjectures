## What changed

The proof of `WeilConjectures.GeneratorReduction.tensorQuotientTranspose_onGood`
is factored into an ordinary coherent tensor-model calculation and a generic
ordinary-to-derived-limit calculation. The item signature and its public import
are unchanged. All edits are in the item, four new proof modules, and their nodes.

The proved helper `ringedTensorChain_eq_strictAugmentation` identifies the supplied
natural tensor chain with the existing strict augmentation by full-coordinate
uniqueness. The item proves the
generic localized cochain transpose calculation from the adjunction-normalized
reduction model, naturality of the limit unit, and the Roos normalization, and
combines the resulting maps using adjunction-unit naturality and functoriality.

## Proved and sorry left

The original hole is closed, with its signature unchanged:
`WeilConjectures.GeneratorReduction.tensorQuotientTranspose_onGood`.
The general theorem `WeilConjectures.pullbackTensorLimitUnit_roos`
(`lem-coef-limit-unit-roos-normalization`) has a complete proof from the existing
K-injective normalization, naturality and full mapping-cocone calculations.

The additional theorem
`WeilConjectures.GeneratorReduction.ringedTensorChain_eq_strictAugmentation`
(`lem-sf-ringed-tensor-chain-identification`) is fully proved. Its normalization
argument is isolated in its own module after profiling showed substantial
type-checking cost for the conversion between the two total-tensor presentations.

Two new holes remain, each with exactly `:= by sorry`:

- `WeilConjectures.tensorReduction_ordinaryModel`
  (`lem-coef-tensor-reduction-ordinary-model`): construct the strict balanced map
  on the fixed ordinary reduction representatives and identify its localization
  in the whole coherent system category, with its finite chain components.
- `WeilConjectures.tensorReduction_ordinaryTranspose`
  (`lem-coef-tensor-reduction-ordinary-transpose`): an ordinary chain calculation
  for any map with those finite chain components; no good-complex or derived
  hypothesis occurs in this step.

The packet closes one old hole and adds two: this is a decomposition, not a net
hole reduction. There are no holes in the item or the generic Roos module and no
holes inside definitions. All five Lean modules have compiled remotely. The successful item compile took
48.7 seconds with profiling enabled; the final packet removes profiling and its
unused simp argument. The delivery command checks the clean packet again.

## No longer needed

No existing public import or source-library declaration is removed. The original
node's direct use of `lem-coef-sequence-adjunction-cochain-transposes` is replaced
by the more direct defining normalization of `pullbackTensorReductionModel` and
the ordinary-to-derived limit/Roos calculation. Total-tensor goodness uses the
already proved `IntegralAmbient.tensor_good`; a direct import or proof dependency
on `KFlatTotalTensorModel` is unnecessary. The extracted tower-realization
node is now cited directly for the actual model declarations. No entire existing
module is claimed pruned: the original proof-dependency modules were not imported
by the item, and other branches may still need them.

## Where the brief, the DAG or earlier work was wrong

The original plan elides the transfer of the simultaneous balanced tensor map to
the fixed ordinary adjunction-normalized reduction representatives. The new
ordinary-model statement isolates that transfer. A second, separate statement
isolates only the ordinary cochain computation.
Equality of finite derived projections alone cannot replace it. In particular,
this delivery makes no faithfulness assertion about derived evaluations and does
not use the disputed every-presentation normalizations discussed in the S9 and
P4 change records.

## New nodes

`lem-coef-limit-unit-roos-normalization` states the generic compatibility of the
universal ordinary-to-derived limit map with the full, zero-homotopy Roos model.

`lem-coef-tensor-reduction-ordinary-model` states the balanced tensor chain model
on the fixed ordinary quotient representatives, its whole-system derived square,
and its finite chain components. It has no limit or adjunction-transpose clause.

`lem-coef-tensor-reduction-ordinary-transpose` states the ordinary transpose
formula assuming only those finite chain components. It has no derived category,
flatness or good-class hypothesis. Zero complexes, empty sites, arbitrary
unbounded complexes and positive exponent one use the same unit formulas.

`lem-sf-ringed-tensor-chain-identification` identifies the supplied ringed tensor
chain with the strict augmentation by its two canonical coordinates.

No change record is needed: no other existing module or node is edited.

## Second reading by K9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
