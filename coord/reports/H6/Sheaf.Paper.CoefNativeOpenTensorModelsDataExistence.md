## What changed

Replaced the sole hole in `nativeOpenTensorModels_data_exists` by a uniform assembly
of the native system model and all finite models. The target statement is unchanged.
No other existing Lean module or another module's DAG node is changed.

The private proved helper `model_of_cochains` applies the existing
`IndependentTensorModel.modelOfOrdinary` to ordinary restriction tensor data. This
constructs the derived restriction comparison and its full representative model,
with its ordinary comparison identified with the supplied one. It applies the existing
`ringedTensorComparison_extension` separately on the ambient and open sites, obtaining
the one-K-flat comparisons, agreement with the given simultaneous tensor models, and
naturality. It then applies projection descent and assembles every field of
`OpenTensorModel`. The ordinary-comparison equality proves the pure-section and
ordinary inverse-unit fields. The item specializes this proof to the exact instances
used by `SystemOpenModel` and `FiniteOpenModel` and uses choice only inside the
existential theorem to assemble the finite family.

Added ordinary/cochain data `OpenTensorCochainData`, with no derived tensor choices,
and two strictly smaller outstanding constructions: native ordinary/cochain geometry,
and generic projection descent from supplied ordinary/cochain data. The latter
constructs only gamma and its two equations; the restriction representative and
one-K-flat tensor comparisons are inputs already constructed in the assembly.
Neither new theorem states existence of `OpenTensorModel`, and neither is the item
with its hypotheses renamed. No definition chooses data from an unproved existence
theorem. All data definitions are structures or explicit native specializations.

All four modules compiled through the server: ordinary data 3.0 s, native cochains
47.3 s, generic descent 13.7 s, and the item 51.5 s. A line-length warning was fixed;
the item scopes the unused-variable linter suppression to the original theorem
because its unchanged existential binder names O and On do not occur in True.
The delivery checks validate the resulting final files.

The item uses private proof imports for the two new constructions and the two
existing tensor construction lemmas. Its original public import is preserved.
New code respects transparency; the item now enables the two transparency-respecting
elaboration options instead of inheriting its previous `false` settings.

## Proved and sorry left

Closed the original textual hole:
`WeilConjectures.CoefSupportOpenTensor.nativeOpenTensorModels_data_exists`
(node `lem-coef-native-open-tensor-models-data-existence`). Its proof and the private
assembly helper have no holes. The item has zero remaining textual `sorry`s.

Added exactly two holes, each the entire body of a named public theorem in its own
module, with a source and proof in words:

- `WeilConjectures.CoefSupportOpenTensor.nativeOpenTensor_cochains_exists`,
  `Sheaf.Paper.CoefNativeOpenTensorCochains`,
  node `lem-coef-native-open-tensor-cochains`.
- `WeilConjectures.CoefSupportOpenTensor.openTensorProjection_descent`,
  `Sheaf.SixFunctors.OpenTensorProjectionDescent`,
  node `lem-sf-open-tensor-projection-descent`.

This is a decomposition: one hole closed, two holes added, not a sorry-free proof
of the mathematical existence assertion. The construction of the restriction model
and the extension to one-K-flat comparisons are proved from existing declarations.
The new ordinary/cochain definition module has zero holes.

## No longer needed

No existing import was removed and no module is withdrawn or claimed pruned.
The item no longer directly applies `lem-sf-open-tensor-normalization` or
`lem-sf-ringed-open-total-tensor-kflat`: their interfaces concern localized-site
operations, while this theorem fixes native operations and arbitrary supplied closed
tensor models. They remain construction dependencies of
`lem-coef-native-open-tensor-cochains`, so they are not pruned from the overall argument.
The item's proof dependencies now name its actual assembly and the two new steps.
No unit statement or unit proof step is bypassed; its unit has empty `realized` lists.

## Where the brief, the DAG or earlier work was wrong

The original two-step plan does not directly typecheck by applying its two named
lemmas. Native open functors, the section-unit formulas, and the arbitrary supplied
tensor models must be identified with the localized-site construction. The new
ordinary/cochain construction isolates the former identification; existing normalized
tensor descent and one-flat comparison extension supply the latter derived models.
Stacks 0GL1 explicitly omits the total-complex details. The new nodes mark their
expanded proofs as agent-written and cite 0E8I, 07A4, 0G7E and the signed total.

The actual Mathlib searches are logged in `searches.jsonl`: LeanFinder returned
scheme-open-immersion facts, Loogle returned general adjunction Hom-equivalence
lemmas, grep found no native model theorem, and LeanSearch returned derived-unit,
sheafification and total-summand facts. Project searches located and reused
`ExactTensorModelConstructionIndependent` and `RingedTensorComparisonExtension`.
The blueprint search returned the finite projection formula and pro-etale projection
formula, not either of the new intermediate statements. The current integral
coefficient dualizing proof was read at `literature/blueprint/latest/`.

The edge cases of the two new assertions were checked in words: the empty open and
zero sheaves give zero projections; zero coefficient rings cause no division; n=0
is the first positive coefficient quotient; arbitrary complexes use direct sums
with two outgoing differential terms per source summand; nonflat horizontal quotient
maps are retained on the whole sequence site, without asserting that evaluation
of an injective is injective or that equality can be detected levelwise.

## New nodes

`def-sf-open-tensor-cochain-data` records the ordinary restriction tensor, its
pure-section normalization and representative preservation, the ordinary projection
with its inverse-unit equation, and its natural signed total. The definition contains
no existence choice and no holes. It fixes the complete lower construction problem.

`lem-coef-native-open-tensor-cochains` supplies that ordinary/cochain data for the
fixed native system functors and every finite stage. It has no derived calculus or
derived tensor argument and no derived model in its conclusion. Its proof explains
localized-site transport, restriction tensor, the unit transpose and totalization.

`lem-sf-open-tensor-projection-descent` is a generic descent step for an already
supplied ordinary/cochain projection, restriction representative and two compatible
one-flat tensor comparisons. It produces the derived projection, its inverse-unit
normalization, and its value on an arbitrary first complex and a flat-term K-flat
second complex. The proof explains descent on resolving pairs, extension in the
first variable, and localization of the chain adjunct equation.

## Second reading by H6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
