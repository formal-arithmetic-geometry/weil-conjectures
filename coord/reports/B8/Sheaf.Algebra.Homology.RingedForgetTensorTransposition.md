## What changed

Reduced `CategoryTheory.RingedForgetTensorTransposition.ringed_forget_tensor_transposition`
with its original signature to tensor descent and normalized uncurrying. The item proves
evaluation preservation by applying uncurrying to the identity; proves double-dual
naturality on both categories using evaluation and braiding naturality; and proves
preservation of the actual double-dual arrow by uncurrying, symmetry, and cancellation
of the tensor and Hom comparison inverses. It then assembles the original `Comparison`
and its uniqueness proof.

The ten existing data declarations are moved verbatim, with their original universe
and variable context, to `RingedForgetTensorTranspositionData` and publicly reexported
from the original module. `TensorComparison` packages only the tensor portion.
The original four public imports stay. The two new theorem modules are proof imports.
The source library is untouched. Change record:
`coord/changes/B8-ringed-forget-transposition-data.md`.

Validation: all four delivery modules compile through `lcompile.py` without warnings.
The unchanged direct importer `Sheaf.Paper.NativeWeilTensorTransport` also compiles
against the delivery and its verification copy has been removed. The original theorem
signature and all ten relocated declaration texts were compared with the source;
both checks are exact. The new dependency closure has no missing node or cycle.

## Proved and sorry left

This is a decomposition, not a sorry-free proof of the full mathematical result.
One original hole is closed, by declaration name:
`CategoryTheory.RingedForgetTensorTransposition.ringed_forget_tensor_transposition`
(node `lem-sf-ringed-forget-tensor-transposition`). Its proof contains no sorry.
The generic categorical calculations are complete private Lean proofs.

Two holes are added, both the entire proof of a named public theorem in its own module:

- `CategoryTheory.RingedForgetTensorTransposition.ringed_forget_tensor_descent`
  (`lem-sf-ringed-forget-tensor-descent`): construction and coherent unique extension
  of the tensor comparison, without any Hom, transpose or delta conclusion.
- `CategoryTheory.RingedForgetTensorTransposition.ringed_forget_normalized_uncurry`
  (`lem-sf-ringed-forget-normalized-uncurry`): the normalized uncurry equation for a
  supplied tensor comparison and the fixed two-injective Hom comparison.

Each split has its source and complete proof in words in both its docstring and node.
No definition contains a hole and no arbitrary witness is selected in a definition.

## No longer needed

No mathematical dependency or module is pruned from the full argument. The original
six direct proof imports are removed from the item because their work belongs to the
split lemmas: `SiteDerivedTensorDescentIndependentCoefficients`, `KFlatTotalTensorModel`,
`KFlatResolutionIndependentCoefficients`, `RingedSiteKInjectiveResolutionsOfUniverses`,
`KInjectiveHomComplexOfUniverses`, and Mathlib `DerivedCategory.KInjective`.
The two split proof plans still name the descent, tensor closure, K-flat resolution,
K-injective Hom and localization tools. Their modules need no extra proof imports until
those proofs are implemented; all signature imports have been retained. Resolutions
already occur in the public dependencies of the supplied representative data.

The item's direct `tool_uses` entries for `lem-weil-pbc-site-derived-tensor-descent`,
`lem-pc-kflat-resolution`, and `lem-pur-kflat-total-tensor-model` are removed: those
lemmas occur in the split proof plans instead. They are still needed transitively.
Neither split bypasses any unit statement or unit proof step.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement was changed. The node's ten-step plan comprises two
substantial representative constructions followed by a formal closed-category
calculation. The delivery isolates exactly these constructions and completes the
calculation. The current rework row was read before copying; the existing module
and its attachment are preserved, not withdrawn. The unchanged original module
successfully compiled with the server's private overlay for its restored dependency.

Edge checks: the identity functor with identity comparisons gives both split formulas;
zero objects give the zero evaluation formulas; odd-degree swaps retain the Koszul
sign through the supplied symmetry coherence; no step assumes delta is invertible.
The formal calculation is generic in two independent category universes.

## New nodes

`def-sf-ringed-forget-tensor-transposition-data` records the relocated comparison data,
with the same existing names and exact definitions. It introduces no new tensor or
Hom object. Searches found generic tensor-Hom data but no competing project notion.

`lem-sf-ringed-forget-tensor-descent` is original steps 1–4: total-complex comparison,
unique tensor descent, structural coherence, and the degree-zero unit normalization.
It states no derived Hom, evaluation, transposition or delta conclusion.

`lem-sf-ringed-forget-normalized-uncurry` is original steps 5–8 up to the normalized
uncurry formula: K-flat source models, K-injective Hom lifts, evaluation on projections
and summands, target augmentation comparison, and independence of choices.
It requires a supplied tensor comparison and the original flat-model preservation
hypothesis, ensuring that the tensor representative square applies to UP and US.
It supplies just one adjunction equation.

All three nodes inherit the owning chapter and unit and the original node's null
blueprint ancestor. Sources are the current blueprint internal-Hom/transposition
paragraph and the Stacks derived tensor and Hom-complex constructions. Searches were
actually run through msearch (LeanSearch, Loogle, LeanFinder and grep); the generic
adjunction-naturality hits are used for the complete formal calculation.

## Second reading by B8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
