## What changed

Proved `WeilConjectures.integralScalarFiniteLevel_bounds` from the actual target
uniformizer power filtration, the existing
`AlgebraicGeometry.Scheme.filteredCoefficientTensor_constructible_bounds`, and
explicit comparison steps. The original theorem signature and its two public
imports are unchanged. Added private proof imports of the two new modules and
`Mathlib.Data.Int.Interval`.

Repair of returned head `08559da5680`: replaced the stale sandbox copy of
`Sheaf.Paper.FilteredCoefficientTensorBounds` with its exact current-main source,
including the complete proof and private helpers landed by J4 in `2eca9c73500`.
The old copy contained the former postponed proof. The current file already
omits both the cyclic `SfCommonStageWeilCohomology` import and the local warning
option responsible for the earlier attribution return. No further edit to that
module is needed. Its exact current source was compiled byte-for-byte, then the unchanged copy
was omitted from the delivery packet so main supplies the dependency. This is
not a withdrawal: there is no `deleted.txt` entry. The obsolete T9 change record
is removed from the packet.
This repair preserves J4's proof instead of replacing it with the old hole.
All four modules compiled with exit code 0 and no diagnostics (reported times
53.9, 45.0, 38.3 and 44.0 seconds). The source import graph has no cycle from the
item; the source hole scanner reports only the named residue-layer theorem.
The original item signature, DAG signature attachments and line widths pass.

`Sheaf.Paper.IntegralScalarResidueLayers` constructs the filtration as power
ideals of the uniformizer image in the lifted finite target ring. Antitonicity,
the first term and the last term are proved. Its remaining statement concerns
only successive quotient layer tensors, before the filtration induction.

`Sheaf.Paper.IntegralScalarRegularTensorComparison` proves the regular tensor
complex comparison without residue, flatness or support hypotheses, then
transports constructibility and vanishing across homology localization.
The main proof applies finite coefficient devissage using `P.property.2`.
Vanishing outside the original interval gives the requested support bound;
containment in the finite integer interval proves finite support.

## Proved and sorry left

The original module has one hole. Closed
`WeilConjectures.integralScalarFiniteLevel_bounds`
(node `lem-sf-integral-scalar-finite-level-bounds`).

Proved `WeilConjectures.integralScalarPowerFiltration_antitone`,
`WeilConjectures.integralScalarPowerFiltration_zero`, and
`WeilConjectures.integralScalarPowerFiltration_last`. The definition
`WeilConjectures.integralScalarPowerFiltration` is an actual construction.
Also proved `WeilConjectures.integralScalarRegularTensorIso` and
`WeilConjectures.integralScalarRegularTensorComparison`
(node `lem-sf-integral-scalar-regular-tensor-comparison`).

One new hole remains: `WeilConjectures.integralScalarResidueLayers_bounds`
(node `lem-sf-integral-scalar-residue-layers`). Its complete proof in words is in
its docstring and node. It is the residue-extension and successive-layer part of
the argument, strictly before the finite filtration induction, regular tensor
comparison and finite-support conclusion. This is a decomposition: one original
hole closed and one lower hole added. No other delivered declaration has a hole.
The generic filtered-tensor theorem is now proved by J4; that proof is preserved
and is not counted as work of this delivery.

## No longer needed

No existing public import or declaration is removed and no module is withdrawn.
The proposed edits to `Sheaf.Paper.FilteredCoefficientTensorBounds` are no longer
needed: J4's current source already removes the cyclic private import and the
warning option. This delivery carries no change to that module and claims no
module pruning for those removals.

Removed the unused proof import
`Sheaf.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctoriality` from the new
comparison module. The old direct proof edge `lem-pur-kflat-change-of-rings`
(`Sheaf.Algebra.Homology.ChangeOfRingsKFlat`) is unnecessary for the main
argument: it tensors the already flat source terms with a coefficient filtration.
The finite-field, DVR, derived-reduction and constructibility dependencies remain
necessary in the residue-layer subargument and move there in the DAG; they are
not claimed pruned from the target closure.

## Where the brief, the DAG or earlier work was wrong

The stated filtered tensor theorem needs bounds for each specific quotient layer,
whereas the original hypothesis bounds only source residue reduction. It also
uses finite constant models rather than geometric stalks. The comparison modules
expose those steps, and the filtration and its boundary laws are proved here.

Bhatt--Scholze Proposition 3.5.1 concerns derived completion and inverse limits;
it does not itself state finite residue extension preserves constructibility.
The subargument is the finite-filtration application in the parent node. The
relevant local-model and Serre facts are Stacks sites-modules
`lemma-tensor-product-locally-constant` and proetale `lemma-constructible-serre`.
The latest blueprint scalar extension proof supplies the balanced associator
and unit argument. The unit record has no realized steps changed.

Blueprint searches for `uniformizer filtration` and `regular coefficient tensor`
returned no existing blueprint nodes. The ancestry script cannot follow the
parent's module-name `created.item`; the new records preserve its recorded
ancestor `def-weil-rationalization-karoubi`, through the parent and scalar
constructibility node. Edge cases checked include n=0, the last layer, zero
complexes, empty strata and empty schemes. No completeness is assumed.

The last return identifies a concurrent dependency proof, not an error in the
item's argument. The stale generic-module copy is now replaced by the exact
current source. No existing dependency definition, statement, public import or proof is
changed by this repaired delivery. The assigned item retains its new proof.

## New nodes

`lem-sf-integral-scalar-residue-layers` records the power filtration and its layer
tensor bound, with only the residue-extension comparison postponed. Its module
is `Sheaf.Paper.IntegralScalarResidueLayers`.

`lem-sf-integral-scalar-regular-tensor-comparison` records the unconditional
regular tensor complex isomorphism and proved homology/constructibility transport.
Its module is `Sheaf.Paper.IntegralScalarRegularTensorComparison`.

No change record is needed: the prior proposed dependency changes are already
in main, and the dependency is preserved verbatim.

## Second reading by T9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
