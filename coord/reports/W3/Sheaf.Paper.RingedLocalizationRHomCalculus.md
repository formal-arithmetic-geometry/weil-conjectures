## What changed

Repair of returned head `7406ac83ac`: removed all four duplicate private theorems
from `SliceTensorNatural`. Their original declarations in the unclaimed
`OpenRestrictionTensorNatural` are now public, with unchanged binders, conclusions
and proof bodies. A proof-only import reuses those exact declarations. The new
change record `coord/changes/W3-shared-tensor-naturality-helpers.md` records this
visibility change and its consumers. The slice-tensor node now records the reuse.

Reduced `CategoryTheory.ringedLocalizationRHom_calculus` to preservation of the
constructed, evaluation-normalized currying comparison under further slice restriction.
Its original signature is unchanged. The proof constructs currying and its simultaneous
naturality, constructs the localization coefficient and tensor-complex transports, and
specializes the remaining general coherence assertion to the proved K-flat models.

The existing model definitions and the two already proved localization-model theorems
move unchanged to `Sheaf.Paper.RingedLocalizationModels`, publicly reexported by the
original module. This prevents an import cycle between the main theorem and its
supporting constructions. The extracted coefficient K-flat subproof is now available
as `localizationSliceCoefficient_kflat`.

`KFlatRHomCurrying` constructs a canonical natural currying isomorphism on K-flat
representatives from the actual degreewise evaluation map, functorial K-injective
resolutions and derived localization. `RingedModelCurrying` transports it through exact
slice restriction and the single-total-tensor comparison. `RingedLocalizationCurrying`
uses the shared natural comparison to prove the required naturality for bounded
localization complexes. Its component formula is definitional, so it does not expand
the full derived comparison term again.

`SliceModuleSheafification` proves that continuous cocontinuous module restriction
commutes with sheafification. `SliceTensorNatural` constructs the tensor comparison
and proves its two-variable naturality. `RingedModelRestriction` constructs the induced
coefficient and ordinary tensor-complex comparisons on derived categories.
`RingedLocalizationRestriction` constructs the further-slice localization coefficient
isomorphism from the identity on fraction presheaves and the sheafification comparison.
All these constructions have actual data and proved structure fields.

The unit route is unchanged. The parent node records the implemented route through
these constructions. The public model definitions are textually identical, so all
original consumer statements retain their meaning and signatures.

## Proved and sorry left

Original holes: one, `CategoryTheory.ringedLocalizationRHom_calculus`.
Its proof body is now complete from the named general coherence theorem.
Added holes: one, `CategoryTheory.LocalizationRHom.modelCurrying_restriction`, in
`Sheaf.Paper.RingedModelCurryingCoherence`, node
`lem-weil-pbc-ringed-model-currying-coherence`.
This is a decomposition: one upper hole closed, one strictly partial coherence
obligation added, net zero holes, zero original holes completely discharged.
There are no other new holes and no holes in definitions.

The remaining theorem supplies restriction isomorphisms compatible with the fixed
currying maps for arbitrary K-flat sheaf coefficients and locally K-flat complexes.
It supplies neither currying, its naturality, nor coefficient or tensor comparisons;
those are constructed and proved in this delivery. Its proof docstring specifies the
product-projection chain comparisons, their derived descent, and the local evaluation
square still needed. Zero sheaves, zero complexes, zero rings and empty sites obey
the same constructions; no boundedness of the derived target is introduced.

New proved declarations include `CategoryTheory.KFlatRHom.chainIso_natural`,
`SheafOfModules.sliceSheafificationComparison_isIso`,
`SheafOfModules.sliceTensorIso_natural`,
`CategoryTheory.localizationSliceCoefficient_kflat`,
`CategoryTheory.LocalizationRHom.modelCurryIso_natural`,
`CategoryTheory.LocalizationRHom.curryIso_natural` and
`CategoryTheory.LocalizationRHom.curryIso_eq_model`.
The old `ringedLocalization_kflat_models` and `ringedLocalization_tensor_product`
were already proved; moving them is not counted as closing holes.

Repair validation: both relevant `import_prune_check.py` checks pass. All eleven
delivery modules compile without warnings against the shared helpers, including
`OpenRestrictionTensorNatural` (12.6 seconds), `SliceTensorNatural` (22.5 seconds),
`RingedModelCurrying` (36.2 seconds), and the main theorem (5.1 seconds).
The three unchanged direct consumers `OpenRestrictionKFlat`,
`OpenRestrictionTensorHomology` and `OpenScalarRestrictionStalkCriterion` also
compile against the changed helper module (29.7, 22.8 and 25.3 seconds respectively).
Their temporary source copies are removed from the delivery.
The retained decomposition has one remaining named hole; this repair introduces
zero additional holes. The older validation below records the retained proof work.

Validation: the main proof assembly and all its supporting modules compile
through `lcompile.py`. The unchanged original consumers
`Sheaf.CategoryTheory.RingedKoszulCompletionReflector` and
`Sheaf.Paper.ExtendedCechCompletionModel` also compile against the extracted interface.
Four further original consumer checks currently stop at shared-cache imports:
`RingedSiteCompleteElementMul` needs `RingedSiteLocalizationFractionComparison`,
`RingedSiteCompleteElementsIdeal` needs `RingedSiteCompleteElementMul`,
`FlatRingedIdealCompleteEquivalence` needs `FlatRingedCechBaseChange`, and
`RestrictionLocalCompleteness` needs `LocalCompleteTestComparison`.
These errors occur before elaborating consumer declarations; no consumer is adapted.
A clean all-files pass checked the shared model comparison in 35.8 seconds, its
localization specialization in 3.2 seconds, and the main theorem in 4.7 seconds,
without warnings. A repeat all-files check accepted all ten unchanged sources from
the compiler cache. The four missing-import consumer checks were repeated with the
same results. `deliver3.py --no-push` reports OK: compilation and preflight passed. The review
class is CODEX because this delivery adds nodes and support modules and extracts
the publicly reexported model interface. No second group reader was invoked.

## No longer needed

The four local copies `SheafOfModules.compose_four_squares`, `inverse_square`,
`tensorObjIsoSheafification_natural` and `tensor_square` in `SliceTensorNatural`
are removed. The original generic proofs in `OpenRestrictionTensorNatural` are
reused. Its proof-only import replaces the direct proof-only
`WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed` import.
No node or module becomes unreachable from this deduplication.

No existing module is withdrawn or made globally unreachable. The generic existential
`ringedInternalHom_tensor_adjunction` is not used to choose currying; its arbitrary
witness would not fix evaluation normalization. The existential
`ringedInternalHom_restriction` also supplies no evaluation square and is not applied.
Their containing module remains needed
for the existing exact-restriction interface and instances. The canonical degreewise
currying construction and its differential and naturality lemmas are used instead.

The original proof dependencies remain needed through the proved model constructions
or the remaining coherence argument. The parent's direct proof-dependency list is
replaced with the new construction nodes, whose dependencies record the retained
underlying arguments. No blueprint unit or unit proof step is bypassed.

Unused experimental constructions, including a duplicate specialized derived
coefficient comparison and a localization-map helper, are omitted. They introduce no
DAG nodes or delivered imports. Proof-only Hom-tensor naturality is imported without
`public` in the new K-flat currying module.

## Where the brief, the DAG or earlier work was wrong

The returned delivery copied four private generic helpers from
`OpenRestrictionTensorNatural`. Being private did not make duplicate proofs
acceptable. They now have one implementation, in their original module;
`SliceTensorNatural` imports and applies them.

The existing `ringedInternalHom_restriction` declaration gives existential restriction
isomorphisms and their successive-composition equation. It states no compatibility
with evaluation or a separately constructed currying map. Choosing its witnesses
independently does not establish the required square: rescaling the restriction maps
illustrates the missing normalization. The remaining named obligation isolates that
normalization and its evaluation square. All stated dependencies were present; the
gap concerns this coherence interface.

The changed model file layout is documented in
`coord/changes/W3-ringed-localization-model-interface.md`. Every old model definition
and the main signature were checked textually against the shared original. No target
statement or mathematical definition changes.

## New nodes

`lem-weil-pbc-kflat-rhom-currying`: the constructed natural currying isomorphism on
K-flat representatives, descended from the canonical chain evaluation map.

`lem-weil-pbc-ringed-localization-complex-models`: the unchanged public model interface,
its already proved K-flat and product-localization assertions, and the extracted
coefficient K-flat certificate.

`lem-weil-pbc-slice-module-sheafification`: the adjunction-defined restriction comparison
for module sheafification and its proved invertibility.

`lem-weil-pbc-slice-tensor-natural`: the canonical continuous cocontinuous tensor
restriction comparison and its proved naturality in both module arguments.

`lem-weil-pbc-ringed-model-currying`: currying for an arbitrary specified K-flat sheaf
coefficient and a complex with K-flat slice restriction, together with a shared natural
isomorphism and its simultaneous chain-map and derived-target naturality.

`lem-weil-pbc-ringed-model-restriction`: actual coefficient and ordinary tensor-complex
derived transports for a specified further-slice coefficient isomorphism.

`lem-weil-pbc-ringed-localization-natural-currying`: the canonical localization currying
family, its simultaneous naturality, and its component formula.

`lem-weil-pbc-ringed-localization-restriction`: further restriction of the localization
coefficient, constructed from fraction presheaves and module sheafification.

`lem-weil-pbc-ringed-model-currying-coherence`: the sole remaining obligation, preservation
of the already constructed model currying maps under normalized slice restriction.
It still needs the product-projection chain restriction construction and the local
evaluation square, followed by descent through the derived localizations.

Change records: `coord/changes/W3-ringed-localization-model-interface.md` and
`coord/changes/W3-shared-tensor-naturality-helpers.md`.

## Second reading by W3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
