## What changed

Repair of the returns at heads 4c45fe90e and 0cf283214: moved the five unchanged fixed
augmentation/ordinary-Hom comparison declarations to
`Sheaf.CategoryTheory.RingedSiteOrdinaryHomComparison`. The item publicly reexports
them. `RingedInternalHomShiftOfUniverses` now imports this lower interface instead
of the duality compatibility theorem, breaking the reported cycle. Its signatures
and proofs are unchanged. The unclaimed `RingedSliceHomSourceShift` and
`RingedSiteSignedDualRestriction` receive explicit public duality imports to preserve
their existing model signatures. The unclaimed `CoefficientBidualEvaluationShiftOne`
and `CoefficientBidualTriangleCompatibility` also receive that explicit public import:
their private `import all` does not expose the model, unit and bidual in public signatures.
These five adapted modules have no other changed lines.


In `Sheaf.CategoryTheory.RingedSiteDualityMaps`, proved all four holes without
changing existing signatures or mathematical definitions. Identity-slice and all-slice evaluation
formulas are identified by restriction naturality and Hom extensionality. The signed
bidual localization and unsigned evaluation localization then give the two actual
normalization equations through the fixed augmentation comparisons.

Added tensor-interface lemmas. Functorial flat resolution extends the tensor
comparison from simultaneous K-flat representatives to pairs with either factor K-flat.
The normalized chain maps equal the actual complex braiding, associator and unitors,
which yields full representative coherence with the prescribed coefficient unit.
The scalar-unit proof uses the tensor-unit isomorphism for flatness. Intermediate
generator rewrites and explicit congruence steps keep tensor sheafification opaque.
A private normalization API keeps the localized restriction functor and its localization
isomorphism abstract, and a section-map API records the behavior of termwise restriction.
A private tensor presentation stores the actual total tensor and generators together with
proved naturality and triple-generator extensionality. The generator argument uses these
fields, while a proved bridge retains the original normalization formula. Localization
functors remain locally irreducible throughout the derived comparison calculation.
The categorical representative-square lemma takes both localization and tensor functors
as parameters, so their native constructions are supplied once at the interface.
The natural tensor and Hom isomorphisms are constructed from the given components;
component lemmas expose their maps to a proved categorical duality-compatibility lemma.
The site proof supplies its native comparisons to that lemma once, retaining the
prescribed coefficient-unit isomorphisms and all three original equations.
The generator checks also cover zero terms, shifted complexes and characteristic two;
no sign or scalar invertibility is used.

The restriction argument uses the fixed evaluation-compatible slice comparisons.
The associator comparison is detected on triple local pure tensors, and the scalar-unit
comparison is detected on coefficient degree zero; both are transported along flat-term
K-flat resolutions. The bidual and dual-evaluation equations then follow by transposition.
The ordinary-bidual existence proof reuses the existing signed-bidual localization family
and its uniqueness field. General private bidual components and their section formula remain
verbatim for the two downstream modules that import them through `import all`.
All manually stated public declarations are retained.
Unused generated constructor-injectivity and size-of specification lemmas of the model
are suppressed to avoid expensive artifact generation; the model fields are verbatim.
The delivery validates the complete packet by single-file compilation and preflight.

## Proved and sorry left

Closed all four original holes:

- `CategoryTheory.ringedSiteOrdinaryEvaluation_existsUnique`.
- `CategoryTheory.ringedSiteBidual_normalization`.
- `CategoryTheory.ringedSiteDualEvaluation_normalization`.
- `CategoryTheory.ringedSiteDualityMaps_restriction`.

The four new proved supporting theorems are:

- `CategoryTheory.ringedTensorComparison_extension`.
- `CategoryTheory.ringedTensorConstraint_completion`.
- `CategoryTheory.ringedSlice_tensor_associator`.
- `CategoryTheory.ringedSlice_scalar_unit`.

No `sorry` remains in the item, the five added modules, the adapted internal-Hom shift,
the signed-dual restriction module, or the two adapted coefficient-bidual modules. No holes are added. The adapted
`CategoryTheory.ringedSlice_hom_sourceShift` retains its existing sorry
(node `lem-coef-slice-hom-source-shift`); only its imports change.
The restriction proof is complete from existing stated dependencies; it still depends
on `CategoryTheory.ringedSlice_normalizedComparisons` (node
`lem-weil-pbc-ringed-slice-normalized-comparisons`), through
`CategoryTheory.ringedSlice_evaluation_transpose`. That upstream theorem remains `sorry`.
A fresh `#print axioms` probe shows only `propext`, `Classical.choice` and `Quot.sound`
for the ordinary-evaluation existence theorem and both normalization theorems. It also
shows `sorryAx` for the restriction theorem, as expected from that existing upstream hole.
This delivery closes four local holes, with three of these four theorems fully proved
through their dependencies; the restriction theorem remains conditional on the existing
stated slice-comparison result. No new hole is introduced by this packet.
The earlier claim that unchanged `CoefficientBidualEvaluationShiftOne` compiled in
33.4 seconds against this packet was incorrect and is withdrawn: it had been checked
without the required public-import repair.

The repaired eleven-module packet passed `lcompile.py --all` in dependency order
(exit code 0). In that run the adapted `CoefficientBidualEvaluationShiftOne` passed in
37.0 seconds and its only direct importer, `CoefficientBidualTriangleCompatibility`,
passed in 37.4 seconds. The other adapted consumers passed as well:
`RingedSliceHomSourceShift` in 43.3 seconds and `RingedSiteSignedDualRestriction` in
33.9 seconds. No direct importer of the triangle module exists in the current sources.
A temporary module importing both coefficient-bidual consumers publicly checked
`RingedSiteDualityModel`, `ringedSiteDualityUnit` and `ringedSiteBidual`, and ran the
four axiom probes above (exit code 0, 9.4 seconds). That probe was removed before delivery.
The repaired source overlay has no import cycle among 655 modules reachable from the
item and the two coefficient-bidual consumers. These are the fresh checks of this repair;
the required delivery command runs its compilation and preflight checks again.

## No longer needed

Removed `Sheaf.CategoryTheory.RingedSiteDualityMaps` from the public imports of
`RingedInternalHomShiftOfUniverses`: its proof only needs the shared ordinary-Hom
comparison. The duality model remains needed by the slice source-shift and signed-dual
restriction consumers and the two coefficient-bidual consumers; each now publicly
imports it explicitly. No node is withdrawn.


No modules are withdrawn and no source-library declaration is changed.
Removed the redundant private import of
`WeilConjectures.Algebra.Homology.HomComplexComponents`, which is already publicly
supplied by `CoefficientHomRepresentativeEvaluation`. The private import of
`WeilConjectures.Algebra.Category.ModuleCat.Presheaf.InternalHomUnit` is retained for
the general section-evaluation construction used downstream.
The provisional private import of `RingedSliceEvaluationModels` was removed because
`RingedSliceEvaluationTranspose` already publicly supplies that interface.
The direct composition-model route through `lem-sfb-ringed-hom-composition-model`
(`Sheaf.Algebra.Homology.RingedHomCompositionModel`) and `lem-sc-hom-complex-unit-iso`
is not needed: the existing maps are already actual transposes of composite evaluation
and scalar action. Their naturality and restriction compatibility follow from those
transposes. These nodes are removed from this item’s proof dependencies; no claim is made
that other parents do not need them.

The specialized private coefficient-bidual differential proof is pruned. Its public existence
and uniqueness theorem is retained with a complete proof from signed-bidual localization.
The general section-evaluation, sheaf bidual, bidual components, degree projections and
evaluation formula remain verbatim, as does `RingedSiteComplex`.
`RingedSiteFiniteRetractDualExact` uses `ringedSiteSheafBidual`, and
`CoefficientBidualEvaluationShiftOne` uses the general degree construction and formula.
Removed private helpers:

- `ringedSiteDualityUnit_d`, `ringedSiteDualityUnit_isZero_X`.
- `ringedSiteBidualDegree_comm`.
- `ringedSitePresheafHomObjMap_zero_target`, `ringedSiteHomObjMap_zero_target`,
  `ringedSiteCompSub_zero`, `ringedSiteHomZero_d_proj`, `ringedSiteHomZero_d_eval`.
- `ringedSiteBidualSigns`, `ringedSiteHomObj_isZero_target`, `ringedSiteBidualFormula_ext`.

The model's unused generated constructor-injectivity and size-of specification lemmas
are not needed by any checked consumer. The model fields and all manually stated
public declarations are retained.

The item no longer directly uses `lem-sfb-localized-site-tensor-restriction`; its normalized
restriction model is supplied by `lem-weil-pbc-ringed-slice-evaluation-transpose`. The
localized tensor lemma remains a dependency of that supplied model.

## Where the brief, the DAG or earlier work was wrong

The previous report confused private `import all` access with public signature access.
The reviewer identified unknown `RingedSiteDualityModel`, `ringedSiteDualityUnit` and
`ringedSiteBidual` identifiers in the coefficient-bidual consumers after the shift import
was lowered. Both modules now add the requested public import, retaining all their
existing declarations and proof bodies. The report now explicitly records the upstream
normalized-comparisons sorry rather than suggesting transitive completion.

The previous packet compiled against the published slice-comparison dependency but
failed at landing when that dependency imported the shift module. Its public duality
import made the new restriction proof cyclic. The comparison interface was unnecessarily
located in the duality theorem module. Moving its unchanged declarations repairs the
cycle at its source; the shift node now records the independent comparison dependency.


The ordinary localization formula tests identity slices, whereas the item tests all
slice objects. An explicit naturality and Hom-extensionality bridge is needed.

The normalization prerequisites require full `RingedDerivedTensorCoherence` for the
specified structure. `RingedSiteDualityModel` supplies morphism-level constraints on
simultaneous K-flat representatives. The new proved interface lemmas supply the missing
natural one-K-flat comparison and identify the constraints with actual isomorphisms.

The slice evaluation/transpose interface supplies the counit and braiding equations,
but not the associator and scalar-unit equations used in the dual-evaluation transpose.
The delivery proves those equations directly from its normalized tensor models.

## New nodes

`lem-sfb-ringed-tensor-comparison-extension`, module
`Sheaf.Algebra.Homology.RingedTensorComparisonExtension`: functorial-resolution extension of the
prescribed simultaneous K-flat tensor comparison to one K-flat factor.

`lem-sfb-ringed-tensor-constraint-completion`, module
`Sheaf.Algebra.Homology.RingedTensorConstraintCompletion`: completion of normalized morphism-level
constraints to full tensor coherence, retaining the prescribed coefficient unit.

`lem-sfb-ringed-slice-tensor-constraints`, module
`Sheaf.Algebra.Homology.RingedSliceTensorConstraints`: associator compatibility on representatives
and transport to arbitrary derived objects.

`lem-sfb-ringed-slice-scalar-unit`, module
`Sheaf.Algebra.Homology.RingedSliceScalarUnit`: construction of the restriction coefficient
identification and compatibility of scalar action.

Change record: `coord/changes/ringed-site-duality-model-generated-helpers.md`.
It records the unused generated helper suppression and the downstream source checks.
Existing mathematical statements, record fields and definition bodies are unchanged.
The repaired public imports are listed above. No claimed module needs forced adaptation.

`lem-sfb-ringed-site-ordinary-hom-comparison`, module
`Sheaf.CategoryTheory.RingedSiteOrdinaryHomComparison`: the five existing comparison
declarations moved unchanged, with their elementary IsIso proof. This is not a new hole
or a duplicated notion. Searches found the generic localization APIs and the existing
project comparison; the latter is retained verbatim. Change record:
`coord/changes/ringed-site-ordinary-hom-comparison-import-cycle.md`.

## Second reading by U7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
