# WeilConjectures.CompactSupportCondensedRealization.fieldRefinement_comp

## Reason

The composition proof performs adjunction and equality-transport calculations on
named derived functors. A new local section keeps the
named pullback and pullback compositor irreducible until explicitly unfolded at
the source associativity theorem. This prevents unsuccessful rewrite matching
from expanding the large derived constructions. These commands only affect the
new proof section. The return functor in `fieldPushComp` is now written using the existing
`fieldDerivedLowerStar` name, definitionally equal to its former expanded type.
Its constructor body is unchanged. Every original public import is retained;
the new public Core import reexports the relocated constructions. Exported
instances and reducibility attributes are unchanged.

## Old

```lean
theorem fieldRefinement_comp {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c d e : Compactification f} (r : c.Refinement d) (s : d.Refinement e) :
    fieldRefinement Λ (r.comp s) = fieldRefinement Λ s ≫ fieldRefinement Λ r := by
  sorry
```

The new proof section and its local commands were absent. The old compositor
return type was:

```lean
def fieldPushComp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (fieldDerivedLowerStar Λ f) ⋙
        (fieldDerivedLowerStar Λ g) ≅
      (CondensedRing.lowerStar Λ (f ≫ g)).rightDerivedFunctor :=
  conjugateIsoEquiv
    ((fieldDerivedAdjunction Λ g).comp
      (fieldDerivedAdjunction Λ f))
    (fieldDerivedAdjunction Λ (f ≫ g))
    (fieldDerivedPullComp Λ f g)
```

## New

The compositor now uses exactly the existing named presentation:

```lean
def fieldPushComp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (fieldDerivedLowerStar Λ f) ⋙
        (fieldDerivedLowerStar Λ g) ≅
      fieldDerivedLowerStar Λ (f ≫ g) :=
  conjugateIsoEquiv
    ((fieldDerivedAdjunction Λ g).comp
      (fieldDerivedAdjunction Λ f))
    (fieldDerivedAdjunction Λ (f ≫ g))
    (fieldDerivedPullComp Λ f g)
```

The type unfolds to the former type by the definition of `fieldDerivedLowerStar`;
no object, morphism, compositor, normalization, or hypothesis changes. The source
constructor body above is verbatim. The four direct importers must compile
against this presentation before delivery.

The theorem has the identical signature above and a complete proof. Its new private
composition helpers are inside the new section with these local commands:

```lean
attribute [local irreducible] fieldDerivedUpperStar fieldDerivedLowerStar
  fieldDerivedOpenShriek fieldDerivedPullComp fieldDerivedAdjunction
attribute [local irreducible] CondensedRing.upperStar CondensedRing.lowerStar
  CondensedRing.openImmersionLowerShriek
attribute [local irreducible] conjugateEquiv conjugateIsoEquiv mateEquiv
set_option backward.defeqAttrib.useBackward false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
```

The original local data-cache instances and their final exported registrations
are unchanged. All geometric constructor bodies remain verbatim.

The existing generic helper block, from `rightComparison_shift` through
`IdentityProofHelpers`, moves verbatim to the private proof import
`Sheaf.CategoryTheory.CompactSupportIdentityCalculus`. It does not depend on the
geometric category instances. The old private `normalized_identity_lift` becomes
the proved public `CategoryTheory.normalizedIdentityLift`, with a source/proof
docstring and its own node; its proof is unchanged. The call in the existing
`fieldProperOpen_id` proof is updated to that name. All other moved helpers remain
private and are available through `import all`. Their CanonicalRightDerivedAdjunctionShift
and AdjunctionIdIso proof imports move to that module as well; both dependencies
remain in the import closure. A text comparison confirms that the block is otherwise verbatim after accounting
for that public name and its added docstring. This removes approximately 400
lines of generic calculations from the geometric file. A second extraction moves
another 241 lines of existing generic coefficient-composition and normalized-lift
naturality helpers, also verbatim, to the same private proof import. The ConjugatePaste proof import moves with these generic calculations. The public
`pasteScalar` construction and its helpers that use it stay in the geometric file.
Together these extractions retain all of
their uses and every existing public signature and definition body.

The new local proof section also keeps `fieldDerivedLowerStar`,
`fieldDerivedOpenShriek`, `fieldDerivedAdjunction`, `fieldPushComp`, and
`counitRestrictionNat` irreducible while using their proved APIs. The two generic
modules have complete proofs. The mate square is supplied componentwise, so its
specialization does not depend on reducing associativity of large concrete
composite functors. The explicit equality transports retain the actual index
`(r.comp s).hom` until the transport lemmas eliminate its defining equality.
The public refinement is identified with its assembled natural transformation
before entering the new proof section. Within the section, restriction
normalizations are identified first as natural transformations and then evaluated;
the mate compositor identity is also retained as a natural transformation.
The direct specialization of the generic mate theorem avoids intermediate local
functor aliases. Naturality proves composition of `assembleLiftNat`, and the
original public theorem follows by the proved presentation identity after the
section closes. No target changes meaning.


The final compile-time split moves the original concrete constructions and all
already proved coherence declarations to
`Sheaf.Paper.CondensedCompactSupportProjectionCore` (zero holes), and publicly
imports that module from the item. The two originally holed theorems stay in the
item; composition is proved and the coefficient/refinement square remains holed.
The core has 59 of the original public declarations, with identical names,
attributes, and construction bodies. The sole textual signature change is the
definitionally equal `fieldPushComp` return type recorded above. The original node's `lean`
attachment now lists the two item theorems; the new core node carries the other
59. No mathematical statement changes. The existing generic private helpers are
in their previously described proof module. A copy of the existing private
`fieldProperOpen_spec` proof provides the normalization API in the item without
exporting it. The original local cache registrations are reactivated for the
composition proof, and the original exported instance-registration footer remains
verbatim at the end of the item. All original public imports stay in the item,
with the added public core import because the theorem statements use its data.
The construction bodies and their instance choices are unchanged in the core.
The public namespace visible to consumers contains the same original declarations.

## Users

Read-only `tools/downstream.py` reports the following 55 downstream modules.
None is edited. The four direct importers are
`Sheaf.Paper.CompactSupportCondensedRealization`,
`Sheaf.Paper.CompactSupportRealizationFactorization`,
`Sheaf.Paper.CompactSupportRealizationFactorNormalization`, and
`Sheaf.Paper.CondensedCompositorRealization`.
All five delivery modules and all four unchanged direct consumers compiled
successfully in compile result `a2a715f29da4acabf4ec147f`, within the required
limits. The axiom printer compiled in the same run. The consumer copies and
printer were removed from the packet afterward. A declaration-table comparison
confirmed all 61 original public names remain, all public non-theorem bodies
match exactly, and every recorded Lean signature matches the corresponding
declaration. The sole textual signature change is the definitionally equal
`fieldPushComp` return type above. Profiling of the earlier combined file showed
many modest costs rather than an individual slow declaration; the core and
private-helper extractions provide separate compilation units. No profiling
options remain in the packet.
Holders were not queried because no module other than the assigned item is modified.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.CondensedCompactSupportProjection | J3 | Composition proved; original constructions reexported from the core. |
| Sheaf.Paper.CompactSupportCondensedRealization | not queried; unchanged | Same declaration signatures through public core import; no adaptation. |
| Sheaf.Paper.CompactSupportRealizationFactorNormalization | not queried; unchanged | Same declaration signatures through public core import; no adaptation. |
| Sheaf.Paper.CompactSupportRealizationFactorization | not queried; unchanged | Same declaration signatures through public core import; no adaptation. |
| Sheaf.Paper.CondensedCompositorRealization | not queried; unchanged | Same declaration signatures through public core import; no adaptation. |
| Sheaf.Paper.CondensedExceptionalCounitRepresentation | not queried; unchanged | Same declaration signatures through public core import; no adaptation. |
| Sheaf.Paper.CondensedExceptionalRealizationProperties | not queried; unchanged | Same declaration signatures through public core import; no adaptation. |
| Sheaf.Paper.CondensedExceptionalReconstruction | not queried; unchanged | Same declaration signatures through public core import; no adaptation. |
| Sheaf.Paper.CondensedExceptionalReconstructionData | not queried; unchanged | Same declaration signatures through public core import; no adaptation. |
| Sheaf.Paper.CondensedExceptionalRefinementCounits | not queried; unchanged | Same declaration signatures through public core import; no adaptation. |
| Sheaf.Paper.CondensedExceptionalSystemRecognition | not queried; unchanged | Same declaration signatures through public core import; no adaptation. |
| Sheaf.Paper.CondensedOpenCoefficientModels | not queried; unchanged | Same declaration signatures through public core import; no adaptation. |
| Sheaf.Paper.CondensedOpenCounitComparisons | not queried; unchanged | Same declaration signatures through public core import; no adaptation. |
| Sheaf.Paper.CondensedOpenCounitRealization | not queried; unchanged | Same declaration signatures through public core import; no adaptation. |
| Sheaf.Paper.CondensedOpenCounitRealizationSupport | not queried; unchanged | Same declaration signatures through public core import; no adaptation. |
| Sheaf.Paper.CondensedOpenCounitUnits | not queried; unchanged | Same declaration signatures through public core import; no adaptation. |
| Sheaf.Paper.CondensedOpenUnitComparison | not queried; unchanged | Same declaration signatures through public core import; no adaptation. |
| Sheaf.Paper.ExceptionalRealizationNormalization | not queried; unchanged | Same declaration signatures through public core import; no adaptation. |
| Sheaf.Paper.ExceptionalReconstructionComparison | not queried; unchanged | Same declaration signatures through public core import; no adaptation. |
| Sheaf.Paper.ExceptionalReconstructionContext | not queried; unchanged | Same declaration signatures through public core import; no adaptation. |
| Sheaf.Paper.ExceptionalReconstructionPresentations | not queried; unchanged | Same declaration signatures through public core import; no adaptation. |
| Sheaf.Paper.FilteredCondensedCanonicalComparisons | not queried; unchanged | Same declaration signatures through public core import; no adaptation. |
| Sheaf.Paper.FilteredCondensedCounitBijective | not queried; unchanged | Same declaration signatures through public core import; no adaptation. |
| Sheaf.Paper.FilteredCondensedCounitFiniteFormula | not queried; unchanged | Same declaration signatures through public core import; no adaptation. |
| Sheaf.Paper.FilteredCondensedRepresentingPair | not queried; unchanged | Same declaration signatures through public core import; no adaptation. |
| Sheaf.Paper.FilteredCondensedRepresentingPairData | not queried; unchanged | Same declaration signatures through public core import; no adaptation. |
| Sheaf.Paper.GeneralCondensedWeilRealization | not queried; unchanged | Same declaration signatures through public core import; no adaptation. |
| Sheaf.Paper.MixedCupCoefficientChange | not queried; unchanged | Same declaration signatures through public core import; no adaptation. |
| Sheaf.Paper.MixedCupCoefficientSquare | not queried; unchanged | Same declaration signatures through public core import; no adaptation. |
| Sheaf.Paper.MixedCupFieldCoordinates | not queried; unchanged | Same declaration signatures through public core import; no adaptation. |
| Sheaf.Paper.MixedCupFieldNormalization | not queried; unchanged | Same declaration signatures through public core import; no adaptation. |
| Sheaf.Paper.MixedCupFieldOperations | not queried; unchanged | Same declaration signatures through public core import; no adaptation. |
| Sheaf.Paper.MixedCupOperationComparisons | not queried; unchanged | Same declaration signatures through public core import; no adaptation. |
| Sheaf.Paper.MixedCupRingedNormalization | not queried; unchanged | Same declaration signatures through public core import; no adaptation. |
| Sheaf.Paper.MixedCupTensorClosure | not queried; unchanged | Same declaration signatures through public core import; no adaptation. |
| Sheaf.Paper.MixedCupTensorComparisons | not queried; unchanged | Same declaration signatures through public core import; no adaptation. |
| Sheaf.Paper.MixedCupTensorElementary | not queried; unchanged | Same declaration signatures through public core import; no adaptation. |
| Sheaf.Paper.MixedCupTensorNormalization | not queried; unchanged | Same declaration signatures through public core import; no adaptation. |
| Sheaf.Paper.NativeWeilScalarFrobeniusCounit | not queried; unchanged | Same declaration signatures through public core import; no adaptation. |
| Sheaf.Paper.PurCoordinateRepresentingFamily | not queried; unchanged | Same declaration signatures through public core import; no adaptation. |
| Sheaf.Paper.PurIntegralRepresentingPair | not queried; unchanged | Same declaration signatures through public core import; no adaptation. |
| Sheaf.Paper.PurIntegralRepresentingPairData | not queried; unchanged | Same declaration signatures through public core import; no adaptation. |
| Sheaf.Paper.PurIntegralSupportComparison | not queried; unchanged | Same declaration signatures through public core import; no adaptation. |
| Sheaf.Paper.PurIntegralSupportComparisonData | not queried; unchanged | Same declaration signatures through public core import; no adaptation. |
| Sheaf.Paper.PurIntegralSupportDerivedComparison | not queried; unchanged | Same declaration signatures through public core import; no adaptation. |
| Sheaf.Paper.PurIntegralSupportOrdinaryComparison | not queried; unchanged | Same declaration signatures through public core import; no adaptation. |
| Sheaf.Paper.PurRepresentingPairFiniteScalar | not queried; unchanged | Same declaration signatures through public core import; no adaptation. |
| Sheaf.Paper.PurSupportPresentationAlpha | not queried; unchanged | Same declaration signatures through public core import; no adaptation. |
| Sheaf.Paper.ReconstructedBrownMateLaws | not queried; unchanged | Same declaration signatures through public core import; no adaptation. |
| Sheaf.Paper.ReconstructedPairRefinementCoherence | not queried; unchanged | Same declaration signatures through public core import; no adaptation. |
| Sheaf.Paper.ReconstructedPairRefinementData | not queried; unchanged | Same declaration signatures through public core import; no adaptation. |
| Sheaf.Paper.ReconstructedRefinementCommon | not queried; unchanged | Same declaration signatures through public core import; no adaptation. |
| Sheaf.Paper.ReconstructedRefinementSingleDegree | not queried; unchanged | Same declaration signatures through public core import; no adaptation. |
| Sheaf.Paper.ReconstructedRefinementTraceSquare | not queried; unchanged | Same declaration signatures through public core import; no adaptation. |
| Sheaf.Paper.ReconstructedRefinementTraceTransport | not queried; unchanged | Same declaration signatures through public core import; no adaptation. |
| Sheaf.Paper.RefinementFiniteOriginEvaluation | not queried; unchanged | Same declaration signatures through public core import; no adaptation. |

## Status

landed 20261027T012851-L-2342239 2026-10-27 (merge of deliver/J3/Sheaf.Paper.CondensedCompactSupportProjection)
