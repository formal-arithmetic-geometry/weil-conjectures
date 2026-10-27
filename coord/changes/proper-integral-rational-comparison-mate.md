# AlgebraicGeometry.ProEtale.CondensedRing.properIntegralRationalScalarComparison

## Reason

The original specialized counit-transpose expression repeatedly unfolds tensor-resolution
instances when compared with the canonical coefficient-change mate. Use the same canonical
arrow expressed as `derivedPushHom`, with exactly the coefficient map and flatness argument
of `integralRationalScalarPullIso`. The proved private `push_counit_formula` identifies this
mate with the original specified counit transpose for arbitrary scalar and geometric
adjunctions. No arrow, inverse, coefficient map or adjunction is chosen anew.

## Old

```lean
def properIntegralRationalScalarComparison (ℓ : ℕ) [Fact ℓ.Prime]
    {F E : PadicAlgCl.FiniteIntermediateField ℓ} (i : F ≤ E)
    {U V : Scheme.{u}} (h : U ⟶ V)
    (J : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ F.1) U))) :
    (integralRationalScalarExtension ℓ i V).obj
          ((moduleObjectDerivedPushforward (Profinite.padicIntegersRingObj ℓ F.1) h).obj J) ⟶
      (moduleObjectDerivedPushforward (Profinite.continuousMapRingObj E.1) h).obj
        ((integralRationalScalarExtension ℓ i U).obj J) :=
  (derivedUpperStarLowerStarAdjunction (Profinite.continuousMapRingObj E.1) h).homEquiv _ _
    ((integralRationalScalarPullIso ℓ i h).inv.app
        ((moduleObjectDerivedPushforward (Profinite.padicIntegersRingObj ℓ F.1) h).obj J) ≫
      (integralRationalScalarExtension ℓ i U).map
          ((derivedUpperStarLowerStarAdjunction
            (Profinite.padicIntegersRingObj ℓ F.1) h).counit.app J))
```

## New

```lean
def properIntegralRationalScalarComparison (ℓ : ℕ) [Fact ℓ.Prime]
    {F E : PadicAlgCl.FiniteIntermediateField ℓ} (i : F ≤ E)
    {U V : Scheme.{u}} (h : U ⟶ V)
    (J : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ F.1) U))) :
    (integralRationalScalarExtension ℓ i V).obj
          ((moduleObjectDerivedPushforward (Profinite.padicIntegersRingObj ℓ F.1) h).obj J) ⟶
      (moduleObjectDerivedPushforward (Profinite.continuousMapRingObj E.1) h).obj
        ((integralRationalScalarExtension ℓ i U).obj J) :=
  letI : ∀ X : Scheme.{u}, PreservesFiniteLimits
      (Mod.extendScalars (coefficientMap (integralRationalCoefficientMap ℓ i) X)) :=
    fun X ↦
      letI : PreservesFiniteLimits (Mod.extendScalars (padicIntegersToPadicSubfield X ℓ F)) :=
        (padicIntegers_invertEll X ℓ F).choose_spec.2.choose_spec.2.2.choose_spec.2.2.2
      letI : PreservesFiniteLimits (Mod.extendScalars (padicSubfieldRingObjMap X ℓ i)) :=
        (cartesianCoefficients_finiteFree ℓ i).2.2 X |>.2
      letI := comp_preservesFiniteLimits
        (Mod.extendScalars (padicIntegersToPadicSubfield X ℓ F))
        (Mod.extendScalars (padicSubfieldRingObjMap X ℓ i))
      preservesFiniteLimits_of_natIso
        ((Mod.extendScalarsComp (padicIntegersToPadicSubfield X ℓ F)
          (padicSubfieldRingObjMap X ℓ i)).symm ≪≫
            Mod.extendScalarsIsoOfEq (coefficientMap_comp
              (padicIntegersRingObjToContinuousMapRingObj ℓ F)
              (Profinite.padicSubfieldRingObjMap ℓ i) X).symm)
  (derivedPushHom (integralRationalCoefficientMap ℓ i) h).app J
```

## Users

`tools/downstream.py Sheaf.Paper.ProperIntegralRationalScalarComparison --uses
integralRationalScalarExtension integralRationalScalarPullIso
properIntegralRationalScalarComparison` reports zero downstream modules. The only uses of
these names are in the item module. DAG parents with unfinished proofs are preserved.

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.Paper.ProperIntegralRationalScalarComparison` | Y8 | Same comparison, expressed by its canonical mate; final proof uses mate pasting. |

All existing public signatures and all other public definition bodies remain verbatim.
No target statement changes. The proved generic counit identity preserves the specified
normalization. The definition change reopens target-definition review under the stage-3 rule.

## Status

landed 20261024T191841-L-518679 2026-10-24 (merge of deliver/Y8/Sheaf.Paper.ProperIntegralRationalScalarComparison)
