# CategoryTheory.ringedExtendedCech_complete_iff_unit_isIso

## Reason

Separate the single-object geometric fixed-object criterion from the categorical reflection
argument. The latter can use the already proved finite-Cech idempotence calculation after
transport through a finite generating cover. The old core had no proof dependencies and left
both completeness and the universal mapping bijection in a single hole.

## Old

The assigned core declaration (signature preserved verbatim):

```lean
theorem ringedExtendedCech_reflector_core
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (O : Sheaf J CommRingCat.{u})
    [HasDerivedCategory.{w} (ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))]
    [∀ U : C, HasDerivedCategory.{w} (ringedSiteModules.{u}
      ((sheafCompose (J.over U) (forget₂ CommRingCat RingCat)).obj (O.over U)))]
    (I : ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))
    (ι : I ⟶ SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))
    [Mono ι] [I.IsFiniteType]
    (K : ringedSiteComplex O) (ε : K ⟶ ringedSiteRingComplex O)
    (hK : HasLocalExtendedCechDescription O I ι K ε) :
    (∀ E : ringedSiteDerived O,
      IsLocallyDerivedRingedIdealComplete O I ι
        ((ringedCechCompletionFunctor O K).obj E)) ∧
    (∀ (E L : ringedSiteDerived O),
      IsLocallyDerivedRingedIdealComplete O I ι L →
      Function.Bijective
        (fun h : (ringedCechCompletionFunctor O K).obj E ⟶ L ↦
          ringedCechCompletionUnit O K ε E ≫ h))
```

There was no independent single-object criterion available below this declaration. Existing
criteria in UnitPowerCompleteness and RingedKoszulCompletionReflector use the parent reflector
and therefore cannot prove this core without an import cycle.

## New

The assigned core has the same signature. Its proof establishes idempotence by finite-cover
transport and the universal mapping bijection by inverse units and functoriality. It imports
the following strictly smaller geometric obligation in its own module:

```lean
theorem ringedExtendedCech_complete_iff_unit_isIso
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (O : Sheaf J CommRingCat.{u})
    [HasDerivedCategory.{w} (ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))]
    [∀ U : C, HasDerivedCategory.{w} (ringedSiteModules.{u}
      ((sheafCompose (J.over U) (forget₂ CommRingCat RingCat)).obj (O.over U)))]
    (I : ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))
    (ι : I ⟶ SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))
    [Mono ι] [I.IsFiniteType]
    (K : ringedSiteComplex O) (ε : K ⟶ ringedSiteRingComplex O)
    (hK : HasLocalExtendedCechDescription O I ι K ε)
    (E : ringedSiteDerived O) :
    IsLocallyDerivedRingedIdealComplete O I ι E ↔
      IsIso (ringedCechCompletionUnit O K ε E)
```

No definition, instance, target signature, or existing public import changes. No consumer
adaptation is required. This is a decomposition, with one old hole closed and one new hole.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.ExtendedCechReflectorCore | S7 | Uses the new criterion; existing signature stays identical. |
| Sheaf.Paper.ExtendedCechCompletionModel | unclaimed | Existing core consumer; no adaptation or change in meaning. |

The new module has only the assigned core as a consumer in this packet. Existing consumers of
the core see the same declaration with exactly its former type, so all downstream statements
retain their meanings. The new criterion gives no new assumption to a target.

## Status

landed 20261025T203137-L-2786071 2026-10-25 (merge of deliver/S7/Sheaf.Paper.ExtendedCechReflectorCore)
