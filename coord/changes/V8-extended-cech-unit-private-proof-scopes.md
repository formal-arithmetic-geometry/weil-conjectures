# CategoryTheory.ringedExtendedCech_unit_isIso_implies_complete

## Reason

Complete the original proof while retaining the exact public statement and the
three public imports. The conservative interface comparison records added
`open`, `variable`, `section`, and option commands, even though these only support
the proof. This record documents their effects and the existing consumers.

## Old

```lean
theorem ringedExtendedCech_unit_isIso_implies_complete
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (O : Sheaf J CommRingCat.{u})
    [HasDerivedCategory.{w} (ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))]
    [∀ U : C, HasDerivedCategory.{w}
      (ringedSiteModules.{u}
        ((sheafCompose (J.over U) (forget₂ CommRingCat RingCat)).obj (O.over U)))]
    (I : ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))
    (ι : I ⟶ SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))
    [Mono ι] [I.IsFiniteType]
    (K : ringedSiteComplex O) (ε : K ⟶ ringedSiteRingComplex O)
    (hK : HasLocalExtendedCechDescription O I ι K ε)
    (E : ringedSiteDerived O) :
    IsIso (ringedCechCompletionUnit O K ε E) →
      IsLocallyDerivedRingedIdealComplete O I ι E
```

## New

```lean
theorem ringedExtendedCech_unit_isIso_implies_complete
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (O : Sheaf J CommRingCat.{u})
    [HasDerivedCategory.{w} (ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))]
    [∀ U : C, HasDerivedCategory.{w}
      (ringedSiteModules.{u}
        ((sheafCompose (J.over U) (forget₂ CommRingCat RingCat)).obj (O.over U)))]
    (I : ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))
    (ι : I ⟶ SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))
    [Mono ι] [I.IsFiniteType]
    (K : ringedSiteComplex O) (ε : K ⟶ ringedSiteRingComplex O)
    (hK : HasLocalExtendedCechDescription O I ι K ε)
    (E : ringedSiteDerived O) :
    IsIso (ringedCechCompletionUnit O K ε E) →
      IsLocallyDerivedRingedIdealComplete O I ι E
```

The signatures are verbatim identical. All newly added declarations are private
proved theorems. Their section `LocalCalculation` and its module/category variables
end before the existing public theorem. The expanded `open` commands and
`open scoped BigOperators` only resolve names in this module. The
`synthInstance.maxSize` option supports elaboration of the categorical proof;
it exports no instance or attribute. All new imports are proof-only imports.
There are no new public declarations, definitions, instances, or attributes.
No target statement or any definition used by a target changes.

## Users

`tools/downstream.py Sheaf.Paper.ExtendedCechUnitIsoImpliesComplete --uses
CategoryTheory.ringedExtendedCech_unit_isIso_implies_complete` lists the following
two textual users. The external consumer was read in full: it applies this theorem
to prove the reverse implication of the fixed-object criterion, with exactly the
unchanged arguments. It needs no adaptation. Holders are from the current claims.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.ExtendedCechUnitIsoImpliesComplete | V8 | Completes the proof; public signature unchanged. |
| Sheaf.Paper.ExtendedCechCompleteUnitCriterion | unclaimed | Applies the unchanged theorem; no adaptation. |

## Status

landed 20261026T024154-L-643306 2026-10-26 (merge of deliver/V8/Sheaf.Paper.ExtendedCechUnitIsoImpliesComplete)
