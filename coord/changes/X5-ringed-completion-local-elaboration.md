# CategoryTheory.ringedPushforward_completion

## Reason

Repeated elaboration of the unchanged image-ideal interface unfolds generic
multicospan-based sheaf-composition instances. Diagnostics record hundreds of
multicospan reductions and thousands of small-category reductions. The theorem
sometimes reaches the unchanged 60-second limit. Restricting instance search
locally to the existing limit-preservation instance avoids those large proof
terms. Both disabled instance attributes are restored after this declaration.
This is an elaboration change only: no public declaration signature, public
import, definition, or mathematical statement changes. The static interface
check conservatively records the new scoped attribute command, hence this record.

## Old

The statement before its proof, verbatim:

```lean
theorem ringedPushforward_completion
    {C X : Type u} [SmallCategory C] [SmallCategory X]
    {J : GrothendieckTopology C} {K : GrothendieckTopology X}
    (RY : Sheaf J CommRingCat.{u}) (RX : Sheaf K CommRingCat.{u})
    [HasDerivedCategory.{wY} (ringedSiteModules.{u, u, u, u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj RY))]
    [HasDerivedCategory.{wX} (ringedSiteModules.{u, u, u, u}
      ((sheafCompose K (forget₂ CommRingCat RingCat)).obj RX))]
    [∀ U : C, HasDerivedCategory.{wY} (ringedSiteModules.{u, u, u, u}
      ((sheafCompose (J.over U) (forget₂ CommRingCat RingCat)).obj (RY.over U)))]
    [∀ U : X, HasDerivedCategory.{wX} (ringedSiteModules.{u, u, u, u}
      ((sheafCompose (K.over U) (forget₂ CommRingCat RingCat)).obj (RX.over U)))]
    (f : RingedToposMorphism
      ((sheafCompose K (forget₂ CommRingCat RingCat)).obj RX)
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj RY))
    (IY : ringedSiteModules.{u, u, u, u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj RY))
    (ιY : IY ⟶ SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj RY))
    [Mono ιY] [IY.IsFiniteType]
    (IX : ringedSiteModules.{u, u, u, u} ((sheafCompose K (forget₂ CommRingCat RingCat)).obj RX))
    (ιX : IX ⟶ SheafOfModules.unit ((sheafCompose K (forget₂ CommRingCat RingCat)).obj RX))
    [Mono ιX]
    (hImage : ∀ (N : ringedSiteModules.{u, u, u, u}
      ((sheafCompose K (forget₂ CommRingCat RingCat)).obj RX))
      (j : N ⟶ SheafOfModules.unit ((sheafCompose K (forget₂ CommRingCat RingCat)).obj RX)),
      Mono j →
      (∃ k : f.inverse.obj ((SheafOfModules.toSheaf
          ((sheafCompose J (forget₂ CommRingCat RingCat)).obj RY) ⋙
          sheafCompose J (forget AddCommGrpCat)).obj IY) ⟶
          (SheafOfModules.toSheaf ((sheafCompose K (forget₂ CommRingCat RingCat)).obj RX) ⋙
            sheafCompose K (forget AddCommGrpCat)).obj N,
        (k ≫ (SheafOfModules.toSheaf ((sheafCompose K (forget₂ CommRingCat RingCat)).obj RX) ⋙
            sheafCompose K (forget AddCommGrpCat)).map j : _ ⟶ (sheafCompose K (forget RingCat)).obj
              ((sheafCompose K (forget₂ CommRingCat RingCat)).obj RX)) =
          (f.inverse.map ((SheafOfModules.toSheaf
          ((sheafCompose J (forget₂ CommRingCat RingCat)).obj RY) ⋙
            sheafCompose J (forget AddCommGrpCat)).map ιY) : _ ⟶ f.inverse.obj
              ((sheafCompose J (forget RingCat)).obj
                ((sheafCompose J (forget₂ CommRingCat RingCat)).obj RY))) ≫ f.ringMap) ↔
      ∃ a : IX ⟶ N, a ≫ j = ιX)
    (Rf : ringedSiteDerived.{u, wX} RX ⥤ ringedSiteDerived.{u, wY} RY)
    (ρ : f.modules.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
      DerivedCategory.Q.{wY} (C := ringedSiteModules.{u, u, u, u}
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj RY)) ⟶
      DerivedCategory.Q.{wX} (C := ringedSiteModules.{u, u, u, u}
        ((sheafCompose K (forget₂ CommRingCat RingCat)).obj RX)) ⋙ Rf)
    (hRf : Rf.IsRightDerivedFunctor ρ
      (HomologicalComplex.quasiIso (ringedSiteModules.{u, u, u, u}
        ((sheafCompose K (forget₂ CommRingCat RingCat)).obj RX)) (ComplexShape.up ℤ)))
    (hCompute : ∀ I : CochainComplex (ringedSiteModules.{u, u, u, u}
      ((sheafCompose K (forget₂ CommRingCat RingCat)).obj RX)) ℤ,
      I.IsKInjective → IsIso (ρ.app I))
    (ΛX : ringedSiteDerived.{u, wX} RX ⥤ ringedSiteDerived.{u, wX} RX)
    (ΛY : ringedSiteDerived.{u, wY} RY ⥤ ringedSiteDerived.{u, wY} RY)
    (ηX : 𝟭 (ringedSiteDerived.{u, wX} RX) ⟶ ΛX)
    (ηY : 𝟭 (ringedSiteDerived.{u, wY} RY) ⟶ ΛY)
    (hCompleteX : ∀ M : ringedSiteDerived.{u, wX} RX,
      IsLocallyDerivedRingedIdealComplete.{u, wX} RX IX ιX (ΛX.obj M))
    (hCompleteY : ∀ M : ringedSiteDerived.{u, wY} RY,
      IsLocallyDerivedRingedIdealComplete.{u, wY} RY IY ιY (ΛY.obj M))
    (hReflectX : ∀ M L : ringedSiteDerived.{u, wX} RX,
      IsLocallyDerivedRingedIdealComplete.{u, wX} RX IX ιX L →
      Function.Bijective (fun a : ΛX.obj M ⟶ L ↦ ηX.app M ≫ a))
    (hReflectY : ∀ M L : ringedSiteDerived.{u, wY} RY,
      IsLocallyDerivedRingedIdealComplete.{u, wY} RY IY ιY L →
      Function.Bijective (fun a : ΛY.obj M ⟶ L ↦ ηY.app M ≫ a)) :
    (∀ M : ringedSiteDerived.{u, wX} RX,
      IsLocallyDerivedRingedIdealComplete.{u, wX} RX IX ιX M →
      IsLocallyDerivedRingedIdealComplete.{u, wY} RY IY ιY (Rf.obj M)) ∧
    ∃ γ : Rf ⋙ ΛY ≅ ΛX ⋙ Rf,
      (∀ M : ringedSiteDerived.{u, wX} RX,
        ηY.app (Rf.obj M) ≫ γ.hom.app M = Rf.map (ηX.app M)) ∧
      ∀ (M : ringedSiteDerived.{u, wX} RX) (a : ΛY.obj (Rf.obj M) ⟶ Rf.obj (ΛX.obj M)),
        ηY.app (Rf.obj M) ≫ a = Rf.map (ηX.app M) → a = γ.hom.app M
```

## New

The same statement with declaration-local elaboration attributes:

```lean
attribute [-instance] hasSheafCompose_of_preservesMulticospan
  hasSheafComposeEssentiallySmallSite in
theorem ringedPushforward_completion
    {C X : Type u} [SmallCategory C] [SmallCategory X]
    {J : GrothendieckTopology C} {K : GrothendieckTopology X}
    (RY : Sheaf J CommRingCat.{u}) (RX : Sheaf K CommRingCat.{u})
    [HasDerivedCategory.{wY} (ringedSiteModules.{u, u, u, u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj RY))]
    [HasDerivedCategory.{wX} (ringedSiteModules.{u, u, u, u}
      ((sheafCompose K (forget₂ CommRingCat RingCat)).obj RX))]
    [∀ U : C, HasDerivedCategory.{wY} (ringedSiteModules.{u, u, u, u}
      ((sheafCompose (J.over U) (forget₂ CommRingCat RingCat)).obj (RY.over U)))]
    [∀ U : X, HasDerivedCategory.{wX} (ringedSiteModules.{u, u, u, u}
      ((sheafCompose (K.over U) (forget₂ CommRingCat RingCat)).obj (RX.over U)))]
    (f : RingedToposMorphism
      ((sheafCompose K (forget₂ CommRingCat RingCat)).obj RX)
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj RY))
    (IY : ringedSiteModules.{u, u, u, u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj RY))
    (ιY : IY ⟶ SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj RY))
    [Mono ιY] [IY.IsFiniteType]
    (IX : ringedSiteModules.{u, u, u, u} ((sheafCompose K (forget₂ CommRingCat RingCat)).obj RX))
    (ιX : IX ⟶ SheafOfModules.unit ((sheafCompose K (forget₂ CommRingCat RingCat)).obj RX))
    [Mono ιX]
    (hImage : ∀ (N : ringedSiteModules.{u, u, u, u}
      ((sheafCompose K (forget₂ CommRingCat RingCat)).obj RX))
      (j : N ⟶ SheafOfModules.unit ((sheafCompose K (forget₂ CommRingCat RingCat)).obj RX)),
      Mono j →
      (∃ k : f.inverse.obj ((SheafOfModules.toSheaf
          ((sheafCompose J (forget₂ CommRingCat RingCat)).obj RY) ⋙
          sheafCompose J (forget AddCommGrpCat)).obj IY) ⟶
          (SheafOfModules.toSheaf ((sheafCompose K (forget₂ CommRingCat RingCat)).obj RX) ⋙
            sheafCompose K (forget AddCommGrpCat)).obj N,
        (k ≫ (SheafOfModules.toSheaf ((sheafCompose K (forget₂ CommRingCat RingCat)).obj RX) ⋙
            sheafCompose K (forget AddCommGrpCat)).map j : _ ⟶ (sheafCompose K (forget RingCat)).obj
              ((sheafCompose K (forget₂ CommRingCat RingCat)).obj RX)) =
          (f.inverse.map ((SheafOfModules.toSheaf
          ((sheafCompose J (forget₂ CommRingCat RingCat)).obj RY) ⋙
            sheafCompose J (forget AddCommGrpCat)).map ιY) : _ ⟶ f.inverse.obj
              ((sheafCompose J (forget RingCat)).obj
                ((sheafCompose J (forget₂ CommRingCat RingCat)).obj RY))) ≫ f.ringMap) ↔
      ∃ a : IX ⟶ N, a ≫ j = ιX)
    (Rf : ringedSiteDerived.{u, wX} RX ⥤ ringedSiteDerived.{u, wY} RY)
    (ρ : f.modules.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
      DerivedCategory.Q.{wY} (C := ringedSiteModules.{u, u, u, u}
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj RY)) ⟶
      DerivedCategory.Q.{wX} (C := ringedSiteModules.{u, u, u, u}
        ((sheafCompose K (forget₂ CommRingCat RingCat)).obj RX)) ⋙ Rf)
    (hRf : Rf.IsRightDerivedFunctor ρ
      (HomologicalComplex.quasiIso (ringedSiteModules.{u, u, u, u}
        ((sheafCompose K (forget₂ CommRingCat RingCat)).obj RX)) (ComplexShape.up ℤ)))
    (hCompute : ∀ I : CochainComplex (ringedSiteModules.{u, u, u, u}
      ((sheafCompose K (forget₂ CommRingCat RingCat)).obj RX)) ℤ,
      I.IsKInjective → IsIso (ρ.app I))
    (ΛX : ringedSiteDerived.{u, wX} RX ⥤ ringedSiteDerived.{u, wX} RX)
    (ΛY : ringedSiteDerived.{u, wY} RY ⥤ ringedSiteDerived.{u, wY} RY)
    (ηX : 𝟭 (ringedSiteDerived.{u, wX} RX) ⟶ ΛX)
    (ηY : 𝟭 (ringedSiteDerived.{u, wY} RY) ⟶ ΛY)
    (hCompleteX : ∀ M : ringedSiteDerived.{u, wX} RX,
      IsLocallyDerivedRingedIdealComplete.{u, wX} RX IX ιX (ΛX.obj M))
    (hCompleteY : ∀ M : ringedSiteDerived.{u, wY} RY,
      IsLocallyDerivedRingedIdealComplete.{u, wY} RY IY ιY (ΛY.obj M))
    (hReflectX : ∀ M L : ringedSiteDerived.{u, wX} RX,
      IsLocallyDerivedRingedIdealComplete.{u, wX} RX IX ιX L →
      Function.Bijective (fun a : ΛX.obj M ⟶ L ↦ ηX.app M ≫ a))
    (hReflectY : ∀ M L : ringedSiteDerived.{u, wY} RY,
      IsLocallyDerivedRingedIdealComplete.{u, wY} RY IY ιY L →
      Function.Bijective (fun a : ΛY.obj M ⟶ L ↦ ηY.app M ≫ a)) :
    (∀ M : ringedSiteDerived.{u, wX} RX,
      IsLocallyDerivedRingedIdealComplete.{u, wX} RX IX ιX M →
      IsLocallyDerivedRingedIdealComplete.{u, wY} RY IY ιY (Rf.obj M)) ∧
    ∃ γ : Rf ⋙ ΛY ≅ ΛX ⋙ Rf,
      (∀ M : ringedSiteDerived.{u, wX} RX,
        ηY.app (Rf.obj M) ≫ γ.hom.app M = Rf.map (ηX.app M)) ∧
      ∀ (M : ringedSiteDerived.{u, wX} RX) (a : ΛY.obj (Rf.obj M) ⟶ Rf.obj (ΛX.obj M)),
        ηY.app (Rf.obj M) ≫ a = Rf.map (ηX.app M) → a = γ.hom.app M
```

The backward definitional-equality options are also scoped to individual proofs.
The original global instance attribute remains verbatim. The private isomorphism
invariance helper caches its sheaf-composition instance as a private binder.
There is no new global attribute or instance.

## Users

`tools/downstream.py --uses ringedPushforward_completion` finds no use outside
the declaration's own module; it lists 817 transitive importers. Their visible
signatures, imports and instance environment are unchanged. The single direct
importer is included below. No consumer adaptation is required or delivered.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.RingedPushforwardCompletion | X5 | Local elaboration only; original public signature unchanged. |
| Sheaf.Paper.PbcScalarExtension | unclaimed | Unchanged; private import and all visible declarations remain compatible. |

## Status

landed 20261020T211858-L-3513524 2026-10-20 (merge of deliver/X5/Sheaf.Paper.RingedPushforwardCompletion)
