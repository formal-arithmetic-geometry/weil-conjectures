/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedTensorStructure
public import WeilConjectures.AlgebraicGeometry.DerivedPullback
public import WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
import WeilConjectures.AlgebraicGeometry.DerivedDirectImageCompositionUnbounded
import WeilConjectures.AlgebraicGeometry.DerivedAdjoint
import WeilConjectures.AlgebraicGeometry.DerivedPullbackAcrossUniversesMonoidalAdjunction
import Mathlib.CategoryTheory.Adjunction.Mates

/-! # Functor comparisons across a scheme-isomorphism square

## References

* [Stacks Project, Tag 08EU](https://stacks.math.columbia.edu/tag/08EU)
* [Stacks Project, Tag 06YI](https://stacks.math.columbia.edu/tag/06YI)
* [Stacks Project, Tag 079V](https://stacks.math.columbia.edu/tag/079V)
-/

@[expose] public section

universe u w w'
open CategoryTheory MonoidalCategory
namespace AlgebraicGeometry
set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false in
private noncomputable def moduleIsoEquivalence {X Y : Scheme.{u}} (s : X ≅ Y) :
    SheafOfModules.{u} (moduleRings X.toRingedSpace) ≌
      SheafOfModules.{u} (moduleRings Y.toRingedSpace) :=
  CategoryTheory.Equivalence.mk (SheafOfModules.pushforward s.hom.toRingCatSheafHom)
    (SheafOfModules.pushforward s.inv.toRingCatSheafHom)
    ((Scheme.Modules.pushforwardComp s.hom s.inv ≪≫
      Scheme.Modules.pushforwardCongr s.hom_inv_id ≪≫ Scheme.Modules.pushforwardId X).symm)
    (Scheme.Modules.pushforwardComp s.inv s.hom ≪≫
      Scheme.Modules.pushforwardCongr s.inv_hom_id ≪≫ Scheme.Modules.pushforwardId Y)

set_option backward.isDefEq.respectTransparency false in
private theorem iso_directImage {X Y : Scheme.{u}} (s : X ≅ Y)
    [HasDerivedCategory.{w'} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (a : schemeDerivedCategory X ≌ schemeDerivedCategory Y)
    (ha : DerivedCategory.Q ⋙ a.functor ≅
      (@Functor.mapHomologicalComplex ℤ
        (SheafOfModules.{u} (moduleRings X.toRingedSpace))
        (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) _ _ _ _
        (SheafOfModules.pushforward s.hom.toRingCatSheafHom)
        ⟨fun _ _ ↦ rfl⟩ (ComplexShape.up ℤ)) ⋙ DerivedCategory.Q) :
    Nonempty (a.functor ≅ schemeDerivedDirectImage s.hom) := by
  let F := (moduleIsoEquivalence s).functor
  have : F.IsEquivalence := (moduleIsoEquivalence s).isEquivalence_functor
  have : F.Additive := Functor.additive_of_preserves_binary_products F
  let W := HomologicalComplex.quasiIso
    (SheafOfModules.{u} (moduleRings X.toRingedSpace)) (ComplexShape.up ℤ)
  let G := F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q
  let : Localization.Lifting DerivedCategory.Q W G a.functor := ⟨ha⟩
  exact ⟨Localization.liftNatIso DerivedCategory.Q W G G a.functor
    F.mapDerivedCategory (Iso.refl G) ≪≫
      F.rightDerivedFunctorIsoMapDerivedCategory.symm⟩

set_option backward.isDefEq.respectTransparency false in
private theorem iso_tensor {X Y : Scheme.{u}} (s : X ≅ Y)
    [HasDerivedCategory.{w'} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (a : schemeDerivedCategory X ≌ schemeDerivedCategory Y)
    (ha : DerivedCategory.Q ⋙ a.functor ≅
      (@Functor.mapHomologicalComplex ℤ
        (SheafOfModules.{u} (moduleRings X.toRingedSpace))
        (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) _ _ _ _
        (SheafOfModules.pushforward s.hom.toRingCatSheafHom)
        ⟨fun _ _ ↦ rfl⟩ (ComplexShape.up ℤ)) ⋙ DerivedCategory.Q) :
    Nonempty (tensor (schemeDerivedCategory X) ⋙ a.functor ≅
      a.functor.prod a.functor ⋙ tensor (schemeDerivedCategory Y)) := by
  obtain ⟨e⟩ := iso_directImage s a ha
  obtain ⟨m, ⟨adj⟩⟩ := exists_derivedPullbackAcrossUniverses_monoidal_adjunction s.hom
  let : (derivedPullbackAcrossUniverses s.hom).Monoidal := m.toMonoidal
  let adj' : derivedPullbackAcrossUniverses s.hom ⊣ a.functor :=
    adj.ofNatIsoRight e.symm
  let E := adj'.toEquivalence
  let : E.functor.Monoidal := by
    change (derivedPullbackAcrossUniverses s.hom).Monoidal
    infer_instance
  let : a.functor.Monoidal := E.inverseMonoidal
  exact ⟨(Functor.Monoidal.μNatIso a.functor).symm⟩

private theorem pullback_comparison
    {C C' D D' : Type*} [Category C] [Category C'] [Category D] [Category D']
    (a : C' ≌ C) (b : D' ≌ D)
    {L : C ⥤ D} {R : D ⥤ C} {L' : C' ⥤ D'} {R' : D' ⥤ C'}
    (adj : L ⊣ R) (adj' : L' ⊣ R')
    (β : R' ⋙ a.functor ≅ b.functor ⋙ R) :
    Nonempty (a.functor ⋙ L ≅ L' ⋙ b.functor) := by
  let δ : L ⋙ b.inverse ≅ a.inverse ⋙ L' :=
    (conjugateIsoEquiv (a.symm.toAdjunction.comp adj')
      (adj.comp b.symm.toAdjunction)).symm β
  exact ⟨(Functor.rightUnitor _).symm ≪≫
    Functor.isoWhiskerLeft _ b.counitIso.symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft a.functor δ ≪≫
        (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight a.unitIso.symm L' ≪≫ Functor.leftUnitor L') b.functor⟩

/-- Tensor, pullback and direct-image comparisons for equivalences induced by
scheme isomorphisms. No adjunction or projection mate is part of this assertion. -/
theorem schemeIso_derived_functor_comparisons
    (X Y X' Y' : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [HasDerivedCategory.{w'} (SheafOfModules.{u} (moduleRings X'.toRingedSpace))]
    [HasDerivedCategory.{w'} (SheafOfModules.{u} (moduleRings Y'.toRingedSpace))]
    (f : X ⟶ Y) (g : X' ⟶ Y') (eX : X' ≅ X) (eY : Y' ≅ Y)
    (hcomm : g ≫ eY.hom = eX.hom ≫ f)
    (a : schemeDerivedCategory Y' ≌ schemeDerivedCategory Y)
    (b : schemeDerivedCategory X' ≌ schemeDerivedCategory X)
    (ha : DerivedCategory.Q ⋙ a.functor ≅
      (@Functor.mapHomologicalComplex ℤ
        (SheafOfModules.{u} (moduleRings Y'.toRingedSpace))
        (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) _ _ _ _
        (SheafOfModules.pushforward eY.hom.toRingCatSheafHom)
        ⟨fun _ _ ↦ rfl⟩ (ComplexShape.up ℤ)) ⋙ DerivedCategory.Q)
    (hb : DerivedCategory.Q ⋙ b.functor ≅
      (@Functor.mapHomologicalComplex ℤ
        (SheafOfModules.{u} (moduleRings X'.toRingedSpace))
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) _ _ _ _
        (SheafOfModules.pushforward eX.hom.toRingCatSheafHom)
        ⟨fun _ _ ↦ rfl⟩ (ComplexShape.up ℤ)) ⋙ DerivedCategory.Q) :
    Nonempty (tensor (schemeDerivedCategory Y') ⋙ a.functor ≅
      a.functor.prod a.functor ⋙ tensor (schemeDerivedCategory Y)) ∧
    Nonempty (tensor (schemeDerivedCategory X') ⋙ b.functor ≅
      b.functor.prod b.functor ⋙ tensor (schemeDerivedCategory X)) ∧
    Nonempty (a.functor ⋙ derivedPullback f ≅ derivedPullback g ⋙ b.functor) ∧
    Nonempty (schemeDerivedDirectImage g ⋙ a.functor ≅
      b.functor ⋙ schemeDerivedDirectImage f) := by
  obtain ⟨ea⟩ := iso_directImage eY a ha
  obtain ⟨eb⟩ := iso_directImage eX b hb
  obtain ⟨cg⟩ := derivedDirectImageComposition g eY.hom
  obtain ⟨cf⟩ := derivedDirectImageComposition eX.hom f
  let β : schemeDerivedDirectImage g ⋙ a.functor ≅
      b.functor ⋙ schemeDerivedDirectImage f :=
    Functor.isoWhiskerLeft _ ea ≪≫ cg.symm ≪≫
      eqToIso (congrArg (fun k ↦ schemeDerivedDirectImage k) hcomm) ≪≫ cf ≪≫
      Functor.isoWhiskerRight eb.symm _
  obtain ⟨adjf⟩ := nonempty_derivedPullbackAdjunction f
  obtain ⟨adjg⟩ := nonempty_derivedPullbackAdjunction g
  exact ⟨iso_tensor eY a ha, iso_tensor eX b hb,
    pullback_comparison a b adjf adjg β, ⟨β⟩⟩

end AlgebraicGeometry
