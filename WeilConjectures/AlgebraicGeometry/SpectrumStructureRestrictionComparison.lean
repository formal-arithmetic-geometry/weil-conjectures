/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.KoszulOpenSystem
public import WeilConjectures.AlgebraicGeometry.DerivedTensorAugmentation
public import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
import all WeilConjectures.AlgebraicGeometry.SchemeIsoDerivedLocalizations
import WeilConjectures.AlgebraicGeometry.SchemeIsoDerivedRestrictionSquare
import Mathlib.CategoryTheory.Adjunction.Unique

/-! # Structure and restriction comparisons for a spectrum presentation

## References

* [Stacks Project, Tag 08DC](https://stacks.math.columbia.edu/tag/08DC)
-/

@[expose] public section

universe u w
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
namespace AlgebraicGeometry.Scheme

attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxSize 512 in
set_option maxHeartbeats 1000000 in
-- The derived localization and full restriction comparisons require extra heartbeats.
/-- Isomorphism transport identifies the spectrum structure complex and the full
restriction functor, including transport from localized sites to open subschemes. -/
theorem exists_spectrum_structure_restriction_comparison
    (A : Type u) [CommRing A] (X : Scheme.{u}) (s : Spec (.of A) ≅ X)
    (U : X.Opens) (V : (Spec (.of A)).Opens) (hV : s.hom ⁻¹ᵁ U = V)
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))]
    [∀ V : (Spec (.of A)).Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings (Spec (.of A)).toRingedSpace).over V))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ V : X.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over V))]
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))]
    (e : schemeDerivedCategory (Spec (.of A)) ≌ schemeDerivedCategory X)
    (he : DerivedCategory.Q ⋙ e.functor ≅
      (@Functor.mapHomologicalComplex ℤ
        (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) _ _ _ _
        (SheafOfModules.pushforward s.hom.toRingCatSheafHom)
        ⟨fun _ _ ↦ rfl⟩ (ComplexShape.up ℤ)) ⋙ DerivedCategory.Q) :
    letI := SheafOfModules.monoidalCategory X.sheaf
    letI := (SheafOfModules.tensorClosed X.sheaf).1.some
    let T := HomologicalComplex.tensorUnit
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) (ComplexShape.up ℤ)
    ∃ hV : HasDerivedCategory.{w}
        (SheafOfModules.{u} (moduleRings V.toScheme.toRingedSpace)),
      letI := hV
      ∃ G : DerivedCategory (SheafOfModules.{u} (moduleRings V.toScheme.toRingedSpace)) ≌
        DerivedCategory (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)),
        Nonempty (e.functor.obj (koszulOpenStructure A) ≅ DerivedCategory.Q.obj T) ∧
        Nonempty (e.functor ⋙
          ((SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U) ⋙
            Equivalence.functor
              (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
              (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
              (Modules.overEquiv U)).mapDerivedCategory ≅
          ((SheafOfModules.overFunctor.{u} (moduleRings (Spec (.of A)).toRingedSpace) V) ⋙
            Equivalence.functor
              (C := SheafOfModules.{u}
                ((moduleRings (Spec (.of A)).toRingedSpace).over V))
              (D := SheafOfModules.{u} (moduleRings V.toScheme.toRingedSpace))
              (Modules.overEquiv V)).mapDerivedCategory ⋙ G.functor) := by
  classical
  subst V
  let := SheafOfModules.monoidalCategory X.sheaf
  let := (SheafOfModules.tensorClosed X.sheaf).1.some
  let V := s.hom ⁻¹ᵁ U
  let EV : SheafOfModules.{u} ((moduleRings (Spec (.of A)).toRingedSpace).over V) ≌
      SheafOfModules.{u} (moduleRings V.toScheme.toRingedSpace) := Modules.overEquiv V
  obtain ⟨hLoc⟩ := hasDerivedCategory_of_equivalence EV.symm
  let := hLoc
  let EU : SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U) ≌
      SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace) := Modules.overEquiv U
  have : EV.functor.Additive := Functor.additive_of_preserves_binary_products _
  have : EV.inverse.Additive := Functor.additive_of_preserves_binary_products _
  have : EU.functor.Additive := Functor.additive_of_preserves_binary_products _
  have : EU.inverse.Additive := Functor.additive_of_preserves_binary_products _
  let dV := EV.mapDerivedCategory
  let dU := EU.mapDerivedCategory
  obtain ⟨eO, ⟨hO⟩⟩ := exists_scheme_iso_derived_restriction_square s e he U
  let G := (dV.symm.trans eO).trans dU
  refine ⟨hLoc, G, ?_, ?_⟩
  · let M := SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)
    let N := SheafOfModules.{u} (moduleRings X.toRingedSpace)
    let S := (HomologicalComplex.single M (.up ℤ) 0).obj
      (SheafOfModules.unit (moduleRings (Spec (.of A)).toRingedSpace))
    let k : (((koszulOpenTilde A).mapHomologicalComplex (.up ℤ)).obj
        (((ChainComplex.single₀ (ModuleCat.{u} A)).obj (ModuleCat.of A A)).extend
          ComplexShape.embeddingDownNat)) ≅ S :=
      ((koszulOpenTilde A).mapHomologicalComplex (.up ℤ)).mapIso
        (HomologicalComplex.extendSingleIso ComplexShape.embeddingDownNat
          (ModuleCat.of A A) 0 0 rfl) ≪≫
      (HomologicalComplex.singleMapHomologicalComplex (koszulOpenTilde A) (.up ℤ) 0).app
        (ModuleCat.of A A) ≪≫
      (HomologicalComplex.single M (.up ℤ) 0).mapIso tildeSelf
    let e₀ := moduleIsoEquivalence s
    have : e₀.functor.Additive := Functor.additive_of_preserves_binary_products _
    let b : e₀.functor ≅ Modules.restrictFunctor s.inv :=
      Adjunction.leftAdjointUniq e₀.toAdjunction (Modules.restrictAdjunction s.inv)
    let z : e₀.functor.obj
        (SheafOfModules.unit (moduleRings (Spec (.of A)).toRingedSpace)) ≅
        SheafOfModules.unit (moduleRings X.toRingedSpace) :=
      b.app _ ≪≫ Modules.restrictUnitIso s.inv
    let j : (e₀.functor.mapHomologicalComplex (.up ℤ)).obj S ≅
        HomologicalComplex.tensorUnit N (.up ℤ) :=
      (HomologicalComplex.singleMapHomologicalComplex e₀.functor (.up ℤ) 0).app _ ≪≫
        (HomologicalComplex.single N (.up ℤ) 0).mapIso z
    exact ⟨e.functor.mapIso (DerivedCategory.Q.mapIso k) ≪≫
      he.app S ≪≫ DerivedCategory.Q.mapIso j⟩
  · let LS := SheafOfModules.overFunctor.{u} (moduleRings (Spec (.of A)).toRingedSpace) V
    let LX := SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U
    let b : e.functor ⋙ (LX ⋙ EU.functor).mapDerivedCategory ≅
        (LS.mapDerivedCategory ⋙ eO.functor) ⋙ dU.functor :=
      isoWhiskerLeft _ (Functor.mapDerivedCategoryCompIso LX EU.functor).symm ≪≫
      (Functor.associator _ _ _).symm ≪≫ isoWhiskerRight hO _
    let c : (LS ⋙ EV.functor).mapDerivedCategory ⋙ G.functor ≅
        (LS.mapDerivedCategory ⋙ eO.functor) ⋙ dU.functor :=
      isoWhiskerRight (Functor.mapDerivedCategoryCompIso LS EV.functor).symm G.functor ≪≫
      Functor.associator _ _ _ ≪≫
      isoWhiskerLeft _
        ((Functor.associator dV.functor (dV.inverse ⋙ eO.functor) dU.functor).symm ≪≫
          isoWhiskerRight
            ((Functor.associator dV.functor dV.inverse eO.functor).symm ≪≫
              isoWhiskerRight dV.unitIso.symm eO.functor ≪≫ Functor.leftUnitor _)
            dU.functor) ≪≫
      (Functor.associator _ _ _).symm
    exact ⟨b ≪≫ c.symm⟩

end AlgebraicGeometry.Scheme
