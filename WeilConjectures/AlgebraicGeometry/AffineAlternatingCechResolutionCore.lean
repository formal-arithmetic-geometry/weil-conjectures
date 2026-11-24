/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.AlgebraicGeometry.AffineAlternatingCechModel
public import WeilConjectures.AlgebraicGeometry.DerivedBaseChangeUnitCompatibility
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import WeilConjectures.AlgebraicGeometry.AffineAlternatingCechAugmentedConstruction
import WeilConjectures.AlgebraicGeometry.AffineOpenPushforwardPullbackAcyclic
import WeilConjectures.AlgebraicGeometry.AffineOpenPushforwardAcyclic
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusHomology
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u w
open CategoryTheory Limits
namespace AlgebraicGeometry
noncomputable section

private theorem unit_isIso_of_acyclic
    {Y Z : Scheme.{u}} (f : Y ⟶ Z)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    (K : CochainComplex Y.Modules ℤ) [K.IsStrictlyGE 0]
    (hK : ∀ n, (RingedSpace.moduleDirectImage f.toLRSHom.toShHom).rightAcyclic
      (K.X n)) :
    IsIso ((RingedSpace.moduleDirectImage f.toLRSHom.toShHom).rightDerivedFunctorUnit.app
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K)) := by
  let F := RingedSpace.moduleDirectImage f.toLRSHom.toShHom
  have : PreservesFiniteLimits F := by
    change PreservesFiniteLimits (Scheme.Modules.pushforward f)
    have := (Scheme.Modules.pullbackPushforwardAdjunction f).rightAdjoint_preservesLimits.{0, 0}
    infer_instance
  let L : CochainComplex.Plus Y.Modules := ⟨K, 0, inferInstance⟩
  let H := (HomotopyCategory.Plus.quotient Y.Modules).obj L
  have hunit : IsIso (F.rightDerivedFunctorPlusUnith.app H) :=
    F.isIso_rightDerivedFunctorPlusUnit_app_of_rightAcyclic L hK
  have he : F.rightDerivedFunctorPlusιUnit.app H ≫
      F.rightDerivedFunctorPlusCompatibility.hom.app (DerivedCategory.Plus.Qh.obj H) =
      F.ιRightDerivedFunctorUnit.app H := by
    simp [Functor.rightDerivedFunctorPlusCompatibility]
  have : IsIso (F.ιRightDerivedFunctorUnit.app H) := by
    rw [← he]
    dsimp only [Functor.rightDerivedFunctorPlusιUnit, Functor.whiskerRight_app]
    infer_instance
  exact this

set_option linter.unusedVariables false in
/-- Core alternating Cech resolution data and the four comparison isomorphisms.
(Stacks, Tags 02KG and 02KH). -/
theorem affineAlternatingCech_resolution_core
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {A B : CommRingCat.{u}} {X : Scheme.{u}} (f : X ⟶ Spec A)
    [QuasiCompact f] [IsSeparated f] (g : Spec B ⟶ Spec A)
    {r : ℕ} (U : Fin r → X.Opens) (hU : iSup U = ⊤)
    (haffine : ∀ i, IsAffineOpen (U i))
    [(Scheme.Modules.tensorPullback g).Additive]
    [(Scheme.Modules.tensorPullback (pullback.fst f g)).Additive]
    (G : X.Modules) [SheafOfModules.IsQuasicoherent.{u} G] :
    ∃ (D : HomotopyCategory
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) (ComplexShape.up ℤ))
      (a : (HomotopyCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj G ⟶ D)
      (q : ((Scheme.Modules.pushforward f).mapHomotopyCategory
          (ComplexShape.up ℤ)).obj D ≅
        (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
          (affineAlternatingCechModel f U G)),
      IsIso (DerivedCategory.Qh.map a) ∧
      IsIso ((DerivedCategory.Qh (C := SheafOfModules.{u}
        (moduleRings (pullback f g).toRingedSpace))).map
        (((Scheme.Modules.tensorPullback (pullback.fst f g)).mapHomotopyCategory
          (ComplexShape.up ℤ)).map a)) ∧
      IsIso ((RingedSpace.moduleDirectImage f.toLRSHom.toShHom).rightDerivedFunctorUnit.app D) ∧
      IsIso ((RingedSpace.moduleDirectImage
        (pullback.snd f g).toLRSHom.toShHom).rightDerivedFunctorUnit.app
          (((Scheme.Modules.tensorPullback (pullback.fst f g)).mapHomotopyCategory
            (ComplexShape.up ℤ)).obj D)) ∧
      (∃ C : CochainComplex
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ,
        Nonempty (D ≅ (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj C) ∧
        ∀ k : ℤ, ∃ (n : ℕ) (W : Fin n → X.Opens),
          (∀ j, IsAffineOpen (W j)) ∧
          Nonempty (C.X k ≅ ∏ᶜ fun j : Fin n ↦
            (Scheme.Modules.pushforward (W j).ι).obj (G.restrict (W j).ι))) := by
  obtain ⟨C, ε, ⟨q⟩, hε, hpε, hterms⟩ :=
    exists_affineAlternatingCech_augmented_construction f g U hU haffine G
  let : HasDerivedCategory.{w} X.Modules := inferInstanceAs
    (HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace)))
  let : HasDerivedCategory.{w} (pullback f g).Modules := inferInstanceAs
    (HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings (pullback f g).toRingedSpace)))
  let K := C.extend ComplexShape.embeddingUpNat
  let P := Scheme.Modules.tensorPullback (pullback.fst f g)
  let F := RingedSpace.moduleDirectImage f.toLRSHom.toShHom
  let F' := RingedSpace.moduleDirectImage (pullback.snd f g).toLRSHom.toShHom
  let e := HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat G 0 0 rfl
  let b := e.inv ≫ HomologicalComplex.extendMap ε ComplexShape.embeddingUpNat
  let D := (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K
  let a := (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map b
  have : QuasiIso ε := hε
  have : QuasiIso (HomologicalComplex.extendMap ε ComplexShape.embeddingUpNat) :=
    (HomologicalComplex.quasiIso_extendMap_iff ε ComplexShape.embeddingUpNat).2 hε
  have : QuasiIso b := inferInstance
  have : QuasiIso ((P.mapHomologicalComplex (ComplexShape.up ℤ)).map
      (HomologicalComplex.extendMap ε ComplexShape.embeddingUpNat)) := hpε
  have : QuasiIso ((P.mapHomologicalComplex (ComplexShape.up ℤ)).map b) := by
    dsimp only [b]
    rw [Functor.map_comp]
    infer_instance
  have hC : ∀ k, F.rightAcyclic (C.X k) := by
    intro k
    obtain ⟨n, W, hW, ⟨eW⟩⟩ := hterms k
    apply F.rightAcyclic.prop_of_iso eW.symm
    have : F.rightAcyclic.IsClosedUnderFiniteProducts :=
      ObjectProperty.IsClosedUnderFiniteProducts.mk'
    apply F.rightAcyclic.prop_product
    intro j
    exact affine_open_pushforward_rightAcyclic f (W j) (hW j) G
  have hpC : ∀ k, F'.rightAcyclic (P.obj (C.X k)) := by
    intro k
    obtain ⟨n, W, hW, ⟨eW⟩⟩ := hterms k
    let T := fun j : Fin n ↦
      (Scheme.Modules.pushforward (W j).ι).obj (G.restrict (W j).ι)
    have : PreservesLimitsOfShape (Discrete (Fin n)) P := inferInstance
    apply F'.rightAcyclic.prop_of_iso
      ((P.mapIso eW) ≪≫ PreservesProduct.iso P T).symm
    have : F'.rightAcyclic.IsClosedUnderFiniteProducts :=
      ObjectProperty.IsClosedUnderFiniteProducts.mk'
    apply F'.rightAcyclic.prop_product
    intro j
    exact affine_open_pushforward_pullback_rightAcyclic f g (W j) (hW j) G
  have hK : ∀ k, F.rightAcyclic (K.X k) :=
    HomologicalComplex.prop_extend_X _ ComplexShape.embeddingUpNat hC
  let Z : X.Modules := HasZeroObject.zero.choose
  have hZ : IsZero Z := HasZeroObject.zero.choose_spec
  have : ObjectProperty.ContainsZero (F'.rightAcyclic.inverseImage P) :=
    ⟨⟨Z, hZ, F'.rightAcyclic.prop_of_isZero
      (Functor.map_isZero P (hZ))⟩⟩
  have hpK : ∀ k, F'.rightAcyclic
      (((P.mapHomologicalComplex (ComplexShape.up ℤ)).obj K).X k) := by
    intro k
    exact HomologicalComplex.prop_extend_X
      (F'.rightAcyclic.inverseImage P) ComplexShape.embeddingUpNat hpC k
  refine ⟨D, a, ((Scheme.Modules.pushforward f).mapHomotopyCategoryFactors
      (ComplexShape.up ℤ)).app K ≪≫
      (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).mapIso q, ?_, ?_, ?_, ?_, ?_⟩
  · exact Localization.inverts DerivedCategory.Qh
      (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ)) _
      ((HomotopyCategory.quotient_map_mem_quasiIso_iff b).2
        (show QuasiIso b from inferInstance))
  · change IsIso (DerivedCategory.Qh.map
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
        ((P.mapHomologicalComplex (ComplexShape.up ℤ)).map b)))
    exact Localization.inverts DerivedCategory.Qh
      (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ)) _
      ((HomotopyCategory.quotient_map_mem_quasiIso_iff _).2
        (show QuasiIso ((P.mapHomologicalComplex (ComplexShape.up ℤ)).map b) from
          inferInstance))
  · exact unit_isIso_of_acyclic f K hK
  · have : CochainComplex.IsStrictlyGE
        ((P.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) 0 :=
      inferInstance
    exact unit_isIso_of_acyclic (pullback.snd f g)
      ((P.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) hpK
  · refine ⟨K, ⟨Iso.refl _⟩, ?_⟩
    intro k
    by_cases hk : 0 ≤ k
    · obtain ⟨n, W, hW, ⟨eW⟩⟩ := hterms k.toNat
      refine ⟨n, W, hW,
        ⟨(C.extendXIso ComplexShape.embeddingUpNat (Int.toNat_of_nonneg hk)) ≪≫ eW⟩⟩
    · refine ⟨0, Fin.elim0, (fun j ↦ Fin.elim0 j),
        ⟨(C.isZero_extend_X ComplexShape.embeddingUpNat k (by
          intro i hi
          change (i : ℤ) = k at hi
          omega)).iso (by
            apply (IsZero.iff_id_eq_zero _).2
            apply Pi.hom_ext
            intro j
            exact Fin.elim0 j)⟩⟩
end
end AlgebraicGeometry
