/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekProjection
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.FlatModuleCat
public import WeilConjectures.CategoryTheory.Sites.FlatLocalRelations

import Sheaf.CategoryTheory.DerivedMonoidalClosed
import WeilConjectures.CategoryTheory.DerivedModuleFreeGeneration
import WeilConjectures.CategoryTheory.DerivedCategory.Coproducts
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.ShiftComparison
import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapShift
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Unit
import WeilConjectures.Mathlib.CategoryTheory.Triangulated.Generators
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Monoidal
import WeilConjectures.Algebra.Homology.HomotopyCategory.MapMonoidal
import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapMonoidal
import WeilConjectures.CategoryTheory.Sites.ConstantSheafMonoidal
import WeilConjectures.CategoryTheory.Monoidal.OplaxOfLaxSquare
import Mathlib.CategoryTheory.Triangulated.Adjunction

/-!
# Projection on constant coefficients for coproduct-preserving compact support

Source: Stacks Project, Cohomology on Sites, projection formula and generation by
free coefficient complexes.
(blueprint: lem-exc-proetale-constant-support-projection)

Proof: compare the two exact coproduct-preserving coefficient functors, check the
projection on the tensor unit, and extend across the localizing generators of the derived
module category.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory Abelian Limits MonoidalCategory
open scoped CategoryTheory.Functor
universe uC uD

section ExactTensorComparison

variable {C : Type uC} [Category.{u + 1} C] [Abelian C]
  [IsGrothendieckAbelian.{u + 1} C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
  [Abelian.HasFunctorialFlatResolution C]
  {D : Type uD} [Category.{u + 1} D] [Abelian D]
  [IsGrothendieckAbelian.{u + 1} D]
  [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalClosed D] [BraidedCategory D]
  [Abelian.HasFunctorialFlatResolution D]

variable (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [F.PreservesFlat] [F.IsLeftAdjoint] [F.Monoidal]

omit [Abelian.HasFunctorialFlatResolution D] [PreservesFiniteLimits F]
  [PreservesFiniteColimits F] [F.Monoidal] in
private theorem commonFlat_iso_aux
    (K : DerivedCategory C) :
    ∃ P : HomotopyCategory C (.up ℤ),
      (HomotopyCategory.quasiIso C (.up ℤ)).kFlat P ∧ F.kFlatMap P ∧
        Nonempty (K ≅ DerivedCategory.Qh.obj P) := by
  let resolution := (inferInstance : Abelian.HasFunctorialFlatResolution C).some.reduced
  let K₀ := DerivedCategory.Q.objPreimage K
  refine ⟨(HomotopyCategory.quotient _ _).obj (resolution.resolutionFunctor.obj K₀),
    (HomotopyCategory.kFlat_quotient_obj_iff _).mpr
      (resolution.kFlat_resolutionFunctor_obj ObjectProperty.flat.essImage_ι_le K₀),
    F.kFlatMap_quotient_obj_resolutionFunctor_obj resolution K₀, ?_⟩
  exact ⟨(DerivedCategory.Q.objObjPreimageIso K).symm ≪≫
    (asIso (DerivedCategory.Q.map (resolution.resolutionNatTrans.app K₀))).symm⟩

private noncomputable def derivedUnitComparison :
    F.leftDerivedFunctor.obj (𝟙_ _) ⟶ 𝟙_ (DerivedCategory D) := by
  have := DerivedCategory.isIso_ε_Qh.{u + 1, u + 1, uD} D
  exact F.leftDerivedFunctor.map (Functor.LaxMonoidal.ε DerivedCategory.Qh) ≫
    F.leftDerivedFunctorCounit.app (𝟙_ _) ≫
    DerivedCategory.Qh.map ((HomotopyCategory.quotient D (.up ℤ)).map
      F.mapCochainComplexεIso.inv) ≫
    inv (Functor.LaxMonoidal.ε DerivedCategory.Qh)

omit [F.PreservesFlat] [F.IsLeftAdjoint] in
private theorem derivedUnitComparison_isIso : IsIso (derivedUnitComparison F) := by
  have := DerivedCategory.isIso_ε_Qh.{u + 1, u + 1, uC} C
  have := DerivedCategory.isIso_ε_Qh.{u + 1, u + 1, uD} D
  unfold derivedUnitComparison
  infer_instance

private theorem derivedComparison_rightUnit (K : DerivedCategory C) :
    (F.leftDerivedTensorComparison.app K).app (𝟙_ _) ≫
      F.leftDerivedFunctor.obj K ◁ derivedUnitComparison F ≫
        (ρ_ (F.leftDerivedFunctor.obj K)).hom = F.leftDerivedFunctor.map (ρ_ K).hom := by
  generalize hcomp : F.leftDerivedTensorComparison = φ
  have := DerivedCategory.isIso_ε_Qh.{u + 1, u + 1, uD} D
  obtain ⟨P, _, _, ⟨e⟩⟩ := commonFlat_iso_aux F K
  have := Functor.LaxMonoidal.isIso_μ_tensorUnit_right DerivedCategory.Qh
    ((F.mapHomotopyCategory (.up ℤ)).obj P)
  have h : (ρ_ (F.leftDerivedFunctor.obj K)).inv =
      F.leftDerivedFunctor.map (ρ_ K).inv ≫ (φ.app K).app (𝟙_ _) ≫
        F.leftDerivedFunctor.obj K ◁ derivedUnitComparison F := by
    apply Functor.OplaxMonoidal.oplax_right_unitality_of_iso φ e.symm
    have hδ := F.leftDerivedTensorComparison_app_app_comp_tensorHom
    rw [hcomp] at hδ
    have hsource := Functor.OplaxMonoidal.oplax_right_unitality_of_lax_square
      (Q₁ := DerivedCategory.Qh) (Q₂ := DerivedCategory.Qh)
      (F := F.mapHomotopyCategory (.up ℤ)) φ
      (fun P ↦ F.leftDerivedFunctorCounit.app P)
      (fun _ _ f ↦ F.leftDerivedFunctorCounit.naturality f) hδ P
    simpa only [derivedUnitComparison, Functor.mapHomotopyCategory_η F,
      Functor.mapCochainComplex_η F] using hsource
  apply (cancel_epi (F.leftDerivedFunctor.map (ρ_ K).inv)).mp
  rw [← F.leftDerivedFunctor.map_comp, Iso.inv_hom_id, F.leftDerivedFunctor.map_id]
  simpa only [Category.assoc, Iso.inv_hom_id] using
    congrArg (fun f ↦ f ≫ (ρ_ (F.leftDerivedFunctor.obj K)).hom) h.symm

variable [F.leftDerivedFunctor.CommShift ℤ]
  [NatTrans.CommShift
    (F₁ := DerivedCategory.Qh ⋙ F.leftDerivedFunctor)
    (F₂ := F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    F.leftDerivedFunctorCounit ℤ]

private theorem exactComparison_commShift_aux
    (K : DerivedCategory C) :
    NatTrans.CommShift
      (F₁ := tensorLeft K ⋙ F.leftDerivedFunctor)
      (F₂ := F.leftDerivedFunctor ⋙ tensorLeft (F.leftDerivedFunctor.obj K))
      (F.leftDerivedTensorComparison.app K) ℤ := by
  generalize hcomp : F.leftDerivedTensorComparison = φ
  obtain ⟨P, hP, hFP, ⟨e⟩⟩ := commonFlat_iso_aux F K
  let τP : tensorLeft (DerivedCategory.Qh.obj P) ⋙ F.leftDerivedFunctor ⟶
      F.leftDerivedFunctor ⋙ tensorLeft (F.leftDerivedFunctor.obj (DerivedCategory.Qh.obj P)) :=
    φ.app (DerivedCategory.Qh.obj P)
  have : NatTrans.CommShift τP ℤ := by
    apply DerivedCategory.commShift_of_tensorLeft_fac F F.leftDerivedFunctor
      F.leftDerivedFunctorCounit P hP hFP
    intro M
    have h := F.leftDerivedTensorComparison_app_app_comp_tensorHom P M
    rw [hcomp] at h
    simpa only [τP, Functor.leftDerivedDerivedTensor, Functor.comp_obj,
      DerivedCategory.tensorLeftCounit, Functor.bifunctorCounit₁_app,
      Functor.LaxMonoidal.μNatTrans_app_app,
      MonoidalCategory.tensorHom_def, Category.assoc] using h
  have he : φ.app K =
      Functor.whiskerRight ((curriedTensor _).map e.hom) F.leftDerivedFunctor ≫ τP ≫
        Functor.whiskerLeft F.leftDerivedFunctor
          ((curriedTensor _).map (F.leftDerivedFunctor.map e.inv)) := by
    ext M
    have h := NatTrans.congr_app (φ.naturality e.hom) M
    dsimp [τP] at h ⊢
    rw [← Category.assoc, h, Category.assoc]
    simp [← comp_whiskerRight, ← Functor.map_comp]
  have : NatTrans.CommShift ((curriedTensor (DerivedCategory C)).map e.hom) ℤ :=
    Functor.CommShift₂.commShift_map
      (G := curriedTensor (DerivedCategory C)) (h := .int) e.hom
  have : NatTrans.CommShift
      ((curriedTensor (DerivedCategory D)).map (F.leftDerivedFunctor.map e.inv)) ℤ :=
    Functor.CommShift₂.commShift_map
      (G := curriedTensor (DerivedCategory D)) (h := .int) (F.leftDerivedFunctor.map e.inv)
  rw [he]
  infer_instance

end ExactTensorComparison

section ProjectionData

variable {C : Type uC} [Category.{u + 1} C] [Abelian C]
  [IsGrothendieckAbelian.{u + 1} C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
  [Abelian.HasFunctorialFlatResolution C]
  {D : Type uD} [Category.{u + 1} D] [Abelian D]
  [IsGrothendieckAbelian.{u + 1} D]
  [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalClosed D] [BraidedCategory D]
  [Abelian.HasFunctorialFlatResolution D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [F.PreservesFlat] [F.IsLeftAdjoint] [F.Monoidal]

private theorem projection_data_aux
    (R : DerivedCategory D ⥤ DerivedCategory C) (adj : F.leftDerivedFunctor ⊣ R)
    (E : DerivedCategory D) :
    ∃ sL : F.leftDerivedFunctor.CommShift ℤ, letI := sL
      ∃ sR : R.CommShift ℤ, letI := sR
        F.leftDerivedFunctor.IsTriangulated ∧ R.IsTriangulated ∧
        (let τ : tensorLeft (R.obj E) ⟶ (F.leftDerivedFunctor ⋙ tensorLeft E) ⋙ R :=
          (adj.rightAdjointProjectionMap F.leftDerivedTensorComparison).app E
        NatTrans.CommShift τ ℤ ∧ IsIso (τ.app (𝟙_ _))) := by
  generalize he : F.leftDerivedFunctorIsoMapDerivedCategory = e
  let := Functor.CommShift.ofIso e.symm ℤ
  have := Functor.CommShift.ofIso_compatibility
    e.symm ℤ
  have : NatTrans.CommShift e.hom ℤ :=
    inferInstanceAs
      (NatTrans.CommShift e.symm.inv ℤ)
  have : F.leftDerivedFunctor.IsTriangulated :=
    Functor.isTriangulated_of_iso e.symm
  have : NatTrans.CommShift F.leftDerivedFunctorCounit ℤ := by
    have hfac := F.leftDerivedFunctorIsoMapDerivedCategory_hom_fac
    rw [he] at hfac
    rw [← hfac]
    infer_instance
  let := adj.rightAdjointCommShift ℤ
  have := Adjunction.commShift_of_leftAdjoint adj ℤ
  have := Adjunction.isTriangulated_rightAdjoint adj
  have : F.leftDerivedFunctor.IsLeftAdjoint := adj.isLeftAdjoint
  let τ : tensorLeft (R.obj E) ⟶ (F.leftDerivedFunctor ⋙ tensorLeft E) ⋙ R :=
    (adj.rightAdjointProjectionMap F.leftDerivedTensorComparison).app E
  have := exactComparison_commShift_aux F (R.obj E)
  have : NatTrans.CommShift τ ℤ :=
    Adjunction.commShift_rightAdjointProjectionMap_app adj F.leftDerivedTensorComparison E
  have hunit : IsIso (τ.app (𝟙_ _)) := by
    have := derivedUnitComparison_isIso F
    have hη := derivedComparison_rightUnit F
    have h := adj.rightAdjointProjectionMap_rightUnitality
      F.leftDerivedTensorComparison (derivedUnitComparison F) hη E
    let g := R.map (E ◁ derivedUnitComparison F) ≫ R.map (ρ_ E).hom
    have : IsIso g := by dsimp only [g]; infer_instance
    have : IsIso (τ.app (𝟙_ _) ≫ g) := by
      change IsIso (_ ≫ R.map (E ◁ derivedUnitComparison F) ≫ R.map (ρ_ E).hom)
      rw [h]
      infer_instance
    exact IsIso.of_isIso_comp_right (τ.app (𝟙_ _)) g
  exact ⟨inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, hunit⟩

end ProjectionData

section CoefficientGeneration

variable {T : Type uC} [Category.{u + 1} T] [HasZeroObject T] [Preadditive T]
  [HasShift T ℤ] [∀ n : ℤ, (shiftFunctor T n).Additive] [Pretriangulated T]

private theorem coefficient_generation_aux (R : Type (u + 1)) [CommRing R]
    (J : DerivedCategory (ModuleCat.{u + 1} R) ⥤ T)
    [J.CommShift ℤ] [J.IsTriangulated]
    [∀ I : Type (u + 1), PreservesColimitsOfShape (Discrete I) J]
    (F G : T ⥤ T)
    [F.CommShift ℤ] [G.CommShift ℤ] [F.IsTriangulated] [G.IsTriangulated]
    [∀ I : Type (u + 1), PreservesColimitsOfShape (Discrete I) F]
    [∀ I : Type (u + 1), PreservesColimitsOfShape (Discrete I) G]
    (α : F ⟶ G) [NatTrans.CommShift α ℤ] (U : T) (hu : IsIso (α.app U))
    (e₀ : J.obj ((DerivedCategory.singleFunctor (ModuleCat.{u + 1} R) 0).obj
      (ModuleCat.of R (ULift.{0} R))) ≅ U) (M : DerivedCategory (ModuleCat.{u + 1} R)) :
    IsIso (α.app (J.obj M)) := by
  let β := Functor.whiskerLeft J α
  apply derivedModuleFreeGeneration.{u + 1, 0} R M (fun N ↦ IsIso (β.app N))
  · intro n
    exact (NatTrans.isIso_app_iff_of_iso α
      ((J.commShiftIso n).app _ ≪≫ (shiftFunctor _ n).mapIso e₀)).mpr
        ((NatTrans.isIso_app_shift_iff α _ n).mpr hu)
  · intro I N S ι hc hN
    have : IsIso (Functor.whiskerLeft (Discrete.functor N) β) := by
      rw [NatTrans.isIso_iff_isIso_app]
      intro i
      exact hN i.as
    exact isIso_app_coconePt_of_preservesColimit (Discrete.functor N) β (Cofan.mk S ι) hc
  · intro T ht h₁ h₂
    exact NatTrans.isIso_app_obj₃_of_isIso_app_obj₁₂ β ht h₁ h₂
  · intro N P h hP
    have := hP
    exact NatTrans.isIso_app_of_retract β h

end CoefficientGeneration

namespace AlgebraicGeometry
open Scheme
namespace ProEtale

section SupportTensor

variable (A : Type uC) [Category.{u + 1} A] [Abelian A]
  [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] [UpperStarPreservesFlat A]

private noncomputable def supportTensorIso {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) (K : DerivedCategory (Sheaf (ProEt.topology X) A)) :
    (rightDerivedLowerStarDerivedTensorLeftDerivedUpperStar A c.g).obj
        (D((c.i)_!open[A]).obj K) ≅
      (L((f)^*[A]) ⋙ tensorLeft K) ⋙ rightDerivedLowerShriekOfCompactification A c :=
  Functor.isoWhiskerRight
    (Functor.isoWhiskerLeft L((c.g)^*[A])
      ((derivedOpenImmersionLowerShriekProjectionIso A c.i).app K).symm)
    R((c.g)_*[A]) ≪≫
  Functor.isoWhiskerRight
    (Functor.isoWhiskerRight (leftDerivedUpperStarCompactificationIso A c) (tensorLeft K))
    (rightDerivedLowerShriekOfCompactification A c)

@[no_expose] private noncomputable def projectionMate {X Y : Scheme.{u}} (p : X ⟶ Y) :
    derivedTensorRightDerivedLowerStar A p ⟶
      rightDerivedLowerStarDerivedTensorLeftDerivedUpperStar A p :=
  (derivedUpperStarLowerStarAdjunction A p).rightAdjointProjectionMap
    (upperStar A p).leftDerivedTensorComparison

private theorem projectionMap_eq_generic {X Y : Scheme.{u}} (p : X ⟶ Y) :
    rightDerivedLowerStarProjectionMap A p = projectionMate A p := by
  rfl

private theorem proetale_projection_data {X Y : Scheme.{u}} (p : X ⟶ Y)
    (E : DerivedCategory (Sheaf (ProEt.topology X) A)) :
    ∃ sL : (L((p)^*[A])).CommShift ℤ, letI := sL
      ∃ sR : (R((p)_*[A])).CommShift ℤ, letI := sR
        (L((p)^*[A])).IsTriangulated ∧ (R((p)_*[A])).IsTriangulated ∧
        (let τ : tensorLeft (R((p)_*[A]).obj E) ⟶
            (L((p)^*[A]) ⋙ tensorLeft E) ⋙ R((p)_*[A]) := (projectionMate A p).app E
        NatTrans.CommShift τ ℤ ∧ IsIso (τ.app (𝟙_ _))) := by
  exact projection_data_aux (upperStar A p) R((p)_*[A])
    (derivedUpperStarLowerStarAdjunction A p) E

private theorem supportProjection_of_coefficients
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    [∀ I : Type (u + 1), PreservesColimitsOfShape (Discrete I)
      (rightDerivedLowerShriekOfCompactification A c)]
    (Λ : Type (u + 1)) [CommRing Λ]
    (J : DerivedCategory (ModuleCat.{u + 1} Λ) ⥤
      DerivedCategory (Sheaf (ProEt.topology Y) A))
    [J.CommShift ℤ] [J.IsTriangulated]
    [∀ I : Type (u + 1), PreservesColimitsOfShape (Discrete I) J]
    (e₀ : J.obj ((DerivedCategory.singleFunctor (ModuleCat.{u + 1} Λ) 0).obj
      (ModuleCat.of Λ (ULift.{0} Λ))) ≅ 𝟙_ _)
    (K : DerivedCategory (Sheaf (ProEt.topology X) A))
    (M : DerivedCategory (ModuleCat.{u + 1} Λ)) :
    IsIso (((rightDerivedLowerStarProjectionMap A c.g).app
      (D((c.i)_!open[A]).obj K)).app (J.obj M)) := by
  let E := (openImmersionLowerShriek A c.i).mapDerivedCategory.obj K
  let F := tensorLeft (R((c.g)_*[A]).obj E)
  let G := (L((c.g)^*[A]) ⋙ tensorLeft E) ⋙ R((c.g)_*[A])
  let α : F ⟶ G := (projectionMate A c.g).app E
  let e := supportTensorIso A c K
  have htensor (Z : Scheme.{u}) (T : DerivedCategory (Sheaf (ProEt.topology Z) A)) :
      (tensorLeft T).IsLeftAdjoint :=
    DerivedCategory.tensorLeft_isLeftAdjoint_of_hasFunctorialFlatResolution _ T
  have hcopG (I : Type (u + 1)) : PreservesColimitsOfShape (Discrete I) G := by
    have : (L((f)^*[A])).IsLeftAdjoint :=
      (derivedUpperStarLowerStarAdjunction A f).isLeftAdjoint
    have := htensor X K
    have : PreservesColimitsOfShape (Discrete I)
        ((L((f)^*[A]) ⋙ tensorLeft K) ⋙ rightDerivedLowerShriekOfCompactification A c) :=
      inferInstance
    exact preservesColimitsOfShape_of_natIso e.symm
  have hcopF (I : Type (u + 1)) : PreservesColimitsOfShape (Discrete I) F :=
    inferInstanceAs (PreservesColimitsOfShape (Discrete I) (tensorLeft (R((c.g)_*[A]).obj E)))
  obtain ⟨sL, sR, hL, hR, hs, hu⟩ := proetale_projection_data A c.g E
  let := sL
  let := sR
  have := hL
  have := hR
  have : NatTrans.CommShift α ℤ := hs
  have : F.IsTriangulated := inferInstanceAs (tensorLeft (R((c.g)_*[A]).obj E)).IsTriangulated
  have : G.IsTriangulated := inferInstanceAs
    ((L((c.g)^*[A]) ⋙ tensorLeft E) ⋙ R((c.g)_*[A])).IsTriangulated
  have hfinal : IsIso (α.app (J.obj M)) :=
    coefficient_generation_aux Λ J F G α _ hu e₀ M
  have heq := congrArg (fun τ ↦ (τ.app E).app (J.obj M))
    (projectionMap_eq_generic A c.g)
  have hgoal := Eq.mpr (congrArg (fun z ↦ IsIso z) heq) hfinal
  exact hgoal

end SupportTensor

noncomputable instance preservesFiniteLimits_constantSheaf_proetale
    (Y : Scheme.{u}) (R : Type (u + 1)) [CommRing R] :
    PreservesFiniteLimits
      (constantSheaf (ProEt.topology Y) (ModuleCat.{u + 1} R)) := by
  apply comp_preservesFiniteLimits


attribute [-instance] ModuleCat.MonoidalCategory.instBraidedCategory in
@[no_expose] private noncomputable def constantGeneratorIso
    (R₀ : Type (u + 1)) [CommRing R₀] (Y : Scheme.{u}) :
    (constantSheaf (ProEt.topology Y) (ModuleCat.{u + 1} R₀)).mapDerivedCategory.obj
      ((DerivedCategory.singleFunctor (ModuleCat.{u + 1} R₀) 0).obj
        (ModuleCat.of R₀ (ULift.{0} R₀))) ≅
      𝟙_ (DerivedCategory (Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} R₀))) :=
  (Functor.mapDerivedCategorySingleFunctor _ 0).app _ ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso
      ((constantSheaf (ProEt.topology Y) (ModuleCat.{u + 1} R₀)).mapIso
        (ULift.moduleEquiv : ULift.{0} R₀ ≃ₗ[R₀] R₀).toModuleIso ≪≫
        (Functor.Monoidal.εIso (constantSheaf (ProEt.topology Y)
          (ModuleCat.{u + 1} R₀))).symm) ≪≫
    DerivedCategory.singleFunctorObjUnitIso _

attribute [-instance] ModuleCat.MonoidalCategory.instBraidedCategory in
/-- Constant coefficient complexes satisfy compact-support projection.
Source: Stacks Tags 07A4 and 0G7E.
(blueprint: lem-exc-proetale-constant-support-projection)

Proof: the two sides are exact triangulated coproduct-preserving functors of the coefficient
complex. The projection is an isomorphism at the tensor unit; localizing generation by the
regular module extends this to all coefficients. -/
theorem isIso_constantSupportProjection
    (R₀ : Type (u + 1)) [CommRing R₀] [IsNoetherianRing R₀]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    [∀ I : Type (u + 1), PreservesColimitsOfShape (Discrete I)
      (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} R₀) c)]
    (K : DerivedCategory (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} R₀)))
    (M : DerivedCategory (ModuleCat.{u + 1} R₀)) :
    IsIso (((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} R₀) c.g).app
      ((openImmersionLowerShriek (ModuleCat.{u + 1} R₀) c.i).mapDerivedCategory.obj K)).app
        ((constantSheaf (ProEt.topology Y) (ModuleCat.{u + 1} R₀)).mapDerivedCategory.obj M))  := by
  have (I : Type (u + 1)) : PreservesColimitsOfShape (Discrete I)
      (constantSheaf (ProEt.topology Y) (ModuleCat.{u + 1} R₀)).mapDerivedCategory := by
    infer_instance
  exact supportProjection_of_coefficients (ModuleCat.{u + 1} R₀) c R₀
    (constantSheaf (ProEt.topology Y) (ModuleCat.{u + 1} R₀)).mapDerivedCategory
    (constantGeneratorIso R₀ Y) K M

end ProEtale
end AlgebraicGeometry
