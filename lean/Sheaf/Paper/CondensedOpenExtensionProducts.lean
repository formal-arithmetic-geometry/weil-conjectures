/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A3
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionLowerShriek
import Sheaf.AlgebraicGeometry.ProEtaleOpenExtensionProducts
import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars
import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
import WeilConjectures.CategoryTheory.DerivedCategory.Adjunction

/-!
# Products for the condensed-coefficient extension by zero.

Source: blueprint main-20261015, integral extension by zero
(blueprint: lem-sfb-condensed-open-extension-products).
-/

@[expose] public section

set_option autoImplicit false

attribute [local irreducible] DerivedCategory.monoidalClosed
  CategoryTheory.Mod.monoidalClosed AlgebraicGeometry.ProEtale.upperStarFromPoint

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open AlgebraicGeometry.Scheme
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

universe v₁ v₂ v₁' v₂' w₁ w₂

private theorem preservesLimitsOtherDerived
    {C : Type v₁} [Category.{v₂} C] [Abelian C] [HasDerivedCategory.{w₁} C]
    {D : Type v₁'} [Category.{v₂'} D] [Abelian D] [HasDerivedCategory.{w₂} D]
    (hC : ULift.{0} (HasDerivedCategory.{max v₁ v₂} C))
    (hD : ULift.{0} (HasDerivedCategory.{max v₁' v₂'} D))
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (I : Type (u + 1))
    (h : letI := hC.down; letI := hD.down;
      PreservesLimitsOfShape (Discrete I) F.mapDerivedCategory) :
    PreservesLimitsOfShape (Discrete I) F.mapDerivedCategory := by
  let QC := DerivedCategory.Q (C := C)
  let QD := DerivedCategory.Q (C := D)
  let QC' := @DerivedCategory.Q C _ _ hC.down
  let QD' := @DerivedCategory.Q D _ _ hD.down
  let WC := HomologicalComplex.quasiIso C (.up ℤ)
  let WD := HomologicalComplex.quasiIso D (.up ℤ)
  let eC := Localization.uniq QC QC' WC
  let eD := Localization.uniq QD QD' WD
  let F' := letI := hC.down; letI := hD.down; F.mapDerivedCategory
  have : PreservesLimitsOfShape (Discrete I) F' := h
  let a : QC ⋙ (eC.functor ⋙ F') ≅ F.mapHomologicalComplex (.up ℤ) ⋙ QD' :=
    (Functor.associator _ _ _).symm ≪≫
      isoWhiskerRight (Localization.compUniqFunctor QC QC' WC) F' ≪≫
      (letI := hC.down; letI := hD.down; F.mapDerivedCategoryFactors)
  let b : QC ⋙ (F.mapDerivedCategory ⋙ eD.functor) ≅
      F.mapHomologicalComplex (.up ℤ) ⋙ QD' :=
    (Functor.associator _ _ _).symm ≪≫
      isoWhiskerRight F.mapDerivedCategoryFactors eD.functor ≪≫
      Functor.associator _ _ _ ≪≫
      isoWhiskerLeft _ (Localization.compUniqFunctor QD QD' WD)
  let : Localization.Lifting QC WC (F.mapHomologicalComplex (.up ℤ) ⋙ QD')
      (eC.functor ⋙ F') := ⟨a⟩
  let : Localization.Lifting QC WC (F.mapHomologicalComplex (.up ℤ) ⋙ QD')
      (F.mapDerivedCategory ⋙ eD.functor) := ⟨b⟩
  let e := Localization.liftNatIso QC WC
    (F.mapHomologicalComplex (.up ℤ) ⋙ QD')
    (F.mapHomologicalComplex (.up ℤ) ⋙ QD')
    (eC.functor ⋙ F') (F.mapDerivedCategory ⋙ eD.functor) (Iso.refl _)
  have : PreservesLimitsOfShape (Discrete I) (F.mapDerivedCategory ⋙ eD.functor) :=
    preservesLimitsOfShape_of_natIso e
  exact preservesLimitsOfShape_of_reflects_of_preserves F.mapDerivedCategory eD.functor

/-- Products for the condensed-coefficient extension by zero.
Source: blueprint main-20261015, sk-cor-int-compactness-ii-extension-zero.proof.md,
proof (1), sums, products, and arbitrary limits; Stacks Tag 09BP.

Proof: internal modules form a Grothendieck abelian category. Resolve a family by
K-injectives; its termwise product is K-injective, so localization gives a product
in the derived category. This proves existence for every family, including the empty
family. Take the reduced closed complement of j. Apply
proEtale_openExtension_products_derivedLimits to B = condensedRingObj Λ X.
The existing linearOpenImmersionLowerShriek is its ringSheafOpenExtension.
The coefficient morphism condensedPullbackHom Λ j is invertible; restriction along
it is an exact equivalence and its termwise derived functor preserves products.
The composition isomorphism mapDerivedCategoryCompIso identifies the recorded
condensed open extension with that restriction followed by the linear extension.
Transport product preservation across this isomorphism.
(blueprint: lem-sfb-condensed-open-extension-products). -/
theorem condensedOpenExtensionProducts
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {U X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j] :
    HasProducts.{u + 1} (DerivedCategory
      (Mod (Sheaf (ProEt.topology U) Ab.{u + 1}) (condensedRingObj Λ U))) ∧
    (∀ I : Type (u + 1), PreservesLimitsOfShape (Discrete I)
      (openImmersionLowerShriek Λ j).mapDerivedCategory)  := by
  classical
  refine ⟨?_, ?_⟩
  · intro I
    infer_instance
  · intro I
    let T : TopologicalSpace.Closeds X := ⟨(Set.range j)ᶜ,
      (j.isOpenEmbedding.isOpen_range).isClosed_compl⟩
    let i := (Scheme.IdealSheafData.vanishingIdeal T).subschemeι
    have hi : IsClosedImmersion i := inferInstance
    have hU : Set.range j = (Set.range i)ᶜ := by
      simp [i, T]
    have hp := (proEtale_openExtension_products_derivedLimits i j hU
      (condensedRingObj Λ X)).2.1 I
    have hlinear : PreservesLimitsOfShape (Discrete I)
        (linearOpenImmersionLowerShriek Λ j).mapDerivedCategory :=
      preservesLimitsOtherDerived
        ⟨HasDerivedCategory.standard _⟩
        ⟨HasDerivedCategory.standard _⟩ (linearOpenImmersionLowerShriek Λ j) I hp
    let R : Mod (Sheaf (ProEt.topology U) Ab.{u + 1}) (condensedRingObj Λ U) ⥤
        Mod (Sheaf (ProEt.topology U) Ab.{u + 1})
          ((AlgebraicGeometry.ProEtale.upperStar Ab.{u + 1} j).obj (condensedRingObj Λ X)) :=
      Mod.comap (condensedPullbackHom Λ j)
    let e := Mod.comapEquivalenceOfIsIso (condensedPullbackHom Λ j)
    have : e.symm.functor.Additive := inferInstanceAs
      (Mod.comap (asIso (condensedPullbackHom Λ j)).inv).Additive
    have : e.symm.inverse.Additive := inferInstanceAs R.Additive
    have : R.mapDerivedCategory.IsRightAdjoint :=
      e.symm.toAdjunction.mapDerivedCategoryAdjunction.isRightAdjoint
    exact preservesLimitsOfShape_of_natIso
      (Functor.mapDerivedCategoryCompIso R (linearOpenImmersionLowerShriek Λ j)).symm

end AlgebraicGeometry.ProEtale.CondensedRing
