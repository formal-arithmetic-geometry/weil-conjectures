/- Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S2 -/
module

public import Sheaf.Paper.StrictScalarTowerAssociator
public import Sheaf.Paper.ConstantScalarTowerMates
import all Sheaf.CategoryTheory.DerivedExactSquareCoherence
import Sheaf.CategoryTheory.DerivedCategory.ExactRestrictionComposition

/-! # Composition of restriction and proper image on constant scalar towers

Source: Stacks 03DA, 0D6E and 0940; strict scalar composition, auxiliary Step 2.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [local irreducible] CategoryTheory.Functor.mapDerivedCategory
  CategoryTheory.Functor.rightDerivedFunctor
universe u v w
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale.StrictTower
namespace WeilConjectures.PurStrictScalar

private theorem unitCompatible_iff_unitNormalized
    {A B C D : Type (v + 1)}
    [Category.{v} A] [Category.{v} B] [Category.{v} C] [Category.{v} D]
    [Abelian A] [Abelian B] [Abelian C] [Abelian D]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]
    [HasDerivedCategory.{w} C] [HasDerivedCategory.{w} D]
    [Abelian.HasKInjectiveResolutions A] [Abelian.HasKInjectiveResolutions C]
    (H : A ⥤ B) (G : C ⥤ D) (V : A ⥤ C) (W : B ⥤ D)
    [H.Additive] [G.Additive] [V.Additive] [W.Additive]
    [PreservesFiniteLimits V] [PreservesFiniteColimits V]
    [PreservesFiniteLimits W] [PreservesFiniteColimits W]
    (α : H ⋙ W ≅ V ⋙ G)
    (δ : H.rightDerivedFunctor ⋙ W.mapDerivedCategory ≅
      V.mapDerivedCategory ⋙ G.rightDerivedFunctor) :
    unitCompatible H G V W α δ ↔
      CategoryTheory.ExactDerivedSquare.unitNormalized H G V W
        V.mapDerivedCategory W.mapDerivedCategory
        V.mapDerivedCategoryFactors W.mapDerivedCategoryFactors α.hom δ.hom := by
  rfl

private theorem normalizedRestriction_composition
    {A₀ A₁ A₂ B₀ B₁ B₂ : Type (v + 1)}
    [Category.{v} A₀] [Category.{v} A₁] [Category.{v} A₂]
    [Category.{v} B₀] [Category.{v} B₁] [Category.{v} B₂]
    [Abelian A₀] [Abelian A₁] [Abelian A₂]
    [Abelian B₀] [Abelian B₁] [Abelian B₂]
    [HasDerivedCategory.{w} A₀] [HasDerivedCategory.{w} A₁]
    [HasDerivedCategory.{w} A₂] [HasDerivedCategory.{w} B₀]
    [HasDerivedCategory.{w} B₁] [HasDerivedCategory.{w} B₂]
    [Abelian.HasKInjectiveResolutions A₀] [Abelian.HasKInjectiveResolutions A₁]
    [Abelian.HasKInjectiveResolutions A₂]
    (H₀ : A₀ ⥤ B₀) (H₁ : A₁ ⥤ B₁) (H₂ : A₂ ⥤ B₂)
    (x₀ : A₀ ⥤ A₁) (x₁ : A₁ ⥤ A₂) (x₂ : A₀ ⥤ A₂)
    (y₀ : B₀ ⥤ B₁) (y₁ : B₁ ⥤ B₂) (y₂ : B₀ ⥤ B₂)
    [H₀.Additive] [H₁.Additive] [H₂.Additive]
    [x₀.Additive] [x₁.Additive] [x₂.Additive]
    [y₀.Additive] [y₁.Additive] [y₂.Additive]
    [PreservesFiniteLimits x₀] [PreservesFiniteColimits x₀]
    [PreservesFiniteLimits x₁] [PreservesFiniteColimits x₁]
    [PreservesFiniteLimits x₂] [PreservesFiniteColimits x₂]
    [PreservesFiniteLimits y₀] [PreservesFiniteColimits y₀]
    [PreservesFiniteLimits y₁] [PreservesFiniteColimits y₁]
    [PreservesFiniteLimits y₂] [PreservesFiniteColimits y₂]
    (c₀ : H₀ ⋙ y₀ ≅ x₀ ⋙ H₁) (c₁ : H₁ ⋙ y₁ ≅ x₁ ⋙ H₂)
    (c₂ : H₀ ⋙ y₂ ≅ x₂ ⋙ H₂)
    (δ₀ : H₀.rightDerivedFunctor ⋙ y₀.mapDerivedCategory ≅
      x₀.mapDerivedCategory ⋙ H₁.rightDerivedFunctor)
    (δ₁ : H₁.rightDerivedFunctor ⋙ y₁.mapDerivedCategory ≅
      x₁.mapDerivedCategory ⋙ H₂.rightDerivedFunctor)
    (δ₂ : H₀.rightDerivedFunctor ⋙ y₂.mapDerivedCategory ≅
      x₂.mapDerivedCategory ⋙ H₂.rightDerivedFunctor)
    (ρZ : x₀ ⋙ x₁ ≅ x₂) (ρW : y₀ ⋙ y₁ ≅ y₂)
    (hn₀ : CategoryTheory.ExactDerivedSquare.unitNormalized H₀ H₁ x₀ y₀
      x₀.mapDerivedCategory y₀.mapDerivedCategory
      x₀.mapDerivedCategoryFactors y₀.mapDerivedCategoryFactors c₀.hom δ₀.hom)
    (hn₁ : CategoryTheory.ExactDerivedSquare.unitNormalized H₁ H₂ x₁ y₁
      x₁.mapDerivedCategory y₁.mapDerivedCategory
      x₁.mapDerivedCategoryFactors y₁.mapDerivedCategoryFactors c₁.hom δ₁.hom)
    (hn₂ : CategoryTheory.ExactDerivedSquare.unitNormalized H₀ H₂ x₂ y₂
      x₂.mapDerivedCategory y₂.mapDerivedCategory
      x₂.mapDerivedCategoryFactors y₂.mapDerivedCategoryFactors c₂.hom δ₂.hom)
    (hc : ∀ N : A₀, ρW.hom.app (H₀.obj N) ≫ c₂.hom.app N =
      y₁.map (c₀.hom.app N) ≫ c₁.hom.app (x₀.obj N) ≫ H₂.map (ρZ.hom.app N))
    (K : DerivedCategory.{w} A₀) :
    y₁.mapDerivedCategory.map (δ₀.hom.app K) ≫
        δ₁.hom.app (x₀.mapDerivedCategory.obj K) ≫
        H₂.rightDerivedFunctor.map
          ((Functor.exactDerivedRestrictionComposition x₀ x₁ x₂ ρZ).hom.app K) =
      (Functor.exactDerivedRestrictionComposition y₀ y₁ y₂ ρW).hom.app
          (H₀.rightDerivedFunctor.obj K) ≫ δ₂.hom.app K := by
  have h := CategoryTheory.ExactDerivedSquare.normalized_naturality
    H₀ H₂ (x₀ ⋙ x₁) (y₀ ⋙ y₁) x₂ y₂
    (x₀.mapDerivedCategory ⋙ x₁.mapDerivedCategory) x₂.mapDerivedCategory
    (y₀.mapDerivedCategory ⋙ y₁.mapDerivedCategory) y₂.mapDerivedCategory
    (Functor.isoWhiskerRight x₀.mapDerivedCategoryFactors x₁.mapDerivedCategory ≪≫
      Functor.isoWhiskerLeft (x₀.mapHomologicalComplex (.up ℤ)) x₁.mapDerivedCategoryFactors)
    x₂.mapDerivedCategoryFactors
    (Functor.isoWhiskerRight y₀.mapDerivedCategoryFactors y₁.mapDerivedCategory ≪≫
      Functor.isoWhiskerLeft (y₀.mapHomologicalComplex (.up ℤ)) y₁.mapDerivedCategoryFactors)
    y₂.mapDerivedCategoryFactors
    (Functor.whiskerRight c₀.hom y₁ ≫ Functor.whiskerLeft x₀ c₁.hom) c₂.hom
    (Functor.whiskerRight δ₀.hom y₁.mapDerivedCategory ≫
      Functor.whiskerLeft x₀.mapDerivedCategory δ₁.hom) δ₂.hom
    (CategoryTheory.ExactDerivedSquare.normalized_comp H₀ H₁ x₀ y₀ H₂ x₁ y₁
      c₀ c₁ δ₀ δ₁ hn₀ hn₁) hn₂ ρZ.hom ρW.hom
    (Functor.exactDerivedRestrictionComposition x₀ x₁ x₂ ρZ).hom
    (Functor.exactDerivedRestrictionComposition y₀ y₁ y₂ ρW).hom
    (fun P ↦ by
      simpa only [Functor.exactDerivedRestrictionComposition,
        Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
        Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app,
        NatIso.mapHomologicalComplex, Category.assoc]
        using Functor.exactDerivedRestrictionComposition_hom_factors x₀ x₁ x₂ ρZ P)
    (fun P ↦ by
      simpa only [Functor.exactDerivedRestrictionComposition,
        Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
        Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app,
        NatIso.mapHomologicalComplex, Category.assoc]
        using Functor.exactDerivedRestrictionComposition_hom_factors y₀ y₁ y₂ ρW P)
    (fun N ↦ by
      simpa only [NatTrans.comp_app, Functor.whiskerRight_app,
        Functor.whiskerLeft_app, Functor.comp_map, Category.assoc] using hc N)
  have hh := NatTrans.congr_app h K
  change (Functor.exactDerivedRestrictionComposition y₀ y₁ y₂ ρW).hom.app
        (H₀.rightDerivedFunctor.obj K) ≫ δ₂.hom.app K =
    (y₁.mapDerivedCategory.map (δ₀.hom.app K) ≫
      δ₁.hom.app (x₀.mapDerivedCategory.obj K)) ≫
      H₂.rightDerivedFunctor.map
        ((Functor.exactDerivedRestrictionComposition x₀ x₁ x₂ ρZ).hom.app K) at hh
  rw [Category.assoc] at hh
  exact hh.symm

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (F : Type u) [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
  (i : E →ₐ[ℚ_[l]] F)
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (j : F →ₐ[ℚ_[l]] L)

private theorem properRestriction_unitNormalized {Z W : Scheme.{u}} (g : Z ⟶ W) :
    CategoryTheory.ExactDerivedSquare.unitNormalized
      (towerDirectImage (ULift.{u + 1} (Padic.coefficientExtensionIntegers l F)) g)
      (towerDirectImage (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) g)
      (restrict l E F i Z) (restrict l E F i W)
      (U l E F i Z) (U l E F i W)
      (restrict l E F i Z).mapDerivedCategoryFactors
      (restrict l E F i W).mapDerivedCategoryFactors
      (properRestrictionOrdinary l E F i g).hom (properRestriction l E F i g).hom := by
  apply (unitCompatible_iff_unitNormalized _ _ _ _
    (properRestrictionOrdinary l E F i g) (properRestriction l E F i g)).mp
  unfold properRestriction
  exact (properRestriction_existsUnique l E F i g).choose_spec.1

private theorem restrictionComposition_section (V : Scheme.{u})
    (N : Towers (ULift.{u + 1} (Padic.coefficientExtensionIntegers l L)) V)
    (n : ℕᵒᵖ) (Q : V.ProEtᵒᵖ) (x : (N.obj n).val.obj Q) :
    (((towerScalarRestrictionCompositionOrdinary l E F i L j V).hom.app N).app n).val.app
      Q x = x := by
  exact (pbcRestrictComp_exists (constantMap l E F i V) (constantMap l F L j V)
    (constantMap l E L (j.comp i) V) (by
      unfold constantMap
      rw [← Functor.map_comp]
      congr 1)).exists.choose_spec (N.obj n) Q x

private theorem properRestrictionOrdinary_composition {Z W : Scheme.{u}} (g : Z ⟶ W)
    (N : Towers (ULift.{u + 1} (Padic.coefficientExtensionIntegers l L)) Z) :
    (towerScalarRestrictionCompositionOrdinary l E F i L j W).hom.app
          ((towerDirectImage (ULift.{u + 1} (Padic.coefficientExtensionIntegers l L))
            g).obj N) ≫
        (properRestrictionOrdinary l E L (j.comp i) g).hom.app N =
      (restrict l E F i W).map ((properRestrictionOrdinary l F L j g).hom.app N) ≫
        (properRestrictionOrdinary l E F i g).hom.app ((restrict l F L j Z).obj N) ≫
        (towerDirectImage (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) g).map
          ((towerScalarRestrictionCompositionOrdinary l E F i L j Z).hom.app N) := by
  let H₀ := towerDirectImage (ULift.{u + 1} (Padic.coefficientExtensionIntegers l L)) g
  let x₀ := restrict l F L j Z
  let c₀ := properRestrictionOrdinary l F L j g
  let c₁ := properRestrictionOrdinary l E F i g
  let c₂ := properRestrictionOrdinary l E L (j.comp i) g
  let ρZ := towerScalarRestrictionCompositionOrdinary l E F i L j Z
  let ρW := towerScalarRestrictionCompositionOrdinary l E F i L j W
  apply NatTrans.ext
  funext n
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro V
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  have h₀ := eq_of_heq
    ((properRestrictionOrdinary_existsUnique l F L j g).choose_spec.1 N n.unop V)
  have h₁ := eq_of_heq
    ((properRestrictionOrdinary_existsUnique l E F i g).choose_spec.1
      (x₀.obj N) n.unop V)
  have h₂ := eq_of_heq
    ((properRestrictionOrdinary_existsUnique l E L (j.comp i) g).choose_spec.1
      N n.unop V)
  change ((c₂.hom.app N).app n).val.app V
      (((ρW.hom.app (H₀.obj N)).app n).val.app V x) =
    ((ρZ.hom.app N).app n).val.app ((proEtaleBaseChange g).op.obj V)
      (((c₁.hom.app (x₀.obj N)).app n).val.app V
        (((c₀.hom.app N).app n).val.app V x))
  rw [restrictionComposition_section, restrictionComposition_section]
  exact (congrFun h₂ x).trans
    ((congrFun h₁ (((c₀.hom.app N).app n).val.app V x)).trans
      (congrFun h₀ x)).symm

/-- The two successive coefficient restrictions commute with proper image under
its canonical whole-complex normalization.
Source: Stacks 03DA, 0D6E and 0940; auxiliary Step 2 of strict scalar composition
(blueprint: lem-pur-strict-proper-restriction-composition).

Proof: first compare the ordinary squares on whole strict towers. Each proper
restriction comparison and each coefficient restriction compositor is identity
on underlying sections over the same base-change object. Their two composites
are therefore equal by extensionality of natural transformations and module
sheaf morphisms. This includes all quotient transitions. Next use the canonical
right-derived unit equation that defines properRestriction at each of the three
coefficient maps. Pasting the first two normalized squares gives a normalized
square for successive restriction. Naturality of normalized squares with respect
to the ordinary restriction compositor identifies it with the direct square.
Equivalently, evaluate on a K-injective representative, cancel the invertible
source unit, and use the ordinary equality and naturality of the target unit;
K-injective representatives are essentially surjective in the derived category.
All vertical restrictions are exact, so this proof is valid for unbounded towers
and does not use properness of g, nonempty schemes, or nonzero objects. -/
theorem properRestriction_composition {Z W : Scheme.{u}} (g : Z ⟶ W)
    (K : Derived (ULift.{u + 1} (Padic.coefficientExtensionIntegers l L)) Z) :
    (U l E F i W).map ((properRestriction l F L j g).hom.app K) ≫
        (properRestriction l E F i g).hom.app ((U l F L j Z).obj K) ≫
        (R (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) g).map
          ((towerScalarRestrictionComposition l E F i L j Z).hom.app K) =
      (towerScalarRestrictionComposition l E F i L j W).hom.app
          ((R (ULift.{u + 1} (Padic.coefficientExtensionIntegers l L)) g).obj K) ≫
        (properRestriction l E L (j.comp i) g).hom.app K := by
  let H₀ := towerDirectImage (ULift.{u + 1} (Padic.coefficientExtensionIntegers l L)) g
  let H₁ := towerDirectImage (ULift.{u + 1} (Padic.coefficientExtensionIntegers l F)) g
  let H₂ := towerDirectImage (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) g
  let x₀ := restrict l F L j Z
  let y₀ := restrict l F L j W
  let x₁ := restrict l E F i Z
  let y₁ := restrict l E F i W
  let x₂ := restrict l E L (j.comp i) Z
  let y₂ := restrict l E L (j.comp i) W
  let δ₀ := properRestriction l F L j g
  let δ₁ := properRestriction l E F i g
  let δ₂ := properRestriction l E L (j.comp i) g
  let c₀ := properRestrictionOrdinary l F L j g
  let c₁ := properRestrictionOrdinary l E F i g
  let c₂ := properRestrictionOrdinary l E L (j.comp i) g
  let ρZ := towerScalarRestrictionCompositionOrdinary l E F i L j Z
  let ρW := towerScalarRestrictionCompositionOrdinary l E F i L j W
  have hn₀ : CategoryTheory.ExactDerivedSquare.unitNormalized H₀ H₁ x₀ y₀
      x₀.mapDerivedCategory y₀.mapDerivedCategory
      x₀.mapDerivedCategoryFactors y₀.mapDerivedCategoryFactors c₀.hom δ₀.hom := by
    exact properRestriction_unitNormalized l F L j g
  have hn₁ : CategoryTheory.ExactDerivedSquare.unitNormalized H₁ H₂ x₁ y₁
      x₁.mapDerivedCategory y₁.mapDerivedCategory
      x₁.mapDerivedCategoryFactors y₁.mapDerivedCategoryFactors c₁.hom δ₁.hom := by
    exact properRestriction_unitNormalized l E F i g
  have hn₂ : CategoryTheory.ExactDerivedSquare.unitNormalized H₀ H₂ x₂ y₂
      x₂.mapDerivedCategory y₂.mapDerivedCategory
      x₂.mapDerivedCategoryFactors y₂.mapDerivedCategoryFactors c₂.hom δ₂.hom := by
    exact properRestriction_unitNormalized l E L (j.comp i) g
  have hc (N : Towers (ULift.{u + 1} (Padic.coefficientExtensionIntegers l L)) Z) :
      ρW.hom.app (H₀.obj N) ≫ c₂.hom.app N =
        y₁.map (c₀.hom.app N) ≫ c₁.hom.app (x₀.obj N) ≫
          H₂.map (ρZ.hom.app N) :=
    properRestrictionOrdinary_composition l E F i L j g N
  change y₁.mapDerivedCategory.map (δ₀.hom.app K) ≫
      δ₁.hom.app (x₀.mapDerivedCategory.obj K) ≫
      H₂.rightDerivedFunctor.map
        ((Functor.exactDerivedRestrictionComposition x₀ x₁ x₂ ρZ).hom.app K) =
    (Functor.exactDerivedRestrictionComposition y₀ y₁ y₂ ρW).hom.app
        (H₀.rightDerivedFunctor.obj K) ≫ δ₂.hom.app K
  exact normalizedRestriction_composition H₀ H₁ H₂ x₀ x₁ x₂ y₀ y₁ y₂
    c₀ c₁ c₂ δ₀ δ₁ δ₂ ρZ ρW hn₀ hn₁ hn₂ hc K

end WeilConjectures.PurStrictScalar
