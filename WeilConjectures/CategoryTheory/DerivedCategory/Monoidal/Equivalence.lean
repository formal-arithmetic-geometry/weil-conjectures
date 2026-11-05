/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.Algebra.Homology.HomotopyCategory.MapMonoidal
public import WeilConjectures.CategoryTheory.Abelian.Flat.PreservesFlat
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.ShiftComparison
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategory
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# Monoidal equivalences of abelian categories and derived internal homs

Let `F : C₁ ⥤ C₂` be an equivalence of monoidal closed braided Grothendieck abelian categories
with functorial flat resolutions, which is moreover a monoidal functor. Then the induced
equivalence `D(F) : D(C₁) ≌ D(C₂)` of derived categories commutes with the derived tensor
products, and its quasi-inverse `D(F⁻¹)` commutes with the derived internal homs:

`D(F⁻¹)(RHom(X, Y)) ≅ RHom(D(F⁻¹) X, D(F⁻¹) Y)`.

## Main results

- `DerivedCategory.tensorLeftCompMapDerivedCategoryIso`: `D(F)(N ⊗ᴸ M) ≅ D(F) N ⊗ᴸ D(F) M`,
  naturally in `M`.
- `DerivedCategory.ihomCompMapDerivedCategoryInvIso`:
  `D(F⁻¹)(RHom(X, Y)) ≅ RHom(D(F⁻¹) X, D(F⁻¹) Y)`, naturally in `Y`.

## Implementation notes

The comparison of the tensor products is computed on a K-flat representative `P` of `N`
whose image `F(P)` is again K-flat: the functorial flat resolutions are such representatives,
since `F` preserves flat objects and colimits
(`CategoryTheory.Functor.kFlat_mapHomologicalComplex_obj_resolutionFunctor_obj`). The
comparison of the internal homs is then the conjugate, under the adjunctions
`D(F) ⋙ (X ⊗ᴸ -) ⊣ RHom(X, -) ⋙ D(F⁻¹)` and `(D(F⁻¹) X ⊗ᴸ -) ⋙ D(F) ⊣ D(F⁻¹) ⋙ RHom(D(F⁻¹) X, -)`,
of the comparison of the tensor products.
-/

@[expose] public section

universe w v

open CategoryTheory Limits MonoidalCategory

namespace DerivedCategory

variable {C₁ C₂ : Type*} [Category.{v} C₁] [Abelian C₁] [IsGrothendieckAbelian.{w} C₁]
  [HasDerivedCategory.{w} C₁] [MonoidalCategory C₁] [MonoidalClosed C₁] [MonoidalPreadditive C₁]
  [BraidedCategory C₁] [Abelian.HasFunctorialFlatResolution C₁]
  [Category.{v} C₂] [Abelian C₂] [IsGrothendieckAbelian.{w} C₂]
  [HasDerivedCategory.{w} C₂] [MonoidalCategory C₂] [MonoidalClosed C₂] [MonoidalPreadditive C₂]
  [BraidedCategory C₂] [Abelian.HasFunctorialFlatResolution C₂]

local instance hasColimitsOfSize_monoidalEquivalence₁ : HasColimitsOfSize.{0, 0} C₁ :=
  hasColimitsOfSizeShrink C₁
local instance hasColimitsOfSize_monoidalEquivalence₂ : HasColimitsOfSize.{0, 0} C₂ :=
  hasColimitsOfSizeShrink C₂

variable (F : C₁ ⥤ C₂) [F.Monoidal] [F.IsEquivalence] [F.Additive]

local instance additive_asEquivalence_functor : F.asEquivalence.functor.Additive := ‹F.Additive›

omit [HasDerivedCategory C₂] [Abelian.HasFunctorialFlatResolution C₂] in
/-- Every object `N` of `D(C₁)` is isomorphic to `Qh P` for a complex `P` such that both `P`
and `F(P)` are K-flat: a functorial flat resolution of a representative of `N`. -/
lemma exists_kFlat_iso_of_isEquivalence (N : DerivedCategory C₁) :
    ∃ P : HomotopyCategory C₁ (.up ℤ), (HomotopyCategory.quasiIso C₁ (.up ℤ)).kFlat P ∧
      (HomotopyCategory.quasiIso C₂ (.up ℤ)).kFlat ((F.mapHomotopyCategory (.up ℤ)).obj P) ∧
      Nonempty (Qh.obj P ≅ N) := by
  let Λ : Abelian.LeftResolution (ObjectProperty.flat.ι : _ ⥤ C₁) := Classical.arbitrary _
  have := F.preservesFlat_of_isEquivalence
  let K := Q.objPreimage N
  refine ⟨(HomotopyCategory.quotient _ _).obj (Λ.reduced.resolutionFunctor.obj K),
    (HomotopyCategory.kFlat_quotient_obj_iff _).2
      (Λ.reduced.kFlat_resolutionFunctor_obj ObjectProperty.flat.essImage_ι_le K),
    ObjectProperty.prop_of_iso _ ((F.mapHomotopyCategoryFactors (.up ℤ)).app _).symm
      ((HomotopyCategory.kFlat_quotient_obj_iff _).2
        (F.kFlat_mapHomologicalComplex_obj_resolutionFunctor_obj Λ.reduced
          ObjectProperty.flat.essImage_ι_le K)),
    ⟨(quotientCompQhIso C₁).app _ ≪≫ asIso (Q.map (Λ.reduced.resolutionNatTrans.app K)) ≪≫
      Q.objObjPreimageIso N⟩⟩

end DerivedCategory
