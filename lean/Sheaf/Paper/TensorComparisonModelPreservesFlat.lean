/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.SemilinearSystemModels
import Sheaf.Algebra.Homology.RingedDerivedTensorNative
import Sheaf.Algebra.Homology.BoundedFlatIndependentCoefficients
import Sheaf.Algebra.Homology.TensorColimitsIndependentCoefficients

/-! # Flat modules preserved by a normalized tensor model

Source: Stacks 06YS and 07A4.
(blueprint: lem-coef-semilinear-tensor-model-preserves-flat)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true
set_option genInjectivity false
set_option genSizeOfSpec false
universe c v r
open CategoryTheory CategoryTheory.Limits Opposite
namespace WeilConjectures.SemilinearSections
attribute [local irreducible] Functor.mapDerivedCategory Functor.mapDerivedCategoryFactors
  HasDerivedCategory.standard DerivedCategory SheafOfModules.monoidalCategory
  CoefficientClosedStructure.tensor

variable {C₀ C₁ : Type c} [Category.{v} C₀] [Category.{v} C₁]
  [EssentiallySmall.{max c v r} C₀] [EssentiallySmall.{max c v r} C₁]
  (J₀ : GrothendieckTopology C₀) (J₁ : GrothendieckTopology C₁)
  (R₀ : Sheaf J₀ CommRingCat.{max c v r}) (R₁ : Sheaf J₁ CommRingCat.{max c v r})

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
private theorem siteFlat_of_catFlat (M : Mod.{c, v, max c v r} J₀ R₀)
    (h : letI := SheafOfModules.isMonoidal_W_independentCoefficients R₀
      letI := SheafOfModules.monoidalCategory R₀
      ObjectProperty.flat M) : SheafOfModules.IsFlatOnSite (J := J₀) (R := R₀) M := by
  exact (exactFunctor _ _).prop_of_iso
    (SheafOfModules.siteSheafTensorRightIso R₀ M).symm h.2

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
/-- A normalized tensor model preserves flat modules.
Source: Stacks 06YS and 07A4, flat complexes and derived tensor comparison.
(blueprint: lem-coef-semilinear-tensor-model-preserves-flat).

Proof: put a flat module in degree zero. Its terms are flat (all other terms
vanish), and the bounded-above flat criterion makes it K-flat. The model sends
this complex to a K-flat complex. Mapping a single complex is isomorphic to the
single complex of the image module. The converse K-flat single-complex criterion
therefore makes that image categorically flat. The natural isomorphism between
categorical sheaf tensor and site sheaf tensor gives the asserted site flatness. -/
theorem tensorComparisonModel_preserves_flat
    (F : Mod.{c, v, max c v r} J₀ R₀ ⥤ Mod.{c, v, max c v r} J₁ R₁)
    [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (S₀ : Closed.{c, v, r} J₀ R₀) (S₁ : Closed.{c, v, r} J₁ R₁)
    (T₀ : Models.{c, v, r} J₀ R₀ S₀) (T₁ : Models.{c, v, r} J₁ R₁ S₁)
    (μ : S₀.tensor ⋙ F.mapDerivedCategory ≅
      (F.mapDerivedCategory.prod F.mapDerivedCategory) ⋙ S₁.tensor)
    (t : TensorComparisonModel.{c, v, r} J₀ J₁ R₀ R₁ F S₀ S₁ T₀ T₁ μ)
    (M : Mod.{c, v, max c v r} J₀ R₀)
    (hM : SheafOfModules.IsFlatOnSite (J := J₀) (R := R₀) M) :
    SheafOfModules.IsFlatOnSite (J := J₁) (R := R₁) (F.obj M) := by
  let := SheafOfModules.isMonoidal_W_independentCoefficients R₀
  let := SheafOfModules.monoidalCategory R₀
  -- A single flat module is K-flat, and K-flatness of its image detects flatness.
  let P := (CochainComplex.singleFunctor (Mod.{c, v, max c v r} J₀ R₀) 0).obj M
  have hf : flatTerms.{c, v, r} J₀ R₀ P := by
    intro i
    apply siteFlat_of_catFlat.{c, v, r} J₀ R₀
    by_cases hi : i = 0
    · subst i
      exact ObjectProperty.prop_of_iso ObjectProperty.flat
        (HomologicalComplex.singleObjXSelf (.up ℤ) 0 M).symm
        (SheafOfModules.flat_to_cat R₀ M hM)
    · exact ObjectProperty.flat_of_isZero
        (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 M i hi)
  have hk := SheafOfModules.isKFlatIndependentCoefficients_of_boundedAbove_flatOnSite
    R₀ P 0 hf
  have ht := t.kflat P hk hf
  let := SheafOfModules.isMonoidal_W_independentCoefficients R₁
  let := SheafOfModules.monoidalCategory R₁
  let := SheafOfModules.symmetricCategory R₁
  let := SheafOfModules.tensorPreadditive R₁
  have (N : Mod.{c, v, max c v r} J₁ R₁) :
      PreservesColimitsOfSize.{0, 0} (MonoidalCategory.tensorLeft N) := by
    have := SheafOfModules.tensorLeft_preservesColimits_independentCoefficients R₁ N
    exact preservesColimitsOfSize_shrink _
  have (N : Mod.{c, v, max c v r} J₁ R₁) :
      PreservesColimitsOfSize.{0, 0} (MonoidalCategory.tensorRight N) :=
    preservesColimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight N)
  have hcat := CategoryTheory.RingedDerivedNative.kFlat.{c, v, r} J₁ R₁ _ ht
  have hcat' := (HomotopyCategory.kFlat_quotient_obj_iff _).1 hcat
  have hs := ObjectProperty.prop_of_iso
    (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat
    ((HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).app M) hcat'
  exact siteFlat_of_catFlat.{c, v, r} J₁ R₁ _
    ((CochainComplex.kFlat_single_obj_iff_flat (F.obj M) 0).1 hs)


end WeilConjectures.SemilinearSections
