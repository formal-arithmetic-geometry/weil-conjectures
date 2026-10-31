/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.AdicQbarRealization.Native.NativeAdicFiniteNormalization
public import WeilConjectures.SixFunctors.Isomorphism.IsomorphismComparisonScalarExtension

/-! # The ambient scalar maps used in realization reindexing

Source: Bhatt--Scholze, Remark 6.8.15 and Proposition 6.8.14.
(blueprint: def-sf-adic-reindex-scalar-maps).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
set_option Elab.async false
attribute [local irreducible] HasDerivedCategory.standard

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProEtale
open AlgebraicGeometry.Scheme
namespace WeilConjectures.AdicQbarRealization
open AlgebraicallyClosedCoefficients (Index Coefficient coefficientInclusion)
open GeneralAlgebraicallyClosedCoefficients (inclusion stageSystem integralTransition)

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)

/-- Both completed coefficient transports lift the same finite projections. -/
theorem completedRingReindex_eq {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g] :
    podCompletedRingMap l E g = inverseImageCompletedCoefficientMap l E g := by
  apply limit.hom_ext
  intro n
  unfold podCompletedRingMap inverseImageCompletedCoefficientMap
  erw [limit.lift_π]

/-- Equality transport between two presentations of the same completed inverse image.
Both coefficient maps are the limit lift of the normalized finite constant maps. -/
def completedReindexModel {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g] :
    podCompletedDerivedInverseImage l E g ≅ inverseImageIntegralDerived l E g := by
  letI : (inverseImageIntegralModules l E g).Additive :=
    isoSectionwiseModuleInverseImage_additive g (inverseImageCompletedCoefficientMap l E g)
  letI : PreservesFiniteLimits (inverseImageIntegralModules l E g) :=
    isoSectionwiseModuleInverseImage_limits g (inverseImageCompletedCoefficientMap l E g)
  letI : PreservesFiniteColimits (inverseImageIntegralModules l E g) :=
    isoSectionwiseModuleInverseImage_colimits g (inverseImageCompletedCoefficientMap l E g)
  exact Functor.mapDerivedCategoryNatIso (eqToIso (by
    exact congrArg (fun c ↦ isoSectionwiseModuleInverseImage.{u, u} g c.hom)
      (show asIso (podCompletedRingMap l E g) =
          asIso (inverseImageCompletedCoefficientMap l E g) from
        Iso.ext (completedRingReindex_eq l E g))))

/-- The finite-free exact scalar model, with the counit-normalized universal tensor model. -/
def scalarExactModel (W : Scheme.{u}) :
    integralOrdinaryDerivedScalar l E L ι W ≅ completedDerivedScalarExtension l E L ι W :=
  (isomorphismScalarModel_existsUnique l E L ι W).exists.choose

/-- Reindex ordinary derived coefficient tensors, before applying any completion map.
The map is constructed from the section-normalized tensor map on module sheaves. -/
def completedScalarReindex {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g] :
    podCompletedDerivedInverseImage l E g ⋙ completedDerivedScalarExtension l E L ι X ≅
      completedDerivedScalarExtension l E L ι Y ⋙ podCompletedDerivedInverseImage l L g :=
  Functor.isoWhiskerLeft _ (scalarExactModel l E L ι X).symm ≪≫
    Functor.isoWhiskerRight (completedReindexModel l E g) _ ≪≫
    isomorphismScalarTensorDerived l E L ι g ≪≫
    Functor.isoWhiskerLeft _ (completedReindexModel l L g).symm ≪≫
    Functor.isoWhiskerRight (scalarExactModel l E L ι Y) _

/-- The canonical native balancing map, followed by the specified completion map. -/
def nativeScalarTransition (W : Scheme.{u})
    (R : LocallyFiniteAdicRealization.Realization l W)
    (E L : Index l (PadicAlgCl l)) (h : E ≤ L)
    (K : DerivedCategory (integralTowerModules l (Coefficient.{u} l (PadicAlgCl l) E) W)) :
    (pbcDerivedExtend (coefficientMap l W R E)).obj K ⟶
      (pbcDerivedExtend (coefficientMap l W R L)).obj
        ((integralScalarExtension l (Coefficient.{u} l (PadicAlgCl l) E)
          (Coefficient.{u} l (PadicAlgCl l) L)
          (coefficientInclusion l (PadicAlgCl l) E L h) W).obj K) :=
  (pbcReductionNormalization
      (completedCoefficientMap l (Coefficient.{u} l (PadicAlgCl l) E)
        (Coefficient.{u} l (PadicAlgCl l) L)
        (coefficientInclusion l (PadicAlgCl l) E L h) W)
      (coefficientMap l W R L) (coefficientMap l W R E)
      (R.coefficient_scalar E L h) K).inv ≫
    (pbcDerivedExtend (coefficientMap l W R L)).map
      ((completedScalarComparison l (Coefficient.{u} l (PadicAlgCl l) E)
        (Coefficient.{u} l (PadicAlgCl l) L)
        (coefficientInclusion l (PadicAlgCl l) E L h) W).app K)

end WeilConjectures.AdicQbarRealization
