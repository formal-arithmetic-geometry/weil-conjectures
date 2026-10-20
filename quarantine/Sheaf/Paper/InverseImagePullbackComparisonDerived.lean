/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NJ
-/
module

public import Sheaf.AlgebraicGeometry.ProEtale.InverseImagePullbackComparison
public import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import Sheaf.Algebra.Homology.TensorColimitsIndependentCoefficients

/-!
# The specified integral comparison at an arbitrary derived object

Source: Bhatt--Scholze, Section 6.5, Lemma 6.5.9(4); the chosen-resolution formula
in part (b) (blueprint: def-weil-inverse-image-pullback-comparison).

This is the recorded comparison transported through a representative of a derived
object and a flat-term K-flat resolution. No new naturality assertion is imposed.
The finite comparisons and all coefficient maps are publicly retained.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry.Scheme WeilConjectures
namespace AlgebraicGeometry.ProEtale

/-- Evaluate part (b) on the chosen representative and its chosen K-flat resolution,
then transport its two endpoints by the representative isomorphism. The resolution
is used only through the localized specified comparison. Source: Bhatt--Scholze,
Section 6.5, Lemma 6.5.9(4)
(blueprint: def-weil-inverse-image-pullback-comparison). -/
def inverseImagePullbackComparisonDerived
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X Y : AlgebraicGeometry.Scheme.{t}} (g : X ⟶ Y) [IsIso g]
    (hX : ∀ x : X, IsUnit (l : X.presheaf.stalk x))
    (hY : ∀ y : Y, IsUnit (l : Y.presheaf.stalk y))
    (K : DerivedCategory (integralTowerModules l E Y)) :
    (inverseImageIntegralDerived l E g).obj K ⟶
      (integralDerivedPullback l E g).obj K := by
  let M := DerivedCategory.Q.objPreimage K
  let e : DerivedCategory.Q.obj M ≅ K := DerivedCategory.Q.objObjPreimageIso K
  let h := CochainComplex.exists_isKFlatResolutionIndependentCoefficients
    (R := completedIntegralCommRingSheafUnrestricted l E Y) M
  let P := h.choose
  let q := h.choose_spec.choose
  let hq := h.choose_spec.choose_spec
  letI : QuasiIso q := hq.2.2.1
  exact (inverseImageIntegralDerived l E g).map e.inv ≫
    inverseImagePullbackComparison l E g hX hY M
      ⟨P, hq.1, fun i ↦ (exactFunctor _ _).prop_of_iso
        (SheafOfModules.siteSheafTensorRightIso _ (P.X i)).symm (hq.2.1 i)⟩ q ≫
      (integralDerivedPullback l E g).map e.hom

end AlgebraicGeometry.ProEtale
