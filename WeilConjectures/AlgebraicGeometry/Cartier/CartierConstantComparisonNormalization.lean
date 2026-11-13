/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Cartier.CartierKummerData
public import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.CategoryTheory.Sites.Equivalence
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Sites.Sheafification
public import WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
public import Mathlib.CategoryTheory.Monoidal.CommGrp_
public import Mathlib.CategoryTheory.Monoidal.Ring
public import Mathlib.CategoryTheory.Adjunction.Limits
public import WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
public import WeilConjectures.SixFunctors.ProEtale.ConstructibleSheaf
public import WeilConjectures.SixFunctors.ProEtale.Comparison.UpperStar
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import all WeilConjectures.AlgebraicGeometry.Cartier.CartierClosedExchangeComparison

/-!
# Normalization and naturality of the Cartier constant comparison

Source: Stacks Project, Sites and
Sheaves, Tags 0H7J and 00WX.

The inverse images below are the functors on fixed-coefficient module-valued sheaves.
The etale constant structure map is written as the adjunct of the sheafification extension
of the constant-presheaf unit. The pro-etale structure map is the published map with
that same definition. The commutation isomorphism is the conjugate of the canonical
commutation of direct images along base change and the inclusion of sites.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.Etale

/-- The Cartier constant comparison equals the uniqueness-of-left-adjoints isomorphism,
is invertible, and commutes with inverse image along every closed immersion.
Source: Stacks Project, Sites and Sheaves, Tags 0H7J and 00WX. -/
theorem cartierConstantComparison_normalization (A : Type (u + 1)) [CommRing A] :
    (∀ T : Scheme.{u},
      cartierConstantComparison A T =
          ((ProEtale.comparisonUpperStarConstantSheafIso A T).app (ModuleCat.of A A)).hom ∧
        IsIso (cartierConstantComparison A T)) ∧
    (∀ {D Z : Scheme.{u}} (i : D ⟶ Z) [IsClosedImmersion i],
      (ProEtale.comparisonUpperStarUpperStarIso (ModuleCat.{u + 1} A) i).hom.app
          (ordinaryFiniteConstant A Z) ≫
        (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) D).map
          (((upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) i).homEquiv _ _).symm
            (((sheafificationAdjunction Z.smallEtaleTopology
                (ModuleCat.{u + 1} A)).homEquiv _ _).symm
              (Functor.whiskerLeft (MorphismProperty.Over.pullback @Etale ⊤ i).op
                (toSheafify D.smallEtaleTopology
                  ((Functor.const D.Etaleᵒᵖ).obj (ModuleCat.of A A)))))) ≫
        ((ProEtale.comparisonUpperStarConstantSheafIso A D).app (ModuleCat.of A A)).hom =
      (Scheme.proEtaleSheafInverseImage i (ModuleCat.{u + 1} A)).map
          (cartierConstantComparison A Z) ≫
        Scheme.proEtaleConstantInverseImageMap i (ModuleCat.{u + 1} A)
          (ModuleCat.of A A)) := by
  have hnorm (T : Scheme.{u}) :
      cartierConstantComparison A T =
        ((ProEtale.comparisonUpperStarConstantSheafIso A T).app (ModuleCat.of A A)).hom := by
    exact (ProEtale.comparison_constant_inverse A T (ModuleCat.of A A)).symm
  constructor
  · intro T
    refine ⟨hnorm T, ?_⟩
    rw [hnorm T]
    infer_instance
  · intro D Z i _
    have hr : ProEtale.lowerStarComparisonLowerStarIso (ModuleCat.{u + 1} A) i =
        ProEtale.lowerStarCompComparisonLowerStarIso i (ModuleCat.{u + 1} A) := by
      apply Iso.ext
      apply NatTrans.ext
      funext S
      apply Sheaf.hom_ext
      apply NatTrans.ext
      funext W
      dsimp only [ProEtale.lowerStarComparisonLowerStarIso,
        ProEtale.lowerStarCompComparisonLowerStarIso]
      change 𝟙 _ = (𝟙 _ ≫ S.obj.map (𝟙 _)) ≫ 𝟙 _
      simp only [Category.id_comp, Category.comp_id]
      exact (S.obj.map_id _).symm
    have hc : ProEtale.comparisonUpperStarUpperStarIso (ModuleCat.{u + 1} A) i =
        ProEtale.comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} A) i := by
      unfold ProEtale.comparisonUpperStarUpperStarIso
        ProEtale.comparisonUpperStarCompUpperStarIso
      rw [hr]
    rw [hnorm Z, hc]
    simpa only [Iso.app_hom, ProEtale.etale_constant_inverse,
      ProEtale.ConstantProof.constantInverse, ProEtale.ConstantProof.constantDirect,
      Scheme.Hom.Etale, lowerStar, ordinaryFiniteConstant, constantSheaf,
      Functor.comp_obj, ProEtale.upperStar, Scheme.proEtaleSheafInverseImage,
      Scheme.proEtaleBaseChange, Scheme.smallEtaleTopology] using
      (ProEtale.comparison_constants A i).symm

end AlgebraicGeometry.Etale
