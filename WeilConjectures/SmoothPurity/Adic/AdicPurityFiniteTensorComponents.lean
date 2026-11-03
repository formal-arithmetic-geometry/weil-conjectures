/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SmoothPurity.Adic.AdicPurityRootComparisons
import WeilConjectures.SixFunctors.Finite.Scalar.Tensor.FiniteScalarTensorRealizationPure
import WeilConjectures.SixFunctors.Supporting.Tensor.ProEtaleTensorPairNaturality
import WeilConjectures.SixFunctors.Orientation.OrientationFiniteCoefficientTwists
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
/-! # Components of the intrinsic finite tensor comparison
Source: blueprint def-coefficient-twists-detailed, finite reduction clause.
(blueprint: lem-pur-adic-finite-tensor-components).
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures

-- Compare the two existing sheafifications of the sectionwise tensor.
private def tensorPresentation (T : Scheme.{u})
    (R : Sheaf (ProEt.topology T) CommRingCat.{u + 1})
    (M N : proEtaleRingModules T R) :
    (SheafOfModules.siteSheafTensorRight N).obj M ≅
      ((proEtaleOrdinaryTensor T R).obj M).obj N :=
  (PresheafOfModules.sheafification.{u + 1} (𝟙 _)).mapIso
    ((SheafOfModules.siteTensorRightIso R N.val).app M.val) ≪≫
      (SheafOfModules.tensorObjIsoSheafification.{u, u + 1, u + 1} M N).symm

private theorem tensorPresentation_pure (T : Scheme.{u})
    (R : Sheaf (ProEt.topology T) CommRingCat.{u + 1})
    (M N : proEtaleRingModules T R) (W : T.ProEtᵒᵖ)
    (x : M.val.obj W) (y : N.val.obj W) :
    (tensorPresentation T R M N).hom.val.app W
        (SheafOfModules.siteSheafTensorTmul (A := R) M N W x y) =
      proEtaleTensorPair T R M N W x y := by
  let adj := PresheafOfModules.sheafificationAdjunction.{u + 1}
    (𝟙 ((sheafCompose (ProEt.topology T)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R).obj)
  let q := (SheafOfModules.siteTensorRightIso R N.val).app M.val
  have h := congrArg (fun z ↦ z.app W (x ⊗ₜ[R.obj.obj W] y))
    (adj.unit.naturality q.hom).symm
  change ((PresheafOfModules.sheafification.{u + 1} (𝟙 _)).map q.hom).val.app W
      (SheafOfModules.siteSheafTensorTmul (A := R) M N W x y) =
    (adj.unit.app (M.val ⊗ N.val)).app W (x ⊗ₜ[R.obj.obj W] y) at h
  exact congrArg ((SheafOfModules.tensorObjIsoSheafification.{u, u + 1, u + 1} M N).inv.val.app W) h

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (n : ℕ) (T : Scheme.{u})
section TwistReduction
variable [hInvert : ∀ x : T, Invertible (l : T.residueField x)]
include hInvert

-- Retain the established invertibility binder; scalar realization needs no such hypothesis.
set_option linter.unusedSectionVars false in
set_option maxHeartbeats 600000 in
-- Allow elaboration to compare the fixed-scalar and intrinsic tensor presentations.
/-- The intrinsic finite tensor comparison on one module, normalized on all
scalar-unit pure tensors.
Source: def-coefficient-twists-detailed, finite tensor realization; Stacks 00YV and 03EK.
(blueprint: lem-pur-adic-finite-tensor-components).
Proof: the normalized root identification `k` of the restricted Tate line
(def-sf-orientation-finite-line-comparisons) gives, after realization and the
equivalence counit, an isomorphism `c : F(N) ≅ L`; naturality of the scalar
sheafification unit and the normalization of `k` give `c(η_N y) = y`, hence
`c⁻¹ y = η_N y`. Sheafifying the sectionwise comparison `siteTensorRightIso` and
composing with the inverse of `tensorObjIsoSheafification` presents the site
tensor as the monoidal tensor, sending each site pure tensor to
`proEtaleTensorPair` of the same sections. Compose this presentation for `F(M)`
and `L` with `𝟙 ⊗ c⁻¹` and the inverse of the `finiteScalarOrdinaryTensorIso`
component at `(M, N)`. On a scalar-unit pure tensor, naturality of
`proEtaleTensorPair` and `finiteScalarTensorRealization_pure` identify the
image with the inverse scalar comparison applied to the forward one, which
cancel to the displayed equation. All identities are functorial and hold also
for `d = 0`, zero modules and empty test objects. -/
theorem adicPurityFiniteTensor_component (d : ℕ)
    (M : Sheaf (ProEt.topology T) (ModuleCat.{u + 1} (finiteTateCoefficient l E n))) :
    ∃ e : (SheafOfModules.siteSheafTensorRight
        (A := integralCoefficientCommRingSheaf l E T n)
        (finiteCoefficientTwist l E T n (d : ℤ))).obj
          ((sfIntrinsicModuleEquivalence T
            (Padic.coefficientExtensionRing l E (n + 1))).functor.obj M) ≅
      (sfIntrinsicModuleEquivalence T
        (Padic.coefficientExtensionRing l E (n + 1))).functor.obj
          (M ⊗ finiteTateProSheaf l E n T d),
      ∀ (W : T.ProEtᵒᵖ) (x : M.obj.obj W)
        (y : (finiteCoefficientTwist l E T n (d : ℤ)).val.obj W),
        e.hom.val.app W
          (SheafOfModules.siteSheafTensorTmul
            (A := integralCoefficientCommRingSheaf l E T n) _ _ W
            (sfIntrinsicRealizationUnit T (Padic.coefficientExtensionRing l E (n + 1)) M W x) y) =
        sfIntrinsicRealizationUnit T (Padic.coefficientExtensionRing l E (n + 1))
          (M ⊗ finiteTateProSheaf l E n T d) W
          ((Functor.LaxMonoidal.μ (sheafToPresheaf (ProEt.topology T)
            (ModuleCat.{u + 1} (finiteTateCoefficient l E n))) M
              (finiteTateProSheaf l E n T d)).app W (x ⊗ₜ[finiteTateCoefficient l E n] y)) := by
  let R := Padic.coefficientExtensionRing l E (n + 1)
  let L := finiteCoefficientTwist l E T n (d : ℤ)
  let N := finiteTateProSheaf l E n T d
  let F := (sfIntrinsicModuleEquivalence T R).functor
  let q := sfIntrinsicModuleEquivalence T R
  obtain ⟨k, hk, _⟩ := sfOrientationFixedRootSheaf_existsUnique l E T n d
  let c : F.obj N ≅ L := F.mapIso k.symm ≪≫ q.counitIso.app L
  have hc (W : T.ProEtᵒᵖ) (y : L.val.obj W) :
      c.hom.val.app W (sfIntrinsicRealizationUnit T R N W y) = y := by
    have hη := congrArg (fun z ↦ z.app W y)
      ((PresheafOfModules.sheafificationAdjunction.{u + 1}
        (ProEtale.finiteCoefficientIntrinsicScalarMap T R)).unit.naturality
          ((ProEtale.finiteCoefficientModulePresheaf T.ProEt
            (ULift.{u + 1} R)).map k.inv.hom))
    change sfIntrinsicRealizationUnit T R (q.inverse.obj L) W (k.inv.hom.app W y) =
      (F.map k.inv).val.app W (sfIntrinsicRealizationUnit T R N W y) at hη
    change (q.counitIso.hom.app L).val.app W
      ((F.map k.inv).val.app W (sfIntrinsicRealizationUnit T R N W y)) = y
    rw [← hη]
    exact hk W y
  let := SheafOfModules.monoidalCategory (integralCoefficientCommRingSheaf l E T n)
  let s := tensorPresentation T (integralCoefficientCommRingSheaf l E T n) (F.obj M) L
  let t := (finiteScalarOrdinaryTensorIso T R).app (M, N)
  let e := s ≪≫
      tensorIso (Iso.refl (F.obj M)) c.symm ≪≫
      t.symm
  refine ⟨e, ?_⟩
  intro W x y
  have hci : c.inv.val.app W y = sfIntrinsicRealizationUnit T R N W y := by
    have h := congrArg (fun z ↦ z.val.app W (sfIntrinsicRealizationUnit T R N W y))
      c.hom_inv_id
    change c.inv.val.app W (c.hom.val.app W
      (sfIntrinsicRealizationUnit T R N W y)) = _ at h
    rw [hc] at h
    exact h
  change t.inv.val.app W ((𝟙 (F.obj M) ⊗ₘ c.inv).val.app W
    (s.hom.val.app W (SheafOfModules.siteSheafTensorTmul
      (A := integralCoefficientCommRingSheaf l E T n) (F.obj M) L W
      (sfIntrinsicRealizationUnit T R M W x) y))) = _
  rw [tensorPresentation_pure]
  have hp := (proEtaleTensorPair_natural T (integralCoefficientCommRingSheaf l E T n)
    (M := F.obj M) (M' := F.obj M) (N := L) (N' := F.obj N)
    (𝟙 (F.obj M)) c.inv W (sfIntrinsicRealizationUnit T R M W x) y).trans
      (congrArg (proEtaleTensorPair T (integralCoefficientCommRingSheaf l E T n)
        (F.obj M) (F.obj N) W (sfIntrinsicRealizationUnit T R M W x)) hci)
  have ht := finiteScalarTensorRealization_pure T R M N W x y
  have hi := congrArg (fun z ↦ z.val.app W
    (sfIntrinsicRealizationUnit T R (M ⊗ N) W
      ((Functor.LaxMonoidal.μ (sheafToPresheaf (ProEt.topology T)
        (ModuleCat.{u + 1} (finiteTateCoefficient l E n))) M N).app W
          (x ⊗ₜ[finiteTateCoefficient l E n] y)))) t.hom_inv_id
  change t.inv.val.app W (t.hom.val.app W _) = _ at hi
  exact (congrArg (t.inv.val.app W) hp).trans
    ((congrArg (t.inv.val.app W) ht).symm.trans hi)

end TwistReduction
end WeilConjectures
