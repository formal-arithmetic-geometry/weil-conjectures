/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.AdicQbarRealization.Proper.NativeProperCoefficientOperations
import all WeilConjectures.AlgebraicGeometry.ProEtaleModuleInverseImageCanonicalUnit
import all WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
import all WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import all WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import all Mathlib.AlgebraicGeometry.Sites.Proetale
import all Mathlib.CategoryTheory.Sites.ConstantSheaf
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import all Mathlib.CategoryTheory.Sites.Equivalence
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
import all WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Category.ModuleCat.AB
import all Mathlib.Algebra.Category.ModuleCat.Sheaf
import all Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import all Mathlib.Algebra.Homology.ShortComplex.ShortExact
import all Mathlib.CategoryTheory.Sites.Sheafification
import all WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
import all Mathlib.CategoryTheory.Monoidal.CommGrp_
import all Mathlib.CategoryTheory.Monoidal.Ring
import all Mathlib.CategoryTheory.Adjunction.Limits
import all WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
import all WeilConjectures.AlgebraicGeometry.ProEtaleModelRingPresentation
import all WeilConjectures.CategoryTheory.SheafPullbackUnitPresentation
import all Mathlib.CategoryTheory.Sites.Pullback
import all Mathlib.CategoryTheory.Sites.CartesianMonoidal
import all WeilConjectures.CategoryTheory.SheafPullbackForgetComparison
import all WeilConjectures.CategoryTheory.ModuleInverseImageAdjunction
import all WeilConjectures.CategoryTheory.ModuleInverseImageAction
import all Mathlib.Algebra.Category.Ring.Limits
import all WeilConjectures.CategoryTheory.ModuleInverseImageActionOfPresentations
import all WeilConjectures.AlgebraicGeometry.EtaleInverseImageModuleAdjunction
import WeilConjectures.SixFunctors.LocallyFiniteAdicCompactSupport.NativeCoefficientInverseImage
import WeilConjectures.SixFunctors.LocallyFiniteAdicRealization.LocallyFiniteAdicCoefficientSystem
import WeilConjectures.SixFunctors.ProEtale.Adic.PadicAlgClSheafRing

/-! # The coefficient map for native ordinary pullback

Source: Bhatt--Scholze, Remark 6.8.15; native locally finite functions.
(blueprint: lem-sf-native-pullback-coefficient-map)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option linter.style.haveILetI false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme
open scoped CategoryTheory.Obj
namespace WeilConjectures.AdicQbarRealization.Proper

variable (l : ℕ) [Fact l.Prime] {X Y : Scheme.{u}} (p : X ⟶ Y)
  (R : LocallyFiniteAdicRealization.Realization l X)
  (S : LocallyFiniteAdicRealization.Realization l Y)

/-- Precomposition of locally finite functions is the adjunct of a coefficient map.
Source: Bhatt--Scholze, Remark 6.8.15 and the native locally finite function sheaf.
(blueprint: lem-sf-native-pullback-coefficient-map).

Proof: precompose a locally finite continuous function with the first projection
of the scheme pullback. Local finiteness is preserved by continuous precomposition.
The pointwise ring operations commute with precomposition, and pullback functoriality
proves naturality. Take its inverse image/direct image adjunct. Applying the adjunction
bijection again recovers the constructed map, so its values are exactly the stated
precompositions. The existing native_coefficient_inverse_image theorem identifies this
adjunct with the normalized native coefficient inverse-image isomorphism. Applying it
to the commutative coefficient structures supplied by coefficientSystem_exists gives
its invertibility. This works for empty schemes without a nonemptiness hypothesis. -/
theorem nativePullbackCoefficientMap :
    ∃ c : (adicTowerInverseImage p).obj (ring l Y S) ⟶ ring l X R,
      IsIso c ∧ ∀ (V : Y.ProEtᵒᵖ) (s : (ring l Y S).obj.obj V)
        (x : ((proEtaleBaseChange p).obj V.unop).left),
      (((proEtaleSheafAdjunction p CommRingCat.{u + 1}).homEquiv _ _ c).hom.app V s).down.1 x =
        s.down.1 ((pullback.fst V.unop.hom p).base x) := by
  letI : ∀ T : Scheme.{u}, IsCommMonObj (LocallyFiniteAdicRealization.abRing l T) :=
    fun T ↦ (Classical.choice
      (LocallyFiniteAdicRealization.coefficientSystem_exists l T)).commutative
  obtain ⟨c, hc, _⟩ := LocallyFiniteAdicCompactSupport.native_coefficient_inverse_image l p
  exact ⟨c.hom, c.isIso_hom, hc⟩

/-- Normalization on native functions forces the coefficient map to be an isomorphism.
Source: Bhatt--Scholze, Remark 6.8.15.
(blueprint: lem-sf-native-pullback-coefficient-map).

Proof: compare with the native coefficient inverse-image isomorphism. Adjunction
reduces equality of the ring maps to equality of their adjuncts. On each test object,
the normalized formulas identify every function pointwise. Thus the maps agree and
the given coefficient map is invertible. Empty test objects use the same extensionality. -/
theorem nativePullbackCoefficient_isIso (O : Operations l p R S) : IsIso O.coefficient := by
  obtain ⟨c, hc, hf⟩ := nativePullbackCoefficientMap l p R S
  have he : O.coefficient = c := by
    apply ((proEtaleSheafAdjunction p CommRingCat.{u + 1}).homEquiv _ _).injective
    apply Sheaf.hom_ext
    ext V s
    apply ULift.ext
    apply Subtype.ext
    apply ContinuousMap.ext
    intro x
    exact (O.functions V s x).trans (hf V s x).symm
  rw [he]
  exact hc

/-- The ordinary balanced module pullback has the prescribed insertion-of-one unit.
Source: Stacks Tags 03D2 and 03D7; Bhatt--Scholze Remark 6.8.15.
(blueprint: lem-sf-native-pullback-coefficient-map).

Proof: compose the canonical inverse-image module adjunction on the small model
with the normalized scalar extension adjunction. The composite right adjoint is
identified with direct image along the adjunct coefficient map by the identity
on sections. The composite unit is the inverse-image unit followed by one tensor
that section. The canonical inverse-image unit is the model unit on sections.
The stated unit equation determines an adjunction uniquely by extensionality. -/
theorem nativePullbackModuleAdjunction
    (c : (adicTowerInverseImage p).obj (ring l Y S) ⟶ ring l X R) :
    ∃! adj : ContinuousRational.modulePull p c ⊣
        ContinuousRational.DirectImage.modulePush p c,
      ∀ (M : modules l Y S) (V : Y.ProEt) (m : M.val.obj (op V)),
      (adj.unit.app M).val.app (op V) m = ContinuousRational.moduleUnit p c M V m := by
  let ai := AlgebraicGeometry.Scheme.canonicalAdjunction p (ring l Y S)
  let a := ai.comp (pbcScalarAdjunction c)
  let er : pbcRestrict c ⋙ AlgebraicGeometry.Scheme.T p (ring l Y S) ≅
      ContinuousRational.DirectImage.modulePush p c := by
    refine NatIso.ofComponents (fun M ↦ ?_) ?_
    · apply (SheafOfModules.fullyFaithfulForget _).preimageIso
      exact PresheafOfModules.isoMk (fun V ↦ Iso.refl _) (by intros; rfl)
    · intro M N f
      ext V x
      rfl
  let adj := a.ofNatIsoRight er
  have hu (M : modules l Y S) (V : Y.ProEt) (m : M.val.obj (op V)) :
      (adj.unit.app M).val.app (op V) m = ContinuousRational.moduleUnit p c M V m := by
    change ((pbcScalarAdjunction c).unit.app
      ((proEtaleModuleInverseImage p (ring l Y S)).obj M)).val.app
      (op ((proEtaleBaseChange p).obj V)) ((ai.unit.app M).val.app (op V) m) = _
    refine ((pbcScalarAdjunction_exists c).exists.choose_spec _ _ _).trans ?_
    unfold ContinuousRational.moduleUnit
    congr 1
    exact AlgebraicGeometry.Scheme.canonicalUnit_sections p (ring l Y S) M (op V) m
  refine ⟨adj, hu, ?_⟩
  intro adj' hadj'
  apply Adjunction.ext
  ext M V m
  exact (hadj' M V.unop m).trans (hu M V.unop m).symm

end WeilConjectures.AdicQbarRealization.Proper
