/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedFourierTransform
public import WeilConjectures.AlgebraicGeometry.Internal.InternalSignedTateTwist
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
public import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMapCondensedRingSupplement
public import WeilConjectures.AlgebraicGeometry.Finite.FiniteDiscreteCoefficientTriangulated
public import Mathlib.CategoryTheory.Monoidal.CommMon_
public import WeilConjectures.CategoryTheory.CommutativeSiteDerivedConstantModuleFunctor
public import WeilConjectures.CategoryTheory.Constant.ConstantModuleFiniteTypeReflection
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import WeilConjectures.CategoryTheory.ModuleObjects.ConstantRingSheaf
public import WeilConjectures.ProEtaleCoefficients.BoundedConstructibleCounterexample.NonFiniteMultiplicationKernel
public import Mathlib.FieldTheory.IsSepClosed
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
public import WeilConjectures.CategoryTheory.RingObjects.RingPresheaf
public import WeilConjectures.CategoryTheory.RingObjects.Ab
public import WeilConjectures.CategoryTheory.SheafTensor
public import Mathlib.Algebra.TrivSqZeroExt.Basic
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.RingTheory.Finiteness.Defs
public import WeilConjectures.CategoryTheory.SiteConstantModuleFunctorGeneral
public import Mathlib.CategoryTheory.Sites.Limits
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.GlobalSections
public import WeilConjectures.CategoryTheory.ModuleObjects.Free
public import WeilConjectures.CategoryTheory.ModuleObjects.MapMod
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.CategoryTheory.Monoidal.Mod
public import WeilConjectures.CategoryTheory.InternalAbelianSheafModuleEquivalence
public import WeilConjectures.CategoryTheory.Site.SiteConstantModuleHomSupplement
public import WeilConjectures.CategoryTheory.ProEtaleCoefficients.SectionActionInternal
public import WeilConjectures.CategoryTheory.ModuleObjects.ConstantRingPresheaf
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.PreservesSheafification
public import WeilConjectures.AlgebraicGeometry.ProEtaleObjectPullbackRestriction
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.IsoClosed
public import Mathlib.Algebra.Field.ULift
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMapGlobalSections
public import Mathlib.FieldTheory.IsAlgClosed.Basic

import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleClosedPushforward
import WeilConjectures.AlgebraicGeometry.CondensedRegularSingleShiftBounded
import WeilConjectures.AlgebraicGeometry.CondensedFourierTransformMembershipSplit
import WeilConjectures.AlgebraicGeometry.CondensedFourierTwistMembershipSplit

/-! # One calculation in the first Fourier formulas

Source: current blueprint, lem-fd-first-formula.proof.md.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- The six bounded-constructibility clauses for both coefficient models.

Source: current blueprint, first-formula proof, coefficient and constructibility clauses
(blueprint: lem-fd-first-formula-membership).

Proof in words. For either coefficient model the regular module is locally free of rank one,
hence constructible, so its degree-zero complex and the degree-one shift of that complex are
bounded constructible ([lem-fd-regular-single-shift-bounded]). The affine line over k is
Noetherian, being of finite type over a field, and the zero section is a closed immersion;
bounded-constructible stability of closed direct image ([sk-thm-sf-ctf-stability]) applied to
the regular complex on Spec k gives the degree-zero origin skyscraper. The four transform
memberships are [lem-fd-fourier-transform-membership-split], whose proof is the
Artin--Schreier kernel preservation argument of [thm-fd-transform-well-defined] for the
arbitrary finite field k0. The two signed-twisted skyscraper memberships are
[lem-fd-fourier-twist-membership-split]: the positive Tate line and its dual are locally free
of rank one, and tensor and shift preserve bounded constructibility. No comparison isomorphism
is asserted here. -/
theorem first_formula_membership
    (p ℓ : ℕ) [Fact p.Prime] [Fact ℓ.Prime] (hpℓ : p ≠ ℓ)
    (k₀ : Type u) [Field k₀] [Fintype k₀] [CharP k₀ p]
    (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (hμ : ∀ ζ : rootsOfUnity p (PadicAlgCl ℓ), ((ζ : (PadicAlgCl ℓ)ˣ) : PadicAlgCl ℓ) ∈ E.1)
    (ψ : AddChar k₀ E) (hψ : ψ ≠ 1)
    (k : Type u) [Field k] [Algebra k₀ k] (hk : Finite k ∨ IsAlgClosed k)
    (c : Compactification (pullback.snd
      (AffineSpace PUnit (Spec (.of k)) ↘ Spec (.of k))
      (AffineSpace PUnit (Spec (.of k)) ↘ Spec (.of k)))) :
  (boundedConstructible _ ((DerivedCategory.singleFunctor _ 0).obj
      (Mod.regular (condensedRingObj (Profinite.continuousMapRingObj E.1) (AffineSpace PUnit
        (Spec (.of k)))))) ∧
  boundedConstructible _ ((CondensedRing.lowerStar (Profinite.continuousMapRingObj E.1)
      (AffineSpace.zeroSection PUnit (Spec (.of k)))).rightDerivedFunctor.obj
        ((DerivedCategory.singleFunctor _ 0).obj
          (Mod.regular (condensedRingObj (Profinite.continuousMapRingObj E.1) (Spec (.of k)))))) ∧
  boundedConstructible _ ((condensedFieldFourierTransform (Profinite.continuousMapRingObj E.1) k₀
        k ((Profinite.continuousMapConstRingHom E).toMonoidHom.compAddChar ψ) c).obj
    ((DerivedCategory.singleFunctor _ 0).obj
      (Mod.regular (condensedRingObj (Profinite.continuousMapRingObj E.1) (AffineSpace PUnit
        (Spec (.of k))))))) ∧
  boundedConstructible _ ((condensedFieldFourierTransform (Profinite.continuousMapRingObj E.1) k₀
        k ((Profinite.continuousMapConstRingHom E).toMonoidHom.compAddChar ψ) c).obj
    ((CondensedRing.lowerStar (Profinite.continuousMapRingObj E.1)
      (AffineSpace.zeroSection PUnit (Spec (.of k)))).rightDerivedFunctor.obj
        ((DerivedCategory.singleFunctor _ 0).obj
          (Mod.regular (condensedRingObj (Profinite.continuousMapRingObj E.1) (Spec (.of k))))))) ∧
  boundedConstructible _ ((shiftFunctor _ (-1 : ℤ)).obj
    (spInternalComplexTwist (AffineSpace PUnit (Spec (.of k))) _ (spRationalTwist (AffineSpace
        PUnit (Spec (.of k))) ℓ E)
      ((CondensedRing.lowerStar (Profinite.continuousMapRingObj E.1)
      (AffineSpace.zeroSection PUnit (Spec (.of k)))).rightDerivedFunctor.obj
        ((DerivedCategory.singleFunctor _ 0).obj
          (Mod.regular (condensedRingObj (Profinite.continuousMapRingObj E.1) (Spec (.of k))))))
        (-1))) ∧
  boundedConstructible _ ((shiftFunctor _ (1 : ℤ)).obj
    ((DerivedCategory.singleFunctor _ 0).obj
      (Mod.regular (condensedRingObj (Profinite.continuousMapRingObj E.1) (AffineSpace PUnit
        (Spec (.of k)))))))) ∧
  (boundedConstructible _ ((DerivedCategory.singleFunctor _ 0).obj
      (Mod.regular (condensedRingObj (Profinite.padicAlgClRingObj ℓ) (AffineSpace PUnit (Spec
        (.of k)))))) ∧
  boundedConstructible _ ((CondensedRing.lowerStar (Profinite.padicAlgClRingObj ℓ)
      (AffineSpace.zeroSection PUnit (Spec (.of k)))).rightDerivedFunctor.obj
        ((DerivedCategory.singleFunctor _ 0).obj
          (Mod.regular (condensedRingObj (Profinite.padicAlgClRingObj ℓ) (Spec (.of k)))))) ∧
  boundedConstructible _ ((condensedFieldFourierTransform (Profinite.padicAlgClRingObj ℓ) k₀ k
        ((Profinite.PadicAlgCl.constRingHom ℓ).toMonoidHom.compAddChar
        (E.1.subtype.toMonoidHom.compAddChar ψ)) c).obj
    ((DerivedCategory.singleFunctor _ 0).obj
      (Mod.regular (condensedRingObj (Profinite.padicAlgClRingObj ℓ) (AffineSpace PUnit (Spec
        (.of k))))))) ∧
  boundedConstructible _ ((condensedFieldFourierTransform (Profinite.padicAlgClRingObj ℓ) k₀ k
        ((Profinite.PadicAlgCl.constRingHom ℓ).toMonoidHom.compAddChar
        (E.1.subtype.toMonoidHom.compAddChar ψ)) c).obj
    ((CondensedRing.lowerStar (Profinite.padicAlgClRingObj ℓ)
      (AffineSpace.zeroSection PUnit (Spec (.of k)))).rightDerivedFunctor.obj
        ((DerivedCategory.singleFunctor _ 0).obj
          (Mod.regular (condensedRingObj (Profinite.padicAlgClRingObj ℓ) (Spec (.of k))))))) ∧
  boundedConstructible _ ((shiftFunctor _ (-1 : ℤ)).obj
    (spInternalComplexTwist (AffineSpace PUnit (Spec (.of k))) _ (spQbarTwist (AffineSpace PUnit
        (Spec (.of k))) ℓ)
      ((CondensedRing.lowerStar (Profinite.padicAlgClRingObj ℓ)
      (AffineSpace.zeroSection PUnit (Spec (.of k)))).rightDerivedFunctor.obj
        ((DerivedCategory.singleFunctor _ 0).obj
          (Mod.regular (condensedRingObj (Profinite.padicAlgClRingObj ℓ) (Spec (.of k)))))) (-1))) ∧
  boundedConstructible _ ((shiftFunctor _ (1 : ℤ)).obj
    ((DerivedCategory.singleFunctor _ 0).obj
      (Mod.regular (condensedRingObj (Profinite.padicAlgClRingObj ℓ) (AffineSpace PUnit (Spec
        (.of k)))))))) := by
  classical
  have hregE : boundedConstructible
      (condensedRingObj (Profinite.continuousMapRingObj E.1)
        (AffineSpace PUnit (Spec (.of k))))
      ((DerivedCategory.singleFunctor _ 0).obj
        (Mod.regular (condensedRingObj (Profinite.continuousMapRingObj E.1)
          (AffineSpace PUnit (Spec (.of k)))))) := by
    exact (regular_single_shift_bounded
      (Λ := Profinite.continuousMapRingObj E.1)
      (AffineSpace PUnit (Spec (.of k)))).1
  have hregQ : boundedConstructible
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ)
        (AffineSpace PUnit (Spec (.of k))))
      ((DerivedCategory.singleFunctor _ 0).obj
        (Mod.regular (condensedRingObj (Profinite.padicAlgClRingObj ℓ)
          (AffineSpace PUnit (Spec (.of k)))))) := by
    exact (regular_single_shift_bounded
      (Λ := Profinite.padicAlgClRingObj ℓ)
      (AffineSpace PUnit (Spec (.of k)))).1
  have hdeltaE : boundedConstructible
      (condensedRingObj (Profinite.continuousMapRingObj E.1)
        (AffineSpace PUnit (Spec (.of k))))
      ((CondensedRing.lowerStar (Profinite.continuousMapRingObj E.1)
        (AffineSpace.zeroSection PUnit (Spec (.of k)))).rightDerivedFunctor.obj
        ((DerivedCategory.singleFunctor _ 0).obj
          (Mod.regular (condensedRingObj (Profinite.continuousMapRingObj E.1)
            (Spec (.of k)))))) := by
    let V := AffineSpace PUnit (Spec (.of k))
    have : IsNoetherian V := isNoetherian_of_locallyOfFiniteType (V ↘ Spec (.of k))
    exact CondensedRing.boundedConstructible_rightDerivedLowerStar_of_isClosedImmersion
      (Profinite.continuousMapRingObj E.1)
      (AffineSpace.zeroSection PUnit (Spec (.of k)))
      (regular_single_shift_bounded
        (Λ := Profinite.continuousMapRingObj E.1) (Spec (.of k))).1
  have hdeltaQ : boundedConstructible
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ)
        (AffineSpace PUnit (Spec (.of k))))
      ((CondensedRing.lowerStar (Profinite.padicAlgClRingObj ℓ)
        (AffineSpace.zeroSection PUnit (Spec (.of k)))).rightDerivedFunctor.obj
        ((DerivedCategory.singleFunctor _ 0).obj
          (Mod.regular (condensedRingObj (Profinite.padicAlgClRingObj ℓ)
            (Spec (.of k)))))) := by
    let V := AffineSpace PUnit (Spec (.of k))
    have : IsNoetherian V := isNoetherian_of_locallyOfFiniteType (V ↘ Spec (.of k))
    exact CondensedRing.boundedConstructible_rightDerivedLowerStar_of_isClosedImmersion
      (Profinite.padicAlgClRingObj ℓ)
      (AffineSpace.zeroSection PUnit (Spec (.of k)))
      (regular_single_shift_bounded
        (Λ := Profinite.padicAlgClRingObj ℓ) (Spec (.of k))).1
  have hshiftE : boundedConstructible
      (condensedRingObj (Profinite.continuousMapRingObj E.1)
        (AffineSpace PUnit (Spec (.of k))))
      ((shiftFunctor _ (1 : ℤ)).obj
        ((DerivedCategory.singleFunctor _ 0).obj
          (Mod.regular (condensedRingObj (Profinite.continuousMapRingObj E.1)
            (AffineSpace PUnit (Spec (.of k))))))) := by
    exact (regular_single_shift_bounded
      (Λ := Profinite.continuousMapRingObj E.1)
      (AffineSpace PUnit (Spec (.of k)))).2
  have hshiftQ : boundedConstructible
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ)
        (AffineSpace PUnit (Spec (.of k))))
      ((shiftFunctor _ (1 : ℤ)).obj
        ((DerivedCategory.singleFunctor _ 0).obj
          (Mod.regular (condensedRingObj (Profinite.padicAlgClRingObj ℓ)
            (AffineSpace PUnit (Spec (.of k))))))) := by
    exact (regular_single_shift_bounded
      (Λ := Profinite.padicAlgClRingObj ℓ)
      (AffineSpace PUnit (Spec (.of k)))).2
  have htrans := first_formula_transform_membership_split p ℓ hpℓ k₀ E hμ ψ hψ k hk c
  have htwist := first_formula_twist_membership_split p ℓ hpℓ k₀ E hμ ψ hψ k hk c
  exact ⟨⟨hregE, hdeltaE, htrans.1, htrans.2.1, htwist.1, hshiftE⟩,
    ⟨hregQ, hdeltaQ, htrans.2.2.1, htrans.2.2.2, htwist.2, hshiftQ⟩⟩

end AlgebraicGeometry.ProEtale
