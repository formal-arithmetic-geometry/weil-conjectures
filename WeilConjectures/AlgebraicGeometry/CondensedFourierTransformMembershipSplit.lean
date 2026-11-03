/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedFourierTransform
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

/-! The four Fourier-transform membership clauses split from the first formula theorem.
(blueprint: lem-fd-fourier-transform-membership-split) -/

@[expose] public noncomputable section
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- The four transform-membership clauses in the first Fourier formula.

Source: current blueprint, lem-fd-first-formula.proof.md, the six membership clauses (the
transform memberships), applying thm-fd-transform-well-defined.md clause (2)
(blueprint: lem-fd-fourier-transform-membership-split).

Proof in words. Fix one of the two coefficient models. The Artin--Schreier kernel of the
character on the product of the two affine lines is locally free of rank one: on the finite
etale Artin--Schreier cover of degree q it is trivialized, and the character values lie in
the coefficients because E contains the p-th roots of unity. Pullback along the first
projection preserves bounded constructibility; tensor with a locally free module in degree
zero preserves it; extension by zero along the open immersion of the compactification
preserves it. The product is of finite type over k, which has characteristic p different
from ell, so ell is invertible and proper direct image to the second affine line preserves
bounded constructibility; the final shift by the rank one does too. Apply this to the
regular complex and to the origin skyscraper, both bounded constructible. The existing
theorem `condensedFourierTransform_boundedConstructible_ellAdic` gives the argument only for
characters of the prime field; the remaining work is the same argument for an arbitrary
finite field k0 with the degree-q kernel. -/
theorem first_formula_transform_membership_split
    (p ℓ : ℕ) [Fact p.Prime] [Fact ℓ.Prime] (hpℓ : p ≠ ℓ)
    (k₀ : Type u) [Field k₀] [Fintype k₀] [CharP k₀ p]
    (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (hμ : ∀ ζ : rootsOfUnity p (PadicAlgCl ℓ),
      ((ζ : (PadicAlgCl ℓ)ˣ) : PadicAlgCl ℓ) ∈ E.1)
    (ψ : AddChar k₀ E) (hψ : ψ ≠ 1)
    (k : Type u) [Field k] [Algebra k₀ k] (hk : Finite k ∨ IsAlgClosed k)
    (c : Compactification (pullback.snd
      (AffineSpace PUnit (Spec (.of k)) ↘ Spec (.of k))
      (AffineSpace PUnit (Spec (.of k)) ↘ Spec (.of k)))) :
  (boundedConstructible _ ((condensedFieldFourierTransform
      (Profinite.continuousMapRingObj E.1) k₀ k
      ((Profinite.continuousMapConstRingHom E).toMonoidHom.compAddChar ψ) c).obj
    ((DerivedCategory.singleFunctor _ 0).obj
      (Mod.regular (condensedRingObj (Profinite.continuousMapRingObj E.1)
        (AffineSpace PUnit (Spec (.of k))))))) ∧
  (boundedConstructible _ ((condensedFieldFourierTransform
      (Profinite.continuousMapRingObj E.1) k₀ k
      ((Profinite.continuousMapConstRingHom E).toMonoidHom.compAddChar ψ) c).obj
    ((CondensedRing.lowerStar (Profinite.continuousMapRingObj E.1)
      (AffineSpace.zeroSection PUnit (Spec (.of k)))).rightDerivedFunctor.obj
      ((DerivedCategory.singleFunctor _ 0).obj
        (Mod.regular (condensedRingObj (Profinite.continuousMapRingObj E.1)
          (Spec (.of k))))))) ) ∧
  (boundedConstructible _ ((condensedFieldFourierTransform
      (Profinite.padicAlgClRingObj ℓ) k₀ k
      ((Profinite.PadicAlgCl.constRingHom ℓ).toMonoidHom.compAddChar
        (E.1.subtype.toMonoidHom.compAddChar ψ)) c).obj
    ((DerivedCategory.singleFunctor _ 0).obj
      (Mod.regular (condensedRingObj (Profinite.padicAlgClRingObj ℓ)
        (AffineSpace PUnit (Spec (.of k))))))) ∧
  boundedConstructible _ ((condensedFieldFourierTransform
      (Profinite.padicAlgClRingObj ℓ) k₀ k
      ((Profinite.PadicAlgCl.constRingHom ℓ).toMonoidHom.compAddChar
        (E.1.subtype.toMonoidHom.compAddChar ψ)) c).obj
    ((CondensedRing.lowerStar (Profinite.padicAlgClRingObj ℓ)
      (AffineSpace.zeroSection PUnit (Spec (.of k)))).rightDerivedFunctor.obj
      ((DerivedCategory.singleFunctor _ 0).obj
        (Mod.regular (condensedRingObj (Profinite.padicAlgClRingObj ℓ)
          (Spec (.of k))))))) ) ) := by
  sorry

end AlgebraicGeometry.ProEtale
