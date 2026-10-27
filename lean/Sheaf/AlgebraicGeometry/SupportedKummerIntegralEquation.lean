/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q1
-/
module

public import Sheaf.AlgebraicGeometry.CartierReductionData
import all Sheaf.AlgebraicGeometry.EtaleSupportedIntegralDerivedUnit

/-!
# Integral equation of a normalized supported Kummer boundary

Source: blueprint lem-amb-cartier-kummer-map, relative boundary and scalar extension.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Etale
open Scheme

set_option linter.auxLemma false in
attribute [local instance 100000] DerivedCategoryModule._proof_1 DerivedCategoryModule._proof_2
attribute [local instance 10000] cachedAbSheafify cachedModSheafify
attribute [local irreducible] HasDerivedCategory.ofIsGrothendieckAbelian
  DerivedCategory.singleFunctors Ext.homEquiv Ext.comp Ext.mk₀ Ext.mapExactFunctor

/-- Forgetting coefficients and evaluating at the integral supported generator identifies
any normalized supported Kummer boundary with the common pole extension followed by
its Kummer extension and coefficient root map. No finiteness or positivity is needed.
Source: blueprint lem-amb-cartier-kummer-map, relative extension and scalar paragraph;
Stacks 03PL and 0A45 (blueprint: lem-asd-supported-kummer-integral-equation).

Proof: specialize the relative boundary specification to the complementary open of D.
The extension supplied there satisfies the pole-boundary specification for every
complementary open, because all such opens are equal. The uniqueness of the integral
pole class therefore identifies its extension class with cartierPoleBoundary. Substitute
this equality in the final Yoneda-product equation of the boundary specification. -/
theorem supported_kummer_integral_equation
    (A : Type (u + 1)) [CommRing A] (N : ℕ) (hA : (N : A) = 0)
    {D T : Scheme.{u}} (i : D ⟶ T) [IsClosedImmersion i] (hI : i.ker.IsInvertible)
    (hT : IsUnit (N : Γ(T, ⊤)))
    (κ : Ext ((lowerStar (ModuleCat.{u + 1} A) i).obj (ordinaryFiniteConstant A D))
      (finiteEtaleTateLine T N A hA) 2)
    (hκ : SupportedKummerBoundary A N hA i hI hT κ) :
    (Ext.mk₀ (supportedIntegralGenerator A i)).comp
        (κ.mapExactFunctor (RawModuleScalarComparison.forget A T)) (zero_add 2) =
      ((cartierPoleBoundary i hI).comp (T.kummerSequence_shortExact N hT).extClass rfl).comp
        (Ext.mk₀ (ordinaryFiniteRootMap A N hA T)) (add_zero 2) := by
  classical
  let := hI.isInvertible_dual_toModules
  let := Scheme.Modules.IsInvertible.sheafOfModules_isInvertible
    (Scheme.Modules.dual i.ker.toModules)
  let W : T.Opens := ⟨(Set.range i.base)ᶜ, i.isClosedEmbedding.isClosed_range.isOpen_compl⟩
  unfold SupportedKummerBoundary at hκ
  obtain ⟨τ, E, a, b, hab, hE, f, hτ, hf, hb, hzero, hext⟩ := hκ W rfl
  have hEspec : CartierPoleBoundarySpec i hI hE.extClass := by
    intro W' hW'
    have hw : W' = W := by
      apply TopologicalSpace.Opens.ext
      exact hW'
    subst W'
    exact ⟨τ, E, a, b, hab, hE, f, hτ, hf, hb, hzero, rfl⟩
  have hEβ : hE.extClass = cartierPoleBoundary i hI :=
    (Classical.choose_spec (cartierPoleBoundary_existsUnique i hI)).2 _ hEspec
  rw [← hEβ]
  exact hext


end AlgebraicGeometry.Etale
