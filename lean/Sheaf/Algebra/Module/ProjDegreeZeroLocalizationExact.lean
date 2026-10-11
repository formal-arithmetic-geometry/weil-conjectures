/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
import Sheaf.Algebra.Module.DegreeZeroFractions
import Mathlib.Algebra.Module.GradedModule
import Mathlib.Algebra.DirectSum.Module
import Mathlib.Algebra.Module.LocalizedModule.Exact
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization

/-!
# Exactness of degree-zero localization on the projective line

Source: Stacks Project, Constructions, Lemma 01M7 (5), and Algebra, Section 00JM
(blueprint: lem-sc-p1-proj-degreezero-localization-exact).
-/

universe u v₀ v₁ v₂

open MvPolynomial SetLike

namespace LocalizedModule

attribute [local instance] moduleOfIsLocalization MvPolynomial.gradedAlgebra

/-- Degree-zero homogeneous localization of a short exact graded sequence over `k[x₀,x₁]`
is short exact over its degree-zero localized ring. The existential submodules have exactly
the equal-degree fractions as carriers; the existential linear maps are exactly the restrictions
of the ordinary localization maps. The module gradings are internal direct sums of additive
subgroups indexed by all integers, as in the landed graded-module siblings.
Thus the modules and maps are uniquely specified.

Source: Stacks Project, Constructions, Lemma 01M7 (5), and Algebra, Section 00JM.
Proof: (1) Apply `lem-sc-p1-localization-short-exact` to the homogeneous denominators outside
the prime, giving ordinary localization exactness, including injectivity and surjectivity.
(2) Homogeneous localization has the induced grading `deg(y/h) = deg(y) - deg(h)`;
the fraction maps are well defined by the ordinary localization equivalence relation and
preserve this grading. (3) Apply `lem-sc-p1-graded-degree-component-exact` in degree zero.
Its components are precisely the equal-degree fractions, and its maps send `y/h` to `φ(y)/h`.
(blueprint: lem-sc-p1-proj-degreezero-localization-exact) -/
theorem proj_degreeZero_localization_shortExact
    {k : Type u} [Field k]
    {M₀ : Type v₀} {M₁ : Type v₁} {M₂ : Type v₂}
    [AddCommGroup M₀] [AddCommGroup M₁] [AddCommGroup M₂]
    [Module (MvPolynomial (Fin 2) k) M₀]
    [Module (MvPolynomial (Fin 2) k) M₁]
    [Module (MvPolynomial (Fin 2) k) M₂]
    (𝓜₀ : ℤ → AddSubgroup M₀) (𝓜₁ : ℤ → AddSubgroup M₁)
    (𝓜₂ : ℤ → AddSubgroup M₂)
    (h𝓜₀ : DirectSum.IsInternal 𝓜₀) (h𝓜₁ : DirectSum.IsInternal 𝓜₁)
    (h𝓜₂ : DirectSum.IsInternal 𝓜₂)
    (hsmul₀ : ∀ (n : ℕ) (z : ℤ) (a : MvPolynomial (Fin 2) k) (y : M₀),
      a ∈ homogeneousSubmodule (Fin 2) k n → y ∈ 𝓜₀ z → a • y ∈ 𝓜₀ (n + z))
    (hsmul₁ : ∀ (n : ℕ) (z : ℤ) (a : MvPolynomial (Fin 2) k) (y : M₁),
      a ∈ homogeneousSubmodule (Fin 2) k n → y ∈ 𝓜₁ z → a • y ∈ 𝓜₁ (n + z))
    (hsmul₂ : ∀ (n : ℕ) (z : ℤ) (a : MvPolynomial (Fin 2) k) (y : M₂),
      a ∈ homogeneousSubmodule (Fin 2) k n → y ∈ 𝓜₂ z → a • y ∈ 𝓜₂ (n + z))
    (f : M₀ →ₗ[MvPolynomial (Fin 2) k] M₁)
    (g : M₁ →ₗ[MvPolynomial (Fin 2) k] M₂)
    (hf : ∀ (z : ℤ) (y : M₀), y ∈ 𝓜₀ z → f y ∈ 𝓜₁ z)
    (hg : ∀ (z : ℤ) (y : M₁), y ∈ 𝓜₁ z → g y ∈ 𝓜₂ z)
    (hinj : Function.Injective f) (hex : Function.Exact f g)
    (hsurj : Function.Surjective g)
    (p : Ideal (MvPolynomial (Fin 2) k)) [p.IsPrime]
    (hp : p.IsHomogeneous (homogeneousSubmodule (Fin 2) k))
    (hproj : ¬ (HomogeneousIdeal.irrelevant
      (homogeneousSubmodule (Fin 2) k)).toIdeal ≤ p) :
    let 𝒜 := homogeneousSubmodule (Fin 2) k
    let T := homogeneousSubmonoid 𝒜 ⊓ p.primeCompl
    let H := HomogeneousLocalization 𝒜 T
    letI : Module H (LocalizedModule T M₀) :=
      Module.compHom (LocalizedModule T M₀) (algebraMap H (Localization T))
    letI : Module H (LocalizedModule T M₁) :=
      Module.compHom (LocalizedModule T M₁) (algebraMap H (Localization T))
    letI : Module H (LocalizedModule T M₂) :=
      Module.compHom (LocalizedModule T M₂) (algebraMap H (Localization T))
    let Z₀ := degreeZeroFractions (fun n : ℕ => (𝒜 n : Set _))
      (fun n : ℕ => (𝓜₀ n : Set M₀)) T
    let Z₁ := degreeZeroFractions (fun n : ℕ => (𝒜 n : Set _))
      (fun n : ℕ => (𝓜₁ n : Set M₁)) T
    let Z₂ := degreeZeroFractions (fun n : ℕ => (𝒜 n : Set _))
      (fun n : ℕ => (𝓜₂ n : Set M₂)) T
    ∃ (N₀ : Submodule H (LocalizedModule T M₀))
      (N₁ : Submodule H (LocalizedModule T M₁))
      (N₂ : Submodule H (LocalizedModule T M₂)),
      (N₀ : Set _) = Z₀ ∧ (N₁ : Set _) = Z₁ ∧ (N₂ : Set _) = Z₂ ∧
      ∃ (f₀ : N₀ →ₗ[H] N₁) (g₀ : N₁ →ₗ[H] N₂),
        (∀ x : N₀, (f₀ x : LocalizedModule T M₁) =
          IsLocalizedModule.map T (mkLinearMap T M₀) (mkLinearMap T M₁) f x) ∧
        (∀ y : N₁, (g₀ y : LocalizedModule T M₂) =
          IsLocalizedModule.map T (mkLinearMap T M₁) (mkLinearMap T M₂) g y) ∧
        Function.Injective f₀ ∧ Function.Exact f₀ g₀ ∧ Function.Surjective g₀ := by
  sorry

end LocalizedModule
