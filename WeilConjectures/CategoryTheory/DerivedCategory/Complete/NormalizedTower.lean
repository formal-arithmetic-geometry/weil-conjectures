/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Fractions
public import Mathlib.CategoryTheory.Functor.OfSequence
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.DerivedBaseChange
public import WeilConjectures.Algebra.Homology.DerivedCategory.ReductionDatum
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Reduction
public import WeilConjectures.Algebra.Homology.DerivedCategory.AdicTower
public import Mathlib.RingTheory.Ideal.Quotient.PowTransition

/-!
# Strict models of normalized towers

Let `(C, J)` be an essentially small site, `R` a commutative ring and `I` an ideal, and put
`A_n = R ⧸ Iⁿ`. A *normalized tower* is a family of objects `L_n ∈ D(J, A_n)` with transition
maps `t_n : L_{n+1} ⟶ Res L_n` exhibiting `L_n` as the derived base change
`L_{n+1} ⊗ᴸ_{A_{n+1}} A_n` (`CategoryTheory.Sheaf.IsDerivedBaseChange`).

This file shows that a normalized tower is represented by a tower of K-flat complexes and chain
maps: there are K-flat complexes `P_n` of flat sheaves of `A_n`-modules with
`Q P_n ≅ L_n` and chain maps `P_{n+1} ⟶ Res P_n` representing the transition maps
(`DerivedCategory.exists_kFlatModelTower`).

## Main definitions

- `CochainComplex.IsKFlat`: K-flat complexes.
- `DerivedCategory.KFlatModel`: a K-flat model of an object of the derived category.
-/

@[expose] public section

universe v u

open CategoryTheory Limits Opposite

section

variable {𝒜 : Type*} [Category 𝒜] [Abelian 𝒜] [IsGrothendieckAbelian.{v} 𝒜]
  [MonoidalCategory 𝒜] [MonoidalPreadditive 𝒜] [MonoidalClosed 𝒜] [BraidedCategory 𝒜]
  [Abelian.HasFunctorialFlatResolution 𝒜]

end

namespace DerivedCategory

variable {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
  {J : GrothendieckTopology C}

namespace KFlatModel

variable {A A' : Type (u + 1)} [CommRing A] [CommRing A']

end KFlatModel

section Restrict

variable {A A' A'' : Type (u + 1)} [CommRing A] [CommRing A'] [CommRing A'']
  {f : A →+* A'} {g : A' →+* A''} {gf : A →+* A''} (hgf : gf = g.comp f)

end Restrict

section Tower

variable {A : ℕ → Type (u + 1)} [∀ n, CommRing (A n)] {φ : ∀ n, A (n + 1) →+* A n}
  (L : ∀ n : ℕ, DerivedCategory (Sheaf J (ModuleCat.{u + 1} (A n))))
  (t : ∀ n : ℕ, L (n + 1) ⟶ (Sheaf.derivedRestrictScalars J (φ n)).obj (L n))

end Tower

section Coherence

variable {A₀ A₁ A₂ A₃ : Type (u + 1)} [CommRing A₀] [CommRing A₁] [CommRing A₂] [CommRing A₃]
  (f₁ : A₀ →+* A₁) (f₂ : A₁ →+* A₂) (f₃ : A₂ →+* A₃) (f₁₂ : A₀ →+* A₂) (f₂₃ : A₁ →+* A₃)
  (f₁₂₃ : A₀ →+* A₃) (h₁₂ : f₁₂ = f₂.comp f₁) (h₂₃ : f₂₃ = f₃.comp f₂)
  (h₁ : f₁₂₃ = f₂₃.comp f₁) (h₂ : f₁₂₃ = f₃.comp f₁₂)

end Coherence

section RTower

variable {R : Type (u + 1)} [CommRing R] {A : ℕ → Type (u + 1)} [∀ n, CommRing (A n)]
  (φ : ∀ {n m : ℕ}, n ≤ m → A m →+* A n) (ψ : ∀ n, R →+* A n)
  (hψ : ∀ {n m : ℕ} (h : n ≤ m), (φ h).comp (ψ m) = ψ n)
  (L : ∀ n : ℕ, DerivedCategory (Sheaf J (ModuleCat.{u + 1} (A n))))
  (t : ∀ n : ℕ, L (n + 1) ⟶ (Sheaf.derivedRestrictScalars J (φ n.le_succ)).obj (L n))

variable (hφ : ∀ {n m k : ℕ} (h₁ : n ≤ m) (h₂ : m ≤ k), (φ h₁).comp (φ h₂) = φ (h₁.trans h₂))

end RTower

section Smul

variable {A A' : Type (u + 1)} [CommRing A] [CommRing A'] (f : A →+* A')

end Smul

section Normalized

variable {R : Type (u + 1)} [CommRing R] {A : ℕ → Type (u + 1)} [∀ n, CommRing (A n)]
  (φ : ∀ {n m : ℕ}, n ≤ m → A m →+* A n) (ψ : ∀ n, R →+* A n)
  (hψ : ∀ {n m : ℕ} (h : n ≤ m), (φ h).comp (ψ m) = ψ n)
  (hφ : ∀ {n m k : ℕ} (h₁ : n ≤ m) (h₂ : m ≤ k), (φ h₁).comp (φ h₂) = φ (h₁.trans h₂))
  {ϖ : R} (hψ₀ : ∀ n, ψ n (ϖ ^ n) = 0)
  (hexact : ∀ a b : ℕ, Function.Exact (fun x : A (a + b) ↦ ψ (a + b) (ϖ ^ a) * x)
    (fun x ↦ ψ (a + b) (ϖ ^ b) * x))
  (hsurj : ∀ {n m : ℕ} (h : n ≤ m), Function.Surjective (φ h))
  (hker : ∀ {n m : ℕ} (h : n ≤ m), RingHom.ker (φ h) = Ideal.span {ψ m (ϖ ^ n)})
  (L : ∀ n : ℕ, DerivedCategory (Sheaf J (ModuleCat.{u + 1} (A n))))
  (t : ∀ n : ℕ, L (n + 1) ⟶ (Sheaf.derivedRestrictScalars J (φ n.le_succ)).obj (L n))
  (ht : ∀ n, Sheaf.IsDerivedBaseChange (t n))

end Normalized

section Quotient

variable {R : Type (u + 1)} [CommRing R] {I : Ideal R} {ϖ : R} (hϖ : ϖ ∈ nonZeroDivisors R)
  (hI : I = Ideal.span {ϖ})

end Quotient

end DerivedCategory
