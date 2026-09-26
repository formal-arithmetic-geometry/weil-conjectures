/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.PoincareDuality.Finiteness
public import WeilConjectures.EtaleCohomology.PoincareDuality.Pairing

/-!

# Degreewise duality over a field

Over a field coefficient stage a bounded complex of finite-dimensional spaces splits as the
direct sum of its shifted cohomologies, so the derived Poincaré pairing `β_K` of
`WeilConjectures.EtaleCohomology.PoincareDuality.Pairing` can be read off degree by degree.
The result is a family of perfect pairings

`⟨-,-⟩_i : H^i_c(X, K) ⊗ H^{2d-i}(X, K^∨(d)) ⟶ Λ`.

Eliminating the twist through `Λ(d) ⊗ Λ(-d) ≅ Λ` gives the line-valued form, with values in
`Λ(-d)`. For proper `X` compactly supported and ordinary cohomology agree — the comparison
`Ra_{X!} ⟶ Ra_{X*}` is an isomorphism, `AlgebraicGeometry.ProEtale.isIso_lowerShriekToLowerStar`
— so the same statement holds with `H^i_c` replaced by `H^i`.

At the integral stage `Λ = 𝒪_E` the degreewise form fails: only the derived statement holds
there. This is why the field hypothesis appears.

## Main definitions and results

- `AlgebraicGeometry.ProEtale.degreewisePoincarePairing`: the degreewise pairing `⟨-,-⟩_i`.
- `AlgebraicGeometry.ProEtale.isPerfectPairing_degreewisePoincarePairing`: it is perfect.

-/

@[expose] public section

universe u' u

open CategoryTheory Abelian Limits MonoidalCategory Opposite

namespace AlgebraicGeometry

open Scheme ProEtale

namespace ProEtale

section Definition

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

variable {X Y : Scheme.{u}}

/-- Blueprint `sk-thm-derived-duality`: Degreewise duality over a field.

The degreewise Poincaré pairing `⟨-,-⟩_i : H^i_c(X, K) ⊗ H^{2d-i}(X, K^∨(d)) ⟶ Λ`, the degree
`i` component of the derived Poincaré pairing `β_K`. -/
noncomputable def degreewisePoincarePairing (a : X ⟶ Y) [HasCompactification a] (d : ℕ)
    (γ : ((tateTwist A X (d : ℤ)).obj (𝟙_ _))⟦(2 * d : ℤ)⟧ ≅ dualizingComplex A a)
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)) (i : ℤ) :
    (H_c(a)[A](i)).obj K ⊗
        (cohomology A X (2 * d - i)).obj
          ((tateTwist A X (d : ℤ)).obj ((derivedDual A X).obj (op K))) ⟶
      𝟙_ A :=
  sorry

/-- Blueprint `sk-thm-derived-duality`: Degreewise duality over a field.

The line-valued, untwisted form of the degreewise Poincaré pairing:
`H^i_c(X, K) ⊗ H^{2d-i}(X, K^∨) ⟶ Λ(-d)`, obtained from `degreewisePoincarePairing` by
eliminating the twist through `Λ(d) ⊗ Λ(-d) ≅ Λ`. -/
noncomputable def untwistedDegreewisePoincarePairing (a : X ⟶ Y) [HasCompactification a]
    (d : ℕ) (γ : ((tateTwist A X (d : ℤ)).obj (𝟙_ _))⟦(2 * d : ℤ)⟧ ≅ dualizingComplex A a)
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)) (i : ℤ) :
    (H_c(a)[A](i)).obj K ⊗
        (cohomology A X (2 * d - i)).obj ((derivedDual A X).obj (op K)) ⟶
      twistedCoefficients A (-d : ℤ) :=
  sorry

end Definition

variable {Λ : Type (u + 1)} [Field Λ] {k₀ : Type u} [Field k₀] [Finite k₀] {d : ℕ}

/-- Blueprint `sk-thm-derived-duality`: Degreewise duality over a field.

Over a field coefficient stage, and for `K` perfect over `Λ_X`, the degreewise Poincaré
pairings `⟨-,-⟩_i : H^i_c(X, K) ⊗ H^{2d-i}(X, K^∨(d)) ⟶ Λ` are perfect for every `i`. -/
theorem isPerfectPairing_degreewisePoincarePairing (T : PoincareDualitySetting k₀ d)
    (k : Type u) [Field k] [IsAlgClosed k] [Algebra k₀ k]
    [HasCompactification (T.structureMorphism k)]
    (γ : ((tateTwist (ModuleCat.{u + 1} Λ) (T.geometricFibre k) (d : ℤ)).obj
        (𝟙_ _))⟦(2 * d : ℤ)⟧ ≅
      dualizingComplex (ModuleCat.{u + 1} Λ) (T.structureMorphism k))
    (K : DerivedCategory
      (Sheaf (Scheme.ProEt.topology (T.geometricFibre k)) (ModuleCat.{u + 1} Λ)))
    (hK : IsPerfect (ModuleCat.{u + 1} Λ) K) (i : ℤ) :
    MonoidalClosed.IsPerfectPairing
      (degreewisePoincarePairing (ModuleCat.{u + 1} Λ) (T.structureMorphism k) d γ K i) :=
  sorry

end ProEtale

end AlgebraicGeometry
