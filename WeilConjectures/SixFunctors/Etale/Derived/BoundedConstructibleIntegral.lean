/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Complete.Defs
public import WeilConjectures.CategoryTheory.DerivedCategory.Constructible
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.SixFunctors.Etale.Derived.TorAmplitude

/-!

# The integral stage of the `ℓ`-adic formalism on the étale site

For an ideal `I` of a ring `Λ`, the object property
`AlgebraicGeometry.Etale.DerivedCategory.boundedConstructibleIntegral` of `D(X_ét, Λ)` consists of
the objects which are derived complete for `I` and whose reductions modulo the powers of `I` are
bounded constructible of uniformly bounded Tor amplitude.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Opposite Pretriangulated

open scoped CategoryTheory.Functor TensorProduct

namespace AlgebraicGeometry

open Scheme

namespace Etale

section Integral

variable {Λ : Type (u + 1)} [CommRing Λ] (I : Ideal Λ)

/-- The small étale site of a scheme is essentially small. Instance search does not find this
in the presence of the imports of this file. -/
local instance (X : Scheme.{u}) : EssentiallySmall.{u + 1} X.Etale :=
  have : LocallySmall.{u + 1} X.Etale :=
    @locallySmall_of_univLE X.Etale _ (@univLE_of_max.{u, u + 1} UnivLE.self)
  essentiallySmall_of_small_of_locallySmall _

/-- The integral stage `D^b_c(X, Λ)` of the `ℓ`-adic formalism, for `Λ = 𝒪_E` and `I = 𝔪_E`, as
an object property of `D(X_ét, Λ)`: the objects `K` which are derived complete for `I` and whose
reductions `K ⊗ᴸ Λ/Iⁿ⁺¹` are bounded constructible of Tor amplitude in one common interval
`[a, b]`. -/
def DerivedCategory.boundedConstructibleIntegral (X : Scheme.{u}) :
    ObjectProperty (_root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :=
  fun K ↦ DerivedCategory.derivedComplete X.smallEtaleTopology I K ∧
    ∃ a b : ℤ, ∀ n : ℕ,
      DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X
          ((reductionModIdeal Λ X (I ^ (n + 1))).obj K) ∧
        DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} Λ) X a b
          ((reductionModIdeal Λ X (I ^ (n + 1))).obj K)

end Integral

end Etale

end AlgebraicGeometry
