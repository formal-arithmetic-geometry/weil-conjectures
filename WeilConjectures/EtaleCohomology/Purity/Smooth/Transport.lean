/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Complete.RationalCoefficient
public import WeilConjectures.EtaleCohomology.Purity.Smooth.Basic

/-!
# Smooth purity over `𝒪_E`, `E` and `ℚ̄_ℓ`

Smooth purity is proved at the finite coefficient stage in
`WeilConjectures.EtaleCohomology.Purity.Smooth.Basic`. This file records its extension to the
three remaining coefficient stages of the `ℓ`-adic formalism: the adic category over `𝒪_E`,
its rationalization over `E`, and the colimit over finite extensions `E/ℚ_ℓ` giving `ℚ̄_ℓ`.

In this repository the `𝒪_E` stage is the derived-complete subcategory
`AlgebraicGeometry.DerivedCategory.derivedCompleteIntegral` of the derived category of
sheaves of `𝒪_E`-modules, and the `E` stage is its rationalization
`AlgebraicGeometry.DerivedCategoryDerivedCompleteRational`. Transport therefore has exactly
two clauses: that `Rf^!` preserves derived completeness, and that the purity isomorphism
holds on derived-complete objects, whence it descends to the rationalization.

## Implementation notes

The `ℚ̄_ℓ` stage is the colimit over finite `E/ℚ_ℓ` of the `E` stages. That colimit category
is not yet in the repository, so only the `𝒪_E` clause — from which the `E` clause follows by
applying the rationalization functor, and the `ℚ̄_ℓ` clause by passing to the colimit — is
stated here.

## Main statements

- `AlgebraicGeometry.Etale.derivedCompleteIntegral_rightDerivedUpperShriek`
-/

@[expose] public section

universe w u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme Etale

namespace Etale

variable (l : ℕ) [Fact l.Prime] (E : Type w) [Field E] [Algebra E (PadicAlgCl l)]
  [Small.{u + 1} E] {X Y : Scheme.{u}} (d : ℕ) (f : X ⟶ Y) [IsSeparated f]
  [SmoothOfRelativeDimension d f] [HasCompactification f]

/-- Blueprint `sk-thm-purity-transport`: Smooth purity over `𝒪_E`, `E` and `ℚ̄_ℓ`

**Smooth purity at the adic stages.** Let `f : X ⟶ Y` be smooth separated of pure relative
dimension `d` and let `Λ = 𝒪_E` be the integral coefficient stage. Then `Rf^!` preserves
derived-complete objects, and for a derived-complete `K` the purity map

`γ_{f,K} : (Lf^* K)(d)[2d] ≅ Rf^! K`

of `sk-thm-smooth-purity` holds in the adic category. Naturality in `K`, compatibility with
composition, with étale base change, with the finite reductions `A_{E,n} → A_{E,m}` and with
scalar extension of coefficient fields are inherited from the finite stage; applying the
rationalization functor gives the statement over `E`, and passing to the colimit over finite
`E/ℚ_ℓ` gives it over `ℚ̄_ℓ`.

In particular, for the structure morphism `a_X` of a smooth `X` of pure dimension `d`,
`ω_{X,Λ} = Ra_X^! Λ ≅ Λ_X(d)[2d]`, and the counit of `Ra_{X!} ⊣ Ra_X^!` is the normalized
integration map `RΓ_c(X, Λ_X(d)[2d]) → Λ`. -/
theorem derivedCompleteIntegral_rightDerivedUpperShriek
    (K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology
      (ModuleCat.{u + 1} (Shrink.{u + 1} (PadicAlgCl.integers l E)))))
    (hK : DerivedCategory.derivedCompleteIntegral Y.smallEtaleTopology l E K) :
    DerivedCategory.derivedCompleteIntegral X.smallEtaleTopology l E
      ((Etale.rightDerivedUpperShriek
        (ModuleCat.{u + 1} (Shrink.{u + 1} (PadicAlgCl.integers l E))) f).obj K) ∧
    Nonempty ((Etale.rightDerivedUpperShriek
        (ModuleCat.{u + 1} (Shrink.{u + 1} (PadicAlgCl.integers l E))) f).obj K ≅
      (twistShift (Shrink.{u + 1} (PadicAlgCl.integers l E)) X d).obj
        ((L((f)^*[ModuleCat.{u + 1} (Shrink.{u + 1} (PadicAlgCl.integers l E))])).obj K)) :=
  sorry

end Etale

end AlgebraicGeometry
