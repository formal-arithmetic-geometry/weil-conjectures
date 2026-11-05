/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalarsRetractionLift
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.DerivedComplete.Basic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ModPowReduction

/-!
# Lifting retractions from torsion coefficients to `𝒪_E`-coefficients

Let `E ⊆ ℚ̄_ℓ` be a finite subextension of `ℚ_ℓ` with ring of integers `𝒪_E`, `X` a scheme and
`i : A ⟶ B` a morphism of complexes of `𝒪_{E,X}`-module objects on `X_proét`, with `A` derived
complete. For `n ≥ 1` write `Aₙ = A ⊗ᴸ_{𝒪_E} 𝒪_E/ℓⁿ` and `iₙ : Aₙ ⟶ Bₙ` for the reductions,
complexes of `(𝒪_E/ℓⁿ)_X`-module objects
(`L(Mod.extendScalars (ProEtale.integersModPowReduction X ℓ E n))`).

* `ProEtale.isSplitMono_of_derivedCompleteIntegers_of_retractions`: if there are morphisms
  `rₙ : Bₙ ⟶ Aₙ`, compatible with reduction (`Bₙ₊₁ ⟶ Aₙ₊₁` reduces modulo `ℓⁿ` to `rₙ`,
  `Mod.derivedExtendScalarsReduction`), with `r₁` a retraction of `i₁`, then `i` is a split
  monomorphism. The retraction is obtained by lifting `(rₙ)ₙ` through `A = R lim Aₙ` (the Milnor
  sequence, of which only the surjectivity onto `lim Hom(B, Aₙ)` is used) and correcting by
  derived Nakayama; see `CategoryTheory.Mod.isSplitMono_of_isCenterComplete_of_retractions`.
* `ProEtale.isSplitMono_of_derivedCompleteIntegers_of_unique_retractions`: the compatibility is
  automatic when each `iₙ` has a unique retraction with a property `Pₙ` preserved by reduction,
  for instance the unique retraction invariant under a Galois action, which exists for the
  exchange maps of torsion nearby cycles along a pro-`p` Galois layer (SGA 4½, [Th. finitude],
  Lemme 3.4). The `lim¹` term of the Milnor sequence need not vanish.

The derived complete complexes are complete with respect to the action of `ℓ`
(`ProEtale.isCenterComplete_of_derivedCompleteIntegers`): if `ℓ` acts invertibly on `Z`, the first
derived reduction of `Z` vanishes, since `ℓ = 0` in `𝔽_E`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonObj Pretriangulated

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open Scheme PadicAlgCl CondensedRing

variable {ℓ : ℕ} [Fact ℓ.Prime] {E : Type} [Field E] [Algebra E (PadicAlgCl ℓ)]
  {X : Scheme.{u}}

end AlgebraicGeometry.ProEtale
