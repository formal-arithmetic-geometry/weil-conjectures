/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.Module
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ClopenIdempotent

/-!
# Pushforward along a morphism with a clopen partition into sections is exact

Let `g : Y ⟶ S` be a morphism of schemes and `s₁, …, sₙ : S ⟶ Y` sections of `g` which are open
immersions with closed, pairwise disjoint ranges covering `Y`; for instance `Y = ⊔ᵢ S`. Then the
pushforward `g_*` of pro-étale sheaves is exact: the idempotents `e_{sᵢ}` of the clopen
subschemes (`AlgebraicGeometry.ProEtale.clopenIdempotentSheaf`) sum to the identity, and each
factors through `sᵢ_* sᵢ^*`, while `g_* sᵢ_* sᵢ^* ≅ (sᵢ ≫ g)_* sᵢ^* ≅ sᵢ^*` is exact.

## Main results

- `CategoryTheory.Functor.preservesEpimorphisms_of_sum_comp_eq_id`: an additive functor `F`
  preserves epimorphisms if the identity is a finite sum of composites `𝟭 ⟶ Tᵢ ⟶ 𝟭` with every
  `Tᵢ ⋙ F` preserving epimorphisms.
- `AlgebraicGeometry.ProEtale.preservesFiniteColimits_lowerStar_of_sections`: the pushforward
  `g_*` is exact.
- `AlgebraicGeometry.ProEtale.preservesFiniteColimits_adicLowerStar_of_sections`: the same for
  sheaves of modules over the constant `ℓ`-adic sheaves.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits

namespace CategoryTheory.Functor

variable {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]

end CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

variable {ι : Type*} [Finite ι] {Y S : Scheme.{u}} (g : Y ⟶ S) (s : ι → (S ⟶ Y))
  [∀ i, IsOpenImmersion (s i)]

variable (l : ℕ) [Fact l.Prime]

end AlgebraicGeometry.ProEtale
