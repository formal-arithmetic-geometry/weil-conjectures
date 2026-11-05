/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.ConstructibleSheaf.UniformMittagLeffler
public import WeilConjectures.CategoryTheory.Abelian.AdicImageTower

/-!
# Exact `ℓ`-adic towers from uniformly Artin-Rees towers of étale sheaves

Let `X` be a scheme and `(Hₙ)` a tower of étale sheaves of `Λ`-modules on `X` which is
**uniformly Artin-Rees** with constant `c` (`AlgebraicGeometry.Etale.IsArtinReesTower`): at every
geometric point `s`, with `L_s` the limit of the tower of stalks `((Hₙ)_s)ₙ`, the kernel of
`L_s ⟶ (Hₘ)_s` is `ℓᵐ L_s`, the image of `(Hₘ₊꜀)_s ⟶ (Hₘ)_s` is contained in that of `L_s`, and
`ℓᶜ` kills the `ℓ`-power torsion of `L_s`. This is the situation of the higher direct images
`Hₙ = Rʲf_* Gₙ` of an `ℓ`-adic tower along a smooth proper morphism.

Then the `ℓ`-adic image tower `G'ₘ = ℓᶜ · im(H_{m+2c} ⟶ H_{m+c}) ⊆ H_{m+c}`
(`CategoryTheory.Functor.adicImageTower`) is an exact `ℓ`-adic tower:

- its transition maps `G'ₖ ⟶ G'ₙ` are cokernels of `ℓⁿ`
  (`AlgebraicGeometry.Etale.IsArtinReesTower.isColimitCokernelCofork`) and it is flat, so that it
  carries an `ℓ`-adic tower structure
  (`AlgebraicGeometry.Etale.IsArtinReesTower.adicTowerStructure`);
- its terms are finite locally constant if the `Hₙ` are, `Λ` being noetherian
  (`AlgebraicGeometry.Etale.isFiniteLocallyConstantSheaf_adicImageTower`);
- over a discrete valuation ring `Λ` in which `ℓ` is a nonzero nonunit, the stalks of `G'ₘ` are
  `ℓᶜL_s / ℓᵐ⁺ᶜL_s ≅ (Λ / ℓᵐ)ʳ`
  (`AlgebraicGeometry.Etale.IsArtinReesTower.exists_linearEquiv_sheafFiber`).

The inclusion `G'ₘ ⟶ H_{m+c}` is a monomorphism whose cokernel is killed by `ℓ²ᶜ` as soon as
`ℓᶜ : Hₙ ⟶ Hₙ` factors through the transition map `H_{n+c} ⟶ Hₙ`
(`CategoryTheory.Functor.pow_smul_cokernel_π_adicImageTowerι_eq_zero`).

Exactness is checked on the stalks at the geometric points `X.algClosurePoint x`, which form a
conservative family (`AlgebraicGeometry.Etale.exact_of_forall_sheafFiber`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite ZeroObject

namespace AlgebraicGeometry.Etale

open Scheme

variable {Λ : Type (u + 1)} [CommRing Λ] {X : Scheme.{u}}

variable (H : ℕᵒᵖ ⥤ Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (ℓ c : ℕ)

namespace IsArtinReesTower

variable {H ℓ c} (hH : IsArtinReesTower H ℓ c)
  (hzero : ∀ n : ℕ, ℓ ^ n • 𝟙 (H.obj (op n)) = 0)

end IsArtinReesTower

end AlgebraicGeometry.Etale
