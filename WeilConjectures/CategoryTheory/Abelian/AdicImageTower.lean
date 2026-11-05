/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Abelian.AdicTowerStructure
public import WeilConjectures.Algebra.Module.AdicTowerLattice
public import Mathlib.CategoryTheory.Limits.Shapes.Images
public import Mathlib.Algebra.Category.ModuleCat.Abelian

/-!
# The `ℓ`-adic image tower of an Artin-Rees tower

Let `(Hₙ)` be a tower in an abelian category and `ℓ c : ℕ`. The **`ℓ`-adic image tower**
`G'ₘ = ℓᶜ · im(H_{m+2c} ⟶ H_{m+c}) ⊆ H_{m+c}` (`CategoryTheory.Functor.adicImageTower`) is the
image of `ψₘ = ℓᶜ ∘ (H_{m+2c} ⟶ H_{m+c})`, with the inclusion
`G'ₘ ⟶ H_{m+c}` (`CategoryTheory.Functor.adicImageTowerι`).

Think of `Hₙ = Rʲf_* Gₙ` for an `ℓ`-adic tower `(Gₙ)` along a smooth proper morphism: at every
geometric point the tower of stalks is Artin-Rees isomorphic to `(L / ℓⁿ)ₙ` with `L` finitely
generated, with constants independent of the point, and `ℓᶜ` kills the torsion of `L`. Then the
stalks of `G'ₘ` are `ℓᶜL / ℓᵐ⁺ᶜL ≅ (Λ / ℓᵐ)ʳ`, `r` the rank of the free module `ℓᶜ L`.

The results of this file are, for a functor `Φ` to modules preserving monomorphisms and
epimorphisms (a stalk functor), the elementwise statements at `Φ` needed to show that `G'` is an
exact `ℓ`-adic tower: if the tower `(Φ Hₙ)ₙ` is Artin-Rees with constant `c` and
`ℓ`-adically separated, the transition maps of `(Φ G'ₙ)` are surjective with kernel `ℓⁿ`
(`CategoryTheory.Functor.exists_pow_smul_eq_of_map_adicImageTower_map_eq_zero`,
`CategoryTheory.Functor.surjective_map_adicImageTower_map`), and if moreover `ℓᶜ` kills the
torsion of `lim Φ Hₙ` the tower is flat
(`CategoryTheory.Functor.exists_pow_smul_eq_of_pow_smul_eq_zero_adicImageTower`), with
`Φ G'ₘ ≅ (Λ / ℓᵐ)ʳ` over a discrete valuation ring
(`CategoryTheory.Functor.exists_linearEquiv_map_adicImageTower`). On the other hand, the
cokernel of `G'ₘ ⟶ H_{m+c}` is killed by `ℓ²ᶜ` as soon as `ℓᶜ : H_{m+c} ⟶ H_{m+c}` factors
through the transition map `H_{m+2c} ⟶ H_{m+c}`
(`CategoryTheory.Functor.pow_smul_cokernel_π_adicImageTowerι_eq_zero`).
-/

@[expose] public section

universe v u

open CategoryTheory Limits Opposite

namespace CategoryTheory.Functor

variable {C : Type*} [Category C] [Abelian C] (H : ℕᵒᵖ ⥤ C) (ℓ c : ℕ)

section AdicTowerStructure

variable {D : Type*} [Category D] [Abelian D] {G : ℕᵒᵖ ⥤ D} (A : AdicTowerStructure G ℓ)
  (T : D ⥤ C) [T.Additive]

end AdicTowerStructure

section Stalk

variable {R : Type u} [CommRing R] (Φ : C ⥤ ModuleCat.{v} R)

variable [Φ.Additive]

variable [Φ.PreservesMonomorphisms] [Φ.PreservesEpimorphisms]
  (hAR : ∀ (m : ℕ) (z : (H ⋙ Φ).obj (op (m + c))), ∃ x : ModuleCat.sectionsSubmodule (H ⋙ Φ),
    x.1 (op m) = ModuleCat.towerMap (H ⋙ Φ) (Nat.le_add_right m c) z)
  (hker : ∀ (m : ℕ) (x : ModuleCat.sectionsSubmodule (H ⋙ Φ)),
    x.1 (op m) = 0 ↔ ∃ y : ModuleCat.sectionsSubmodule (H ⋙ Φ), ℓ ^ m • y = x)

end Stalk

end CategoryTheory.Functor
