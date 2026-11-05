/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.TateFrobeniusCokernel
public import WeilConjectures.TateTwist.TateModuleUpperStar

/-!
# The geometric Frobenius on the trivialized tower of roots of unity

The Tate module `ℤ_ℓ(1)` is the limit of the tower `n ↦ μ_{ℓⁿ}` of sheaves of roots of unity
with the `ℓ`-th power maps (`AlgebraicGeometry.ProEtale.rootsOfUnityTower`). Over a field `K`
with a compatible system `ζₙ` of primitive `ℓⁿ`-th roots of unity, this tower is the tower
`n ↦ ℤ/ℓⁿ` of reductions of the unit `ℤ`
(`AlgebraicGeometry.ProEtale.cokernelPowTowerIsoRootsOfUnityTower`, from the level
identifications `AlgebraicGeometry.ProEtale.cokernelPowIsoRootsOfUnitySheaf`). The pullback
along a morphism `g` identifies the towers of roots of unity
(`AlgebraicGeometry.ProEtale.upperStarRootsOfUnityTowerHom`) and the towers of reductions
(`AlgebraicGeometry.ProEtale.upperStarCokernelPowTowerIso`).

On the geometric fibre `X̄` of a scheme over a finite field `k`, the pullback along the geometric
Galois Frobenius `g = 𝟙 × σ` reads, on the trivialized tower `n ↦ ℤ/ℓⁿ`, as the compatible
system of scalars `cₙ = χ_ℓ(γ) mod ℓⁿ`, the reductions of the `ℓ`-adic cyclotomic character of
the geometric Frobenius `γ` of `k̄`
(`AlgebraicGeometry.ProEtale.cokernelPowTowerIsoRootsOfUnityTower_geometricGaloisFrobenius`).
A compatible system of integers acts on the tower of reductions through
`AlgebraicGeometry.ProEtale.cokernelPowTowerScalar`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite MonoidalCategory Functor.LaxMonoidal Functor.OplaxMonoidal

/-! ### Scalars on the tower of reductions -/

namespace CategoryTheory.Limits

variable {C : Type*} [Category* C] [Preadditive C] [HasCokernels C] (A : C)

/-- The cokernel of `N : A ⟶ A` is killed by `N`. -/
lemma zsmul_id_cokernel_zsmul_id (N : ℕ) :
    ((N : ℤ) • 𝟙 (cokernel ((N : ℤ) • 𝟙 A))) = 0 := by
  rw [← cancel_epi (cokernel.π ((N : ℤ) • 𝟙 A)), Preadditive.comp_zsmul, Category.comp_id,
    comp_zero, ← Category.id_comp (cokernel.π ((N : ℤ) • 𝟙 A)), ← Preadditive.zsmul_comp,
    cokernel.condition]

end CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale

open Scheme

/-! ### The towers -/

section Towers

variable (X : Scheme.{u}) (ℓ : ℕ)

end Towers

section Trivialization

variable {K : Type u} [Field K] {U : Scheme.{u}} (f : U ⟶ Spec (.of K)) (ℓ : ℕ) [Fact ℓ.Prime]
  {ζ : ℕ → K} (hζ : ∀ n, IsPrimitiveRoot (ζ n) (ℓ ^ n)) (hζ' : ∀ n, ζ (n + 1) ^ ℓ = ζ n)

end Trivialization

/-! ### Pullbacks of the towers -/

section Pullback

variable {X Y : Scheme.{u}} (g : X ⟶ Y) (ℓ : ℕ)

variable {k : Type u} [Field k] (f : Y ⟶ Spec (.of k)) [NeZero (ℓ : k)]

variable {k : Type u} [Field k] (f : Y ⟶ Spec (.of k)) [NeZero (ℓ : k)]

end Pullback

/-! ### The geometric Frobenius -/

section FiniteField

variable (k : Type u) [Field k] [Finite k] (ℓ : ℕ) [Fact ℓ.Prime] [Fact (ringChar k ≠ ℓ)]

/-- The integers `cₙ = (χ_ℓ(γ) mod ℓⁿ).val` of the geometric Frobenius. -/
noncomputable def geometricFrobeniusModularCharacterVal (n : ℕ) : ℤ :=
  ((geometricFrobeniusModularCharacter k ℓ n : (ZMod (ℓ ^ n))ˣ) : ZMod (ℓ ^ n)).val

variable {k ℓ} {X₀ : Scheme.{u}} (a : X₀ ⟶ Spec (.of k)) {ζ : ℕ → AlgebraicClosure k}
  (hζ : ∀ n, IsPrimitiveRoot (ζ n) (ℓ ^ n)) (hζ' : ∀ n, ζ (n + 1) ^ ℓ = ζ n)

end FiniteField

end AlgebraicGeometry.ProEtale
