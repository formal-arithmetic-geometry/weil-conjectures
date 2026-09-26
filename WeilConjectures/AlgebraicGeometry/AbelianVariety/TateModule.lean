/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import WeilConjectures.AlgebraicGeometry.AbelianVariety.Defs
public import WeilConjectures.GroupTheory.TateModule

/-!
# The `ℓ`-adic Tate module of an abelian variety

For an abelian variety `A` over `K` and a prime `ℓ` different from the characteristic, the
`ℓ`-adic Tate module of `A` is the Tate module `AddCommGroup.tateModule` of the group of
geometric points `A(K̄)`, written additively, and its rational form is
`AddCommGroup.rationalTateModule`. Over an algebraically closed field it is free of rank
`2 * g`.

## Main definitions

- `AlgebraicGeometry.specAlgebraicClosure`: `Spec K̄` as a scheme over `K`.
- `AlgebraicGeometry.tateModule`, `AlgebraicGeometry.rationalTateModule`: `T_ℓ A` and `V_ℓ A`.

## Main statements

- `AlgebraicGeometry.nonempty_linearEquiv_tateModule`: `T_ℓ A ≅ ℤ_[ℓ] ^ (2 * g)` and
  `V_ℓ A ≅ ℚ_[ℓ] ^ (2 * g)`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

namespace AlgebraicGeometry

variable {K : Type u} [Field K]

/-- `Spec K̄`, the spectrum of an algebraic closure of `K`, as a scheme over `K`. Its morphisms
to a `K`-scheme are the geometric points of that scheme. -/
noncomputable def specAlgebraicClosure (K : Type u) [Field K] : Over (Spec (.of K)) :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K))))

/-- Blueprint `sk-def-av-tate`: `ℓ`-adic Tate module.

The *`ℓ`-adic Tate module* of an abelian variety `A` over `K` is the inverse limit
`T_ℓ A = lim_n A[ℓ^n](K̄)`, the transition map from level `n + 1` to level `n` being
multiplication by `ℓ`. It is a `ℤ_[ℓ]`-module, and every endomorphism of `A`, as well as every
semilinear automorphism of `A_{K̄}` over an automorphism of `K`, acts on it componentwise. -/
noncomputable def tateModule (ℓ : ℕ) [Fact ℓ.Prime] (A : Over (Spec (.of K))) [GrpObj A]
    [IsCommMonObj A] : AddSubgroup (∀ _ : ℕ, Additive (specAlgebraicClosure K ⟶ A)) :=
  AddCommGroup.tateModule ℓ (Additive (specAlgebraicClosure K ⟶ A))

noncomputable instance (ℓ : ℕ) [Fact ℓ.Prime] (A : Over (Spec (.of K))) [GrpObj A]
    [IsCommMonObj A] : Module ℤ_[ℓ] (tateModule ℓ A) :=
  inferInstanceAs (Module ℤ_[ℓ]
    (AddCommGroup.tateModule ℓ (Additive (specAlgebraicClosure K ⟶ A))))

/-- The rational Tate module `V_ℓ A = T_ℓ A ⊗_{ℤ_[ℓ]} ℚ_[ℓ]` of an abelian variety. -/
noncomputable def rationalTateModule (ℓ : ℕ) [Fact ℓ.Prime] (A : Over (Spec (.of K))) [GrpObj A]
    [IsCommMonObj A] : Type u :=
  AddCommGroup.rationalTateModule ℓ (Additive (specAlgebraicClosure K ⟶ A))

noncomputable instance (ℓ : ℕ) [Fact ℓ.Prime] (A : Over (Spec (.of K))) [GrpObj A]
    [IsCommMonObj A] : AddCommGroup (rationalTateModule ℓ A) :=
  inferInstanceAs (AddCommGroup
    (AddCommGroup.rationalTateModule ℓ (Additive (specAlgebraicClosure K ⟶ A))))

noncomputable instance (ℓ : ℕ) [Fact ℓ.Prime] (A : Over (Spec (.of K))) [GrpObj A]
    [IsCommMonObj A] : Module ℚ_[ℓ] (rationalTateModule ℓ A) :=
  inferInstanceAs (Module ℚ_[ℓ]
    (AddCommGroup.rationalTateModule ℓ (Additive (specAlgebraicClosure K ⟶ A))))

/-- Blueprint `sk-prop-av-tate-rank`: The `ℓ`-adic Tate module is free of rank `2g`.

Let `A` be an abelian variety of dimension `g` over an algebraically closed field `K` and let
`ℓ ≠ char K`. Then `T_ℓ A ≅ ℤ_[ℓ] ^ (2 * g)` and `V_ℓ A ≅ ℚ_[ℓ] ^ (2 * g)`. -/
theorem nonempty_linearEquiv_tateModule [IsAlgClosed K] (p : ℕ) [CharP K p] (ℓ : ℕ)
    [Fact ℓ.Prime] (hℓ : ℓ ≠ p) (A : Over (Spec (.of K))) [GrpObj A] [IsCommMonObj A]
    [IsAbelianVariety A] (g : ℕ) (hg : topologicalKrullDim A.left = (g : ℕ∞)) :
    Nonempty (tateModule ℓ A ≃ₗ[ℤ_[ℓ]] (Fin (2 * g) → ℤ_[ℓ])) ∧
      Nonempty (rationalTateModule ℓ A ≃ₗ[ℚ_[ℓ]] (Fin (2 * g) → ℚ_[ℓ])) :=
  sorry

end AlgebraicGeometry
