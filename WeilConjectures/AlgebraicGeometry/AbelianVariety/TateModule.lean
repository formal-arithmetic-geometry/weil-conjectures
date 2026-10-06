/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.AbelianVariety.Basic
public import WeilConjectures.AlgebraicGeometry.SpecAlgebraicClosure
public import WeilConjectures.AlgebraicGeometry.FrobeniusFixedPoints
public import WeilConjectures.GroupTheory.TateModule
public import WeilConjectures.NumberTheory.TateModule

/-!
# The `ℓ`-adic Tate module of an abelian variety

For an abelian variety `A` over `K` and a prime `ℓ` different from the characteristic, the
`ℓ`-adic Tate module of `A` is the Tate module `AddCommGroup.tateModule` of the group of
geometric points `A(K̄)`, written additively, and its rational form is
`AddCommGroup.rationalTateModule`. Over an algebraically closed field it is free of rank
`2 * g`.

The two definitions live in the `IsAbelianVariety` namespace, both because the blueprint node
they realise is about abelian varieties and so that they do not shadow
`AddCommGroup.tateModule` and `AddCommGroup.rationalTateModule`.

## Main definitions

- `AlgebraicGeometry.IsAbelianVariety.tateModule`,
  `AlgebraicGeometry.IsAbelianVariety.rationalTateModule`: `T_ℓ A` and `V_ℓ A`.
- `AlgebraicGeometry.IsAbelianVariety.geometricPointsAddEquiv`: the action of `Gal(K̄/K)` on the
  geometric points `A(K̄)` by coordinates.

## Main statements

- `AlgebraicGeometry.IsAbelianVariety.nonempty_linearEquiv_tateModule`: `T_ℓ A ≅ ℤ_[ℓ] ^ (2g)`.
- `AlgebraicGeometry.IsAbelianVariety.nonempty_linearEquiv_rationalTateModule`:
  `V_ℓ A ≅ ℚ_[ℓ] ^ (2g)`.
- `AlgebraicGeometry.IsAbelianVariety.eq_zero_of_map_geometricFrobenius_eq_self`: over a finite
  field, the geometric Frobenius fixes no nonzero vector of `V_ℓ A`.

## TODO

The functoriality of `T_ℓ` — the action of an endomorphism of `A`, and the semilinear action of
an automorphism of `K` on `T_ℓ A_{K̄}` — is what the Weil conjectures actually use; only the
action of `Gal(K̄/K)` on `T_ℓ A` is declared here.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

namespace AlgebraicGeometry

namespace IsAbelianVariety

variable {K : Type u} [Field K] (ℓ : ℕ) [Fact ℓ.Prime] (A : Over (Spec (.of K))) [GrpObj A]
  [IsAbelianVariety A]

/-- Blueprint `sk-def-av-tate`: `ℓ`-adic Tate module.

The *`ℓ`-adic Tate module* of an abelian variety `A` over `K` is the inverse limit
`T_ℓ A = lim_n A[ℓ^n](K̄)`, the transition map from level `n + 1` to level `n` being
multiplication by `ℓ`. It is a `ℤ_[ℓ]`-module. -/
noncomputable def tateModule :
    AddSubgroup (∀ _ : ℕ, Additive (Scheme.specAlgebraicClosure K ⟶ A)) :=
  AddCommGroup.tateModule ℓ (Additive (Scheme.specAlgebraicClosure K ⟶ A))

noncomputable instance tateModule.instModule : Module ℤ_[ℓ] (tateModule ℓ A) :=
  inferInstanceAs (Module ℤ_[ℓ]
    (AddCommGroup.tateModule ℓ (Additive (Scheme.specAlgebraicClosure K ⟶ A))))

/-- The rational Tate module `V_ℓ A = ℚ_[ℓ] ⊗_{ℤ_[ℓ]} T_ℓ A` of an abelian variety. -/
noncomputable def rationalTateModule : Type u :=
  AddCommGroup.rationalTateModule ℓ (Additive (Scheme.specAlgebraicClosure K ⟶ A))

noncomputable instance rationalTateModule.instAddCommGroup :
    AddCommGroup (rationalTateModule ℓ A) :=
  inferInstanceAs (AddCommGroup
    (AddCommGroup.rationalTateModule ℓ (Additive (Scheme.specAlgebraicClosure K ⟶ A))))

noncomputable instance rationalTateModule.instModule : Module ℚ_[ℓ] (rationalTateModule ℓ A) :=
  inferInstanceAs (Module ℚ_[ℓ]
    (AddCommGroup.rationalTateModule ℓ (Additive (Scheme.specAlgebraicClosure K ⟶ A))))

/-- Blueprint `sk-prop-av-tate-rank`: The `ℓ`-adic Tate module is free of rank `2g`.

Let `A` be an abelian variety of dimension `g` over an algebraically closed field `K` and let
`ℓ ≠ char K`. Then `T_ℓ A ≅ ℤ_[ℓ] ^ (2 * g)`. -/
theorem nonempty_linearEquiv_tateModule [IsAlgClosed K] (p : ℕ) [CharP K p] (hℓ : ℓ ≠ p) :
    Nonempty (tateModule ℓ A ≃ₗ[ℤ_[ℓ]] (Fin (2 * IsAbelianVariety.dim A) → ℤ_[ℓ])) :=
  sorry

/-- Blueprint `sk-prop-av-tate-rank`: The `ℓ`-adic Tate module is free of rank `2g`.

Let `A` be an abelian variety of dimension `g` over an algebraically closed field `K` and let
`ℓ ≠ char K`. Then `V_ℓ A ≅ ℚ_[ℓ] ^ (2 * g)`. -/
theorem nonempty_linearEquiv_rationalTateModule [IsAlgClosed K] (p : ℕ) [CharP K p]
    (hℓ : ℓ ≠ p) :
    Nonempty (rationalTateModule ℓ A ≃ₗ[ℚ_[ℓ]] (Fin (2 * IsAbelianVariety.dim A) → ℚ_[ℓ])) :=
  sorry

section Galois

variable {A}

omit [IsAbelianVariety A] in
/-- The action of `σ ∈ Gal(K̄/K)` on the group `A(K̄)` of geometric points of a group
scheme `A` over `K` (for instance an abelian variety), by coordinates: `P ↦ Spec σ ≫ P`. It is
a group automorphism. -/
noncomputable def geometricPointsAddEquiv (σ : Gal(AlgebraicClosure K/K)) :
    Additive (Scheme.specAlgebraicClosure K ⟶ A) ≃+ Additive (Scheme.specAlgebraicClosure K ⟶ A)
    where
  toFun P := .ofMul (Scheme.specAlgebraicClosureMap σ.toAlgHom ≫ (P.toMul : _ ⟶ A))
  invFun P := .ofMul (Scheme.specAlgebraicClosureMap σ.symm.toAlgHom ≫ (P.toMul : _ ⟶ A))
  left_inv P := Additive.toMul.injective <| by
    simp only [toMul_ofMul]
    rw [← Category.assoc, Scheme.specAlgebraicClosureMap_symm_comp_self, Category.id_comp]
  right_inv P := Additive.toMul.injective <| by
    simp only [toMul_ofMul]
    rw [← Category.assoc, Scheme.specAlgebraicClosureMap_comp_symm, Category.id_comp]
  map_add' P Q := congr_arg Additive.ofMul (MonObj.comp_mul _ P.toMul Q.toMul)

omit [IsAbelianVariety A] in
theorem geometricPointsAddEquiv_apply (σ : Gal(AlgebraicClosure K/K))
    (P : Additive (Scheme.specAlgebraicClosure K ⟶ A)) :
    geometricPointsAddEquiv σ P =
      .ofMul (Scheme.specAlgebraicClosureMap σ.toAlgHom ≫ (P.toMul : _ ⟶ A)) :=
  rfl

omit [IsAbelianVariety A] in
theorem geometricPointsAddEquiv_inv (σ : Gal(AlgebraicClosure K/K)) :
    geometricPointsAddEquiv (A := A) σ⁻¹ = (geometricPointsAddEquiv σ).symm :=
  AddEquiv.ext fun _ ↦ rfl

variable (A) [Fintype K]

/-- Blueprint `prop-av-tate-no-frobenius-fixed` (finiteness step): over a finite field `k₀`, the
group `A^σ` of geometric points of `A` fixed by the arithmetic Frobenius `σ` is finite (it is the
group `A(k₀)` of rational points). -/
theorem finite_setOf_frobenius_fixed :
    {P | geometricPointsAddEquiv (A := A)
      (FiniteField.frobeniusAlgEquivOfAlgebraic K (AlgebraicClosure K)) P = P}.Finite :=
  have : CompactSpace A.left := QuasiCompact.compactSpace_of_compactSpace A.hom
  (Scheme.finite_setOf_specAlgebraicClosureMap_frobenius_comp_eq_self A).preimage
    (Additive.toMul.injective.injOn)

/-- Blueprint `prop-av-tate-no-frobenius-fixed`: no Frobenius-fixed vectors on the Tate module.

Let `A` be an abelian variety over a finite field `k₀` and `F = σ⁻¹` the geometric Frobenius,
acting on the geometric points `A(k̄)` by coordinates. Then `F` fixes no nonzero vector of the
`ℓ`-adic Tate module `T_ℓ A`: the fixed group `A^σ` is finite
(`AlgebraicGeometry.IsAbelianVariety.finite_setOf_frobenius_fixed`), so this is
`AddCommGroup.eq_zero_of_mem_tateModule_of_forall_symm_fixed`. -/
theorem eq_zero_of_mem_tateModule_of_forall_geometricFrobenius_fixed {t : ℕ → _}
    (ht : t ∈ tateModule ℓ A) (hst : ∀ n, geometricPointsAddEquiv
      (FiniteField.geometricFrobeniusAlgEquivOfAlgebraic K (AlgebraicClosure K)) (t n) = t n) :
    t = 0 :=
  AddCommGroup.eq_zero_of_mem_tateModule_of_forall_symm_fixed _
    (finite_setOf_frobenius_fixed A) ht fun n ↦ by
      rw [← geometricPointsAddEquiv_inv, ← FiniteField.geometricFrobeniusAlgEquivOfAlgebraic_eq_inv]
      exact hst n

/-- Blueprint `prop-av-tate-no-frobenius-fixed`: no Frobenius-fixed vectors on the Tate module.

Let `A` be an abelian variety over a finite field `k₀` and `F = σ⁻¹` the geometric Frobenius,
acting on the geometric points `A(k̄)` by coordinates. Then `F` fixes no nonzero vector of the
rational Tate module: `(V_ℓ A)^F = 0`. The fixed group `A^σ` is finite
(`AlgebraicGeometry.IsAbelianVariety.finite_setOf_frobenius_fixed`), so this is
`AddCommGroup.rationalTateModule.eq_zero_of_map_symm_eq_self`. -/
theorem eq_zero_of_map_geometricFrobenius_eq_self {v : rationalTateModule ℓ A}
    (hv : AddCommGroup.rationalTateModule.map (geometricPointsAddEquiv
      (FiniteField.geometricFrobeniusAlgEquivOfAlgebraic K (AlgebraicClosure K))).toAddMonoidHom v =
      v) :
    v = 0 :=
  AddCommGroup.rationalTateModule.eq_zero_of_map_symm_eq_self _
    (finite_setOf_frobenius_fixed A) <| by
      rwa [← geometricPointsAddEquiv_inv,
        ← FiniteField.geometricFrobeniusAlgEquivOfAlgebraic_eq_inv]

end Galois

end IsAbelianVariety

end AlgebraicGeometry
