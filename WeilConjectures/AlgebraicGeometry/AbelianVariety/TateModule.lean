/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.AbelianVariety.Basic
public import WeilConjectures.AlgebraicGeometry.AbelianVariety.Torsion
public import WeilConjectures.AlgebraicGeometry.SpecAlgebraicClosure
public import WeilConjectures.AlgebraicGeometry.FrobeniusFixedPoints
public import WeilConjectures.GroupTheory.TateModule
public import Mathlib.Algebra.Group.Equiv.Defs
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Data.Set.Finite.Basic

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
- `AlgebraicGeometry.SemilinearGrpHom`: homomorphisms of group schemes which are semilinear over
  an endomorphism of the base, and `AlgebraicGeometry.SemilinearGrpHom.mapPoints`, their action
  on points.
- `AlgebraicGeometry.IsAbelianVariety.tateModuleMap`,
  `AlgebraicGeometry.IsAbelianVariety.rationalTateModuleMap`: the componentwise action of a
  homomorphism (e.g. an endomorphism) of abelian varieties on `T_ℓ` and `V_ℓ`.
- `AlgebraicGeometry.IsAbelianVariety.tateModuleSemilinearMap`: the componentwise action of a
  semilinear homomorphism on `T_ℓ`.
- `AlgebraicGeometry.IsAbelianVariety.galoisRepresentation`: the action of `Gal(K̄/K)` on `T_ℓ A`.
- `AlgebraicGeometry.IsAbelianVariety.pointsAddEquivGeometricPoints`: over an algebraically
  closed field `K`, `A(K) ≃ A(K̄)`.
- `AlgebraicGeometry.IsAbelianVariety.tateModuleEquivTorsionPoints`: `T_ℓ A = lim_n A[ℓ ^ n](K̄)`.

## Main statements

- `AlgebraicGeometry.IsAbelianVariety.nonempty_linearEquiv_tateModule`: `T_ℓ A ≅ ℤ_[ℓ] ^ (2g)`.
- `AlgebraicGeometry.IsAbelianVariety.nonempty_linearEquiv_rationalTateModule`:
  `V_ℓ A ≅ ℚ_[ℓ] ^ (2g)`.
- `AlgebraicGeometry.IsAbelianVariety.eq_zero_of_map_geometricFrobenius_eq_self`: over a finite
  field, the geometric Frobenius fixes no nonzero vector of `V_ℓ A`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

namespace AlgebraicGeometry

namespace SemilinearGrpHom

variable {S : Scheme.{u}} {e : S ⟶ S} {A B : Over S} [GrpObj A] [GrpObj B]

end SemilinearGrpHom

namespace IsAbelianVariety

variable {K : Type u} [Field K] (ℓ : ℕ) [Fact ℓ.Prime] (A : Over (Spec (.of K))) [GrpObj A]
  [IsAbelianVariety A]

/-- Blueprint `def-wf-abelian-tate-module`: `ℓ`-adic Tate module.

The *`ℓ`-adic Tate module* of an abelian variety `A` over `K` is the inverse limit
`T_ℓ A = lim_n A[ℓ^n](K̄)`, the transition map from level `n + 1` to level `n` being
multiplication by `ℓ`. It is a `ℤ_[ℓ]`-module.

This is also blueprint `def-wf-abelian-tate-module`. It is defined as the Tate module
`T_ℓ (A(K̄))` of the group of geometric points; the identification with compatible systems of
points of the torsion subgroup schemes `A[ℓ ^ n]` is
`AlgebraicGeometry.IsAbelianVariety.tateModuleEquivTorsionPoints`. -/
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

omit [IsAbelianVariety A] in
/-- Over an algebraically closed field `K`, the structure morphism `Spec K̄ ⟶ Spec K` is an
isomorphism. -/
instance isIso_toUnit_specAlgebraicClosure [IsAlgClosed K] :
    IsIso (toUnit (Scheme.specAlgebraicClosure K)) := by
  have : IsIso (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K))) :=
    (RingEquiv.ofBijective _ IsAlgClosed.algebraMap_bijective_of_isIntegral).toCommRingCatIso
      |>.isIso_hom
  have : IsIso ((Over.forget _).map (toUnit (Scheme.specAlgebraicClosure K))) :=
    inferInstanceAs (IsIso (Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K)))))
  exact isIso_of_reflects_iso _ (Over.forget _)

omit [IsAbelianVariety A] in
/-- Over an algebraically closed field `K`, the geometric points `A(K̄)` of a group scheme `A`
are its `K`-points `A(K)`. -/
noncomputable def pointsAddEquivGeometricPoints [IsAlgClosed K] :
    Additive (𝟙_ (Over (Spec (.of K))) ⟶ A) ≃+ Additive (Scheme.specAlgebraicClosure K ⟶ A)
    where
  toFun P := .ofMul (toUnit _ ≫ P.toMul)
  invFun P := .ofMul (inv (toUnit (Scheme.specAlgebraicClosure K)) ≫ P.toMul)
  left_inv P := by simp
  right_inv P := by simp
  map_add' P Q := congr_arg Additive.ofMul (MonObj.comp_mul _ P.toMul Q.toMul)

/-- Over an algebraically closed field `K` and for `ℓ ≠ char K`, the group `A(K̄)` is
`ℓ`-divisible (blueprint `lem-sc-isogeny-surjective`) and its `ℓ`-torsion has order `ℓ ^ (2g)`
(blueprint `lem-sc-ntorsion-etale`). -/
theorem exists_zsmul_eq_and_natCard_torsionBy [IsAlgClosed K] (p : ℕ) [CharP K p] (hℓ : ℓ ≠ p) :
    (∀ x : Additive (Scheme.specAlgebraicClosure K ⟶ A), ∃ y, (ℓ : ℤ) • y = x) ∧
      Nat.card (AddSubgroup.torsionBy (Additive (Scheme.specAlgebraicClosure K ⟶ A)) (ℓ : ℤ)) =
        ℓ ^ (2 * IsAbelianVariety.dim A) := by
  have hℓ' : (ℓ : ℕ).Prime := Fact.out
  let e := pointsAddEquivGeometricPoints A
  refine ⟨fun x ↦ ?_, ?_⟩
  · obtain ⟨a, ha⟩ := surjective_npow_points (A := A) ℓ hℓ'.pos (e.symm x).toMul
    refine ⟨e (.ofMul a), ?_⟩
    rw [← map_zsmul, natCast_zsmul, ← e.eq_symm_apply]
    exact congr_arg Additive.ofMul ha
  · have hp : ¬ p ∣ ℓ := fun h ↦ by
      rcases CharP.char_is_prime_or_zero K p with hp | rfl
      · exact hℓ ((Nat.prime_dvd_prime_iff_eq hp hℓ').1 h).symm
      · exact hℓ'.ne_zero (Nat.eq_zero_of_zero_dvd h)
    obtain ⟨f⟩ := nonempty_addEquiv_torsionBy p A ℓ hℓ'.pos hp
    rw [← Nat.card_congr (e.toEquiv.subtypeEquiv fun x ↦ ?_), Nat.card_congr f.toEquiv,
      Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card, Fintype.card_fin]
    simp only [AddSubgroup.torsionBy, Submodule.mem_toAddSubgroup, Submodule.mem_torsionBy_iff]
    rw [AddEquiv.toEquiv_eq_coe, EquivLike.coe_coe, ← map_zsmul, AddEquiv.map_eq_zero_iff]

/-- Blueprint `sk-prop-av-tate-rank`: The `ℓ`-adic Tate module is free of rank `2g`.

This is also the blueprint proposition `prop-av-tate-rank`.

Let `A` be an abelian variety of dimension `g` over an algebraically closed field `K` and let
`ℓ ≠ char K`. Then `T_ℓ A ≅ ℤ_[ℓ] ^ (2 * g)`.

The group `A(K̄)` is `ℓ`-divisible (blueprint `lem-sc-isogeny-surjective`) and its `ℓ`-torsion has
`ℓ ^ (2g)` elements (blueprint `lem-sc-ntorsion-etale`), so this is
`AddCommGroup.tateModule.nonempty_linearEquiv_of_natCard_eq`. -/
theorem nonempty_linearEquiv_tateModule [IsAlgClosed K] (p : ℕ) [CharP K p] (hℓ : ℓ ≠ p) :
    Nonempty (tateModule ℓ A ≃ₗ[ℤ_[ℓ]] (Fin (2 * IsAbelianVariety.dim A) → ℤ_[ℓ])) :=
  have h := exists_zsmul_eq_and_natCard_torsionBy ℓ A p hℓ
  AddCommGroup.tateModule.nonempty_linearEquiv_of_natCard_eq ℓ _ h.1 _ h.2

/-- Blueprint `sk-prop-av-tate-rank`: The `ℓ`-adic Tate module is free of rank `2g`.

This is also the blueprint proposition `prop-av-tate-rank`.

Let `A` be an abelian variety of dimension `g` over an algebraically closed field `K` and let
`ℓ ≠ char K`. Then `V_ℓ A ≅ ℚ_[ℓ] ^ (2 * g)`: this is the base change of
`AlgebraicGeometry.IsAbelianVariety.nonempty_linearEquiv_tateModule` to `ℚ_[ℓ]`. -/
theorem nonempty_linearEquiv_rationalTateModule [IsAlgClosed K] (p : ℕ) [CharP K p]
    (hℓ : ℓ ≠ p) :
    Nonempty (rationalTateModule ℓ A ≃ₗ[ℚ_[ℓ]] (Fin (2 * IsAbelianVariety.dim A) → ℚ_[ℓ])) :=
  have h := exists_zsmul_eq_and_natCard_torsionBy ℓ A p hℓ
  AddCommGroup.rationalTateModule.nonempty_linearEquiv_of_natCard_eq ℓ _ h.1 _ h.2

section Functoriality

variable {ℓ A} {B C : Over (Spec (.of K))} [GrpObj B] [IsAbelianVariety B] [GrpObj C]
  [IsAbelianVariety C]

end Functoriality

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

end Galois

end IsAbelianVariety

end AlgebraicGeometry
