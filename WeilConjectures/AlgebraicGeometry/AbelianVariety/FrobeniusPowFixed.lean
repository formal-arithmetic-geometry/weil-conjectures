/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.AbelianVariety.RationalTateModule
public import WeilConjectures.TraceFormula.FrobeniusFixedPointsFinite

/-!
# No vector of the Tate module is fixed by a power of Frobenius

Let `A` be an abelian variety over a finite field `K`, let `F` be the geometric Frobenius of
`K̄ / K`, acting on the geometric points `A(K̄)` by coordinates, and let `m > 0`. The points of
`A(K̄)` fixed by `F ^ m` are the points with coordinates in the finite field fixed by `F ^ m`,
so there are only finitely many of them. Hence `F ^ m` fixes no nonzero vector of `T_ℓ A` or of
`V_ℓ A`, and `F ^ m - 1` is an automorphism of `V_ℓ A` and of all its scalar extensions.

## Main statements

- `AlgebraicGeometry.IsAbelianVariety.finite_setOf_geometricFrobenius_pow_fixed`: the points of
  `A(K̄)` fixed by `F ^ m` form a finite set.
- `IsAbelianVariety.eq_zero_of_galoisRepresentation_geometricFrobenius_pow_eq_self`:
  `(T_ℓ A) ^ {F ^ m} = 0`.
- `IsAbelianVariety.eq_zero_of_rationalTateModuleGaloisMap_geometricFrobenius_pow_eq_self`:
  `(V_ℓ A) ^ {F ^ m} = 0`.
- `IsAbelianVariety.bijective_rationalTateModuleGaloisMap_geometricFrobenius_pow_sub_id`:
  `F ^ m - 1` is an automorphism of `V_ℓ A`.
- `IsAbelianVariety.bijective_baseChange_rationalTateModuleGaloisMap_geometricFrobenius_pow_sub_id`:
  `F ^ m - 1` is an automorphism of `E ⊗ V_ℓ A` for every field extension `E` of `ℚ_ℓ`.
-/

@[expose] public section

universe u v

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

namespace AlgebraicGeometry.IsAbelianVariety

variable {K : Type u} [Field K] [Fintype K] (ℓ : ℕ) [Fact ℓ.Prime] (A : Over (Spec (.of K)))
  [GrpObj A] [IsAbelianVariety A]

/-- Over a finite field `K`, the geometric points of an abelian variety fixed by a positive power
`F ^ m` of the geometric Frobenius form a finite set: such a point factors through `Spec L` for
the finite field `L ⊆ K̄` fixed by `F ^ m`, and `A` has only finitely many `L`-points. -/
theorem finite_setOf_geometricFrobenius_pow_fixed {m : ℕ} (hm : m ≠ 0) :
    {P | geometricPointsAddEquiv (A := A)
      (FiniteField.geometricFrobeniusAlgEquivOfAlgebraic K (AlgebraicClosure K) ^ m) P =
        P}.Finite := by
  set L := ProEtale.CondensedRing.geometricFrobeniusPowFixedField K m
  have := ProEtale.CondensedRing.finite_geometricFrobeniusPowFixedField (k := K) hm
  have hF : FiniteField.geometricFrobeniusAlgEquivOfAlgebraic K (AlgebraicClosure K) =
      FiniteField.geometricFrobenius K (AlgebraicClosure K) := by
    ext x
    rw [eq_comm, FiniteField.geometricFrobenius_eq_iff, Nat.card_eq_fintype_card,
      FiniteField.geometricFrobeniusAlgEquivOfAlgebraic_eq_inv, AlgEquiv.aut_inv]
    exact (FiniteField.frobeniusAlgEquivOfAlgebraic K (AlgebraicClosure K)).apply_symm_apply x
  have := A.hom.finite_fieldPoints L
  set S := {P | geometricPointsAddEquiv (A := A)
    (FiniteField.geometricFrobeniusAlgEquivOfAlgebraic K (AlgebraicClosure K) ^ m) P = P}
  have hfix (P : S) :
      ((show End (Spec (.of (AlgebraicClosure K))) from (geometricFrobeniusField K).hom) ^ m) ≫
        P.1.toMul.left = P.1.toMul.left := by
    have h := congrArg (fun Q ↦ Q.toMul.left) P.2
    simp only [geometricPointsAddEquiv_apply, toMul_ofMul, Over.comp_left,
      Scheme.specAlgebraicClosureMap_left, hF] at h
    rw [ProEtale.CondensedRing.geometricFrobeniusField_hom_pow]
    exact h
  choose g hg using fun P : S ↦
    ProEtale.CondensedRing.exists_comp_eq_of_geometricFrobenius_pow m P.1.toMul.left (hfix P)
  have hg' (P : S) : g P ≫ A.hom = Spec.map (CommRingCat.ofHom (algebraMap K L)) := by
    obtain ⟨φ, hφ⟩ := Spec.map_surjective (g P ≫ A.hom)
    rw [← hφ]
    have h := Over.w P.1.toMul
    rw [← hg P, Category.assoc, ← hφ, ← Spec.map_comp] at h
    have h' := congrArg CommRingCat.Hom.hom (Spec.map_injective h)
    congr 1
    ext a
    exact congrArg (fun ψ ↦ ψ a) h'
  refine Set.finite_coe_iff.mp <| Finite.of_injective (β := A.hom.fieldPoints L)
    (fun P ↦ ⟨g P, hg' P⟩) fun P₁ P₂ h ↦ Subtype.ext <| Additive.toMul.injective <|
      Over.OverMorphism.ext ?_
  rw [← hg P₁, ← hg P₂]
  exact congrArg (_ ≫ ·) (congrArg Subtype.val h)

/-- Blueprint `proposition-no-frobenius-fixed-vector--1`: no vector of the Tate module is fixed
by a power of Frobenius.

Let `A` be an abelian variety over a finite field `K` and `F` the geometric Frobenius, acting on
`T_ℓ A` through the Galois representation. For every `m > 0`, `(T_ℓ A) ^ {F ^ m} = 0`: the points
of `A(K̄)` fixed by `F ^ m` form a finite group
(`AlgebraicGeometry.IsAbelianVariety.finite_setOf_geometricFrobenius_pow_fixed`), so this is
`AddCommGroup.eq_zero_of_mem_tateModule_of_forall_fixed`. -/
theorem eq_zero_of_galoisRepresentation_geometricFrobenius_pow_eq_self {m : ℕ} (hm : 0 < m)
    {t : tateModule ℓ A}
    (ht : galoisRepresentation ℓ A
      (FiniteField.geometricFrobeniusAlgEquivOfAlgebraic K (AlgebraicClosure K) ^ m) t = t) :
    t = 0 :=
  Subtype.ext <| AddCommGroup.eq_zero_of_mem_tateModule_of_forall_fixed _
    (finite_setOf_geometricFrobenius_pow_fixed A hm.ne') t.2
    fun n ↦ congrFun (congrArg Subtype.val ht) n

/-- Blueprint `proposition-no-frobenius-fixed-vector--2`: no vector of the rational Tate module
is fixed by a power of Frobenius.

Let `A` be an abelian variety over a finite field `K` and `F` the geometric Frobenius, acting on
`V_ℓ A` by coordinates. For every `m > 0`, `(V_ℓ A) ^ {F ^ m} = 0`. -/
theorem eq_zero_of_rationalTateModuleGaloisMap_geometricFrobenius_pow_eq_self {m : ℕ}
    (hm : 0 < m) {v : rationalTateModule ℓ A}
    (hv : rationalTateModuleGaloisMap ℓ A
      (FiniteField.geometricFrobeniusAlgEquivOfAlgebraic K (AlgebraicClosure K) ^ m) v = v) :
    v = 0 :=
  AddCommGroup.rationalTateModule.eq_zero_of_map_eq_self _
    (finite_setOf_geometricFrobenius_pow_fixed A hm.ne') hv

/-- Blueprint `proposition-no-frobenius-fixed-vector--3`: a power of Frobenius minus one is an
automorphism of the rational Tate module.

Let `A` be an abelian variety over a finite field `K`, `ℓ` a prime invertible in `K` and `F` the
geometric Frobenius. For every `m > 0`, `F ^ m - 1` is bijective on the finite-dimensional
`ℚ_ℓ`-vector space `V_ℓ A`: it is injective since `F ^ m` has no nonzero fixed vector
(`eq_zero_of_rationalTateModuleGaloisMap_geometricFrobenius_pow_eq_self`).
-/
theorem bijective_rationalTateModuleGaloisMap_geometricFrobenius_pow_sub_id (hℓ : (ℓ : K) ≠ 0)
    {m : ℕ} (hm : 0 < m) :
    Function.Bijective (rationalTateModuleGaloisMap ℓ A
      (FiniteField.geometricFrobeniusAlgEquivOfAlgebraic K (AlgebraicClosure K) ^ m) -
        LinearMap.id (R := ℚ_[ℓ]) (M := rationalTateModule ℓ A)) := by
  have := finiteDimensional_rationalTateModule ℓ A hℓ
  have hinj : Function.Injective (rationalTateModuleGaloisMap ℓ A
      (FiniteField.geometricFrobeniusAlgEquivOfAlgebraic K (AlgebraicClosure K) ^ m) -
        LinearMap.id (R := ℚ_[ℓ]) (M := rationalTateModule ℓ A)) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    rw [LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero] at hv
    exact eq_zero_of_rationalTateModuleGaloisMap_geometricFrobenius_pow_eq_self ℓ A hm hv
  exact ⟨hinj, LinearMap.injective_iff_surjective.1 hinj⟩

/-- Blueprint `proposition-no-frobenius-fixed-vector--4`: a power of Frobenius minus one is an
automorphism of every scalar extension of the rational Tate module.

Let `A` be an abelian variety over a finite field `K`, `ℓ` a prime invertible in `K`, `F` the
geometric Frobenius and `E` a field extension of `ℚ_ℓ`. For every `m > 0`, the `E`-linear
extension of `F ^ m - 1` to `E ⊗_{ℚ_ℓ} V_ℓ A` is bijective, being the base change of the linear
automorphism of
`bijective_rationalTateModuleGaloisMap_geometricFrobenius_pow_sub_id`.
-/
theorem bijective_baseChange_rationalTateModuleGaloisMap_geometricFrobenius_pow_sub_id
    (hℓ : (ℓ : K) ≠ 0) {m : ℕ} (hm : 0 < m) (E : Type v) [Field E] [Algebra ℚ_[ℓ] E] :
    Function.Bijective ((rationalTateModuleGaloisMap ℓ A
      (FiniteField.geometricFrobeniusAlgEquivOfAlgebraic K (AlgebraicClosure K) ^ m) -
        LinearMap.id (R := ℚ_[ℓ]) (M := rationalTateModule ℓ A)).baseChange E) :=
  ((LinearEquiv.ofBijective _
    (bijective_rationalTateModuleGaloisMap_geometricFrobenius_pow_sub_id ℓ A hℓ hm)).baseChange
      ℚ_[ℓ] E _ _).bijective

end AlgebraicGeometry.IsAbelianVariety
