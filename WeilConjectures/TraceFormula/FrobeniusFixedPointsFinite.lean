/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.PointCount
public import WeilConjectures.TraceFormula.WeilTrace

/-!

# Finiteness of the points of degree `n + 1` for an automorphism of finite order

For an automorphism `e` of finite order of a scheme `X` of finite type over a finite field `k`,
the points of degree `n + 1` for the Frobenius twisted by `e`
(`ProEtale.CondensedRing.frobeniusFixedPoints e n`) are finite: they are fixed by a power
`σ^N` of the geometric Frobenius of `Spec k̄`, hence factor through `Spec L` for the finite field
`L ⊆ k̄` fixed by `σ^N`, and there are only finitely many morphisms `Spec L ⟶ X`.

## Main statements

- `ProEtale.CondensedRing.finite_frobeniusFixedPoints_of_powSucc_eq_refl`.

-/

@[expose] public section

universe u

open CategoryTheory FiniteField

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- The powers `e.powSucc n` of an automorphism are the monoid powers `e.hom ^ (n + 1)` in
`End X`. -/
lemma _root_.CategoryTheory.Iso.powSucc_hom_eq_pow {C : Type*} [Category C] {X : C} (e : X ≅ X)
    (n : ℕ) : (e.powSucc n).hom = (show End X from e.hom) ^ (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih => rw [Iso.powSucc_succ, Iso.trans_hom, ih, pow_succ' _ (n + 1)]; rfl

/-- If `x ≫ A = S ≫ x` then `x ≫ A ^ j = S ^ j ≫ x` for the monoid powers in `End`. -/
lemma comp_pow_eq_pow_comp {C : Type*} [Category C] {W X : C} (x : W ⟶ X) (A : End X)
    (S : End W) (h : x ≫ A = S ≫ x) (j : ℕ) : x ≫ (A ^ j : End X) = (S ^ j : End W) ≫ x := by
  induction j with
  | zero => rw [pow_zero, pow_zero, End.one_def, End.one_def, Category.comp_id, Category.id_comp]
  | succ j ih =>
    rw [pow_succ, pow_succ, End.mul_def, End.mul_def, ← Category.assoc, h, Category.assoc, ih,
      Category.assoc]

lemma _root_.CategoryTheory.Over.pow_left {C : Type*} [Category C] {S : C} {X : Over S}
    (a : End X) (j : ℕ) :
    (a ^ j : End X).left = (show End X.left from a.left) ^ j := by
  induction j with
  | zero => rfl
  | succ j ih => rw [pow_succ, pow_succ, End.mul_def, End.mul_def, Over.comp_left, ih]

variable {k : Type u} [Field k] [Finite k]

/-- The `N`-th power of the geometric Frobenius of `Spec k̄` is `Spec` of the `N`-th power of the
geometric Frobenius of `k̄`. -/
lemma geometricFrobeniusField_hom_pow (N : ℕ) :
    (show End (Spec (.of (AlgebraicClosure k))) from (geometricFrobeniusField k).hom) ^ N =
      Spec.map (CommRingCat.ofHom
        ((geometricFrobenius k (AlgebraicClosure k)) ^ N).toRingEquiv.toRingHom) := by
  induction N with
  | zero =>
    rw [pow_zero, pow_zero, End.one_def]
    exact (Spec.map_id _).symm
  | succ N ih =>
    rw [pow_succ, End.mul_def, ih, geometricFrobeniusField_hom, ← Spec.map_comp]
    congr 1
    ext y
    simp [pow_succ', AlgEquiv.mul_apply]

/-- If the `N`-th power of the geometric Frobenius fixes `y`, then `y ^ (#k ^ N) = y`. -/
lemma pow_card_pow_eq_of_geometricFrobenius_pow (N : ℕ) (y : AlgebraicClosure k)
    (hy : ((geometricFrobenius k (AlgebraicClosure k)) ^ N) y = y) :
    y ^ (Nat.card k ^ N) = y := by
  have key : ∀ (N : ℕ) (z : AlgebraicClosure k),
      ((geometricFrobenius k (AlgebraicClosure k)) ^ N) z ^ (Nat.card k ^ N) = z := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      intro z
      rw [pow_succ (geometricFrobenius k (AlgebraicClosure k)) N, AlgEquiv.mul_apply,
        pow_succ (Nat.card k) N, pow_mul, ih, geometricFrobenius_pow_card]
  conv_rhs => rw [← key N y]
  rw [hy]

variable (k) in
/-- The subfield of `k̄` fixed by the `N`-th power of the geometric Frobenius. -/
noncomputable def geometricFrobeniusPowFixedField (N : ℕ) :
    IntermediateField k (AlgebraicClosure k) :=
  Subalgebra.toIntermediateField
    (AlgHom.equalizer ((geometricFrobenius k (AlgebraicClosure k)) ^ N).toAlgHom
      (AlgHom.id k _))
    (fun y hy ↦ by
      change ((geometricFrobenius k (AlgebraicClosure k)) ^ N).toAlgHom y⁻¹ = y⁻¹
      rw [map_inv₀]
      exact congrArg (·⁻¹) hy)

lemma mem_geometricFrobeniusPowFixedField {N : ℕ} {y : AlgebraicClosure k} :
    y ∈ geometricFrobeniusPowFixedField k N ↔
      ((geometricFrobenius k (AlgebraicClosure k)) ^ N) y = y :=
  Iff.rfl

/-- The field fixed by a positive power of the geometric Frobenius is finite. -/
lemma finite_geometricFrobeniusPowFixedField {N : ℕ} (hN : N ≠ 0) :
    Finite (geometricFrobeniusPowFixedField k N) := by
  let p : Polynomial (AlgebraicClosure k) := Polynomial.X ^ (Nat.card k ^ N) - Polynomial.X
  have hp : p ≠ 0 :=
    FiniteField.X_pow_card_pow_sub_X_ne_zero (AlgebraicClosure k) hN Finite.one_lt_card
  have hfin : {y : AlgebraicClosure k | p.IsRoot y}.Finite :=
    Polynomial.finite_setOfPred_isRoot hp
  refine Set.Finite.to_subtype (hfin.subset fun y hy ↦ ?_)
  change p.IsRoot y
  simp only [Polynomial.IsRoot.def, p, Polynomial.eval_sub, Polynomial.eval_pow,
    Polynomial.eval_X]
  rw [pow_card_pow_eq_of_geometricFrobenius_pow N y hy, sub_self]

/-- A geometric point `x : Spec k̄ ⟶ T` fixed by a power `σ^N` of the geometric Frobenius factors
through `Spec L` for the field `L ⊆ k̄` fixed by `σ^N`. -/
lemma exists_comp_eq_of_geometricFrobenius_pow {T : Scheme.{u}} (N : ℕ)
    (x : Spec (.of (AlgebraicClosure k)) ⟶ T)
    (hx : ((show End (Spec (.of (AlgebraicClosure k))) from (geometricFrobeniusField k).hom) ^ N) ≫
      x = x) :
    ∃ g : Spec (.of (geometricFrobeniusPowFixedField k N)) ⟶ T,
      Spec.map (CommRingCat.ofHom (algebraMap (geometricFrobeniusPowFixedField k N)
        (AlgebraicClosure k))) ≫ g = x := by
  set e := Scheme.SpecToEquivOfField (AlgebraicClosure k) T
  set F := ((geometricFrobenius k (AlgebraicClosure k)) ^ N).toRingEquiv.toRingHom
  have hx' : x = Spec.map (e x).2 ≫ T.fromSpecResidueField (e x).1 := (e.left_inv x).symm
  have hfix : ∀ t, F ((e x).2 t) = (e x).2 t := by
    have h₁ : e.symm ⟨(e x).1, (e x).2 ≫ CommRingCat.ofHom F⟩ = e.symm (e x) := by
      change Spec.map ((e x).2 ≫ CommRingCat.ofHom F) ≫ T.fromSpecResidueField (e x).1 =
        Spec.map (e x).2 ≫ T.fromSpecResidueField (e x).1
      rw [Spec.map_comp, Category.assoc, ← hx', ← geometricFrobeniusField_hom_pow, hx]
    have h₂ := eq_of_heq (Sigma.ext_iff.mp (e.symm.injective h₁)).2
    intro t
    exact congrArg (fun φ ↦ φ t) (congrArg CommRingCat.Hom.hom h₂)
  let φ : T.residueField (e x).1 ⟶ .of (geometricFrobeniusPowFixedField k N) :=
    CommRingCat.ofHom ((e x).2.hom.codRestrict (geometricFrobeniusPowFixedField k N).toSubfield
      fun t ↦ hfix t)
  have hφ : φ ≫ CommRingCat.ofHom (algebraMap (geometricFrobeniusPowFixedField k N)
      (AlgebraicClosure k)) = (e x).2 := by
    ext t
    rfl
  refine ⟨Spec.map φ ≫ T.fromSpecResidueField (e x).1, ?_⟩
  rw [← Category.assoc, ← Spec.map_comp, hφ]
  exact e.left_inv x

/-- **Finiteness of the points of degree `n + 1`** for an automorphism `e` of finite order of a
scheme of finite type over a finite field (the finiteness part of blueprint
`thm-trf-frobenius-fixed-points`, for the Frobenius twisted by `e`): a point `x̄` with
`x̄ ≫ e^{n+1} = σ^{n+1} ≫ x̄` is fixed by `σ^{(n+1)(m+1)}` when `e^{m+1} = 𝟙`, so it factors
through `Spec L` for the finite field `L` fixed by `σ^{(n+1)(m+1)}`. -/
theorem finite_frobeniusFixedPoints_of_powSucc_eq_refl {X : Over (Spec (.of k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] (e : X ≅ X)
    (he : ∃ m : ℕ, e.powSucc m = Iso.refl X) (n : ℕ) : Finite (frobeniusFixedPoints e n) := by
  obtain ⟨m, hm⟩ := he
  set N := (n + 1) * (m + 1)
  have hN : N ≠ 0 := Nat.mul_ne_zero (Nat.succ_ne_zero n) (Nat.succ_ne_zero m)
  have hA : (show End X.left from (e.powSucc n).hom.left) ^ (m + 1) = 𝟙 X.left := by
    rw [Iso.powSucc_hom_eq_pow, ← Over.pow_left, ← pow_mul, mul_comm, pow_mul,
      ← Iso.powSucc_hom_eq_pow, hm, Iso.refl_hom, ← End.one_def, one_pow]
    rfl
  have hfix : ∀ x : frobeniusFixedPoints e n,
      ((show End (Spec (.of (AlgebraicClosure k))) from (geometricFrobeniusField k).hom) ^ N) ≫
        x.1 = x.1 := by
    rintro ⟨y, -, hy⟩
    have h := comp_pow_eq_pow_comp y (show End X.left from (e.powSucc n).hom.left)
      (show End _ from ((geometricFrobeniusField k).powSucc n).hom) hy (m + 1)
    rw [hA, Category.comp_id, Iso.powSucc_hom_eq_pow, ← pow_mul] at h
    exact h.symm
  have := finite_geometricFrobeniusPowFixedField (k := k) hN
  set L := geometricFrobeniusPowFixedField k N
  have := X.hom.finite_fieldPoints L
  choose g hg using fun x : frobeniusFixedPoints e n ↦
    exists_comp_eq_of_geometricFrobenius_pow N x.1 (hfix x)
  have hg' : ∀ x : frobeniusFixedPoints e n,
      g x ≫ X.hom = Spec.map (CommRingCat.ofHom (algebraMap k L)) := by
    intro x
    obtain ⟨φ, hφ⟩ := Spec.map_surjective (g x ≫ X.hom)
    rw [← hφ]
    have h := x.2.1
    rw [← hg x, Category.assoc, ← hφ, ← Spec.map_comp, specAlgebraicClosure] at h
    have h' := congrArg CommRingCat.Hom.hom (Spec.map_injective h)
    congr 1
    ext a
    exact congrArg (fun ψ ↦ ψ a) h'
  exact Finite.of_injective (β := X.hom.fieldPoints L) (fun x ↦ ⟨g x, hg' x⟩)
    fun x₁ x₂ h ↦ Subtype.ext (by
      rw [← hg x₁, ← hg x₂]
      exact congrArg (_ ≫ ·) (congrArg Subtype.val h))

end AlgebraicGeometry.ProEtale.CondensedRing
