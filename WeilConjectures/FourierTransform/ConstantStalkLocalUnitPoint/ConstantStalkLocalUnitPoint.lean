/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.DeligneLaumon.LocalFrobeniusTrace

/-! # The embedded geometric point of a finite-field point and its semilinear return

Source: literature/blueprint/latest/blueprint/sec-zeta-weil/sk-thm-weil-final/
prop-every-iterate-trace.md, constant-sheaf clause; return convention of
def-weil-local-frobenius-trace (blueprint: lem-zl-constant-stalk-local-unit-point).

An `F_{q^n}`-point `x` of `Y₀` and an embedding `ι : F_{q^n} → k` over `k₀` give the
geometric point `(x ∘ Spec ι, id) : Spec k → Y₀ ×_{k₀} k`. Its `n`-th positive power of
the geometric Frobenius returns it along the `n`-th power of the field Frobenius.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace WeilConjectures.ConstantStalkLocalUnitPoint

/-- The geometric point `(x ∘ Spec ι, id)` of `Y₀ ×_{k₀} k` defined by a finite-field point
and an embedding of `F_{q^n}` into `k` over `k₀`.
Source: def-weil-local-frobenius-trace, associated geometric point
(blueprint: lem-zl-constant-stalk-local-unit-point). -/
def embeddingPoint (D : FiniteFieldDatum.{u})
    (Y₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    (n : ℕ) (hn : 1 ≤ n) (x : D.extensionPoints Y₀ n hn)
    (iota : D.extensionSubfield n hn →+* D.k)
    (hι : iota.comp (D.extensionEmbedding n hn) = algebraMap D.k₀ D.k) :
    Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left :=
  pullback.lift (Spec.map (CommRingCat.ofHom iota) ≫ x.left) (𝟙 _)
    (by
      rw [Category.assoc, Over.w x, Category.id_comp]
      change Spec.map (CommRingCat.ofHom iota) ≫
        Spec.map (CommRingCat.ofHom (D.extensionEmbedding n hn)) = _
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
      exact congrArg (fun f ↦ Spec.map (CommRingCat.ofHom f)) hι)

/-- Contravariant Spec sends the positive power to the corresponding field power.
Source: geometric-Frobenius construction (blueprint: lem-zl-constant-stalk-local-unit-point). -/
private theorem pointPower_eq (n : ℕ) :
    localPositivePower (frobeniusPointIso D).hom n =
      let := Fintype.ofFinite D.k₀
      Spec.map (CommRingCat.ofHom
        (FiniteField.geometricFrobeniusAlgEquivOfAlgebraic D.k₀ D.k ^ (n + 1)).toRingHom) := by
  let := Fintype.ofFinite D.k₀
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [localPositivePower, ih]
    change Spec.map _ ≫ Spec.map _ = _
    rw [← Spec.map_comp]
    congr 1

/-- Iterating the two Galois-map projections preserves the model projection and
iterates the coefficient projection.
Source: geometric-Frobenius construction (blueprint: lem-zl-constant-stalk-local-unit-point). -/
private theorem frobeniusPower_projections (n : ℕ) :
    localPositivePower (D.geometricFrobenius Y₀).hom n ≫
        pullback.fst Y₀.hom (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) =
      pullback.fst Y₀.hom (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) ∧
    localPositivePower (D.geometricFrobenius Y₀).hom n ≫
        pullback.snd Y₀.hom (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) =
      pullback.snd Y₀.hom (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) ≫
        localPositivePower (frobeniusPointIso D).hom n := by
  let := Fintype.ofFinite D.k₀
  have h := D.galoisMap_projections Y₀.hom
    (FiniteField.geometricFrobeniusAlgEquivOfAlgebraic D.k₀ D.k)
  change (D.geometricFrobenius Y₀).hom ≫ _ = _ ∧
    (D.geometricFrobenius Y₀).hom ≫ _ =
      _ ≫ (frobeniusPointIso D).hom at h
  induction n with
  | zero => exact h
  | succ n ih =>
    constructor
    · rw [localPositivePower, Category.assoc, h.1]
      exact ih.1
    · rw [localPositivePower, Category.assoc, h.2, ← Category.assoc, ih.2,
        Category.assoc]
      rfl

/-- A model map fixed by the point power has the stated semilinear return lift.
Source: pullback uniqueness (blueprint: lem-zl-constant-stalk-local-unit-point). -/
private theorem lift_return (n : ℕ) (a : Spec (.of D.k) ⟶ Y₀.left)
    (c : a ≫ Y₀.hom =
      (𝟙 (Spec (.of D.k))) ≫ Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))
    (ha : localPositivePower (frobeniusPointIso D).hom n ≫ a = a) :
    pullback.lift a (𝟙 _) c ≫ localPositivePower (D.geometricFrobenius Y₀).hom n =
      localPositivePower (frobeniusPointIso D).hom n ≫ pullback.lift a (𝟙 _) c := by
  apply pullback.hom_ext
  · rw [Category.assoc, (frobeniusPower_projections D Y₀ n).1,
      pullback.lift_fst, Category.assoc, pullback.lift_fst, ha]
  · rw [Category.assoc, (frobeniusPower_projections D Y₀ n).2,
      ← Category.assoc, pullback.lift_snd, Category.assoc, pullback.lift_snd,
      Category.id_comp, Category.comp_id]

/-- The semilinear return of the embedded point, `x̄ ≫ g_Y^n = σ^n ≫ x̄`, in the form
required by def-weil-local-frobenius-trace.
Source: def-weil-local-frobenius-trace, return convention
(blueprint: lem-zl-constant-stalk-local-unit-point).
Proof: the subfield `F_{q^n}` has `q^n` elements, so the `n`-th power of the geometric
Frobenius of `k/k₀` fixes the image of `ι` pointwise; hence `σ^n ≫ (Spec ι ≫ x) = Spec ι ≫ x`.
The `n`-th power of the geometric Frobenius of `Y₀ ×_{k₀} k` fixes the first projection and
transports the second projection along `σ^n`. Comparing both projections of the fibre
product, pullback uniqueness gives the equation. -/
theorem embeddingPoint_return (D : FiniteFieldDatum.{u})
    (Y₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    (n : ℕ) (hn : 1 ≤ n) (x : D.extensionPoints Y₀ n hn)
    (iota : D.extensionSubfield n hn →+* D.k)
    (hι : iota.comp (D.extensionEmbedding n hn) = algebraMap D.k₀ D.k) :
    embeddingPoint D Y₀ n hn x iota hι ≫
        localPositivePower (D.geometricFrobenius Y₀).hom (n - 1) =
      localPositivePower (frobeniusPointIso D).hom (n - 1) ≫
        embeddingPoint D Y₀ n hn x iota hι := by
  let := Fintype.ofFinite D.k₀
  have hc : Nat.card (D.extensionSubfield n hn) = D.q ^ n :=
    (FiniteField.exists_unique_subfield_of_closure D.p D.a D.q D.prime D.exponent_pos
      D.cardinality_eq D.k₀ D.card_base D.k n hn).choose_spec.2.1
  have hq : 0 < D.q := by
    rw [← D.card_base]
    exact Nat.card_pos
  have : Finite (D.extensionSubfield n hn) :=
    (Nat.card_pos_iff.mp (by rw [hc]; exact pow_pos hq n)).2
  have hc' : Nat.card (D.extensionSubfield n hn) = Fintype.card D.k₀ ^ n := by
    simpa only [← D.card_base, Nat.card_eq_fintype_card] using hc
  apply lift_return D Y₀ (n - 1)
  rw [← Category.assoc]
  suffices h : localPositivePower (frobeniusPointIso D).hom (n - 1) ≫
      Spec.map (CommRingCat.ofHom iota) = Spec.map (CommRingCat.ofHom iota) by rw [h]
  rw [pointPower_eq, Nat.sub_add_cancel hn, ← Spec.map_comp]
  congr 1
  ext a
  exact FiniteField.geometricFrobeniusAlgEquivOfAlgebraic_pow_apply_of_card_eq
    D.k₀ D.k n hc' iota a

section Helpers

variable (D : FiniteFieldDatum.{u})
  (Y₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency false in
end Helpers

end WeilConjectures.ConstantStalkLocalUnitPoint
