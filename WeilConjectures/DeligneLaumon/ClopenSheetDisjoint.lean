/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.BaseChangeField.Geometric
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-! # Distinct constant-field sheets are disjoint

Source: the cyclic Frobenius-orbit argument in `sk-i-dl-general-real`.
(blueprint: lem-zl-clopen-sheet-disjoint).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory Limits
namespace AlgebraicGeometry.WeilSheaf

private theorem degree_dvd_of_geometricFrobenius_fixes
    {k₀ k₁ : Type u} [Field k₀] [Fintype k₀] [Field k₁] [Finite k₁]
    [Algebra k₀ k₁] (r n : ℕ) (hr : Nat.card k₁ = Nat.card k₀ ^ r)
    (j : k₁ →+* AlgebraicClosure k₀)
    (h : ∀ x, (FiniteField.geometricFrobeniusAlgEquivOfAlgebraic
      k₀ (AlgebraicClosure k₀) ^ n) (j x) = j x) : r ∣ n := by
  let := Fintype.ofFinite k₁
  have hcard : 2 ≤ Nat.card k₀ := by
    rw [Nat.card_eq_fintype_card]
    exact Fintype.one_lt_card
  have hrank : r = Module.finrank k₀ k₁ :=
    Nat.pow_right_injective hcard
      (hr.symm.trans Module.natCard_eq_pow_finrank)
  rw [hrank, ← FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic k₀ k₁,
    orderOf_dvd_iff_pow_eq_one]
  ext x
  have hx := h x
  rw [FiniteField.geometricFrobeniusAlgEquivOfAlgebraic_eq_inv, inv_pow,
    AlgEquiv.aut_inv, AlgEquiv.symm_apply_eq] at hx
  have hx' : x ^ (Fintype.card k₀ ^ n) = x := by
    apply j.injective
    rw [map_pow]
    simpa only [AlgEquiv.coe_pow,
      FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate] using hx.symm
  simpa only [AlgEquiv.coe_pow, FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate,
    AlgEquiv.one_apply] using hx'

/-- A nonreturn power of Frobenius translates the distinguished sheet away from itself.
Source: `sk-i-dl-general-real`, geometric-socle/Frobenius orbit step.
Proof: on the intersection pullback, monicity of the model inclusion identifies
the two maps to `C`. Their structural maps to `Spec k₁` therefore agree. The
closure projection equation identifies the two algebraic-closure coordinates
up to the specified Frobenius power. If the intersection were nonempty, its
map to the spectrum of the algebraic closure would be flat and surjective,
hence epi. Cancellation would make that Frobenius power fix `k₁`. The order
of finite-field Frobenius is the extension degree `r`, contradicting `r ∤ n`.
(blueprint: lem-zl-clopen-sheet-disjoint). -/
theorem clopen_sheet_disjoint_pow
    {k₀ k₁ : Type u} [Field k₀] [Finite k₀] [Field k₁] [Finite k₁]
    [Algebra k₀ k₁] {X C : Scheme.{u}}
    [X.Over (Spec (.of k₀))] [C.Over (Spec (.of k₁))]
    (c : C ⟶ X) [Mono c] (r : ℕ) (hr : Nat.card k₁ = Nat.card k₀ ^ r)
    (v : (C ↘ Spec (.of k₁)).geometricFiber ⟶ (X ↘ Spec (.of k₀)).geometricFiber)
    (hp : v ≫ (X ↘ Spec (.of k₀)).geometricFiberProj =
      (C ↘ Spec (.of k₁)).geometricFiberProj ≫ c)
    (hb : v ≫ (X ↘ Spec (.of k₀)).geometricFiberToAlgebraicClosure =
      (C ↘ Spec (.of k₁)).geometricFiberToAlgebraicClosure ≫
        Spec.map (CommRingCat.ofHom (algebraicClosureAlgEquiv k₀ k₁).symm.toRingHom))
    (n : ℕ) (hn : ¬ r ∣ n) :
    Set.range v.base ∩
      Set.range (v ≫ ((X ↘ Spec (.of k₀)).geometricGaloisFrobenius ^ n).hom).base = ∅ := by
  classical
  let fX := X ↘ Spec (.of k₀)
  let fC := C ↘ Spec (.of k₁)
  let aX := fX.geometricFiberToAlgebraicClosure
  let φ := (fX.geometricGaloisFrobenius ^ n).hom
  let j := (algebraicClosureAlgEquiv k₀ k₁).toRingHom.comp
    (algebraMap k₁ (AlgebraicClosure k₁))
  have hvj : v ≫ aX ≫ Spec.map (CommRingCat.ofHom j) = fC.geometricFiberProj ≫ fC := by
    rw [← Category.assoc, show v ≫ aX = _ from hb, Category.assoc]
    rw [spec_map_comp_spec_map_eq _ _ (algebraMap k₁ (AlgebraicClosure k₁))
      (fun x ↦ by simp [j])]
    exact fC.geometricFiber_condition.symm
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro z hz
  have hz' : z ∈ Set.range (pullback.fst v (v ≫ φ) ≫ v).base := by
    rw [Scheme.Pullback.range_fst_comp]
    exact hz
  obtain ⟨w, _⟩ := hz'
  let p₁ := pullback.fst v (v ≫ φ)
  let p₂ := pullback.snd v (v ≫ φ)
  have hmodel : p₁ ≫ fC.geometricFiberProj = p₂ ≫ fC.geometricFiberProj := by
    apply (cancel_mono c).1
    have heq := congrArg (fun t ↦ t ≫ fX.geometricFiberProj)
      (show p₁ ≫ v = p₂ ≫ v ≫ φ from pullback.condition)
    simpa only [Category.assoc, φ, fX, fC,
      Scheme.Hom.geometricGaloisFrobenius_pow_hom_comp_geometricFiberProj, hp] using heq
  let g := p₂ ≫ v ≫ aX
  have : Surjective g := ⟨fun x ↦ ⟨w, Subsingleton.elim _ _⟩⟩
  have : Epi g := Flat.epi_of_flat_of_surjective g
  have hfix : (specGeometricFrobenius k₀ ^ n).hom ≫
      Spec.map (CommRingCat.ofHom j) = Spec.map (CommRingCat.ofHom j) := by
    apply (cancel_epi g).1
    calc
      g ≫ (specGeometricFrobenius k₀ ^ n).hom ≫ Spec.map (CommRingCat.ofHom j) =
          p₂ ≫ v ≫ φ ≫ aX ≫ Spec.map (CommRingCat.ofHom j) := by
        simpa only [g, φ, aX, Category.assoc] using
          congrArg (fun t ↦ p₂ ≫ v ≫ t ≫ Spec.map (CommRingCat.ofHom j))
            (fX.geometricGaloisFrobenius_pow_hom_comp_geometricFiberToAlgebraicClosure n).symm
      _ = p₁ ≫ v ≫ aX ≫ Spec.map (CommRingCat.ofHom j) := by
        simpa only [Category.assoc] using
          congrArg (fun t ↦ t ≫ aX ≫ Spec.map (CommRingCat.ofHom j))
            (show p₁ ≫ v = p₂ ≫ v ≫ φ from pullback.condition).symm
      _ = p₁ ≫ fC.geometricFiberProj ≫ fC := by rw [hvj]
      _ = p₂ ≫ fC.geometricFiberProj ≫ fC := by
        simpa only [Category.assoc] using congrArg (fun t ↦ t ≫ fC) hmodel
      _ = g ≫ Spec.map (CommRingCat.ofHom j) := by
        simp only [g, Category.assoc, hvj]
  apply hn
  let := Fintype.ofFinite k₀
  apply degree_dvd_of_geometricFrobenius_fixes r n hr j
  rw [specGeometricFrobenius_pow_hom, ← Spec.map_comp] at hfix
  have heq := Spec.map_injective hfix
  intro x
  exact congrArg (fun f : CommRingCat.of k₁ ⟶ CommRingCat.of (AlgebraicClosure k₀) ↦
    f.hom x) heq

end AlgebraicGeometry.WeilSheaf
