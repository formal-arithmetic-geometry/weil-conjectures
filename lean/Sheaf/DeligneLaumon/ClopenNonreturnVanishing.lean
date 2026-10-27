/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A5
-/
module

public import WeilConjectures.WeilSheaf.BaseChangeField.Geometric
public import WeilConjectures.WeilSheaf.Category
public import WeilConjectures.SixFunctors.ProEtale.Adic.OpenImmersion
import Sheaf.DeligneLaumon.ClopenSheetDisjoint

/-! # Vanishing of nonreturn translates on the distinguished sheet

Source: the cyclic Frobenius-orbit argument in `sk-i-dl-general-real`.
(blueprint: lem-zl-clopen-nonreturn-vanishing).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory Limits Endofunctor
open scoped AlgebraicGeometry.ProEtale
namespace AlgebraicGeometry.WeilSheaf

private noncomputable def freePosObjIso
    {Y : Scheme.{u}} {l : ℕ} [Fact l.Prime] (a : Aut Y)
    (M : ProEtale.AdicSheaf l Y) : ∀ n : ℕ,
      IsoAlgebra.Free.posObj (a.inv)_*ᵃ[l] M n ≅ ((a ^ n).inv)_*ᵃ[l].obj M
  | 0 => (ProEtale.adicLowerStarId l Y).symm.app M ≪≫
      (ProEtale.adicLowerStarCongr l (by rw [pow_zero]; rfl)).symm.app M
  | n + 1 => (a.inv)_*ᵃ[l].mapIso (freePosObjIso a M n) ≪≫
      (ProEtale.adicLowerStarComp l (a ^ n).inv a.inv).app M ≪≫
      (ProEtale.adicLowerStarCongr l
        (by rw [pow_succ, Aut.Aut_mul_def, Iso.trans_inv])).symm.app M

private noncomputable def freeNegObjIso
    {Y : Scheme.{u}} {l : ℕ} [Fact l.Prime] (a : Aut Y)
    (M : ProEtale.AdicSheaf l Y) : ∀ n : ℕ,
      IsoAlgebra.Free.negObj (a.inv)_*ᵃ[l] M n ≅ ((a ^ (n + 1)).hom)_*ᵃ[l].obj M
  | 0 => by
      let e := Iso.isoInverseOfIsoFunctor
        (G := (a.inv)_*ᵃ[l].asEquivalence)
        (G' := ProEtale.adicLowerStarEquivalence l a.symm) (Iso.refl _)
      simpa only [IsoAlgebra.Free.negObj, Functor.asEquivalence_inverse,
        ProEtale.adicLowerStarEquivalence_inverse, Iso.symm_inv, Nat.zero_add,
        pow_one] using e.app M
  | n + 1 => by
      let e := Iso.isoInverseOfIsoFunctor
        (G := (a.inv)_*ᵃ[l].asEquivalence)
        (G' := ProEtale.adicLowerStarEquivalence l a.symm) (Iso.refl _)
      exact e.app _ ≪≫ (a.hom)_*ᵃ[l].mapIso (freeNegObjIso a M n) ≪≫
        (ProEtale.adicLowerStarComp l (a ^ (n + 1)).hom a.hom).app M ≪≫
        (ProEtale.adicLowerStarCongr l
          (by rw [pow_succ', Aut.Aut_mul_def, Iso.trans_hom])).symm.app M

private theorem disjoint_range_inv
    {Y D : Scheme.{u}} (v : D ⟶ Y) (a : Y ≅ Y)
    (h : Set.range v.base ∩ Set.range (v ≫ a.hom).base = ∅) :
    Set.range v.base ∩ Set.range (v ≫ a.inv).base = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem] at h ⊢
  rintro z ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
  apply h (v y)
  refine ⟨⟨y, rfl⟩, x, ?_⟩
  have heq := congrArg a.hom (hx.trans hy.symm)
  simpa only [Scheme.Hom.comp_apply, Scheme.inv_hom_apply] using heq

/-- A translate not divisible by the constant-field degree misses the original sheet.
Source: `sk-i-dl-general-real`, geometric-socle/Frobenius orbit step, as used in
`lem-zl-clopen-return-saturation-epi`, proof steps 1--2.

Proof: the two projection equations identify `v` with the sheet determined by the
chosen embedding of `k₁` in the algebraic closure. Monicity of `c` ensures that
intersections of its translated sheets can be checked before mapping to `X`.
If a translate met the original sheet, cancellation of the nonempty
intersection's epimorphic map to the spectrum of the algebraic closure would
make the Frobenius power fix `k₁`. Its order there is `r`, since
`#k₁ = (#k₀)^r`. Thus the ranges are disjoint when `r` does not divide `n`.
For negative `n` use inverse Frobenius, whose action is the inverse cycle.
Iterated inverse image identifies the displayed object with pullback of extension
by zero along that translate. Extension by zero restricts to zero on a disjoint
open, so the object is zero. This also covers the empty scheme.
(blueprint: lem-zl-clopen-nonreturn-vanishing). -/
theorem isZero_clopen_nonreturn_freeObj
    {k₀ k₁ : Type u} [Field k₀] [Finite k₀] [Field k₁] [Finite k₁]
    [Algebra k₀ k₁] {l : ℕ} [Fact l.Prime]
    {X C : Scheme.{u}} [X.Over (Spec (.of k₀))] [C.Over (Spec (.of k₁))]
    (c : C ⟶ X) [Mono c]
    (r : ℕ) (hr : Nat.card k₁ = Nat.card k₀ ^ r)
    (v : (C ↘ Spec (.of k₁)).geometricFiber ⟶ (X ↘ Spec (.of k₀)).geometricFiber)
    [IsOpenImmersion v]
    (hp : v ≫ (X ↘ Spec (.of k₀)).geometricFiberProj =
      (C ↘ Spec (.of k₁)).geometricFiberProj ≫ c)
    (hb : v ≫ (X ↘ Spec (.of k₀)).geometricFiberToAlgebraicClosure =
      (C ↘ Spec (.of k₁)).geometricFiberToAlgebraicClosure ≫
        Spec.map (CommRingCat.ofHom (algebraicClosureAlgEquiv k₀ k₁).symm.toRingHom))
    (M : ProEtale.AdicSheaf l (C ↘ Spec (.of k₁)).geometricFiber)
    (n : ℤ) (hn : ¬ (r : ℤ) ∣ n) :
    IsZero ((v)^*ᵃ[l].obj
      (IsoAlgebra.Free.obj (frobeniusPullback k₀ l X) ((v)_!ᵃ[l].obj M) n)) := by
  let a := (X ↘ Spec (.of k₀)).geometricGaloisFrobenius
  let S := (v)_!ᵃ[l].obj M
  cases n with
  | ofNat n =>
    have hn' : ¬ r ∣ n := fun h ↦ hn (Int.natCast_dvd_natCast.mpr h)
    have hz := ProEtale.isZero_adicUpperStar_adicOpenImmersionLowerShriek v
      (v ≫ (a ^ n).hom) (clopen_sheet_disjoint_pow c r hr v hp hb n hn') M
    exact hz.of_iso
      ((v)^*ᵃ[l].mapIso (freePosObjIso a S n) ≪≫
        (v)^*ᵃ[l].mapIso ((ProEtale.adicUpperStarIsoLowerStarInv l (a ^ n)).symm.app S) ≪≫
        (ProEtale.adicUpperStarComp l v (a ^ n).hom).symm.app S)
  | negSucc n =>
    have hn' : ¬ r ∣ n + 1 := by
      intro h
      apply hn
      exact Int.dvd_neg.mpr (Int.natCast_dvd_natCast.mpr h)
    have hd := disjoint_range_inv v (a ^ (n + 1))
      (clopen_sheet_disjoint_pow c r hr v hp hb (n + 1) hn')
    have hz := ProEtale.isZero_adicUpperStar_adicOpenImmersionLowerShriek v
      (v ≫ (a ^ (n + 1)).inv) hd M
    exact hz.of_iso
      ((v)^*ᵃ[l].mapIso (freeNegObjIso a S n) ≪≫
        (v)^*ᵃ[l].mapIso
          ((ProEtale.adicUpperStarIsoLowerStarInv l (a ^ (n + 1)).symm).symm.app S) ≪≫
        (ProEtale.adicUpperStarComp l v (a ^ (n + 1)).inv).symm.app S)

end AlgebraicGeometry.WeilSheaf
