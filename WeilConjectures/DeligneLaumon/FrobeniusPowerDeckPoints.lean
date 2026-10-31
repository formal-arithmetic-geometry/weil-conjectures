/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.BaseChangeField.Geometric
public import WeilConjectures.AlgebraicGeometry.GeometricFrobenius.Points

/-! # Frobenius deck translates of finite points

Source: `sk-i-dl-general-real`, geometric orbit argument, point selection.
(blueprint: lem-zl-frobenius-power-deck-points).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme.Hom

variable {k₀ : Type u} [Field k₀] [Finite k₀]
  {X : Scheme.{u}}
  [X.Over (Spec (CommRingCat.of k₀))]
  {k₁ : Type u} [Field k₁] [Finite k₁] [Algebra k₀ k₁]
  [Algebra.IsAlgebraic k₀ k₁]
  {C : Scheme.{u}} [C.Over (Spec (CommRingCat.of k₁))] {c : C ⟶ X}

/-- The actual translate of a geometric point, through the canonical
constant-field comparison. Source: the geometric orbit argument.
(blueprint: lem-zl-frobenius-power-deck-points). -/
noncomputable def frobeniusPowerTranslatePoint
    (hc : IsPullback c (C ↘ Spec (.of k₁)) (X ↘ Spec (.of k₀))
      (Spec.map (CommRingCat.ofHom (algebraMap k₀ k₁))))
    (j : ℕ) (s : Spec (.of (AlgebraicClosure k₁)) ⟶
      (C ↘ Spec (.of k₁)).geometricFiber) :
    Spec (.of (AlgebraicClosure k₁)) ⟶ (C ↘ Spec (.of k₁)).geometricFiber :=
  s ≫ (geometricFiberBaseChangeIso hc).inv ≫
    ((X ↘ Spec (.of k₀)).geometricGaloisFrobenius ^ j).hom ≫
      (geometricFiberBaseChangeIso hc).hom

private theorem geometricFrobenius_natural
    {K L M : Type u} [Field K] [Fintype K] [Field L] [Field M]
    [Algebra K L] [Algebra K M] [Algebra.IsAlgebraic K L] [Algebra.IsAlgebraic K M]
    (β : L →+* M) (n : ℕ) (x : L) :
    β ((FiniteField.geometricFrobeniusAlgEquivOfAlgebraic K L ^ n) x) =
      (FiniteField.geometricFrobeniusAlgEquivOfAlgebraic K M ^ n) (β x) := by
  simp only [FiniteField.geometricFrobeniusAlgEquivOfAlgebraic_eq_inv]
  simp only [inv_pow]
  simp only [AlgEquiv.aut_inv]
  rw [AlgEquiv.eq_symm_apply, AlgEquiv.coe_pow,
    FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate]
  dsimp only
  rw [← map_pow]
  congr 1
  have h := AlgEquiv.apply_symm_apply (FiniteField.frobeniusAlgEquivOfAlgebraic K L ^ n) x
  rwa [AlgEquiv.coe_pow, FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate] at h

omit [Finite k₀] [Finite k₁] [Algebra.IsAlgebraic k₀ k₁] in
private theorem exists_deck_iso
    (hc : IsPullback c (C ↘ Spec (.of k₁)) (X ↘ Spec (.of k₀))
      (Spec.map (CommRingCat.ofHom (algebraMap k₀ k₁))))
    (e : Aut (Spec (.of k₁)))
    (he : e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap k₀ k₁)) =
      Spec.map (CommRingCat.ofHom (algebraMap k₀ k₁))) :
    ∃ d : Aut C, d.hom ≫ c = c ∧
      d.hom ≫ (C ↘ Spec (.of k₁)) = (C ↘ Spec (.of k₁)) ≫ e.hom := by
  let f := X ↘ Spec (.of k₀)
  let b := Spec.map (CommRingCat.ofHom (algebraMap k₀ k₁))
  let m := pullback.map f b f b (𝟙 X) e.hom (𝟙 _) (by simp) (by simpa using he.symm)
  let d := hc.isoPullback ≪≫ asIso m ≪≫ hc.isoPullback.symm
  refine ⟨d, ?_, ?_⟩
  · simp [d, m, f, b, Category.assoc]
  · simp [d, m, f, b, Category.assoc]

private theorem residueCard_eq_card {K : Type u} [Field K] [Finite K]
    {Y : Scheme.{u}} (f : Y ⟶ Spec (.of K)) (x : Y.finitePoints) :
    f.residueCard x.1 = Nat.card (Y.residueField x.1) := by
  let := (f.residueFieldAlgebraMap x.1).toAlgebra
  have : Finite (Y.residueField x.1) := x.2
  exact (Module.natCard_eq_pow_finrank (K := K) (V := Y.residueField x.1)).symm

/-- The translated lift lies over a deck-related finite point of equal residue size.
Source: first step of `lem-zl-geometric-power-orbit-stalk` in `sk-i-dl-general-real`.
(blueprint: lem-zl-frobenius-power-deck-points).

Proof: The j-th geometric Frobenius of the algebraic closure of k0 preserves
the embedded finite field k1. Its restriction induces a deck automorphism d of
the cartesian model C over X. The defining projections of the canonical
geometric-fibre isomorphism show that the displayed translated lift lies over
t'=d(t). Scheme automorphisms induce residue-field isomorphisms, so t' has
finite residue field of the same absolute cardinality. For finite points over
k1, residueCard equals that absolute residue cardinality.
No assertion equates this lift with the independently chosen lift of t'. -/
theorem exists_frobenius_power_deck_point
    (hc : IsPullback c (C ↘ Spec (CommRingCat.of k₁)) (X ↘ Spec (CommRingCat.of k₀))
      (Spec.map (CommRingCat.ofHom (algebraMap k₀ k₁))))
    (j : ℕ) (t : C.finitePoints) :
    ∃ t' : C.finitePoints,
      c t'.1 = c t.1 ∧
      (C ↘ Spec (.of k₁)).residueCard t'.1 = (C ↘ Spec (.of k₁)).residueCard t.1 ∧
      ((frobeniusPowerTranslatePoint hc j
          ((C ↘ Spec (.of k₁)).geometricFiberPointOfFinitePoint t)) ≫
        (C ↘ Spec (.of k₁)).geometricFiberProj).base
          (IsLocalRing.closedPoint (AlgebraicClosure k₁)) = t'.1 := by
  let := Fintype.ofFinite k₀
  let φ := FiniteField.geometricFrobeniusAlgEquivOfAlgebraic k₀ k₁ ^ j
  let e : Aut (Spec (.of k₁)) := Scheme.Spec.mapIso φ.toRingEquiv.toCommRingCatIso.op
  have he : e.hom = Spec.map (CommRingCat.ofHom φ.toRingHom) := rfl
  have hb : e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap k₀ k₁)) =
      Spec.map (CommRingCat.ofHom (algebraMap k₀ k₁)) := by
    rw [he]
    exact spec_map_comp_spec_map_eq _ _ _ φ.commutes
  obtain ⟨d, hd, hd'⟩ := exists_deck_iso hc e hb
  have hσ : (specGeometricFrobenius k₀ ^ j).hom ≫
        Spec.map (CommRingCat.ofHom (algebraicClosureEmbedding (k₀ := k₀) (k₀' := k₁))) =
      Spec.map (CommRingCat.ofHom (algebraicClosureEmbedding (k₀ := k₀) (k₀' := k₁))) ≫
        e.hom := by
    rw [specGeometricFrobenius_pow_hom, he, ← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext x
    exact (geometricFrobenius_natural
      (algebraicClosureEmbedding (k₀ := k₀) (k₀' := k₁)) j x).symm
  have hP : ((X ↘ Spec (.of k₀)).geometricGaloisFrobenius ^ j).hom ≫
        geometricFiberToBaseChange hc = geometricFiberToBaseChange hc ≫ d.hom := by
    apply hc.hom_ext
    · simp [hd]
    · simp only [Category.assoc, geometricFiberToBaseChange_comp_snd,
        geometricGaloisFrobenius_pow_hom_comp_geometricFiberToAlgebraicClosure_assoc]
      rw [hd', geometricFiberToBaseChange_comp_snd_assoc, hσ]
  have hi : (geometricFiberBaseChangeIso hc).inv ≫ geometricFiberToBaseChange hc =
      (C ↘ Spec (.of k₁)).geometricFiberProj := by
    rw [Iso.inv_comp_eq]
    exact (geometricFiberBaseChangeHom_comp_geometricFiberProj hc).symm
  have hT (s : Spec (.of (AlgebraicClosure k₁)) ⟶
      (C ↘ Spec (.of k₁)).geometricFiber) :
      frobeniusPowerTranslatePoint hc j s ≫ (C ↘ Spec (.of k₁)).geometricFiberProj =
        s ≫ (C ↘ Spec (.of k₁)).geometricFiberProj ≫ d.hom := by
    simp only [frobeniusPowerTranslatePoint, Category.assoc,
      show (geometricFiberBaseChangeIso hc).hom ≫
          (C ↘ Spec (.of k₁)).geometricFiberProj = geometricFiberToBaseChange hc from
        geometricFiberBaseChangeHom_comp_geometricFiberProj hc]
    rw [hP, ← Category.assoc (geometricFiberBaseChangeIso hc).inv, hi]
  let t' : C.finitePoints :=
    ⟨d.hom t.1, (mem_finitePoints_iff_of_isIso d.hom t.1).2 t.2⟩
  refine ⟨t', ?_, ?_, ?_⟩
  · exact congrArg (fun g : C ⟶ X ↦ g t.1) hd
  · rw [residueCard_eq_card _ t', residueCard_eq_card _ t]
    exact pointNorm_of_isIso d.hom t.1
  · rw [hT, ← Category.assoc, Scheme.Hom.comp_apply,
      geometricFiberPointOfFinitePoint_comp_geometricFiberProj_base]

end AlgebraicGeometry.Scheme.Hom
