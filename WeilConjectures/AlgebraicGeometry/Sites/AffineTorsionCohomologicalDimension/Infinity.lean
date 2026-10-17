/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.AffineTorsionCohomologicalDimension.LocalStep
public import WeilConjectures.AlgebraicGeometry.Sites.AffineTorsionCohomologicalDimension.ProjectiveLine
public import WeilConjectures.AlgebraicGeometry.Sites.AffineTorsionCohomologicalDimension.StalkFormula
public import WeilConjectures.AlgebraicGeometry.Sites.SupportDimension

/-!
# Stalks at infinity of higher direct images along the affine chart

Let `K` be a field, `B = 𝔸ᶜ_K = Spec K[y₁, …, y_c]`, `d = c + 1`, and `j : 𝔸¹_B ⟶ ℙ¹_B` the affine
chart. Assume the affine Artin bound in dimensions `< d`. For a geometric point `s` of `B`
whose image has residue field of transcendence degree `t` over `K`, and `n > d - t`, the stalk
of `Rⁿj_* M` at the point `s ≫ ∞` at infinity vanishes for every torsion sheaf `M`
(`AlgebraicGeometry.ProjectiveLine.isZero_upperStar_infinity_rightDerived_lowerStar_affineChart`).

By the stalk formula (`AlgebraicGeometry.Etale.isZero_upperStar_rightDerived_lowerStar_of_subsingleton_H`)
applied with the chart at infinity `𝔸¹_B ≅ Spec K[y, z] ⟶ ℙ¹_B`, it suffices that
`Hⁿ(𝔸¹_B ×_{ℙ¹_B} Spec R) = 0` for the strict henselization `R` of `K[y, z]` at `s ≫ 0`; this fibre
product is `Spec R[1/z]`, whose torsion cohomological dimension is at most `d - t` by the local
calculation `AlgebraicGeometry.Scheme.hasTorsionCohomologicalDimensionLE_strictHenselization_away`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

/-- Let `p` be a prime of a `K`-algebra `A` with `a ≤ trdeg_K κ(p)`. Then there are `a` elements
of `A` whose images in `κ(p)` are algebraically independent over `K`: the residue field is the
fraction field of `A ⧸ p`, which has the same transcendence degree, and lifts of `a` elements of
a transcendence basis of `A ⧸ p` work. -/
theorem Ideal.exists_algebraicIndependent_residueField {K A : Type u} [Field K] [CommRing A]
    [Algebra K A] (p : Ideal A) [p.IsPrime] (a : ℕ)
    (h : (a : Cardinal) ≤ Algebra.trdeg K p.ResidueField) :
    ∃ σ : Fin a → A, AlgebraicIndependent K (algebraMap A p.ResidueField ∘ σ) := by
  have : FaithfulSMul K (A ⧸ p) :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (algebraMap K (A ⧸ p)).injective
  have : FaithfulSMul (A ⧸ p) p.ResidueField :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 p.injective_algebraMap_quotient_residueField
  have : Algebra.IsAlgebraic (A ⧸ p) p.ResidueField :=
    IsLocalization.isAlgebraic _ (nonZeroDivisors (A ⧸ p))
  have htr : Algebra.trdeg K (A ⧸ p) = Algebra.trdeg K p.ResidueField := by
    rw [← trdeg_add_eq K (A ⧸ p) p.ResidueField, Algebra.trdeg_eq_zero, add_zero]
  obtain ⟨ι, x, hx⟩ := exists_isTranscendenceBasis'.{u} K (A ⧸ p)
  have hι : (a : Cardinal) ≤ Cardinal.mk ι := by rw [hx.cardinalMk_eq_trdeg, htr]; exact h
  obtain ⟨e⟩ : Nonempty (Fin a ↪ ι) := by
    rw [← Cardinal.lift_mk_le']
    simpa using hι
  choose σ hσ using fun i ↦ Ideal.Quotient.mk_surjective (I := p) (x (e i))
  refine ⟨σ, ?_⟩
  have hcomp : algebraMap A p.ResidueField ∘ σ =
      IsScalarTower.toAlgHom K (A ⧸ p) p.ResidueField ∘ (x ∘ e) := by
    ext i
    simp [← hσ]
  rw [hcomp]
  exact (hx.1.comp e e.injective).map' p.injective_algebraMap_quotient_residueField

namespace AlgebraicGeometry

namespace Scheme

/-- A geometric point `s : Spec Ω ⟶ Spec A` with image `y` corresponds to the ring map
`A ⟶ κ(y) ⟶ Ω`. -/
lemma exists_spec_preimage_eq_comp {A : CommRingCat.{u}} {Ω : Type u} [Field Ω]
    (s : Spec (.of Ω) ⟶ Spec A) :
    ∃ g : CommRingCat.of (s (IsLocalRing.closedPoint Ω)).asIdeal.ResidueField ⟶ .of Ω,
      Spec.preimage s = CommRingCat.ofHom (algebraMap A _) ≫ g := by
  refine ⟨(Spec.residueFieldIso A _).inv ≫
    (Spec A).descResidueField (Scheme.stalkClosedPointTo s), ?_⟩
  apply Spec.map_injective
  rw [Spec.map_preimage, Spec.map_comp, Spec.map_comp, Category.assoc,
    Spec.map_residueFieldIso_inv_eq_fromSpecResidueField,
    descResidueField_stalkClosedPointTo_fromSpecResidueField]

/-- The transcendence degree of the residue field of `Spec A` at `y` over `K` is that of
`κ(y) = Frac(A ⧸ y)`. -/
lemma residueFieldTrdeg_Spec {K A : Type u} [Field K] [CommRing A] [Algebra K A]
    (y : Spec (.of A)) :
    residueFieldTrdeg (Spec.map (CommRingCat.ofHom (algebraMap K A))) y =
      Algebra.trdeg K y.asIdeal.ResidueField := by
  unfold residueFieldTrdeg
  letI := (residueFieldHomOfOver (Spec.map (CommRingCat.ofHom (algebraMap K A))) y).toAlgebra
  refine AlgEquiv.trdeg_eq
    { (Spec.residueFieldIso (.of A) y).commRingCatIsoToRingEquiv with commutes' := fun k ↦ ?_ }
  have h : (Scheme.ΓSpecIso (.of K)).inv ≫
      (Spec.map (CommRingCat.ofHom (algebraMap K A))).appTop ≫
        (Spec (.of A)).presheaf.germ ⊤ y trivial ≫ (Spec (.of A)).residue y ≫
          (Spec.residueFieldIso (.of A) y).hom =
      CommRingCat.ofHom (algebraMap K A) ≫ CommRingCat.ofHom (algebraMap A _) := by
    rw [← Category.assoc (Scheme.ΓSpecIso (.of K)).inv, ← ΓSpecIso_inv_naturality,
      Category.assoc, ← Spec.algebraMap_residueFieldIso_inv_assoc, Iso.inv_hom_id,
      Category.comp_id]
  have := congrArg (fun f ↦ f.hom k) h
  simpa [residueFieldHomOfOver, RingHom.algebraMap_toAlgebra,
    IsScalarTower.algebraMap_apply K A y.asIdeal.ResidueField] using this

end Scheme

namespace ProjectiveLine

open Scheme Etale

instance quasiCompact_affineChart (S : Scheme.{u}) : QuasiCompact (affineChart S) := by
  have : QuasiCompact (affineChart S ≫ ProjectiveLine S ↘ S) := by
    rw [affineChart_over]
    infer_instance
  exact QuasiCompact.of_comp _ (ProjectiveLine S ↘ S)

/-- Variant of `isZero_upperStar_infinity_rightDerived_lowerStar_affineChart` with an explicit
number `a ≤ trdeg_K κ(s)` such that `c + 1 - a < n`. -/
theorem isZero_upperStar_infinity_rightDerived_lowerStar_affineChart_of_le {K : Type u}
    [Field K] {c : ℕ} (IH : ∀ e < c + 1, ArtinBound.{u} e)
    (M : Sheaf 𝔸(PUnit.{u + 1}; Spec (.of (MvPolynomial (Fin c) K))).smallEtaleTopology
      AddCommGrpCat.{u + 1}) (hM : M.IsTorsion) (n : ℕ) (hn : 0 < n) {Ω : Type u} [Field Ω]
    [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ Spec (.of (MvPolynomial (Fin c) K))) (a : ℕ)
    (ha : (a : Cardinal.{u}) ≤ residueFieldTrdeg
      (Spec.map (CommRingCat.ofHom (algebraMap K (MvPolynomial (Fin c) K))))
      (s (IsLocalRing.closedPoint Ω))) (han : c + 1 - a < n) :
    IsZero ((s ≫ infinity _)^*[AddCommGrpCat.{u + 1}].obj
      ((((affineChart _)_*[AddCommGrpCat.{u + 1}]).rightDerived n).obj M)) := by
  classical
  let A := MvPolynomial (Fin c) K
  let B : Scheme.{u} := Spec (.of A)
  let P : CommRingCat.{u} := .of (MvPolynomial PUnit.{u + 1} A)
  let e : 𝔸(PUnit.{u + 1}; B) ≅ Spec P := AffineSpace.SpecIso PUnit.{u + 1} (.of A)
  let ι : Spec P ⟶ ProjectiveLine B := e.inv ≫ infinityChart B
  let s' : Spec (.of Ω) ⟶ Spec P := s ≫ AffineSpace.zeroSection PUnit.{u + 1} B ≫ e.hom
  have hs' : s ≫ infinity B = s' ≫ ι := by simp [s', ι, infinity]
  rw [hs']
  refine isZero_upperStar_rightDerived_lowerStar_of_subsingleton_H (affineChart B) ι M s' n hn ?_
  sorry

/-- **Stalks at infinity.** Let `K` be a field, `B = Spec K[y₁, …, y_c]` and `j : 𝔸¹_B ⟶ ℙ¹_B`
the affine chart, and assume the affine Artin bound in dimensions `< c + 1`. Let `s` be a
geometric point of `B` and `n > 0` with `c + 1 < n + trdeg_K κ(s)`. Then for every torsion
abelian étale sheaf `M` on `𝔸¹_B`, the stalk of `Rⁿj_* M` at the geometric point `s ≫ ∞`
vanishes. -/
theorem isZero_upperStar_infinity_rightDerived_lowerStar_affineChart {K : Type u} [Field K]
    {c : ℕ} (IH : ∀ e < c + 1, ArtinBound.{u} e)
    (M : Sheaf 𝔸(PUnit.{u + 1}; Spec (.of (MvPolynomial (Fin c) K))).smallEtaleTopology
      AddCommGrpCat.{u + 1}) (hM : M.IsTorsion) (n : ℕ) (hn : 0 < n) {Ω : Type u} [Field Ω]
    [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ Spec (.of (MvPolynomial (Fin c) K)))
    (hs : ((c + 1 : ℕ) : Cardinal.{u}) < n + residueFieldTrdeg
      (Spec.map (CommRingCat.ofHom (algebraMap K (MvPolynomial (Fin c) K))))
      (s (IsLocalRing.closedPoint Ω))) :
    IsZero ((s ≫ infinity _)^*[AddCommGrpCat.{u + 1}].obj
      ((((affineChart _)_*[AddCommGrpCat.{u + 1}]).rightDerived n).obj M)) := by
  obtain ⟨a, ha, han⟩ : ∃ a : ℕ, (a : Cardinal.{u}) ≤ residueFieldTrdeg
      (Spec.map (CommRingCat.ofHom (algebraMap K (MvPolynomial (Fin c) K))))
      (s (IsLocalRing.closedPoint Ω)) ∧ c + 1 - a < n := by
    by_cases h : ((c + 1 : ℕ) : Cardinal.{u}) ≤ residueFieldTrdeg
      (Spec.map (CommRingCat.ofHom (algebraMap K (MvPolynomial (Fin c) K))))
      (s (IsLocalRing.closedPoint Ω))
    · exact ⟨c + 1, h, by omega⟩
    · push_neg at h
      obtain ⟨m, hm⟩ := Cardinal.lt_aleph0.1 (h.trans (Cardinal.nat_lt_aleph0 _))
      rw [hm] at hs
      refine ⟨m, hm.ge, ?_⟩
      have : c + 1 < n + m := by exact_mod_cast hs
      omega
  exact isZero_upperStar_infinity_rightDerived_lowerStar_affineChart_of_le IH M hM n hn s a ha han

end ProjectiveLine

end AlgebraicGeometry
