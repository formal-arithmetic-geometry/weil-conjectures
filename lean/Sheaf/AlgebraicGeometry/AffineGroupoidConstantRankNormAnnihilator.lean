/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q86
-/
module

public import Sheaf.AlgebraicGeometry.SchemeGroupoidLaws
public import Sheaf.RingTheory.FiniteLocallyFreeNormCharacteristicPolynomial
public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
public import Mathlib.Algebra.Polynomial.Lifts
public import WeilConjectures.AlgebraicGeometry.FiniteLocallyFreeNormCharts
import Sheaf.AlgebraicGeometry.AffineGroupoidPolynomialNormInvariant
import Mathlib.Algebra.Polynomial.Eval.Degree
import Sheaf.AlgebraicGeometry.AffineGroupoidCanonicalNormCharts

/-!
# The constant-rank affine groupoid norm polynomial and its root

Source: Stacks Project, Groupoids, Tag 03BJ, second paragraph of
`lemma-integral-over-invariants`; Tags 03BH, 00DX and 0231
(blueprint: lem-a1-affine-groupoid-constant-rank-norm-annihilator).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

@[instance_reducible]
private noncomputable def pointGroupoid {U R : Scheme.{u}} (s t : R ⟶ U)
    (e : U ⟶ R) (i : R ⟶ R) (c : pullback s t ⟶ R)
    (hG : Scheme.IsGroupoid s t e i c) (H : Scheme.{u}) :
    Groupoid.{u} (H ⟶ U) where
  Hom x y := {a : H ⟶ R // a ≫ s = x ∧ a ≫ t = y}
  id x := ⟨x ≫ e, by simp [Category.assoc, hG.source_id, hG.target_id]⟩
  comp f g := ⟨pullback.lift g.val f.val (g.property.1.trans f.property.2.symm) ≫ c,
    by simp [Category.assoc, hG.source_comp, hG.target_comp, f.property, g.property]⟩
  id_comp := by
    intro x y f
    apply Subtype.ext
    apply hG.comp_id H f.val
    · simp
    · simp [← Category.assoc, f.property.1]
  comp_id := by
    intro x y f
    apply Subtype.ext
    apply hG.id_comp H f.val
    · simp [← Category.assoc, f.property.2]
    · simp
  assoc := by
    intro x y z w f g k
    apply Subtype.ext
    symm
    apply hG.assoc H
      (pullback.lift k.val g.val (k.property.1.trans g.property.2.symm))
      (pullback.lift g.val f.val (g.property.1.trans f.property.2.symm))
    all_goals simp
  inv f := ⟨f.val ≫ i, by
    simp [Category.assoc, hG.source_inv, hG.target_inv, f.property]⟩
  inv_comp := by
    intro x y f
    apply Subtype.ext
    simpa only [← Category.assoc, f.property.2] using hG.comp_inv H f.val
      (pullback.lift f.val (f.val ≫ i) (by simp [Category.assoc, hG.target_inv]))
      (by simp) (by simp)
  comp_inv := by
    intro x y f
    apply Subtype.ext
    simpa only [← Category.assoc, f.property.1] using hG.inv_comp H f.val
      (pullback.lift (f.val ≫ i) f.val (by simp [Category.assoc, hG.source_inv]))
      (by simp) (by simp)

private theorem canonicalNorm_spec {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) (r : ℕ)
    (h : (Spec.map (CommRingCat.ofHom φ)).IsFiniteLocallyFreeOfDegree r) :
    Algebra.IsLocallyFreeDeterminantNorm φ (Algebra.finiteLocallyFreeDeterminantNorm φ r h) :=
  (Classical.choose_spec (Algebra.finiteLocallyFree_norm_characteristicPolynomial φ r h).2).1.1

private theorem canonicalNormPolynomial_properties {A B : Type u}
    [CommRing A] [CommRing B] [Nontrivial A] (φ : A →+* B) (r : ℕ)
    (h : (Spec.map (CommRingCat.ofHom φ)).IsFiniteLocallyFreeOfDegree r) (b : B) :
    (Algebra.finiteLocallyFreeNormPolynomial φ r h b).Monic ∧
    (Algebra.finiteLocallyFreeNormPolynomial φ r h b).natDegree = r ∧
    (Polynomial.map φ (Algebra.finiteLocallyFreeNormPolynomial φ r h b)).eval b = 0 := by
  let hp := Algebra.finiteLocallyFree_norm_characteristicPolynomial φ r h
  obtain ⟨Npoly, hNpoly, hb⟩ := (Classical.choose_spec hp.2).2
  have heq := hNpoly.2
    (Algebra.finiteLocallyFreeDeterminantNorm (Polynomial.mapRingHom φ) r hp.1)
    (canonicalNorm_spec _ _ _)
  have hb' := hb b
  dsimp only [Algebra.finiteLocallyFreeNormPolynomial]
  rw [heq]
  exact ⟨(hb'.2.2 inferInstance).1, (hb'.2.2 inferInstance).2, hb'.2.1⟩

/-- The canonical source norm polynomial of `X - τ(a)` has invariant coefficients
and annihilates `a`. The source and target are written as spectra of `σ` and `τ`;
full faithfulness of `Spec` identifies these with arbitrary affine source and target
maps. The binder `hP` names the specified canonical polynomial, and `P.coeff j` is
the coefficient denoted by `p_j`, including `p_r = 1`. The invariant ring is the
existing equalizer subring `σ.eqLocus τ`; membership in its polynomial ring is
membership in `Polynomial.lifts` of its inclusion.

Source: Stacks Project, Groupoids, Tag 03BJ, second paragraph of
`lemma-integral-over-invariants`; norm invariance is Tag 03BH, Cayley--Hamilton
is Tag 00DX, and the identity-section law is Tag 0231
(blueprint: lem-a1-affine-groupoid-constant-rank-norm-annihilator).

Proof:
1. Apply `lem-a1-finite-locally-free-norm-characteristic-polynomial` to `σ`, degree
   `r`, and `τ(a)`. Its uniquely characterized local determinant norm is the norm
   glued in `lem-pd-finite-locally-free-norm-charts`. It gives the expansion,
   monicity and degree because `A` is nonzero, and annihilation of `τ(a)` by the
   coefficientwise source image. No global basis is needed.
2. Since coefficientwise extension fixes `X`, the target image of `X - C a` is
   `X - C (τ a)`. Apply `lem-a1-affine-groupoid-polynomial-norm-invariant` to this
   polynomial and the given groupoid. The source and target images of its norm
   agree. Comparing coefficients gives invariance of every `p_j`, and hence a
   polynomial over the equalizer subring. The leading coefficient is one.
3. Apply `τ` to the finite evaluation sum, then replace each `τ(p_j)` by `σ(p_j)`.
   This identifies `τ(P.eval a)` with `(Polynomial.map σ P).eval (τ a)`, which is
   zero by step 1. Ring maps preserve the sums, products and powers in this chain.
4. The target identity law from `def-a1-scheme-groupoid-laws` says that the
   identity-section map `ε = (Spec.preimage e).hom` satisfies `ε.comp τ = id`.
   Apply `ε` to the equation in step 3 to obtain `P.eval a = ε(τ(P.eval a)) = 0`.
   This uses the specified identity section, without an extra flatness assumption. -/
theorem affineGroupoid_constantRank_norm_annihilator
    (A B : CommRingCat.{u}) [Nontrivial A] (σ τ : A →+* B)
    (e : Spec A ⟶ Spec B) (i : Spec B ⟶ Spec B)
    (c : pullback (Spec.map (CommRingCat.ofHom σ))
      (Spec.map (CommRingCat.ofHom τ)) ⟶ Spec B)
    (hG : Scheme.IsGroupoid (Spec.map (CommRingCat.ofHom σ))
      (Spec.map (CommRingCat.ofHom τ)) e i c)
    (r : ℕ) (hr : 1 ≤ r)
    (hσ : (Spec.map (CommRingCat.ofHom σ)).IsFiniteLocallyFreeOfDegree r)
    (hτ : (Spec.map (CommRingCat.ofHom τ)).IsFiniteLocallyFreeOfDegree r)
    (a : A) (P : Polynomial A)
    (hP : P = Algebra.finiteLocallyFreeNormPolynomial σ r hσ (τ a)) :
    P = Polynomial.X ^ r +
      ∑ j ∈ Finset.range r, Polynomial.C (P.coeff j) * Polynomial.X ^ j ∧
    (∀ j : ℕ, j < r → σ (P.coeff j) = τ (P.coeff j)) ∧
    P ∈ Polynomial.lifts (σ.eqLocus τ).subtype ∧
    P.Monic ∧ P.natDegree = r ∧ P.coeff r = 1 ∧
    P = Algebra.finiteLocallyFreeDeterminantNorm (Polynomial.mapRingHom σ) r
      (Algebra.finiteLocallyFree_norm_characteristicPolynomial σ r hσ).1
      (Polynomial.map τ (Polynomial.X - Polynomial.C a)) ∧
    (Polynomial.map σ P).eval (τ a) = 0 ∧
    τ (P.eval a) = ∑ j ∈ Finset.range (r + 1), τ (P.coeff j) * τ a ^ j ∧
    (∑ j ∈ Finset.range (r + 1), τ (P.coeff j) * τ a ^ j) =
      ∑ j ∈ Finset.range (r + 1), σ (P.coeff j) * τ a ^ j ∧
    (∑ j ∈ Finset.range (r + 1), σ (P.coeff j) * τ a ^ j) =
      (Polynomial.map σ P).eval (τ a) ∧
    τ (P.eval a) = 0 ∧
    (Spec.preimage e).hom.comp τ = RingHom.id A ∧
    P.eval a = (Spec.preimage e).hom (τ (P.eval a)) ∧
    (Spec.preimage e).hom (τ (P.eval a)) = 0 ∧
    P.eval a = 0 := by
  classical
  have _hr := hr
  have hp := canonicalNormPolynomial_properties σ r hσ (τ a)
  rw [← hP] at hp
  obtain ⟨hmonic, hdegree, hroot⟩ := hp
  have hdet : P = Algebra.finiteLocallyFreeDeterminantNorm (Polynomial.mapRingHom σ) r
      (Algebra.finiteLocallyFree_norm_characteristicPolynomial σ r hσ).1
      (Polynomial.map τ (Polynomial.X - Polynomial.C a)) := by
    simpa only [Algebra.finiteLocallyFreeNormPolynomial,
      Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C] using hP
  let := hσ
  let := hτ
  have hmaps : Polynomial.map σ P = Polynomial.map τ P := by
    let σ' : A →+* B := (Spec.homEquiv (Spec.map (CommRingCat.ofHom σ))).hom
    let τ' : A →+* B := (Spec.homEquiv (Spec.map (CommRingCat.ofHom τ))).hom
    have hs : σ' = σ := congrArg CommRingCat.Hom.hom (Spec.preimage_map _)
    have ht : τ' = τ := congrArg CommRingCat.Hom.hom (Spec.preimage_map _)
    have hr' : (Spec.map (CommRingCat.ofHom
        (Polynomial.mapRingHom σ'))).IsFiniteLocallyFreeOfDegree r := by
      simpa only [hs] using (Algebra.finiteLocallyFree_norm_characteristicPolynomial σ r hσ).1
    have hdet' : P = Algebra.finiteLocallyFreeDeterminantNorm
        (Polynomial.mapRingHom σ') r hr'
        (Polynomial.map τ' (Polynomial.X - Polynomial.C a)) := by
      simpa only [hs, ht] using hdet
    have hc := affineGroupoid_canonicalNorm_chart_formula
      (Polynomial A) (Polynomial B) (Polynomial.mapRingHom σ') r hr'
      (Polynomial.map τ' (Polynomial.X - Polynomial.C a))
    rw [← hdet'] at hc
    have hi := affine_groupoid_polynomial_norm_invariant A B
      (Spec.map (CommRingCat.ofHom σ)) (Spec.map (CommRingCat.ofHom τ)) e i c
      (fun H ↦ ⟨pointGroupoid _ _ e i c hG H, fun _ _ ↦ Equiv.refl _,
        fun _ ↦ rfl, fun _ _ _ ↦ rfl, fun _ _ _ _ _ ↦ rfl⟩)
      (Polynomial.X - Polynomial.C a) P
      hc
    simpa only [Spec.homEquiv, Equiv.coe_fn_mk, Spec.preimage_map,
      CommRingCat.hom_ofHom] using hi
  have hcoeff (j : ℕ) : σ (P.coeff j) = τ (P.coeff j) := by
    simpa only [Polynomial.coeff_map] using congrArg (fun Q ↦ Q.coeff j) hmaps
  have hlifts : P ∈ Polynomial.lifts (σ.eqLocus τ).subtype := by
    apply (Polynomial.lifts_iff_coeff_lifts P).mpr
    intro j
    exact ⟨⟨P.coeff j, hcoeff j⟩, rfl⟩
  have hsumτ : τ (P.eval a) =
      ∑ j ∈ Finset.range (r + 1), τ (P.coeff j) * τ a ^ j := by
    rw [Polynomial.eval_eq_sum_range, hdegree, map_sum]
    simp only [map_mul, map_pow]
  have hsums : (∑ j ∈ Finset.range (r + 1), τ (P.coeff j) * τ a ^ j) =
      ∑ j ∈ Finset.range (r + 1), σ (P.coeff j) * τ a ^ j := by
    simp only [hcoeff]
  have hsumσ : (∑ j ∈ Finset.range (r + 1), σ (P.coeff j) * τ a ^ j) =
      (Polynomial.map σ P).eval (τ a) := by
    rw [Polynomial.eval_map, Polynomial.eval₂_eq_sum_range, hdegree]
  have hτzero : τ (P.eval a) = 0 := hsumτ.trans (hsums.trans (hsumσ.trans hroot))
  have hε : (Spec.preimage e).hom.comp τ = RingHom.id A := by
    have h := congrArg Spec.preimage hG.target_id
    simpa only [Spec.preimage_comp, Spec.preimage_map, Spec.preimage_id,
      CommRingCat.hom_comp, CommRingCat.hom_id, CommRingCat.hom_ofHom] using
      congrArg CommRingCat.Hom.hom h
  have heval : P.eval a = (Spec.preimage e).hom (τ (P.eval a)) := by
    exact (RingHom.congr_fun hε (P.eval a)).symm
  have hεzero : (Spec.preimage e).hom (τ (P.eval a)) = 0 := by rw [hτzero, map_zero]
  refine ⟨?_, fun j _ ↦ hcoeff j, hlifts, hmonic, hdegree, ?_, hdet, hroot,
    hsumτ, hsums, hsumσ, hτzero, hε, heval, hεzero, heval.trans hεzero⟩
  · simpa only [hdegree] using hmonic.as_sum
  · simpa only [hdegree] using hmonic.coeff_natDegree

end AlgebraicGeometry
