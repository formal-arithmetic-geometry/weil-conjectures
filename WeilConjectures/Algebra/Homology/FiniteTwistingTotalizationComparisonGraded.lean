/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.Algebra.Homology.FiniteTwistingTotalizationComparisonFilteredHom
public import WeilConjectures.CategoryTheory.FiniteFiltrationInductionExtension

/-! The graded comparison and quasi-isomorphism part of finite twisting comparison. -/

@[expose] public section
set_option autoImplicit false
universe u v w
open CategoryTheory CategoryTheory.Limits
namespace CochainComplex
variable {C : Type u} [Category.{v} C] [EssentiallySmall.{w} C]
  {J : GrothendieckTopology C}
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
  {R : Sheaf J CommRingCat.{w}} {a b : ℤ}

/--
The tail-preserving comparison has the prescribed graded maps and quasi-isomorphic graded
pieces.
Source: latest blueprint, sk-i-additivity.proof.md, Filtered operations (routine),
lines 12-24 (steps 4-5 of the proof of lem-trf-finite-filtered-totalization-comparison).
Proof:  For an interior weight, cancel the cokernel epi `complexQuotientπ`, use the two
`gradedProjection` identities and the chosen `exists_gradedMap_steps` factorisation, and
transport the resulting map through the two graded isomorphisms.  Outside `[a,b]`, use
the `outside` zero-complex witnesses.  These are independent graded and vanishing cases.
(blueprint: lem-trf-finite-filtered-totalization-comparison-graded)
-/
theorem exists_finiteTwistingTotalization_comparison_graded
    (D D' : FiniteTwistingFamily R a b)
    (M : FiniteTwistingTotalization D) (M' : FiniteTwistingTotalization D')
    (f : ∀ p : ↥(Finset.Icc a b), D.G p ⟶ D'.G p)
    (hf : ∀ p : ↥(Finset.Icc a b), QuasiIso (f p))
    (ψ : FilteredObject.Hom ⟨M.P, M.F⟩ ⟨M'.P, M'.F⟩)
    (hcoord : ∀ (p : ↥(Finset.Icc a b)) (n : ℤ),
      biproduct.ι (fun q : ↥(Finset.Icc a b) ↦ (D.G q).X n) p ≫
          (M.coordinates n).inv ≫ ψ.hom.f n =
        (f p).f n ≫ biproduct.ι
          (fun q : ↥(Finset.Icc a b) ↦ (D'.G q).X n) p ≫
          (M'.coordinates n).inv) :
    (∀ p : ↥(Finset.Icc a b),
      (M.gradedIso p).hom ≫ f p =
        FilteredObject.gradedMapSteps ψ p.val ≫ (M'.gradedIso p).hom) ∧
      (∀ p : ℤ, QuasiIso (FilteredObject.gradedMapSteps ψ p)) := by
  classical
  -- in every degree, `ψ` followed by the target projection to weight `p` is the source
  -- projection followed by `f p`
  have key : ∀ (p : ↥(Finset.Icc a b)) (n : ℤ),
      ψ.hom.f n ≫ (M'.coordinates n).hom ≫
          biproduct.π (fun q : ↥(Finset.Icc a b) ↦ (D'.G q).X n) p =
        (M.coordinates n).hom ≫
          biproduct.π (fun q : ↥(Finset.Icc a b) ↦ (D.G q).X n) p ≫ (f p).f n := by
    intro p n
    apply (cancel_epi (M.coordinates n).inv).1
    simp only [Iso.inv_hom_id_assoc]
    apply biproduct.hom_ext'
    intro q
    rw [reassoc_of% (hcoord q n)]
    simp only [Iso.inv_hom_id_assoc]
    by_cases hqp : q = p
    · subst hqp
      simp only [biproduct.ι_π_self_assoc, biproduct.ι_π_self, Category.comp_id]
    · simp only [biproduct.ι_π_ne_assoc _ hqp, biproduct.ι_π_ne _ hqp, comp_zero,
        zero_comp]
  have hgr : ∀ p : ↥(Finset.Icc a b),
      (M.gradedIso p).hom ≫ f p =
        FilteredObject.gradedMapSteps ψ p.val ≫ (M'.gradedIso p).hom := by
    intro p
    have : Epi (M.F.complexQuotientπ p.val (p.val + 1) (Int.le_add_one le_rfl)) := by
      unfold DecreasingFiltration.complexQuotientπ
      infer_instance
    apply (cancel_epi (M.F.complexQuotientπ p.val (p.val + 1)
      (Int.le_add_one le_rfl))).1
    have hstep := Classical.choose_spec
      (FilteredObject.exists_gradedMap_steps ⟨M.P, M.F⟩ ⟨M'.P, M'.F⟩ ψ p.val)
    have hres := Classical.choose_spec (ψ.preserves p.val)
    apply HomologicalComplex.hom_ext
    intro n
    have h1 : (M.F.complexQuotientπ p.val (p.val + 1) (Int.le_add_one le_rfl)).f n ≫
        (FilteredObject.gradedMapSteps ψ p.val).f n =
          (FilteredObject.restrictionSteps ψ p.val).f n ≫
            (M'.F.complexQuotientπ p.val (p.val + 1) (Int.le_add_one le_rfl)).f n := by
      have h := congrArg (fun k ↦ k.f n) hstep
      simp only [HomologicalComplex.comp_f] at h
      exact h
    have h2 : (FilteredObject.restrictionSteps ψ p.val).f n ≫ (M'.F.step p.val).arrow.f n =
        (M.F.step p.val).arrow.f n ≫ ψ.hom.f n := by
      have h := congrArg (fun k ↦ k.f n) hres
      simp only [HomologicalComplex.comp_f] at h
      exact h
    simp only [HomologicalComplex.comp_f]
    rw [reassoc_of% (M.gradedProjection p n), reassoc_of% h1,
      M'.gradedProjection p n, reassoc_of% h2, key p n]
  refine ⟨hgr, fun p ↦ ?_⟩
  by_cases hp : p ∈ Finset.Icc a b
  · have := hf ⟨p, hp⟩
    have e : FilteredObject.gradedMapSteps ψ p =
        (M.gradedIso ⟨p, hp⟩).hom ≫ f ⟨p, hp⟩ ≫ (M'.gradedIso ⟨p, hp⟩).inv := by
      rw [reassoc_of% (hgr ⟨p, hp⟩), Iso.hom_inv_id, Category.comp_id]
    rw [e]
    infer_instance
  · have hout : p < a ∨ b < p := by
      rw [Finset.mem_Icc] at hp
      omega
    have hA := M.outside p hout
    have hB := M'.outside p hout
    have e : FilteredObject.gradedMapSteps ψ p = (hA.iso hB).hom := hA.eq_of_src _ _
    rw [e]
    infer_instance

end CochainComplex
