/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Regular.RegularSequence
import WeilConjectures.FieldTheory.FinitelyGeneratedFieldCompleteIntersectionModel
import WeilConjectures.RingTheory.RegularSequenceQuotientLocalizationPresentation
import Mathlib.FieldTheory.FinTrdeg
import Mathlib.Tactic.FieldSimp

/-!
# Complete-intersection subalgebras in field extensions

Source: Stacks Project, Algebra, Lemma 07BV.
-/

@[expose] public section

universe u v

namespace FieldTheory

private theorem exists_common_denominator
    {A : Type u} {L : Type v} [CommRing A] [IsDomain A] [Field L]
    (ι : A →+* L) (hι : Function.Injective ι) (E : Finset L)
    (hfrac : ∀ z : L, ∃ a s : A, s ≠ 0 ∧ z = ι a * (ι s)⁻¹) :
    ∃ g : A, g ≠ 0 ∧ ∀ z ∈ E, ∃ a : A, z = ι a * (ι g)⁻¹ := by
  classical
  induction E using Finset.induction_on with
  | empty =>
    exact ⟨1, one_ne_zero, by simp⟩
  | @insert z E hz ih =>
    obtain ⟨a, s, hs, ha⟩ := hfrac z
    obtain ⟨g, hg, hE⟩ := ih
    have hs' : ι s ≠ 0 := fun h ↦ hs (hι (h.trans (map_zero ι).symm))
    have hg' : ι g ≠ 0 := fun h ↦ hg (hι (h.trans (map_zero ι).symm))
    refine ⟨s * g, mul_ne_zero hs hg, ?_⟩
    intro y hy
    rcases Finset.mem_insert.mp hy with rfl | hy
    · refine ⟨a * g, ?_⟩
      rw [ha, map_mul, map_mul]
      field_simp
    · obtain ⟨b, hb⟩ := hE y hy
      refine ⟨b * s, ?_⟩
      rw [hb, map_mul, map_mul]
      field_simp

/-- Every finite subset `E` of a field extension `K/k` is contained in the image of an injective
`k`-algebra map from a complete intersection `k[X₁, …, Xₙ]/(f)`, with `f` a regular sequence.
This is the first assertion of Stacks, Tag 07BV. -/
theorem exists_completeIntersection_subalgebra
    (k : Type u) (K : Type v) [Field k] [Field K] [Algebra k K]
    (E : Finset K) :
    ∃ (n c : ℕ) (f : List (MvPolynomial (Fin n) k)),
      f.length = c ∧
      RingTheory.Sequence.IsRegular (MvPolynomial (Fin n) k) f ∧
      ∃ (ι : ((MvPolynomial (Fin n) k ⧸ Ideal.ofList f) →ₐ[k] K)),
        Function.Injective ι ∧
          ∀ x : K, x ∈ E → ∃ y : (MvPolynomial (Fin n) k ⧸ Ideal.ofList f), ι y = x := by
  classical
  let L := IntermediateField.adjoin k (E : Set K)
  have hL : L.FG := IntermediateField.fg_adjoin_finset E
  let : Algebra.EssFiniteType k L := IntermediateField.essFiniteType_iff.mpr hL
  obtain ⟨t, ht⟩ := IntermediateField.fg_top k L
  let b : Fin (Fintype.card t) → L := (↑) ∘ (Fintype.equivFin t).symm
  have hb : IntermediateField.adjoin k (Set.range b) = ⊤ := by
    simpa [b, Set.range_comp] using ht
  obtain ⟨s, hs⟩ := exists_finset_isTranscendenceBasis k L
  let x : Fin (Fintype.card s) → L := (↑) ∘ (Fintype.equivFin s).symm
  have hx : IsTranscendenceBasis k x := hs.comp_equiv (Fintype.equivFin s).symm
  obtain ⟨n, c, f, _, _, hlen, hf, ι, hι, hfrac, hdom, _⟩ :=
    exists_completeIntersection_fractionField_model k L ⟨_, b, hb⟩ _ x hx
  let A := MvPolynomial (Fin n) k ⧸ Ideal.ofList f
  let : IsDomain A := hdom
  let E' : Finset L := E.attach.image fun z ↦
    ⟨z.1, IntermediateField.subset_adjoin k (E : Set K) z.2⟩
  obtain ⟨g, hg, hE⟩ := exists_common_denominator ι.toRingHom hι E' hfrac
  obtain ⟨q, hq, hqreg, ⟨e⟩⟩ :=
    RingTheory.Sequence.exists_localizationAway_presentation k n f hf g hg
  have hιg : ι g ≠ 0 := fun h ↦ hg (hι (h.trans (map_zero ι).symm))
  let j : Localization.Away g →ₐ[k] L :=
    IsLocalization.Away.liftAlgHom g (isUnit_iff_ne_zero.mpr hιg)
  have hjmap (a : A) : j (algebraMap A (Localization.Away g) a) = ι a :=
    IsLocalization.Away.lift_eq g (isUnit_iff_ne_zero.mpr hιg) a
  have hj : Function.Injective j := by
    apply (IsLocalization.injective_iff_map_algebraMap_eq (Submonoid.powers g)
      j.toRingHom).mpr
    intro a b
    constructor
    · exact congrArg j
    · intro h
      change j (algebraMap A (Localization.Away g) a) =
        j (algebraMap A (Localization.Away g) b) at h
      rw [hjmap, hjmap] at h
      exact congrArg (algebraMap A (Localization.Away g)) (hι h)
  refine ⟨n + 1, c + 1, q, hq.trans (congrArg (· + 1) hlen), hqreg,
    L.val.comp (j.comp e.toAlgHom), L.val.injective.comp (hj.comp e.injective), ?_⟩
  intro z hz
  let z' : L := ⟨z, IntermediateField.subset_adjoin k (E : Set K) hz⟩
  have hz' : z' ∈ E' := Finset.mem_image.mpr ⟨⟨z, hz⟩, by simp, rfl⟩
  obtain ⟨a, ha⟩ := hE z' hz'
  change z' = ι a * (ι g)⁻¹ at ha
  refine ⟨e.symm (algebraMap A (Localization.Away g) a *
    IsLocalization.Away.invSelf g), ?_⟩
  have hinv : j (IsLocalization.Away.invSelf g) = (ι g)⁻¹ := by
    have H := congrArg j (IsLocalization.Away.mul_invSelf
      (S := Localization.Away g) g)
    rw [map_mul, map_one, hjmap] at H
    apply mul_left_cancel₀ hιg
    rw [H, mul_inv_cancel₀ hιg]
  change ↑(j (e (e.symm _))) = z
  rw [e.apply_symm_apply, map_mul, hinv]
  rw [hjmap, ← ha]

end FieldTheory
