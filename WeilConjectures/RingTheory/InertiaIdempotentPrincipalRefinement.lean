/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.RingTheory.Invariant.Basic
public import Mathlib.RingTheory.Ideal.Pointwise
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import WeilConjectures.Mathlib.RingTheory.TotallySplit
public import Mathlib.RingTheory.Localization.Away.Basic
import WeilConjectures.Mathlib.RingTheory.Etale.FiniteSplitting

import Mathlib.GroupTheory.Coset.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic.Ring

/-! # Principal refinement of an isolated inertia component
Source: Stacks Project, Tag 0BST, equivariant refinement and removal of empty fibre factors.
(blueprint: lem-dl-a1-inertia-idempotent-principal-refinement). -/

@[expose] public section
set_option autoImplicit false
universe u v
open scoped TensorProduct

private theorem boolean_orbit
    (S : Type u) [CommRing S] (G : Type v) [Group G] [Fintype G]
    [MulSemiringAction G S] (H : Subgroup G) [DecidablePred (· ∈ H)]
    (e0 : S) (he0 : IsIdempotentElem e0) :
    ∃ (e : S) (n : ℕ) (r : Fin n → G),
      IsIdempotentElem e ∧ (∀ h : H, h.val • e = e) ∧
      (∀ g : G, ∃ (i : Fin n) (h : H), g = r i * h.val) ∧
      OrthogonalIdempotents (fun i ↦ r i • e) ∧
      (∀ g : G, (if g ∈ H then g • e0 else 1 - g • e0) ∣ e) ∧
      e = ∏ g : G, if g ∈ H then g • e0 else 1 - g • e0 := by
  classical
  let F : G → S := fun g ↦ if g ∈ H then g • e0 else 1 - g • e0
  let e : S := ∏ g : G, F g
  have hF (g : G) : IsIdempotentElem (F g) := by
    dsimp [F]
    split_ifs
    · exact he0.map (MulSemiringAction.toRingHom G S g)
    · exact (he0.map (MulSemiringAction.toRingHom G S g)).one_sub
  have he : IsIdempotentElem e := by
    change (∏ g : G, F g) * (∏ g : G, F g) = ∏ g : G, F g
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun g _ ↦ (hF g).eq
  have hdvd (g : G) : F g ∣ e := Finset.dvd_prod_of_mem F (Finset.mem_univ g)
  have hH (h : H) : h.val • e = e := by
    have hf (g : G) : h.val • F g = F (h.val * g) := by
      have hm : h.val * g ∈ H ↔ g ∈ H := H.mul_mem_cancel_left h.2
      simp only [F, hm]
      split_ifs <;> simp [smul_sub, mul_smul]
    calc
      h.val • e = ∏ g : G, h.val • F g :=
        map_prod (MulSemiringAction.toRingHom G S h.val) _ _
      _ = ∏ g : G, F (h.val * g) := Finset.prod_congr rfl fun g _ ↦ hf g
      _ = e := Fintype.prod_equiv (Equiv.mulLeft h.val) _ F (fun _ ↦ rfl)
  let Q := G ⧸ H
  let : Fintype Q := Fintype.ofFinite Q
  let k := Fintype.equivFin Q
  let r : Fin (Fintype.card Q) → G := fun i ↦ (k.symm i).out
  have hrep (g : G) : ∃ (i : Fin (Fintype.card Q)) (h : H), g = r i * h.val := by
    let i := k (QuotientGroup.mk g)
    have hm : (r i)⁻¹ * g ∈ H := QuotientGroup.eq.mp (by simp [r, i])
    exact ⟨i, ⟨(r i)⁻¹ * g, hm⟩, (mul_inv_cancel_left (r i) g).symm⟩
  have hne (i j : Fin (Fintype.card Q)) (hij : i ≠ j) : (r j)⁻¹ * r i ∉ H := by
    intro hm
    apply hij
    have hh : (QuotientGroup.mk (r j) : Q) = QuotientGroup.mk (r i) :=
      QuotientGroup.eq.mpr hm
    simpa only [r, QuotientGroup.out_eq', Equiv.symm_apply_eq, Equiv.apply_symm_apply] using
      congrArg k hh.symm
  have hortho : OrthogonalIdempotents (fun i ↦ r i • e) := by
    refine ⟨fun i ↦ he.map (MulSemiringAction.toRingHom G S (r i)), ?_⟩
    intro i j hij
    have hi : r i • e0 ∣ r i • e := by
      have hh : e0 ∣ e := by simpa [F] using hdvd 1
      exact map_dvd (MulSemiringAction.toRingHom G S (r i)) hh
    have hj : 1 - r i • e0 ∣ r j • e := by
      have hh := map_dvd (MulSemiringAction.toRingHom G S (r j))
        (hdvd ((r j)⁻¹ * r i))
      simpa [F, hne i j hij, smul_sub, ← mul_smul] using hh
    obtain ⟨x, hx⟩ := hi
    obtain ⟨y, hy⟩ := hj
    conv_lhs => rw [hx, hy]
    calc
      (r i • e0 * x) * ((1 - r i • e0) * y) =
          ((r i • e0) * (1 - r i • e0)) * (x * y) := by ring
      _ = 0 := by
        have hh : IsIdempotentElem (r i • e0) :=
          he0.map (MulSemiringAction.toRingHom G S (r i))
        rw [hh.mul_one_sub_self, zero_mul]
  exact ⟨e, _, r, he, hH, hrep, hortho, hdvd, rfl⟩

namespace Ideal

/-- An idempotent isolating one geometric point can, after a principal localization of the
base, be replaced by an inertia-fixed component whose distinct G-translates partition one.
Source: Stacks Project, Tag 0BST, equivariant refinement paragraph and final coset calculation.
(blueprint: lem-dl-a1-inertia-idempotent-principal-refinement).

Proof:
1. Let I be inertia at the kernel of eta. The point eta evaluates g(e0) to one exactly
when eta composed with g equals eta, by the isolating property of e0. This is equivalent
to g belonging to I.
2. Set e equal to the product, over g in G, of g(e0) when g belongs to I and of
1 - g(e0) otherwise. Every factor is idempotent and evaluates to one at eta. Translation
by I permutes the factors, so e is I-fixed. For distinct left cosets represented by r_i
and r_j, the translate r_i(e) contains the factor r_i(e0), whereas r_j(e) contains its
complement, since r_j inverse times r_i is outside I. Thus their product is zero.
3. Every point of the tensor algebra is induced by a point s of R. By transitivity write
s as eta composed with k. Choose a coset representative r_i with k inverse = r_i h,
h in I. The value of r_i(e) at s is the value of h inverse applied to e at eta, hence
one. Orthogonality forces all other values to zero. Therefore the complementary
idempotent 1 - sum_i r_i(e) vanishes at every point over alpha.
4. The finite-algebra shrinking lemma supplies a base element a, nonzero under alpha,
annihilating that complementary idempotent. Invert a and extend alpha uniquely. Its
image is now a unit, so the complement is zero. Transport the idempotents and all
identities along the tensor base-change map. This single localization gives the claimed
complete orthogonal orbit and preserves the selected point. -/
theorem exists_inertia_idempotent_principal_refinement
    (C R : Type u) [CommRing C] [CommRing R] [Algebra C R] [Module.Finite C R]
    (G : Type v) [Group G] [Finite G] [MulSemiringAction G R] [SMulCommClass G C R]
    (q : Ideal R) [q.IsPrime] (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
    (η : R →+* Ω) (hη : RingHom.ker η = q)
    (htrans : ∀ s : RingHom.PointsOver (η.comp (algebraMap C R)) R,
      ∃ g : G, ∀ x : R, s x = η (g • x))
    (A : Type u) [CommRing A] [Algebra C A]
    (α : A →+* Ω) (hα : α.comp (algebraMap C A) = η.comp (algebraMap C R))
    (e0 : A ⊗[C] R) (he0 : IsIdempotentElem e0)
    (ht : (RingHom.PointsOver.tensor hα
      (⟨η, rfl⟩ : RingHom.PointsOver (η.comp (algebraMap C R)) R)) e0 = 1)
    (huniq : ∀ s : RingHom.PointsOver (η.comp (algebraMap C R)) R,
      s.tensor hα e0 = 1 → s = ⟨η, rfl⟩) :
    ∃ (a : A) (_ : α a ≠ 0) (α' : Localization.Away a →+* Ω)
      (hα' : α'.comp (algebraMap C (Localization.Away a)) = η.comp (algebraMap C R)),
      α'.comp (algebraMap A (Localization.Away a)) = α ∧
      ∃ (e : Localization.Away a ⊗[C] R) (n : ℕ) (r : Fin n → G),
        IsIdempotentElem e ∧
        (RingHom.PointsOver.tensor hα'
          (⟨η, rfl⟩ : RingHom.PointsOver (η.comp (algebraMap C R)) R)) e = 1 ∧
        (∀ h : q.inertia G,
          AlgHom.baseChangeFamily (Localization.Away a)
            (MulSemiringAction.toAlgHom C R) h.val e = e) ∧
        (∀ g : G, ∃ (i : Fin n) (h : q.inertia G), g = r i * h.val) ∧
        CompleteOrthogonalIdempotents (fun i ↦
          AlgHom.baseChangeFamily (Localization.Away a)
            (MulSemiringAction.toAlgHom C R) (r i) e) := by
  classical
  let : Fintype G := Fintype.ofFinite G
  let S := A ⊗[C] R
  let ρ : G →* S ≃ₐ[A] S :=
    { toFun g := Algebra.TensorProduct.congr (AlgEquiv.refl : A ≃ₐ[A] A)
        (MulSemiringAction.toAlgAut G C R g)
      map_one' := by
        apply AlgEquiv.ext
        intro z
        induction z using TensorProduct.induction_on with
        | zero => simp
        | tmul a x => simp
        | add x y hx hy => simp only [map_add, hx, hy]
      map_mul' := by
        intro g h
        apply AlgEquiv.ext
        intro z
        induction z using TensorProduct.induction_on with
        | zero => simp
        | tmul a x => simp [mul_smul]
        | add x y hx hy => simp only [map_add, hx, hy] }
  let : MulSemiringAction G S := MulSemiringAction.compHom S ρ
  let t : RingHom.PointsOver (η.comp (algebraMap C R)) R := ⟨η, rfl⟩
  let τ := t.tensor hα
  let sg (g : G) : RingHom.PointsOver (η.comp (algebraMap C R)) R :=
    ⟨η.comp (MulSemiringAction.toRingHom G R g), by
      ext c
      simp only [RingHom.comp_apply, MulSemiringAction.toRingHom_apply, smul_algebraMap]⟩
  have hτ (g : G) (z : S) : τ (g • z) = (sg g).tensor hα z := by
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a x =>
      change t.tensor hα (a ⊗ₜ (g • x)) = (sg g).tensor hα (a ⊗ₜ x)
      simp only [RingHom.PointsOver.tensor_tmul]
      rfl
    | add x y hx hy => simp only [smul_add, map_add, hx, hy]
  have hpoint (g : G) : sg g = t ↔ g ∈ q.inertia G := by
    constructor
    · intro hg x
      have hh : η (g • x) = η x := congrArg (fun k ↦ k x) hg
      have hh' : g • x - x ∈ RingHom.ker η := by
        change η (g • x - x) = 0
        rw [map_sub, hh, sub_self]
      exact hη ▸ hh'
    · intro hg
      apply Subtype.ext
      ext x
      change η (g • x) = η x
      have hh : η (g • x - x) = 0 := by
        exact (show g • x - x ∈ RingHom.ker η from hη.symm ▸ hg x)
      exact sub_eq_zero.mp (by simpa only [map_sub] using hh)
  have hval (g : G) : τ (g • e0) = 1 ↔ g ∈ q.inertia G := by
    rw [hτ]
    constructor
    · intro hh
      exact (hpoint g).mp (huniq (sg g) hh)
    · intro hg
      rw [(hpoint g).mpr hg]
      exact ht
  obtain ⟨e, n, r, he, hH, hr, ho, hdvd, heprod⟩ :=
    boolean_orbit S G (q.inertia G) e0 he0
  have hte : τ e = 1 := by
    rw [heprod, map_prod]
    apply Finset.prod_eq_one
    intro g _
    split_ifs with hg
    · exact (hval g).mpr hg
    · rw [map_sub, map_one]
      have hh := (IsIdempotentElem.iff_eq_zero_or_one.mp
        (he0.map (MulSemiringAction.toRingHom G S g) |>.map τ.1)).resolve_right
        (fun hh ↦ hg ((hval g).mp hh))
      have hz : τ (g • e0) = 0 := hh
      exact (congrArg (fun z : Ω ↦ 1 - z) hz).trans (sub_zero 1)
  have hsum : IsIdempotentElem (1 - ∑ i, r i • e) := ho.isIdempotentElem_sum.one_sub
  have hzero : ∀ y : RingHom.PointsOver α S, y (1 - ∑ i, r i • e) = 0 := by
    intro y
    obtain ⟨s, rfl⟩ := (RingHom.PointsOver.tensorEquiv hα).symm.surjective y
    rw [RingHom.PointsOver.tensorEquiv_symm_apply]
    obtain ⟨k, hk⟩ := htrans s
    have hs (z : S) : s.tensor hα z = τ (k • z) := by
      induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul a x =>
        change s.tensor hα (a ⊗ₜ x) = t.tensor hα (a ⊗ₜ (k • x))
        simp only [RingHom.PointsOver.tensor_tmul]
        exact congrArg (fun z : Ω ↦ α a * z) (hk x)
      | add x y hx hy => simp only [smul_add, map_add, hx, hy]
    obtain ⟨i, h, hi⟩ := hr k⁻¹
    have hki : k * r i = (h.val)⁻¹ := by
      apply mul_right_cancel (b := h.val)
      rw [mul_assoc, ← hi, mul_inv_cancel, inv_mul_cancel]
    have hione : s.tensor hα (r i • e) = 1 := by
      rw [hs, ← mul_smul, hki]
      have hh : (h.val)⁻¹ • e = e := hH h⁻¹
      exact (congrArg τ.1 hh).trans hte
    have hothers (j : Fin n) (hji : j ≠ i) : s.tensor hα (r j • e) = 0 := by
      have hh := congrArg (fun z : S ↦ s.tensor hα z) (ho.ortho hji)
      simpa only [map_mul, hione, mul_one, map_zero] using hh
    rw [map_sub, map_one, map_sum]
    rw [Finset.sum_eq_single i (fun j _ hji ↦ hothers j hji) (by simp), hione, sub_self]
  obtain ⟨a, ha, hae⟩ :=
    Algebra.exists_algebraMap_mul_eq_zero_of_forall_apply_eq_zero α _ hsum hzero
  let L := Localization.Away a
  let α' : L →+* Ω := IsLocalization.Away.lift a (g := α) (isUnit_iff_ne_zero.mpr ha)
  have hαA : α'.comp (algebraMap A L) = α := IsLocalization.lift_comp _
  have hα' : α'.comp (algebraMap C L) = η.comp (algebraMap C R) :=
    RingHom.PointsOver.comp_algebraMap_of_tower hα hαA
  let f : S →ₐ[C] L ⊗[C] R :=
    Algebra.TensorProduct.map (IsScalarTower.toAlgHom C A L) (AlgHom.id C R)
  have hf (g : G) (z : S) :
      f (g • z) = AlgHom.baseChangeFamily L (MulSemiringAction.toAlgHom C R) g (f z) := by
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a x => rfl
    | add x y hx hy => simp only [smul_add, map_add, hx, hy]
  refine ⟨a, ha, α', hα', hαA, f e, n, r, he.map f, ?_, ?_, hr, ?_⟩
  · exact (RingHom.PointsOver.tensor_map hα hαA t e).trans hte
  · intro h
    exact (hf h.val e).symm.trans (congrArg f (hH h))
  · have ho' : OrthogonalIdempotents (fun i ↦
        AlgHom.baseChangeFamily L (MulSemiringAction.toAlgHom C R) (r i) (f e)) := by
      have hh : (fun i ↦ AlgHom.baseChangeFamily L
          (MulSemiringAction.toAlgHom C R) (r i) (f e)) = fun i ↦ f (r i • e) :=
        funext fun i ↦ (hf (r i) e).symm
      rw [hh]
      exact ho.map f.toRingHom
    refine ⟨ho', ?_⟩
    have hu : IsUnit (algebraMap L (L ⊗[C] R) (algebraMap A L a)) :=
      (IsLocalization.Away.algebraMap_isUnit a).map _
    have h0 : algebraMap L (L ⊗[C] R) (algebraMap A L a) *
        (1 - ∑ i, f (r i • e)) = 0 := by
      rw [← map_sum, ← map_one f, ← map_sub, ← IsScalarTower.algebraMap_apply A L _]
      have hh : algebraMap A (L ⊗[C] R) a = f (algebraMap A S a) := by
        change (algebraMap A L a) ⊗ₜ (1 : R) = f (a ⊗ₜ (1 : R))
        rfl
      rw [hh, ← map_mul, hae, map_zero]
    have hh := hu.mul_right_eq_zero.mp h0
    simpa only [hf] using (sub_eq_zero.mp hh).symm

end Ideal
