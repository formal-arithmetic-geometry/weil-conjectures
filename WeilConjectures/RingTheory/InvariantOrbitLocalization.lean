/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.RingTheory.Invariant.Basic
public import Mathlib.RingTheory.Idempotents
public import Mathlib.RingTheory.Localization.Away.Basic
public import WeilConjectures.Mathlib.RingTheory.TotallySplit
import Mathlib.Data.Fintype.Card

/-!
# Localization of invariants at a transitive component

Source: Stacks Project, Tag 0BST, final invariant-ring calculation
(blueprint: lem-dl-a1-invariant-orbit-localization).
-/

@[expose] public section
set_option autoImplicit false
universe u v
open scoped TensorProduct

namespace AlgHom

private theorem orbit_sum_fixed
    (S : Type u) [CommRing S] [Nontrivial S]
    (G : Type v) [Group G] [MulSemiringAction G S]
    (H : Subgroup G) (e : S) (hH : ∀ h : H, h • e = e)
    (n : ℕ) (r : Fin n → G)
    (hr : ∀ g : G, ∃ (i : Fin n) (h : H), g = r i * h.val)
    (hc : CompleteOrthogonalIdempotents (fun i ↦ r i • e))
    (x : S) (hx : ∀ h : H, h • x = x) :
    ∀ g : G, g • (∑ i, r i • (e * x)) = ∑ i, r i • (e * x) := by
  classical
  choose idx h hh using hr
  have hp (g : G) : g • e = r (idx g) • e := by
    calc
      g • e = (r (idx g) * (h g).val) • e := congrArg (fun k : G ↦ k • e) (hh g)
      _ = r (idx g) • e := by
        rw [mul_smul]
        exact congrArg (fun z : S ↦ r (idx g) • z) (hH (h g))
  have he0 : e ≠ 0 := by
    intro he0
    have h10 : (1 : S) = 0 := by
      calc
        1 = ∑ i, r i • e := hc.complete.symm
        _ = 0 := by simp [he0]
    exact one_ne_zero h10
  have hne (i : Fin n) : r i • e ≠ 0 := by
    intro hz
    apply he0
    apply MulAction.injective (r i)
    simpa only [smul_zero] using hz
  have hinj : Function.Injective (fun i : Fin n ↦ r i • e) := by
    intro i j hij
    by_contra hneij
    apply hne i
    calc
      r i • e = (r i • e) * (r i • e) := (hc.idem i).eq.symm
      _ = (r i • e) * (r j • e) := congrArg (fun z : S ↦ (r i • e) * z) hij
      _ = 0 := hc.ortho hneij
  intro g
  let f : Fin n → Fin n := fun i ↦ idx (g * r i)
  have hf : Function.Injective f := by
    intro i j hij
    apply hinj
    apply MulAction.injective g
    calc
      g • (r i • e) = r (f i) • e := (mul_smul g (r i) e).symm.trans (hp _)
      _ = r (f j) • e := by rw [hij]
      _ = g • (r j • e) := ((mul_smul g (r j) e).symm.trans (hp _)).symm
  have hbij : Function.Bijective f := ⟨hf, _root_.Finite.surjective_of_injective hf⟩
  change (MulSemiringAction.toRingHom G S g) (∑ i, r i • (e * x)) = _
  rw [map_sum]
  apply Fintype.sum_bijective f hbij
  intro i
  change g • (r i • (e * x)) = r (idx (g * r i)) • (e * x)
  calc
    g • (r i • (e * x)) = (g * r i) • (e * x) := (mul_smul _ _ _).symm
    _ = (r (idx (g * r i)) * (h (g * r i)).val) • (e * x) :=
      congrArg (fun k : G ↦ k • (e * x)) (hh (g * r i))
    _ = r (idx (g * r i)) • (e * x) := by
      rw [mul_smul, smul_mul']
      exact congrArg (fun z : S ↦ r (idx (g * r i)) • z)
        (congrArg₂ (fun a b : S ↦ a * b) (hH (h (g * r i))) (hx (h (g * r i))))

private theorem orbit_sum_projection
    (S : Type u) [CommRing S]
    (G : Type v) [Group G] [MulSemiringAction G S]
    (H : Subgroup G) (e : S) (hH : ∀ h : H, h • e = e)
    (n : ℕ) (r : Fin n → G)
    (hr : ∀ g : G, ∃ (i : Fin n) (h : H), g = r i * h.val)
    (hc : CompleteOrthogonalIdempotents (fun i ↦ r i • e))
    (x : S) (hx : ∀ h : H, h • x = x) :
    e * (∑ i, r i • (e * x)) = e * x := by
  classical
  obtain ⟨i0, h0, hh0⟩ := hr 1
  have hr0 : r i0 = h0.val⁻¹ := by
    apply mul_right_cancel (b := h0.val)
    simpa using hh0.symm
  have he0 : r i0 • e = e := by
    rw [hr0]
    exact hH h0⁻¹
  have hx0 : r i0 • x = x := by
    rw [hr0]
    exact hx h0⁻¹
  rw [Finset.mul_sum]
  rw [Finset.sum_eq_single i0]
  · rw [smul_mul', he0, hx0, ← mul_assoc]
    have h := hc.idem i0
    rw [he0] at h
    rw [h.eq]
  · intro i _ hi
    have hh : e * (r i • e) = 0 := by
      calc
        e * (r i • e) = (r i0 • e) * (r i • e) := congrArg (fun z : S ↦ z * (r i • e)) he0.symm
        _ = 0 := hc.ortho hi.symm
    rw [smul_mul', ← mul_assoc, hh, zero_mul]
  · simp

private theorem orbit_localization_bijective
    (A S : Type u) [CommRing A] [CommRing S] [Algebra A S]
    (G : Type v) [Group G] [MulSemiringAction G S]
    [SMulCommClass G A S] [Algebra.IsInvariant A S G]
    (hinj : Function.Injective (algebraMap A S))
    (H : Subgroup G) (e : S) (he : IsIdempotentElem e)
    (hH : ∀ h : H, h • e = e) (n : ℕ) (r : Fin n → G)
    (hr : ∀ g : G, ∃ (i : Fin n) (h : H), g = r i * h.val)
    (hc : CompleteOrthogonalIdempotents (fun i ↦ r i • e)) :
    let F := FixedPoints.subalgebra A S H
    let eF : F := ⟨e, hH⟩
    Function.Bijective (algebraMap A (Localization.Away eF)) := by
  classical
  intro F eF
  let L := Localization.Away eF
  have heF : IsIdempotentElem eF := Subtype.ext he.eq
  have heq (x y : F) :
      algebraMap F L x = algebraMap F L y ↔ eF * x = eF * y := by
    constructor
    · intro h
      obtain ⟨k, hk⟩ := IsLocalization.Away.exists_of_eq eF h
      have hk' := congrArg (fun z : F ↦ eF * z) hk
      simpa only [← mul_assoc, ← pow_succ', heF.pow_succ_eq] using hk'
    · intro h
      exact (IsLocalization.eq_iff_exists (Submonoid.powers eF) L).mpr
        ⟨⟨eF, Submonoid.mem_powers _⟩, h⟩
  constructor
  · intro a b hab
    have hF := (heq (algebraMap A F a) (algebraMap A F b)).mp
      (by
        change algebraMap A L a = algebraMap A L b at hab
        simpa only [IsScalarTower.algebraMap_apply A F L] using hab)
    have hS : e * algebraMap A S a = e * algebraMap A S b :=
      congrArg Subtype.val hF
    apply hinj
    have ht (i : Fin n) :
        (r i • e) * algebraMap A S a = (r i • e) * algebraMap A S b := by
      simpa only [smul_mul', smul_algebraMap] using congrArg (fun z : S ↦ r i • z) hS
    have hsum := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl
      (fun i _ ↦ ht i)
    simpa only [← Finset.sum_mul, hc.complete, one_mul] using hsum
  · intro z
    obtain ⟨x, hx⟩ :=
      IsLocalization.Away.algebraMap_surjective_of_isIdempotentElem eF heF z
    rcases subsingleton_or_nontrivial S with hS | hS
    · have : Subsingleton A := hinj.subsingleton
      have : Subsingleton L := (algebraMap A L).codomain_trivial
      exact ⟨0, Subsingleton.elim _ _⟩
    · have hfix := orbit_sum_fixed S G H e hH n r hr hc (x : S) x.2
      obtain ⟨a, ha⟩ := Algebra.IsInvariant.isInvariant (A := A)
        (∑ i, r i • (e * (x : S))) hfix
      refine ⟨a, ?_⟩
      rw [← hx, IsScalarTower.algebraMap_apply A F L]
      apply (heq _ _).mpr
      apply Subtype.ext
      change e * algebraMap A S a = e * (x : S)
      rw [ha]
      exact orbit_sum_projection S G H e hH n r hr hc (x : S) x.2

private theorem invariant_flat_comparison
    (C R B : Type u) [CommRing C] [CommRing R] [CommRing B]
    [Algebra C R] [Algebra C B]
    (ι : Type v) [_root_.Finite ι] (τ : ι → R →ₐ[C] R)
    (j : B →ₐ[C] R) (hj : Function.Injective j)
    (hfixed : ∀ x : R, (∀ h : ι, τ h x = x) ↔ ∃ b : B, j b = x)
    (A : Type u) [CommRing A] [Algebra C A] [Module.Flat C A] :
    ∃ E : A ⊗[C] B ≃ₐ[A]
        AlgHom.fixedPoints (AlgHom.baseChangeFamily A τ),
      ∀ x, (E x : A ⊗[C] R) = Algebra.TensorProduct.map (AlgHom.id A A) j x := by
  classical
  let jH : B →ₐ[C] AlgHom.fixedPoints τ :=
    j.codRestrict _ (fun b ↦ AlgHom.mem_fixedPoints.mpr ((hfixed (j b)).mpr ⟨b, rfl⟩))
  have hjH : Function.Bijective jH := by
    constructor
    · intro b c h
      exact hj (congrArg Subtype.val h)
    · rintro ⟨x, hx⟩
      obtain ⟨b, hb⟩ := (hfixed x).mp (AlgHom.mem_fixedPoints.mp hx)
      exact ⟨b, Subtype.ext hb⟩
  let eH : B ≃ₐ[C] AlgHom.fixedPoints τ := AlgEquiv.ofBijective jH hjH
  let E : A ⊗[C] B ≃ₐ[A] AlgHom.fixedPoints (AlgHom.baseChangeFamily A τ) :=
    (Algebra.TensorProduct.congr (AlgEquiv.refl : A ≃ₐ[A] A) eH).trans
      (AlgHom.tensorFixedPointsEquiv A τ)
  refine ⟨E, ?_⟩
  intro x
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero, Subalgebra.coe_zero]
  | tmul a b => rfl
  | add x y hx hy =>
    simp only [map_add, Subalgebra.coe_add, hx, hy]


/-- Flat base change of the H-invariant ring, localized at a component with stabilizer H,
is the base algebra when the G-translates of that component partition the ring.
Source: Stacks Project, Tag 0BST, final displayed invariant rings and their coset inverse.
(blueprint: lem-dl-a1-invariant-orbit-localization).

Proof:
1. Identify B with the H-fixed subalgebra using the injective map j and the specified image.
The flat equalizer comparison identifies A tensor B with the H-fixed subalgebra of A tensor R.
For G the same comparison and injectivity of C into R identify the full fixed subalgebra
with A. Both identifications commute with the inclusions into A tensor R.
2. The H-fixed idempotent e corresponds to b in A tensor B. Localization at this idempotent
is the e-component of the H-fixed ring: the map sends x/b^k to ex, and the inverse sends
ex to x/1. Idempotence gives both inverse identities.
3. Projection of the G-fixed ring onto the e-component is bijective. Its inverse sends an
H-fixed component x to the sum of r_i(ex). This is independent of representatives because
H fixes both e and x. For g in G, rewrite each g r_i as r_j h. Orthogonality and the coset
cover show that this reindexes the sum, so it is G-fixed.
4. Projection of the sum back to e leaves only the identity component. Conversely a G-fixed
element is recovered from its projection because the translated idempotents sum to one.
The maps preserve addition, multiplication and one, by orthogonality. Under the full fixed
ring identification from step 1 this is exactly the algebra map from A to the localization,
which is therefore bijective. The zero-ring case satisfies the same equations. -/
theorem exists_invariant_orbit_localization
    (C R B : Type u) [CommRing C] [CommRing R] [CommRing B]
    [Algebra C R] [Algebra C B]
    (G : Type v) [Group G] [_root_.Finite G] [MulSemiringAction G R]
    [SMulCommClass G C R] [Algebra.IsInvariant C R G]
    (hinj : Function.Injective (algebraMap C R))
    (H : Subgroup G) (j : B →ₐ[C] R) (hj : Function.Injective j)
    (hfixed : ∀ x : R, (∀ h : H, h • x = x) ↔ ∃ b : B, j b = x)
    (A : Type u) [CommRing A] [Algebra C A] [Module.Flat C A]
    (e : A ⊗[C] R) (he : IsIdempotentElem e)
    (hH : ∀ h : H, baseChangeFamily A (MulSemiringAction.toAlgHom C R) h.val e = e)
    (n : ℕ) (r : Fin n → G)
    (hr : ∀ g : G, ∃ (i : Fin n) (h : H), g = r i * h.val)
    (hc : CompleteOrthogonalIdempotents
      (fun i ↦ baseChangeFamily A (MulSemiringAction.toAlgHom C R) (r i) e)) :
    ∃ b : A ⊗[C] B,
      Algebra.TensorProduct.map (AlgHom.id A A) j b = e ∧
      Function.Bijective (algebraMap A (Localization.Away b)) := by
  classical
  let S := A ⊗[C] R
  let τ : G → R →ₐ[C] R := MulSemiringAction.toAlgHom C R
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
  have hact (g : G) (x : S) : g • x = baseChangeFamily A τ g x := rfl
  have : SMulCommClass G A S := ⟨fun g a x ↦ by
    change (ρ g) (a • x) = a • (ρ g) x
    exact (ρ g).toLinearEquiv.map_smul a x⟩
  have hfull : ∀ x : R, (∀ g : G, τ g x = x) ↔ ∃ c : C, algebraMap C R c = x := by
    intro x
    constructor
    · exact Algebra.IsInvariant.isInvariant x
    · rintro ⟨c, rfl⟩ g
      exact smul_algebraMap g c
  obtain ⟨EC, hEC⟩ := invariant_flat_comparison C R C G τ
    (Algebra.ofId C R) hinj hfull A
  let EC' : A ≃ₐ[A] fixedPoints (baseChangeFamily A τ) :=
    (Algebra.TensorProduct.rid C A A).symm.trans EC
  have hEC' (a : A) : (EC' a : S) = algebraMap A S a := by
    change (EC (a ⊗ₜ (1 : C)) : S) = _
    rw [hEC]
    simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, map_one]
    rfl
  have hAS : Function.Injective (algebraMap A S) := by
    intro a b h
    apply EC'.injective
    apply Subtype.ext
    simpa only [hEC'] using h
  have : Algebra.IsInvariant A S G := ⟨by
    intro x hx
    let x' : fixedPoints (baseChangeFamily A τ) :=
      ⟨x, mem_fixedPoints.mpr (fun g ↦ (hact g x).symm.trans (hx g))⟩
    refine ⟨EC'.symm x', ?_⟩
    rw [← hEC']
    exact congrArg Subtype.val (EC'.apply_symm_apply x')⟩
  obtain ⟨EH, hEH⟩ := invariant_flat_comparison C R B H (fun h ↦ τ h.val)
    j hj hfixed A
  have hEq : fixedPoints (baseChangeFamily A (fun h : H ↦ τ h.val)) =
      FixedPoints.subalgebra A S H := by
    ext x
    simp only [mem_fixedPoints]
    exact Iff.rfl
  let E : A ⊗[C] B ≃ₐ[A] FixedPoints.subalgebra A S H :=
    EH.trans (Subalgebra.equivOfEq _ _ hEq)
  have hE (x : A ⊗[C] B) : (E x : S) =
      Algebra.TensorProduct.map (AlgHom.id A A) j x := hEH x
  have hH' : ∀ h : H, h • e = e := hH
  let eF : FixedPoints.subalgebra A S H := ⟨e, hH'⟩
  let b := E.symm eF
  have hb : Algebra.TensorProduct.map (AlgHom.id A A) j b = e := by
    rw [← hE]
    exact congrArg Subtype.val (E.apply_symm_apply eF)
  refine ⟨b, hb, ?_⟩
  have hbij := orbit_localization_bijective A S G hAS H e he hH' n r hr hc
  let L := Localization.Away b
  let LF := Localization.Away eF
  have hEb : E b = eF := E.apply_symm_apply eF
  have hpow : Submonoid.map E (Submonoid.powers b) = Submonoid.powers eF := by
    rw [Submonoid.map_powers, hEb]
  let EL : L ≃ₐ[A] LF := IsLocalization.algEquivOfAlgEquiv L LF E hpow
  constructor
  · intro a c hac
    apply hbij.1
    have h := congrArg EL hac
    exact (EL.commutes a).symm.trans (h.trans (EL.commutes c))
  · intro z
    obtain ⟨a, ha⟩ := hbij.2 (EL z)
    refine ⟨a, EL.injective ?_⟩
    rw [EL.commutes, ha]

end AlgHom
