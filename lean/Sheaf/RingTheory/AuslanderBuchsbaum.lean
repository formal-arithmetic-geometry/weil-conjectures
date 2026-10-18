/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NR
-/
module

public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Finiteness.Defs
public import Sheaf.RingTheory.GlobalDimension
public import Sheaf.RingTheory.Depth
import Mathlib.RingTheory.Nakayama
import Mathlib.RingTheory.Regular.RegularSequence
import Sheaf.RingTheory.MinimalFiniteFreeResolutionLocal
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.RingTheory.Noetherian.Basic
import Sheaf.AlgebraicGeometry.ExactFreeComplexLastMinors
import Sheaf.RingTheory.DepthInSES
import Sheaf.RingTheory.BoundedProjectiveResolutionDimension
import Mathlib.RingTheory.Regular.ProjectiveDimension
import Sheaf.RingTheory.CohenMacaulayDepthFirstTerm
import Sheaf.RingTheory.DepthExt
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.CategoryTheory.Abelian.Projective.Resolution

/-!
# The Auslander–Buchsbaum depth formula

Source: Stacks Project, Algebra, Tag 090V, proposition-Auslander-Buchsbaum
(blueprint: lem-weil-pbc-auslander-buchsbaum).
-/

@[expose] public section

universe u v

namespace IsLocalRing

open CategoryTheory CategoryTheory.Limits

private theorem depth_cokernel_ge
    {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    {A B C : Type*} [AddCommGroup A] [Module R A] [Module.Finite R A]
    [AddCommGroup B] [Module R B] [Module.Finite R B]
    [AddCommGroup C] [Module R C] [Module.Finite R C]
    (f : A →ₗ[R] B) (g : B →ₗ[R] C)
    (hf : Function.Injective f) (hfg : Function.Exact f g) (hg : Function.Surjective g) :
    min (depth (R := R) B) (depth (R := R) A - 1) ≤ depth (R := R) C := by
  cases subsingleton_or_nontrivial C with
  | inl h =>
    let := h
    rw [depth_subsingleton C]
    exact le_top
  | inr h =>
    let := h
    cases subsingleton_or_nontrivial A with
    | inl h =>
      let := h
      have hfzero : f = 0 := by
        ext a
        rw [Subsingleton.elim a 0, map_zero]
        rfl
      have hginj : Function.Injective g := by
        rw [hfzero] at hfg
        exact (LinearMap.exact_zero_iff_injective _ _).mp hfg
      rw [depth_subsingleton A]
      simpa using (depth_equiv_local (LinearEquiv.ofBijective g ⟨hginj, hg⟩)).le
    | inr h =>
      let := h
      have : Nontrivial B := hf.nontrivial
      exact (depth_in_short_exact f g hf hfg hg).2.1

private theorem projectiveDimension_eq_nat
    {R : Type u} [CommRing R] (M : ModuleCat.{max u v} R) [Nontrivial M]
    (h : ModuleCat.HasFiniteProjectiveDimension M) :
    CategoryTheory.projectiveDimension M =
      (ModuleCat.projectiveDimension M h : WithBot ℕ∞) := by
  classical
  apply eq_of_forall_ge_iff
  intro a
  cases a with
  | bot =>
    constructor
    · intro hz
      have : Limits.IsZero M :=
        (CategoryTheory.projectiveDimension_eq_bot_iff M).mp (le_bot_iff.mp hz)
      exact (not_subsingleton M (ModuleCat.isZero_iff_subsingleton.mp this)).elim
    · intro hz
      change (ModuleCat.projectiveDimension M h : WithBot ℕ∞) ≤ ⊥ at hz
      simp only [le_bot_iff, WithBot.natCast_ne_bot] at hz
  | coe a =>
    cases a with
    | top => simp
    | coe n =>
      constructor
      · intro hn
        have hn' := (CategoryTheory.projectiveDimension_le_iff M n).mp hn
        have hn'' := (ModuleCat.hasProjectiveResolutionLE_iff_hasProjectiveDimensionLE M n).mpr hn'
        exact_mod_cast (Nat.find_min' h hn'')
      · intro hn
        have hn' : ModuleCat.projectiveDimension M h ≤ n := by exact_mod_cast hn
        have hres : ModuleCat.HasProjectiveResolutionLE M n := by
          obtain ⟨P, hP⟩ := Nat.find_spec h
          exact ⟨P, fun i hi ↦ hP i (lt_of_le_of_lt hn' hi)⟩
        apply (CategoryTheory.projectiveDimension_le_iff M n).mpr
        exact (ModuleCat.hasProjectiveResolutionLE_iff_hasProjectiveDimensionLE M n).mp hres

private theorem depth_le_resolution_length_add_depth
    {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (M : ModuleCat.{max u v} R) [Module.Finite R M] [Nontrivial M]
    (e : ℕ) (P : ProjectiveResolution M)
    (hzero : ∀ i : ℕ, e < i → IsZero (P.complex.X i))
    (hfree : ∀ i : ℕ, Module.Finite R (P.complex.X i) ∧ Module.Free R (P.complex.X i)) :
    depth (R := R) R ≤ (e : ℕ∞) + depth (R := R) M := by
  classical
  obtain ⟨d, hd, _⟩ := exists_depth_eq_ext_degree (R := R) R
  let (i : ℕ) : Module.Finite R (P.complex.X i) := (hfree i).1
  let (i : ℕ) : Module.Free R (P.complex.X i) := (hfree i).2
  let X : ℕ → ModuleCat.{max u v} R
    | 0 => M
    | i + 1 => P.complex.X i
  let g : (i : ℕ) → (X (i + 1) ⟶ X i)
    | 0 => P.π.f 0
    | i + 1 => P.complex.d (i + 1) i
  let (i : ℕ) : Module.Finite R (X i) := by
    cases i with
    | zero => exact inferInstanceAs (Module.Finite R M)
    | succ i => exact (hfree i).1
  let (i : ℕ) : Module.Finite R (LinearMap.range (g i).hom) :=
    Module.Finite.of_surjective (g i).hom.rangeRestrict
      (LinearMap.range_eq_top.mp (g i).hom.range_rangeRestrict)
  have hex (i : ℕ) : Function.Exact (g (i + 1)).hom (g i).hom := by
    cases i with
    | zero =>
      exact (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp P.exact₀
    | succ i =>
      exact (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp (P.exact_succ i)
  have htopinj : Function.Injective (g e).hom := by
    have hz : g (e + 1) = 0 := (hzero (e + 1) (by omega)).eq_of_src _ _
    have he := hex e
    rw [hz] at he
    exact (LinearMap.exact_zero_iff_injective _ _).mp he
  have hbound (i : ℕ) (hi : i ≤ e) :
      ((d - (e - i) : ℕ) : ℕ∞) ≤ depth (R := R) (LinearMap.range (g i).hom) := by
    induction hi using Nat.decreasingInduction with
    | self =>
      simp only [Nat.sub_self, Nat.sub_zero]
      rw [← depth_equiv_local (LinearEquiv.ofInjective (g e).hom htopinj)]
      exact hd ▸ depth_free_ge (P.complex.X e)
    | of_succ i hi ih =>
      let f := (LinearMap.range (g (i + 1)).hom).subtype
      let q := (g i).hom.rangeRestrict
      have hq : Function.Surjective q :=
        LinearMap.range_eq_top.mp (g i).hom.range_rangeRestrict
      have hfq : Function.Exact f q := by
        rw [LinearMap.exact_iff]
        simpa only [f, q, Submodule.range_subtype, LinearMap.ker_rangeRestrict] using
          (LinearMap.exact_iff.mp (hex i))
      have hdep := depth_cokernel_ge f q Subtype.val_injective hfq hq
      apply le_trans _ hdep
      apply le_min
      · exact le_trans (by exact_mod_cast Nat.sub_le d (e - i))
          (hd ▸ depth_free_ge (P.complex.X i))
      · have hsub := tsub_le_tsub_right ih 1
        apply le_trans _ hsub
        simpa only [ENat.natCast_sub, Nat.cast_one] using
          (ENat.natCast_le_natCast.mpr
            (show d - (e - i) ≤ d - (e - (i + 1)) - 1 by omega))
  have hepi : Function.Surjective (g 0).hom :=
    (ModuleCat.epi_iff_surjective (P.π.f 0)).mp inferInstance
  have hM := hbound 0 (Nat.zero_le e)
  rw [depth_equiv_local (LinearEquiv.ofTop _ (LinearMap.range_eq_top.mpr hepi))] at hM
  obtain ⟨t, ht, _⟩ := exists_depth_eq_ext_degree (R := R) M
  rw [hd, ht, ← ENat.natCast_add]
  rw [ht] at hM
  have hdt : d - e ≤ t := by exact_mod_cast hM
  exact_mod_cast (show d ≤ e + t by omega)

private theorem projectiveDimension_le_depth_ring
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (M : ModuleCat.{max u v} R) [Module.Finite R M]
    (h : ModuleCat.HasFiniteProjectiveDimension M) :
    (ModuleCat.projectiveDimension M h : ℕ∞) ≤ depth (R := R) R := by
  classical
  let d := ModuleCat.projectiveDimension M h
  change (d : ℕ∞) ≤ _
  by_cases hd0 : d = 0
  · simp [hd0]
  have hd : 1 ≤ d := by omega
  have hres : ModuleCat.HasProjectiveResolutionLE M d := Nat.find_spec h
  obtain ⟨P, hzero, hfree, hminimal⟩ :=
    ModuleCat.exists_minimal_finite_free_resolution M d hres
  let (i : ℕ) : Module.Finite R (P.complex.X i) := (hfree i).1
  let (i : ℕ) : Module.Free R (P.complex.X i) := (hfree i).2
  let n : ℕ → ℕ := fun i ↦ Fintype.card (Module.Free.ChooseBasisIndex R (P.complex.X i))
  let b (i : ℕ) : Module.Basis (Fin (n i)) R (P.complex.X i) :=
    (Module.Free.chooseBasis R (P.complex.X i)).reindex (Fintype.equivFin _)
  let c (i : ℕ) : P.complex.X i ≃ₗ[R] (Fin (n i) → R) := (b i).equivFun
  -- A zero last term would contradict the least possible resolution length.
  have hn : n d ≠ 0 := by
    intro hn
    have hz : CategoryTheory.Limits.IsZero (P.complex.X d) := by
      apply ModuleCat.isZero_iff_subsingleton.mpr
      refine ⟨fun x y ↦ (c d).injective ?_⟩
      ext j
      exact (Fin.elim0 (hn ▸ j))
    have hshort : ModuleCat.HasProjectiveResolutionLE M (d - 1) := by
      refine ⟨P, fun i hi ↦ ?_⟩
      by_cases hid : i = d
      · simpa [hid] using hz
      · exact hzero i (by omega)
    have : d ≤ d - 1 := Nat.find_min' h hshort
    omega
  let f (i : ℕ) : (Fin (n i) → R) →ₗ[R] (Fin (n (i - 1)) → R) :=
    (c (i - 1)).toLinearMap ∘ₗ (P.complex.d i (i - 1)).hom ∘ₗ (c i).symm.toLinearMap
  let φ (i : ℕ) : Matrix (Fin (n (i - 1))) (Fin (n i)) R := LinearMap.toMatrix' (f i)
  have hφ (i : ℕ) (v : Fin (n i) → R) :
      (φ i).mulVec v = c (i - 1) ((P.complex.d i (i - 1)).hom ((c i).symm v)) := by
    exact LinearMap.toMatrix'_mulVec (f i) v
  have hpexact (i : ℕ) (hi : 1 ≤ i) :
      Function.Exact (P.complex.d (i + 1) i).hom (P.complex.d i (i - 1)).hom := by
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i ≠ 0)
    exact (CategoryTheory.ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp
      (P.exact_succ j)
  have hexact (i : ℕ) (hi : 1 ≤ i) (_hie : i + 1 ≤ d) :
      Function.Exact (φ (i + 1)).mulVec (φ i).mulVec := by
    intro v
    constructor
    · intro hv
      have hv' : (P.complex.d i (i - 1)).hom ((c i).symm v) = 0 := by
        apply (c (i - 1)).injective
        simpa only [map_zero, ← hφ] using hv
      obtain ⟨x, hx⟩ := (hpexact i hi _).mp hv'
      refine ⟨c (i + 1) x, ?_⟩
      simp only [hφ, Nat.add_one_sub_one, LinearEquiv.symm_apply_apply, hx,
        LinearEquiv.apply_symm_apply]
    · rintro ⟨x, rfl⟩
      rw [hφ, hφ]
      simp only [Nat.add_one_sub_one, LinearEquiv.symm_apply_apply]
      rw [(hpexact i hi).apply_apply_eq_zero, map_zero]
  have hcomplex (i : ℕ) (hi : 1 ≤ i) (hie : i + 1 ≤ d)
      (v : Fin (n (i + 1)) → R) :
      (φ i).mulVec ((φ (i + 1)).mulVec v) = 0 :=
    (hexact i hi hie).apply_apply_eq_zero v
  have hdinj : Function.Injective (P.complex.d d (d - 1)).hom := by
    have hp := hpexact d hd
    have hz : P.complex.d (d + 1) d = 0 :=
      (hzero (d + 1) (by omega)).eq_of_src _ _
    rw [hz] at hp
    exact (LinearMap.exact_zero_iff_injective _ _).mp hp
  have hinjective : Function.Injective (φ d).mulVec := by
    intro x y hxy
    rw [hφ, hφ] at hxy
    exact (c d).symm.injective (hdinj ((c (d - 1)).injective hxy))
  have hentries (i : Fin (n (d - 1))) (j : Fin (n d)) :
      φ d i j ∈ IsLocalRing.maximalIdeal R := by
    change LinearMap.toMatrix' (f d) i j ∈ _
    rw [LinearMap.toMatrix'_apply]
    let l : P.complex.X (d - 1) →ₗ[R] R :=
      (LinearMap.proj i) ∘ₗ (c (d - 1)).toLinearMap
    have hm : (P.complex.d d (d - 1)).hom ((c d).symm (Pi.single j 1)) ∈
        IsLocalRing.maximalIdeal R • (⊤ : Submodule R (P.complex.X (d - 1))) := by
      have hm := hminimal (d - 1) (by omega)
      have heq : d - 1 + 1 = d := by omega
      rw [heq] at hm
      exact hm (LinearMap.mem_range_self _ _)
    have hl := Submodule.smul_top_le_comap_smul_top (IsLocalRing.maximalIdeal R) l hm
    simpa [l, f, Submodule.mem_comap, Ideal.smul_eq_mul, Ideal.mul_top] using hl
  let I : Ideal R := Ideal.span {z : R | ∃ r : Fin (n d) → Fin (n (d - 1)),
    StrictMono r ∧ z = ((φ d).submatrix r id).det}
  -- Modulo the maximal ideal the last matrix is zero, hence so are its nonempty minors.
  have hI : I ≤ IsLocalRing.maximalIdeal R := by
    apply Ideal.span_le.mpr
    rintro z ⟨r, _hr, rfl⟩
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [(Ideal.Quotient.mk (IsLocalRing.maximalIdeal R)).map_det]
    have hmat : (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R)).mapMatrix
        ((φ d).submatrix r id) = 0 := by
      ext i j
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (hentries (r i) j)
    rw [hmat]
    let : Nonempty (Fin (n d)) := ⟨⟨0, Nat.pos_of_ne_zero hn⟩⟩
    exact Matrix.det_zero
  obtain htop | ⟨rs, hlen, hmem, hreg⟩ :=
    exact_free_complex_last_minors_regular_sequence R d hd n φ hcomplex hexact hinjective
  · exact ((IsLocalRing.maximalIdeal.isMaximal R).ne_top
      (top_le_iff.mp (htop ▸ hI))).elim
  · unfold IsLocalRing.depth Ideal.depth
    split_ifs
    · exact le_top
    · apply le_sSup
      exact ⟨rs, hreg, fun x hx ↦ hI (hmem x hx), by simp [hlen]⟩


/-- The Auslander–Buchsbaum formula for a nonzero finite module of finite projective dimension
 over a commutative Noetherian local ring. Both depths use the unique maximal ideal.
Source: Stacks Project, Algebra, Tag 090V, proposition-Auslander-Buchsbaum
(blueprint: lem-weil-pbc-auslander-buchsbaum).

Proof:
1. Compare the resolution-length projective dimension with Mathlib's Ext projective
   dimension using the bounded-resolution comparison and the least-length property.
2. A finite free resolution of length e gives depth R ≤ e + depth M. Factor its maps
   through their images and apply the depth lemma descending from the injective top map.
   A zero syzygy has infinite depth; if a short exact sequence has zero left term, the
   other two terms are isomorphic. These cases justify all uses of the depth lemma.
3. For any finite module L of finite projective dimension q, minimalize a length-q
   finite free resolution. If q > 0 its last rank is positive, by minimality of q.
   Its last maximal minors lie in the maximal ideal. The exact-free-complex last-minors
   lemma therefore gives a ring-regular sequence of length q, hence q ≤ depth R.
4. Depth is finite by its Ext characterization. Its supremum definition and Nakayama
   give an M-regular sequence rs of length depth M in the maximal ideal. Mathlib's
   projectiveDimension_quotient_eq_add_length_of_isWeaklyRegular gives
   pd(M/(rs)M) = pd M + length rs, with all dimensions taken over R.
5. Apply step 3 to the nonzero finite quotient M/(rs)M. This gives
   pd M + depth M ≤ depth R. Combine it with step 2 by antisymmetry.

The module universe contains the ring universe, so projectivity in ModuleCat agrees
with ordinary module projectivity and the bounded-resolution comparison applies. -/
theorem depth_eq_projectiveDimension_add_depth
    {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (M : Type (max u v)) [AddCommGroup M] [Module R M] [Nontrivial M] [Module.Finite R M]
    (h : ModuleCat.HasFiniteProjectiveDimension (ModuleCat.of R M)) :
    depth (R := R) R =
      (ModuleCat.projectiveDimension (ModuleCat.of R M) h : ℕ∞) + depth (R := R) M := by
  classical
  let L := ModuleCat.of R M
  let e := ModuleCat.projectiveDimension L h
  obtain ⟨P, hzero, hfree, _⟩ :=
    ModuleCat.exists_minimal_finite_free_resolution L e (Nat.find_spec h)
  apply le_antisymm
  · exact depth_le_resolution_length_add_depth L e P hzero hfree
  · obtain ⟨t, ht, _⟩ := exists_depth_eq_ext_degree (R := R) M
    have hm : maximalIdeal R • (⊤ : Submodule R M) ≠ ⊤ :=
      (Submodule.top_ne_ideal_smul_of_le_jacobson_annihilator
        (maximalIdeal_le_jacobson (Module.annihilator R M))).symm
    have hdef : depth (R := R) M = sSup {n : ℕ∞ | ∃ rs : List R,
        RingTheory.Sequence.IsRegular M rs ∧ (∀ r ∈ rs, r ∈ maximalIdeal R) ∧
          n = (rs.length : ℕ∞)} := by
      simp only [depth, Ideal.depth, if_neg hm]
    have hmem : depth (R := R) M ∈ {n : ℕ∞ | ∃ rs : List R,
        RingTheory.Sequence.IsRegular M rs ∧ (∀ r ∈ rs, r ∈ maximalIdeal R) ∧
          n = (rs.length : ℕ∞)} := by
      rw [hdef]
      let : Nonempty {n : ℕ∞ | ∃ rs : List R,
          RingTheory.Sequence.IsRegular M rs ∧ (∀ r ∈ rs, r ∈ maximalIdeal R) ∧
            n = (rs.length : ℕ∞)} :=
        ⟨⟨0, [], RingTheory.Sequence.IsRegular.nil R M, by simp, rfl⟩⟩
      apply ENat.sSup_mem_of_nonempty_of_lt_top
      simpa only [← hdef, ht] using ENat.natCast_lt_top t
    obtain ⟨rs, hrs, hmax, hlen⟩ := hmem
    have hlength : rs.length = t := by
      rw [ht] at hlen
      exact_mod_cast hlen.symm
    let Q := ModuleCat.of R (M ⧸ Ideal.ofList rs • (⊤ : Submodule R M))
    let := hrs.quot_ofList_smul_nontrivial (⊤ : Submodule R M)
    have hqdim : CategoryTheory.projectiveDimension Q = ((e + t : ℕ) : WithBot ℕ∞) := by
      rw [ModuleCat.projectiveDimension_quotient_eq_add_length_of_isWeaklyRegular
        L rs hrs.1 hmax, projectiveDimension_eq_nat L h, hlength]
      exact (Nat.cast_add e t).symm
    have hQres : ModuleCat.HasProjectiveResolutionLE Q (e + t) :=
      (ModuleCat.hasProjectiveResolutionLE_iff_hasProjectiveDimensionLE Q (e + t)).mpr
        ((CategoryTheory.projectiveDimension_le_iff Q (e + t)).mp hqdim.le)
    have hQfin : ModuleCat.HasFiniteProjectiveDimension Q := ⟨e + t, hQres⟩
    have hQdim : ModuleCat.projectiveDimension Q hQfin = e + t := by
      have heq := (projectiveDimension_eq_nat Q hQfin).symm.trans hqdim
      exact_mod_cast heq
    have hbound := projectiveDimension_le_depth_ring Q hQfin
    rw [hQdim, ENat.natCast_add] at hbound
    simpa only [ht] using hbound

end IsLocalRing
