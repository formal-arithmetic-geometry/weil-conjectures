/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
module

public import Mathlib.RingTheory.Localization.Module
public import Mathlib.RingTheory.Support
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.Topology.GDelta.Basic
import Mathlib.Topology.LocalAtTarget
import Mathlib.RingTheory.Localization.Submodule

/-!
# Localization and removal of embedded associated points

Source: Stacks Project, Tag 02M7
(blueprint: lem-sc-hilbert-embedded-points-affine-localization).
-/

@[expose] public section

universe u v

namespace Module

private theorem support_localization
    {R A M N : Type*} [CommRing R] [CommRing A] [Algebra R A]
    (S : Submonoid R) [IsLocalization S A]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [Module A N] [IsScalarTower R A N]
    (g : M →ₗ[R] N) [IsLocalizedModule S g] :
    Module.support A N =
      PrimeSpectrum.comap (algebraMap R A) ⁻¹' Module.support R M := by
  ext q
  rw [Set.mem_preimage, Module.mem_support_iff', Module.mem_support_iff']
  constructor
  · rintro ⟨x, hx⟩
    obtain ⟨⟨m, s⟩, rfl⟩ := IsLocalizedModule.mk'_surjective S g x
    refine ⟨m, fun r hr he ↦ hx (algebraMap R A r) hr ?_⟩
    simp only [Function.uncurry_apply_pair]
    rw [algebraMap_smul, ← IsLocalizedModule.mk'_smul, he,
      IsLocalizedModule.mk'_zero]
  · rintro ⟨m, hm⟩
    refine ⟨g m, fun a ha he ↦ ?_⟩
    obtain ⟨r, s, rfl⟩ := IsLocalization.exists_mk'_eq S a
    have hr : algebraMap R A r ∉ q.asIdeal :=
      fun h ↦ ha ((IsLocalization.mk'_mem_iff (M := S)).mpr h)
    have hzero : g (r • m) = 0 := by
      rw [map_smul, ← algebraMap_smul A,
        ← IsLocalization.mk'_spec A r s, mul_smul, smul_comm, he, smul_zero]
    obtain ⟨u, hu⟩ := (IsLocalizedModule.eq_zero_iff S g).mp hzero
    have huq : algebraMap R A u ∉ q.asIdeal :=
      fun h ↦ q.isPrime.ne_top (q.asIdeal.eq_top_of_isUnit_mem h
        (IsLocalization.map_units A u))
    exact hm (u.val * r)
      (fun h ↦ (q.isPrime.mul_mem_iff_mem_or_mem.mp
        (by simpa only [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap, map_mul] using h)).elim
          huq hr)
      (by simpa [mul_smul, Submonoid.smul_def] using hu)

private theorem closure_support_localization
    {R A M N : Type*} [CommRing R] [CommRing A] [Algebra R A]
    (S : Submonoid R) [IsLocalization S A]
    [AddCommGroup M] [Module R M] [Module.Finite R M]
    [AddCommGroup N] [Module R N] [Module A N] [IsScalarTower R A N]
    (g : M →ₗ[R] N) [IsLocalizedModule S g] (hg : Function.Injective g) :
    closure (PrimeSpectrum.comap (algebraMap R A) '' Module.support A N) =
      Module.support R M := by
  have : Module.Finite A N := Module.Finite.of_isLocalizedModule S g
  rw [Module.support_eq_zeroLocus, PrimeSpectrum.closure_image_comap_zeroLocus,
    Module.support_eq_zeroLocus]
  congr 1
  ext r
  change algebraMap R A r ∈ Module.annihilator A N ↔ r ∈ Module.annihilator R M
  simp only [Module.mem_annihilator]
  constructor
  · intro h m
    apply hg
    simpa using h (g m)
  · intro h x
    obtain ⟨⟨m, s⟩, rfl⟩ := IsLocalizedModule.mk'_surjective S g x
    simp only [Function.uncurry_apply_pair]
    rw [algebraMap_smul, ← IsLocalizedModule.mk'_smul, h, IsLocalizedModule.mk'_zero]

private theorem nowhereDense_preimage_openEmbedding
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {g : X → Y} (hg : Topology.IsOpenEmbedding g) {Z : Set Y}
    (hZ : IsNowhereDense Z) : IsNowhereDense (g ⁻¹' Z) := by
  rw [IsNowhereDense,
    ← hg.isOpenMap.preimage_closure_eq_closure_preimage hg.continuous,
    ← hg.isOpenMap.preimage_interior_eq_interior_preimage hg.continuous,
    hZ, Set.preimage_empty]

private theorem support_localization_openEmbedding
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] (f : R) :
    Topology.IsOpenEmbedding
      (fun p : Module.support (Localization (Submonoid.powers f))
          (LocalizedModule (Submonoid.powers f) M) ↦
        (⟨PrimeSpectrum.comap (algebraMap R (Localization (Submonoid.powers f))) p.val,
          (Set.ext_iff.mp (support_localization (A := Localization (Submonoid.powers f))
            (Submonoid.powers f)
            (LocalizedModule.mkLinearMap (Submonoid.powers f) M)) p.val).mp p.prop⟩ :
          Module.support R M)) := by
  let e := Homeomorph.setCongr
    (support_localization (A := Localization (Submonoid.powers f)) (Submonoid.powers f)
      (LocalizedModule.mkLinearMap (Submonoid.powers f) M))
  exact ((PrimeSpectrum.localization_away_isOpenEmbedding
    (Localization (Submonoid.powers f)) f).restrictPreimage
      (Module.support R M)).comp e.isOpenEmbedding

private theorem nowhereDense_localized
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (f : R) (L : Submodule R M)
    (hL : IsNowhereDense {p : Module.support R M | p.val ∈ Module.support R L}) :
    IsNowhereDense
      {p : Module.support (Localization (Submonoid.powers f))
        (LocalizedModule (Submonoid.powers f) M) |
        p.val ∈ Module.support (Localization (Submonoid.powers f))
          (L.localized (Submonoid.powers f))} := by
  have h := nowhereDense_preimage_openEmbedding (support_localization_openEmbedding (M := M) f) hL
  simpa only [Set.preimage_ofPred_eq, Set.mem_preimage,
    support_localization (A := Localization (Submonoid.powers f))
      (Submonoid.powers f) (L.toLocalized (Submonoid.powers f))] using h

private theorem nowhereDense_of_injective_localization
    {R M : Type*} [CommRing R] [IsNoetherianRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M]
    (f : R) (L : Submodule R M)
    (hinj : Function.Injective (L.toLocalized (Submonoid.powers f)))
    (hL : IsNowhereDense
      {p : Module.support (Localization (Submonoid.powers f))
        (LocalizedModule (Submonoid.powers f) M) |
        p.val ∈ Module.support (Localization (Submonoid.powers f))
          (L.localized (Submonoid.powers f))}) :
    IsNowhereDense {p : Module.support R M | p.val ∈ Module.support R L} := by
  let S := Submonoid.powers f
  let c := PrimeSpectrum.comap (algebraMap R (Localization S))
  let j : Module.support (Localization S) (LocalizedModule S M) → Module.support R M :=
    fun p ↦ ⟨c p.val,
      (Set.ext_iff.mp (support_localization (A := Localization S) S
        (LocalizedModule.mkLinearMap S M)) p.val).mp p.prop⟩
  let E : Set (Module.support (Localization S) (LocalizedModule S M)) :=
    {p | p.val ∈ Module.support (Localization S) (L.localized S)}
  have hsubset := Module.support_subset_of_injective (L.localized S).subtype
    Subtype.val_injective
  have himage : (fun p : Module.support (Localization S) (LocalizedModule S M) ↦
      c p.val) '' E = c '' Module.support (Localization S) (L.localized S) := by
    ext p
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact ⟨q.val, hq, rfl⟩
    · rintro ⟨q, hq, rfl⟩
      exact ⟨⟨q, hsubset hq⟩, hq, rfl⟩
  have hclosure : closure (j '' E) =
      {p : Module.support R M | p.val ∈ Module.support R L} := by
    rw [Topology.IsInducing.subtypeVal.closure_eq_preimage_closure_image, Set.image_image]
    change Subtype.val ⁻¹' closure
      ((fun p : Module.support (Localization S) (LocalizedModule S M) ↦ c p.val) '' E) = _
    rw [himage, closure_support_localization S (L.toLocalized S) hinj]
    rfl
  rw [← hclosure]
  exact ((support_localization_openEmbedding (M := M) f).isInducing.isNowhereDense_image hL).closure

private theorem nowhereDense_support_sup
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (K L : Submodule R M)
    (hK : IsNowhereDense {p : Module.support R M | p.val ∈ Module.support R K})
    (hL : IsNowhereDense {p : Module.support R M | p.val ∈ Module.support R L}) :
    IsNowhereDense {p : Module.support R M | p.val ∈ Module.support R ↥(K ⊔ L)} := by
  have hunion : IsNowhereDense
      ({p : Module.support R M | p.val ∈ Module.support R K} ∪
       {p : Module.support R M | p.val ∈ Module.support R L}) := by
    rw [IsNowhereDense, closure_union,
      interior_union_isClosed_of_interior_empty isClosed_closure hL]
    exact hK
  apply hunion.mono
  intro p hp
  by_contra h
  have hKp : p.val ∉ Module.support R K := fun hkp ↦ h (Or.inl hkp)
  have hLp : p.val ∉ Module.support R L := fun hlp ↦ h (Or.inr hlp)
  rw [Module.notMem_support_iff'] at hKp hLp
  obtain ⟨m, hm⟩ := Module.mem_support_iff'.mp hp
  obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.mp m.prop
  obtain ⟨a, ha, hax⟩ := hKp ⟨x, hx⟩
  obtain ⟨b, hb, hby⟩ := hLp ⟨y, hy⟩
  apply hm (a * b) (fun hh ↦ (p.val.isPrime.mul_mem_iff_mem_or_mem.mp hh).elim ha hb)
  apply Subtype.ext
  change (a * b) • m.val = 0
  have hax' : a • x = 0 := congrArg Subtype.val hax
  have hby' : b • y = 0 := congrArg Subtype.val hby
  rw [← hxy, smul_add, mul_smul, smul_comm a b, hax',
    smul_zero, mul_smul, hby', smul_zero, add_zero]

private theorem le_maximal_nowhereDense_support
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (K L : Submodule R M)
    (hK : Maximal (fun N : Submodule R M ↦
      IsNowhereDense {p : Module.support R M | p.val ∈ Module.support R N}) K)
    (hL : IsNowhereDense {p : Module.support R M | p.val ∈ Module.support R L}) :
    L ≤ K :=
  le_sup_right.trans (hK.2 (nowhereDense_support_sup K L hK.prop hL) le_sup_left)

private theorem injective_localization_power
    {R M : Type*} [CommRing R] [IsNoetherianRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M] (f : R) :
    ∃ n : ℕ, Function.Injective
      ((LocalizedModule.mkLinearMap (Submonoid.powers f) M).domRestrict
        (LinearMap.range (f ^ n • (LinearMap.id : M →ₗ[R] M)))) := by
  let t : Module.End R M := f • LinearMap.id
  have ht (n : ℕ) (m : M) : (t ^ n) m = f ^ n • m := by
    induction n with
    | zero => simp
    | succ n ih => simp [pow_succ, Module.End.mul_apply, t, ih, mul_smul, smul_comm f (f ^ n)]
  obtain ⟨n, hn, hd⟩ := (t.eventually_iSup_ker_pow_eq.and
    t.eventually_disjoint_ker_pow_range_pow).exists
  refine ⟨n, ?_⟩
  apply LinearMap.ker_eq_bot.mp
  apply le_bot_iff.mp
  rintro ⟨m, hm⟩ he
  have hz : LocalizedModule.mkLinearMap (Submonoid.powers f) M m = 0 := he
  obtain ⟨⟨_, k, rfl⟩, hk⟩ :=
    (IsLocalizedModule.eq_zero_iff (Submonoid.powers f) _).mp hz
  have hker : m ∈ LinearMap.ker (t ^ n) := by
    rw [← hn]
    exact (le_iSup (fun j : ℕ ↦ LinearMap.ker (t ^ j)) k)
      (by simpa [ht, Submonoid.smul_def] using hk)
  have hrange : m ∈ LinearMap.range (t ^ n) := by
    obtain ⟨x, hx⟩ := hm
    exact ⟨x, by simpa [ht] using hx⟩
  have hmzero : m = 0 := (Submodule.disjoint_def.mp hd) m hker hrange
  exact Subtype.ext hmzero

private theorem exists_injective_localization_lift
    {R M : Type*} [CommRing R] [IsNoetherianRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M] (f : R)
    (N : Submodule (Localization (Submonoid.powers f))
      (LocalizedModule (Submonoid.powers f) M)) :
    ∃ L : Submodule R M, L.localized (Submonoid.powers f) = N ∧
      Function.Injective (L.toLocalized (Submonoid.powers f)) := by
  let S := Submonoid.powers f
  let g := LocalizedModule.mkLinearMap S M
  let D := (N.restrictScalars R).comap g
  obtain ⟨n, hn⟩ := injective_localization_power (M := M) f
  let t : M →ₗ[R] M := f ^ n • LinearMap.id
  let L := D.map t
  have hLD : L ≤ D := by
    rintro _ ⟨m, hm, rfl⟩
    exact D.smul_mem (f ^ n) hm
  have hlocal : L.localized S = D.localized S := by
    apply le_antisymm
    · exact (Submodule.localized'gi (Localization S) S g).gc.monotone_l hLD
    · rintro x ⟨m, hm, s, rfl⟩
      refine ⟨t m, ⟨m, hm, rfl⟩, (⟨f ^ n, n, rfl⟩ : S) * s, ?_⟩
      exact IsLocalizedModule.mk'_cancel_left g m (⟨f ^ n, n, rfl⟩ : S) s
  refine ⟨L, hlocal.trans ((Submodule.localized'gi (Localization S) S g).l_u_eq N), ?_⟩
  intro x y hxy
  apply Subtype.ext
  exact congrArg (fun z : LinearMap.range t ↦ (z : M)) (hn
    (a₁ := ⟨x.val, by obtain ⟨m, hm, hx⟩ := x.prop; exact ⟨m, hx⟩⟩)
    (a₂ := ⟨y.val, by obtain ⟨m, hm, hy⟩ := y.prop; exact ⟨m, hy⟩⟩)
    (congrArg Subtype.val hxy))

/-- Source: Stacks Project, Tag 02M7
(blueprint: lem-sc-hilbert-embedded-points-affine-localization).
The quotients removing embedded associated points commute with localization.
The two maximality hypotheses specify the quotients constructed in
`exists_maximal_nowhereDense_support_quotient`. The equality on the images of
`m : M` specifies the canonical isomorphism induced by the quotient maps.

Proof:
The support of a localized module is the inverse image of its original support
under the open embedding of prime spectra. Thus localization preserves nowhere
density of support. Supports of sums lie in unions of supports, so maximality
here implies containment of every submodule with nowhere dense support.

Conversely, lift a submodule N of M_f by taking its inverse image D in M.
Noetherian stabilization of the kernels of powers of multiplication by f gives
an n such that localization is injective on f^n M. Put L = f^n D. Localization
identifies L_f with N, while the map L → L_f is injective. Comparing annihilators
therefore identifies Supp(L) with the closure of the image of Supp(N). The same
holds inside Supp(M), by the induced topology. An embedding sends nowhere dense
sets to nowhere dense sets, and taking closure preserves nowhere density. Hence
if N has nowhere dense support, so does L.

Apply these two directions to K and Kf. Maximality gives K_f ≤ Kf and L ≤ K,
so Kf = L_f ≤ K_f. Now Mathlib's `localizedQuotientEquiv` gives the isomorphism;
its formula on quotient classes is `IsLocalizedModule.linearEquiv_symm_apply`.
-/
theorem localization_commutes_with_embedded_point_removal
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M]
    (f : R)
    (K : Submodule R M)
    (Kf : Submodule (Localization (Submonoid.powers f))
      (LocalizedModule (Submonoid.powers f) M))
    (hK : Maximal (fun L : Submodule R M =>
      IsNowhereDense {p : Module.support R M | p.val ∈ Module.support R L}) K)
    (hKf : Maximal (fun L : Submodule (Localization (Submonoid.powers f))
      (LocalizedModule (Submonoid.powers f) M) =>
      IsNowhereDense {p : Module.support (Localization (Submonoid.powers f))
        (LocalizedModule (Submonoid.powers f) M) |
        p.val ∈ Module.support (Localization (Submonoid.powers f)) L}) Kf) :
    ∃ e : LocalizedModule (Submonoid.powers f) (M ⧸ K) ≃ₗ[
      Localization (Submonoid.powers f)]
      ((LocalizedModule (Submonoid.powers f) M) ⧸ Kf),
      ∀ m : M,
        e (LocalizedModule.mkLinearMap (Submonoid.powers f) (M ⧸ K) (K.mkQ m)) =
          Kf.mkQ (LocalizedModule.mkLinearMap (Submonoid.powers f) M m) := by
  let S := Submonoid.powers f
  have hle : K.localized S ≤ Kf :=
    le_maximal_nowhereDense_support Kf (K.localized S) hKf
      (nowhereDense_localized f K hK.prop)
  obtain ⟨L, hL, hinj⟩ := exists_injective_localization_lift f Kf
  have hLnow : IsNowhereDense
      {p : Module.support R M | p.val ∈ Module.support R L} := by
    apply nowhereDense_of_injective_localization f L hinj
    rw [hL]
    exact hKf.prop
  have hLK : L ≤ K := le_maximal_nowhereDense_support K L hK hLnow
  have heq : K.localized S = Kf := le_antisymm hle (by
    rw [← hL]
    exact (Submodule.localized'gi (Localization S) S
      (LocalizedModule.mkLinearMap S M)).gc.monotone_l hLK)
  cases heq
  refine ⟨(localizedQuotientEquiv S K).symm, fun m ↦ ?_⟩
  exact IsLocalizedModule.linearEquiv_symm_apply S (K.toLocalizedQuotient S)
    (LocalizedModule.mkLinearMap S (M ⧸ K)) (K.mkQ m)

end Module
