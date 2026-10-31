/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.RingTheory.Ideal.Operations
public import WeilConjectures.Blowup.Affine.Defs
import WeilConjectures.AlgebraicGeometry.BlowupDominationColonPower
import WeilConjectures.Blowup.Principalization
import WeilConjectures.Blowup.BlowupUniversal

/-!
# Blowup domination and ideal factorization

Source: Illusie--Laszlo--Orgogozo, Travaux de Gabber, Expose XX, section 4.4,
printed p.373 (blueprint: lem-per-blowup-domination-ideal-factorization).

For finitely generated ideals with the same radical, an affine blowup dominates
another precisely when a positive power of its centre factors through the other centre.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.AffineBlowup

private theorem finite_factor_of_mem_mul {R : Type u} [CommRing R]
    {J C : Ideal R} {x : R} (hx : x ∈ J * C) :
    ∃ L : Ideal R, L.FG ∧ L ≤ C ∧ x ∈ J * L := by
  refine Submodule.smul_induction_on hx ?_ ?_
  · intro j hj c hc
    exact ⟨Ideal.span {c}, Submodule.fg_span_singleton c,
      Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hc),
      Ideal.mul_mem_mul hj (Ideal.mem_span_singleton_self c)⟩
  · intro x y hx hy
    obtain ⟨L₁, hfg₁, hle₁, hx⟩ := hx
    obtain ⟨L₂, hfg₂, hle₂, hy⟩ := hy
    exact ⟨L₁ ⊔ L₂, Submodule.FG.sup hfg₁ hfg₂, sup_le hle₁ hle₂,
      Ideal.add_mem _ (Ideal.mul_mono le_rfl le_sup_left hx)
        (Ideal.mul_mono le_rfl le_sup_right hy)⟩

private theorem finite_factor_of_fg_le_mul {R : Type u} [CommRing R]
    {H J C : Ideal R} (hH : H.FG) (hle : H ≤ J * C) :
    ∃ L : Ideal R, L.FG ∧ L ≤ C ∧ H ≤ J * L := by
  induction H, hH using Submodule.fg_induction with
  | singleton x =>
    obtain ⟨L, hfg, hLC, hx⟩ := finite_factor_of_mem_mul
      (hle (Submodule.mem_span_singleton_self x))
    exact ⟨L, hfg, hLC, Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hx)⟩
  | sup H₁ H₂ _ _ ih₁ ih₂ =>
    obtain ⟨L₁, hfg₁, hLC₁, h₁⟩ := ih₁ (le_sup_left.trans hle)
    obtain ⟨L₂, hfg₂, hLC₂, h₂⟩ := ih₂ (le_sup_right.trans hle)
    exact ⟨L₁ ⊔ L₂, Submodule.FG.sup hfg₁ hfg₂, sup_le hLC₁ hLC₂,
      sup_le (h₁.trans (Ideal.mul_mono le_rfl le_sup_left))
        (h₂.trans (Ideal.mul_mono le_rfl le_sup_right))⟩

private theorem propagate_power {R : Type u} [CommRing R]
    (K : Ideal R) (D : ℕ → Ideal R)
    (hmul : ∀ n m, K ^ m * D n ≤ D (n + m))
    {I H : Ideal R} (hI : I ≤ K) (hH : H ≤ K)
    {a i N : ℕ} (hIa : I ^ a ≤ D a) (hai : a ≤ i) (hiN : i ≤ N) :
    I ^ i * H ^ (N - i) ≤ D N := by
  have hexp : a + (i - a + (N - i)) = N := by omega
  calc
    I ^ i * H ^ (N - i) = (I ^ a * I ^ (i - a)) * H ^ (N - i) := by
      rw [← pow_add, Nat.add_sub_of_le hai]
    _ ≤ (D a * K ^ (i - a)) * K ^ (N - i) :=
      Ideal.mul_mono (Ideal.mul_mono hIa (Ideal.pow_right_mono hI _))
        (Ideal.pow_right_mono hH _)
    _ = K ^ (i - a + (N - i)) * D a := by rw [pow_add]; ac_rfl
    _ ≤ D (a + (i - a + (N - i))) := hmul _ _
    _ = D N := congrArg D hexp

private theorem power_le_of_elementwise {R : Type u} [CommRing R]
    (K : Ideal R) (D : ℕ → Ideal R)
    (hmul : ∀ n m, K ^ m * D n ≤ D (n + m))
    (hlocal : ∀ b ∈ K, ∃ e : ℕ, 1 ≤ e ∧ b ^ e ∈ D e) (hK : K.FG) :
    ∃ N : ℕ, 1 ≤ N ∧ K ^ N ≤ D N := by
  suffices key : ∀ (I : Ideal R), I.FG → I ≤ K →
      ∃ N : ℕ, 1 ≤ N ∧ I ^ N ≤ D N from key K hK le_rfl
  intro I hI
  induction I, hI using Submodule.fg_induction with
  | singleton b =>
    intro hle
    obtain ⟨e, he, hb⟩ := hlocal b (hle (Submodule.mem_span_singleton_self b))
    refine ⟨e, he, ?_⟩
    rw [Ideal.submodule_span_eq, Ideal.span_singleton_pow]
    exact Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hb)
  | sup I H _ _ ihI ihH =>
    intro hle
    have hI : I ≤ K := le_sup_left.trans hle
    have hH : H ≤ K := le_sup_right.trans hle
    obtain ⟨a, ha, hIa⟩ := ihI hI
    obtain ⟨b, hb, hHb⟩ := ihH hH
    refine ⟨a + b, by omega, ?_⟩
    rw [← Ideal.add_eq_sup, add_pow, Ideal.sum_eq_sup]
    apply Finset.sup_le
    intro i hi
    have hiN : i ≤ a + b := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
    refine Ideal.mul_le_left.trans ?_
    by_cases hai : a ≤ i
    · exact propagate_power K D hmul hI hH hIa hai hiN
    · have hbi : b ≤ a + b - i := by omega
      have heq : a + b - (a + b - i) = i := by omega
      simpa only [heq, mul_comm] using
        propagate_power K D hmul hH hI hHb hbi (Nat.sub_le (a + b) i)

private theorem factor_of_elementwise_colon {R : Type u} [CommRing R]
    (J K : Ideal R) (hK : K.FG)
    (hlocal : ∀ b ∈ K, ∃ e : ℕ, 1 ≤ e ∧ b ^ e ∈ J * (K ^ e).colon (J : Set R)) :
    ∃ (n : ℕ) (L : Ideal R), 1 ≤ n ∧ L.FG ∧ K ^ n = J * L := by
  let C (n : ℕ) := (K ^ n).colon (J : Set R)
  let D (n : ℕ) := J * C n
  have hD : ∀ n, D n ≤ K ^ n := by
    intro n
    apply Ideal.mul_le.mpr
    intro j hj c hc
    simpa only [mul_comm, smul_eq_mul] using (Submodule.mem_colon.mp hc) j hj
  have hC : ∀ n m, K ^ m * C n ≤ C (n + m) := by
    intro n m
    apply Ideal.mul_le.mpr
    intro k hk c hc
    apply Submodule.mem_colon.mpr
    intro j hj
    have hprod := Ideal.mul_mem_mul ((Submodule.mem_colon.mp hc) j hj) hk
    simpa only [smul_eq_mul, ← pow_add, mul_assoc, mul_left_comm, mul_comm] using hprod
  have hmul : ∀ n m, K ^ m * D n ≤ D (n + m) := by
    intro n m
    calc
      K ^ m * D n = J * (K ^ m * C n) := by dsimp [D]; ac_rfl
      _ ≤ J * C (n + m) := Ideal.mul_mono le_rfl (hC n m)
  obtain ⟨n, hn, hle⟩ := power_le_of_elementwise K D hmul hlocal hK
  obtain ⟨L, hfg, hLC, hL⟩ := finite_factor_of_fg_le_mul hK.pow hle
  exact ⟨n, L, hn, hfg, hL.antisymm ((Ideal.mul_mono le_rfl hLC).trans (hD n))⟩

private noncomputable def centre {R : Type u} [CommRing R] (J : Ideal R) :
    (Spec (.of R)).IdealSheafData :=
  Scheme.IdealSheafData.ofIdealTop (J.map (Scheme.ΓSpecIso (.of R)).inv.hom)

private theorem centre_mul {R : Type u} [CommRing R] (J L : Ideal R) :
    centre (J * L) = centre J * centre L := by
  apply Scheme.IdealSheafData.ext_of_isAffine
  simp [centre, Scheme.IdealSheafData.ideal_mul, Ideal.map_mul]

private theorem centre_pow {R : Type u} [CommRing R] (K : Ideal R) (n : ℕ) :
    centre (K ^ n) = centre K ^ n := by
  apply Scheme.IdealSheafData.ext_of_isAffine
  simp [centre, Scheme.IdealSheafData.ideal_pow, Ideal.map_pow]

private theorem isIso_hom_of_ringEquiv {A B : Type u} [CommRing A] [CommRing B]
    (e : A ≃+* B) (I : Ideal A) (J : Ideal B) (h : I.map e.toRingHom = J) :
    IsIso (hom e.toRingHom h) := by
  have hcomp : e.symm.toRingHom.comp e.toRingHom = RingHom.id A := by
    ext a
    exact e.symm_apply_apply a
  have hcomp' : e.toRingHom.comp e.symm.toRingHom = RingHom.id B := by
    ext b
    exact e.apply_symm_apply b
  have h' : J.map e.symm.toRingHom = I := by
    rw [← h, Ideal.map_map, hcomp, Ideal.map_id]
  refine ⟨⟨hom e.symm.toRingHom h', ?_, ?_⟩⟩
  · rw [← hom_comp]
    exact (hom_congr hcomp' _).trans hom_id
  · rw [← hom_comp]
    exact (hom_congr hcomp _).trans hom_id

private theorem exists_global_comparison {R : Type u} [CommRing R] (J : Ideal R) :
    ∃ g : AffineBlowup J ⟶ (centre J).blowup,
      IsIso g ∧ g ≫ (centre J).blowupMap = toSpec J := by
  let X := Spec (.of R)
  let I := centre J
  let U : X.affineOpens := ⟨⊤, isAffineOpen_top X⟩
  let e := (Scheme.ΓSpecIso (.of R)).commRingCatIsoToRingEquiv
  have hI : (I.ideal U).map e.toRingHom = J := by
    simp only [U, I, centre, Scheme.IdealSheafData.ideal_top_ofIdealTop]
    rw [Ideal.map_map]
    have hid : e.toRingHom.comp (Scheme.ΓSpecIso (.of R)).inv.hom = RingHom.id R := by
      ext r
      exact congrArg (fun f : CommRingCat.of R ⟶ CommRingCat.of R ↦ f r)
        (Scheme.ΓSpecIso (.of R)).inv_hom_id
    rw [hid, Ideal.map_id]
  let f := hom e.toRingHom hI
  have : IsIso f := isIso_hom_of_ringEquiv e (I.ideal U) J hI
  have : IsIso (I.blowupι U) :=
    isIso_of_isOpenImmersion_of_opensRange_eq_top _ (by
      rw [← I.blowupMap_preimage U]
      exact Scheme.Hom.preimage_top _)
  refine ⟨f ≫ I.blowupι U, inferInstance, ?_⟩
  change f ≫ I.blowupι U ≫ I.blowupMap = toSpec J
  rw [I.blowupι_blowupMap, I.blowupNatTrans_app, Category.assoc,
    IsAffineOpen.isoSpec_inv_ι, ← Category.assoc, hom_toSpec]
  have htop : Spec.map (CommRingCat.ofHom e.toRingHom) ≫ U.2.fromSpec = 𝟙 X := by
    change Spec.map (Scheme.ΓSpecIso (.of R)).hom ≫
      (isAffineOpen_top X).fromSpec = 𝟙 X
    rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv,
      ← Spec.map_comp, Iso.inv_hom_id, Spec.map_id]
  rw [Category.assoc, htop, Category.comp_id]

private theorem hom_of_pow_factorization {R : Type u} [CommRing R]
    (J K L : Ideal R) (n : ℕ) (heq : K ^ n = J * L) :
    ∃ f : AffineBlowup K ⟶ AffineBlowup J, f ≫ toSpec J = toSpec K := by
  obtain ⟨gK, hgKiso, hgK⟩ := exists_global_comparison K
  obtain ⟨gJ, hgJiso, hgJ⟩ := exists_global_comparison J
  have : IsIso gK := hgKiso
  have : IsIso gJ := hgJiso
  have hK : ((centre K).comap (toSpec K)).IsInvertible := by
    rw [← hgK, Scheme.IdealSheafData.comap_comp]
    exact (centre K).isInvertible_comap_blowupMap.comap_of_isOpenImmersion gK
  have hprod :
      (((centre J).comap (toSpec K)) * ((centre L).comap (toSpec K))).IsInvertible := by
    rw [← Scheme.IdealSheafData.comap_mul, ← centre_mul, ← heq, centre_pow,
      Scheme.IdealSheafData.comap_pow]
    exact hK.pow n
  obtain ⟨h, hh⟩ := (centre J).exists_lift_blowup hprod.of_mul_left
  refine ⟨h ≫ inv gJ, ?_⟩
  rw [Category.assoc, ← hgJ, IsIso.inv_hom_id_assoc, hh]

/-- Domination of affine blowups with equal-support finitely generated centres is
characterized by factorization of a positive power of the source centre.

Source: Illusie--Laszlo--Orgogozo, Travaux de Gabber, Expose XX, section 4.4,
printed p.373 (blueprint: lem-per-blowup-domination-ideal-factorization).

Proof plan:
1. Choose finite generating lists for `K` and `J`, adjoining zero if necessary.
   By `prop-nagata-affine-blowup-chart-cover`, the charts `A_i = R[K/b_i]` cover
   `AffineBlowup K`. By `def-nagata-blowup-chart-ring`, their elements are fractions
   `c / b_i^d` with `c ∈ K^d`. Thus `K A_i = b_i A_i`, and `b_i` is regular,
   including on zero-ring charts. Use `lem-pc-ideal-sheaf-comap-affine-extension`
   to identify the extended ideal of any centre with its ring-theoretic extension.
2. Given the morphism over `Spec R`, principalization of `J` on its own blowup
   (`thm-nagata-blowup-principalizes-center`) makes its extension on each source
   chart locally principal. Radical equality gives `b_i^a ∈ J` for some `a ≥ 1`.
   If `v` is a local generator of `J A_i`, write `b_i^a = v w`; regularity of `b_i`
   implies regularity of `v`. Hence this ideal sheaf is an invertible module
   (`def-sc-invertible-module`); no general preservation of Cartier divisors by
   arbitrary pullback is asserted.
3. By `lem-sc-affine-invertible-sections`, evaluation on this chart gives finitely
   many `x_ν ∈ J A_i` and linear functionals `φ_ν` with `∑ φ_ν(x_ν) = 1`.
   In `R[1/b_i]` put `z_ν = φ_ν(b_i^a) / b_i^a`. Linearity gives
   `φ_ν(x) = x z_ν`. Writing `x_ν = ∑ j_t q_{tν}` gives fractions `w_t` such
   that `∑ j_t w_t = 1` and every `j_s w_t` lies in `A_i`.
4. Put `C_d = (K^d : J)`. Choose a common positive denominator `b_i^e` for the
   finitely many `w_t` and `j_s w_t`, with the latter numerators in `K^e`.
   Clear the finitely many localization equalities by one further power `b_i^v`.
   Then `e_i = e + v ≥ 1` and the cleared numerators belong to `C_{e_i}`,
   giving `b_i^{e_i} ∈ J C_{e_i}` as an equality in `R` itself.
5. Write `D_d = J C_d`. Then `D_d ≤ K^d` and `K^m D_d ≤ D_{d+m}`.
   For `N = 1 + ∑ (e_i - 1)`, every degree-`N` monomial in the generators of
   `K` has some exponent at least `e_i`, so lies in `D_N`. Therefore `K^N = J C_N`.
6. Express the finitely many monomial generators of `K^N` as finite sums of
   products from `J C_N`. The ideal `L` generated by all the finitely many
   coefficients from `C_N` satisfies `K^N = J L` and is finitely generated.
7. Conversely, if `K^n = J L` with `n ≥ 1`, principalization makes the extension
   of `K^n` on `AffineBlowup K` an effective Cartier ideal. Extension commutes
   with products and powers by `lem-pc-ideal-sheaf-comap-affine-extension`.
   By `lemma-nagata-ideal-invertible-product-factor`, the extension of `J` is
   therefore an effective Cartier ideal too.
8. Apply `thm-nagata-blowup-universal-property` to the ideal sheaf of `J` and
   the structure map of `AffineBlowup K`. The resulting lift lands in the global
   blowup. For the affine base, the terminal affine open identifies the colimit
   of `def-nagata-global-blowup` with the affine model of `def-nagata-affine-blowup`,
   compatibly with the structure map. This gives the required morphism over `Spec R`.
-/
theorem exists_hom_iff_exists_pow_eq_mul_of_radical_eq
    {R : Type u} [CommRing R] (J K : Ideal R) (hJ : J.FG) (hK : K.FG)
    (hrad : J.radical = K.radical) :
    (∃ f : AffineBlowup K ⟶ AffineBlowup J, f ≫ toSpec J = toSpec K) ↔
      ∃ (n : ℕ) (L : Ideal R), 1 ≤ n ∧ L.FG ∧ K ^ n = J * L := by
  constructor
  · rintro ⟨f, hf⟩
    have hKJ : K ≤ J.radical := by
      rw [hrad]
      exact Ideal.le_radical
    exact factor_of_elementwise_colon J K hK
      (exists_pow_mem_mul_colon_of_hom J K hJ hKJ f hf)
  · rintro ⟨n, L, _hn, _hL, heq⟩
    exact hom_of_pow_factorization J K L n heq

end AlgebraicGeometry.AffineBlowup
