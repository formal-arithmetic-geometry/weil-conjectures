/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Blowup.Affine.Functoriality
public import WeilConjectures.Blowup.AdmissibleBlowup
public import WeilConjectures.Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.AlgebraicGeometry.Pullbacks

import WeilConjectures.AlgebraicGeometry.BlowupDominationIdealFactorization
import Mathlib.RingTheory.Finiteness.Ideal
import Mathlib.RingTheory.AdicCompletion.Completeness
import WeilConjectures.AlgebraicGeometry.BlowupClosedFiberOfReesReduction
import WeilConjectures.Blowup.Density
import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Affine
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper

/-! # Full-support admissible blowups and completion

Source: ILO, Exposé XX, §4.4, printed pp. 373–374
(blueprint: lem-per-admissible-modification-system).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AdmissibleModificationSystem

variable {A : Type u} [CommRing A]

/-- The full-support admissible ideals: finite generation and equality of vanishing loci.
Source: ILO XX §4.4, p. 373 (blueprint: lem-per-admissible-modification-system). -/
def Index (I : Ideal A) : Type u :=
  {J : Ideal A // J.FG ∧ PrimeSpectrum.zeroLocus (J : Set A) = PrimeSpectrum.zeroLocus (I : Set A)}

/-- Domination is existence of a morphism of the specified affine blowups over `Spec A`.
Source: ILO XX §4.4, p. 373 (blueprint: lem-per-admissible-modification-system). -/
def Dominates (J K : Ideal A) : Prop :=
  ∃ f : AffineBlowup K ⟶ AffineBlowup J,
    f ≫ AffineBlowup.toSpec J = AffineBlowup.toSpec K

/-- The preserved open `Spec A ∖ V(I)`, as the union of principal opens for elements of I.
Source: ILO XX §4.4, p. 373 (blueprint: lem-per-admissible-modification-system). -/
noncomputable def puncturedOpen (I : Ideal A) : (Spec (.of A)).Opens :=
  ⨆ a : I, PrimeSpectrum.basicOpen (a : A)

/-- The closed fibre of the specified blowup over `Spec (A/I)`.
Source: ILO XX §4.4, pp. 373–374 (blueprint: lem-per-admissible-modification-system). -/
noncomputable def closedFiber (I J : Ideal A) : Scheme.{u} :=
  pullback (AffineBlowup.toSpec J) (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))

/-- A Rees power modulo `I^m` times that power. The module is an ideal, not its ambient ring.
Source: ILO XX §4.4, final Note, p. 374
(blueprint: lem-per-admissible-modification-system). -/
abbrev powerQuotient (I L : Ideal A) (m : ℕ) : Type u :=
  ↥L ⧸ (I ^ m • (⊤ : Submodule A ↥L))

/-- Reduction modulo `I^m` of the existing Rees algebra, with its ordinary ring structure.
Source: ILO XX §4.4, final Note, p. 374
(blueprint: lem-per-admissible-modification-system). -/
abbrev reesQuotient (I J : Ideal A) (m : ℕ) : Type u :=
  reesAlgebra J ⧸ (I ^ m).map (algebraMap A (reesAlgebra J))

private theorem isIso_hom_ringEquiv {B : Type u} [CommRing B] (e : A ≃+* B) (J : Ideal A) :
    IsIso (AffineBlowup.hom e.toRingHom (I := J) rfl) := by
  have hback : (J.map e.toRingHom).map e.symm.toRingHom = J := by
    rw [Ideal.map_map]
    have hcomp : e.symm.toRingHom.comp e.toRingHom = RingHom.id A := by
      ext a
      exact e.symm_apply_apply a
    rw [hcomp, Ideal.map_id]
  let inv := AffineBlowup.hom e.symm.toRingHom hback
  refine ⟨⟨inv, ?_, ?_⟩⟩
  · rw [← AffineBlowup.hom_comp]
    exact (AffineBlowup.hom_congr (by ext a; exact e.apply_symm_apply a) _).trans
      AffineBlowup.hom_id
  · rw [← AffineBlowup.hom_comp]
    exact (AffineBlowup.hom_congr (by ext a; exact e.symm_apply_apply a) _).trans
      AffineBlowup.hom_id

private theorem compl_zeroLocus (J : Ideal A) :
    (PrimeSpectrum.zeroLocus (J : Set A))ᶜ =
      (⨆ a : J, PrimeSpectrum.basicOpen (a : A) :
        TopologicalSpace.Opens (PrimeSpectrum A)) := by
  ext x
  simp only [Set.mem_compl_iff, TopologicalSpace.Opens.coe_iSup, Set.mem_iUnion]
  change (¬ (J : Set A) ⊆ x.asIdeal) ↔ ∃ a : J, (a : A) ∉ x.asIdeal
  simp only [Set.subset_def, not_forall, Subtype.exists, exists_prop, SetLike.mem_coe]

/-- The complement of the centre embeds as a schematically dense open in the affine blowup.

Source: ILO, Exposé XX, §4.4, printed p. 373
(blueprint: lem-per-admissible-modification-system).

Proof: form the ideal sheaf associated with `J` on `Spec A`. Its global blowup is identified
with the affine Rees blowup using the chart over the terminal affine open and the canonical
isomorphism between `A` and the global sections of `Spec A`. The blowup complement theorem
identifies the preimage of the complement of the centre with that complement. The extended
centre is an invertible ideal, so the inclusion of its complement is schematically dominant:
on a principalization chart this is the injective localization at a non-zero-divisor.
Compose the inverse of the restricted blowup map with this inclusion and transport through
the affine comparison. Composition with an isomorphism preserves injectivity on sections.
This argument also applies to the zero ring, a nilpotent centre, and the unit centre.
-/
private theorem exists_dense_open (J : Ideal A) (hJ : J.FG) :
    ∃ j : (⨆ a : J, PrimeSpectrum.basicOpen (a : A) :
        (Spec (.of A)).Opens).toScheme ⟶ AffineBlowup J,
      IsOpenImmersion j ∧
      j ≫ AffineBlowup.toSpec J =
        (⨆ a : J, PrimeSpectrum.basicOpen (a : A) : (Spec (.of A)).Opens).ι ∧
      ∀ W : (AffineBlowup J).Opens, Function.Injective (j.app W) := by
  classical
  let X := Spec (.of A)
  let T : X.affineOpens := ⟨⊤, isAffineOpen_top X⟩
  let e := (Scheme.ΓSpecIso (.of A)).symm.commRingCatIsoToRingEquiv
  let C : X.IdealSheafData := .ofIdealTop (J.map e.toRingHom)
  have hCtop : C.ideal T = J.map e.toRingHom :=
    Scheme.IdealSheafData.ideal_top_ofIdealTop _
  have hb₀ : IsIso (C.blowupι T) := by
    apply isIso_of_isOpenImmersion_of_opensRange_eq_top
    rw [← C.blowupMap_preimage T]
    exact C.blowupMap.preimage_top
  let b : AffineBlowup (J.map e.toRingHom) ⟶ C.blowup :=
    eqToHom (congrArg AffineBlowup hCtop.symm) ≫ C.blowupι T
  have hb : IsIso b := inferInstance
  let a := AffineBlowup.hom e.toRingHom (I := J) rfl
  have ha : IsIso a := isIso_hom_ringEquiv e J
  let c := inv a ≫ b
  have hc : IsIso c := inferInstance
  have htransport {L M : Ideal Γ(X, ⊤)} (h : L = M) :
      eqToHom (congrArg AffineBlowup h) ≫ AffineBlowup.toSpec M =
        AffineBlowup.toSpec L := by
    subst h
    simp
  have hbase : c ≫ C.blowupMap = AffineBlowup.toSpec J := by
    apply (cancel_epi a).mp
    simp only [c, Category.assoc, IsIso.hom_inv_id_assoc]
    dsimp only [b]
    rw [Category.assoc, C.blowupι_blowupMap T, C.blowupNatTrans_app T,
      Category.assoc, IsAffineOpen.isoSpec_inv_ι,
      ← Category.assoc, htransport hCtop.symm, IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv]
    exact (AffineBlowup.hom_toSpec e.toRingHom rfl).symm
  have hsupport : (C.support : Set X) = PrimeSpectrum.zeroLocus (J : Set A) := by
    rw [Scheme.IdealSheafData.coe_support_ofIdealTop, Spec_zeroLocus]
    change PrimeSpectrum.zeroLocus ((J.map e.toRingHom).comap e.toRingHom : Set A) = _
    rw [Ideal.comap_map_of_bijective e.toRingHom e.bijective]
  have hU : C.support.compl =
      (⨆ a : J, PrimeSpectrum.basicOpen (a : A) : X.Opens) := by
    apply TopologicalSpace.Opens.ext
    exact (congrArg Set.compl hsupport).trans (compl_zeroLocus J)
  let U : X.Opens := C.support.compl
  let V := C.blowupMap ⁻¹ᵁ U
  let r := C.blowupMap ∣_ U
  have hr : IsIso r := C.isIso_blowupMap_restrict_support_compl
  have hd : IsSchemeTheoreticallyDominant V.ι := by
    have he : C.blowupMap ⁻¹ᵁ C.support.compl =
        (C.comap C.blowupMap).support.compl := by
      ext y
      simp [Scheme.IdealSheafData.support_comap]
    change IsSchemeTheoreticallyDominant (C.blowupMap ⁻¹ᵁ C.support.compl).ι
    rw [he]
    exact C.isInvertible_comap_blowupMap.isSchemeTheoreticallyDominant_compl_support
  have hcompact : IsCompact (U : Set X) := by
    change IsCompact (C.support : Set X)ᶜ
    rw [hsupport]
    exact (PrimeSpectrum.isRetrocompact_zeroLocus_compl_of_fg hJ).isCompact
  have hcompactSpace : CompactSpace U.toScheme := isCompact_iff_compactSpace.mp hcompact
  let j₀ := inv r ≫ V.ι ≫ inv c
  have hj₀ : IsOpenImmersion j₀ := inferInstance
  have hjdense : IsSchemeTheoreticallyDominant j₀ := inferInstance
  have hsep : Scheme.IsSeparated (AffineBlowup J) := by
    unfold AffineBlowup
    infer_instance
  have hjqc : QuasiCompact j₀ := quasiCompact_of_compactSpace j₀
  have hjbase : j₀ ≫ AffineBlowup.toSpec J = U.ι := by
    rw [← hbase]
    simp only [j₀, Category.assoc, IsIso.inv_hom_id_assoc]
    rw [← morphismRestrict_ι]
    exact IsIso.inv_hom_id_assoc r U.ι
  let u : (⨆ a : J, PrimeSpectrum.basicOpen (a : A) : X.Opens).toScheme ≅ U.toScheme :=
    eqToIso (congrArg Scheme.Opens.toScheme hU.symm)
  refine ⟨u.hom ≫ j₀, inferInstance, ?_, ?_⟩
  · rw [Category.assoc, hjbase]
    have heq : ∀ (U₁ U₂ : X.Opens) (h : U₁ = U₂),
        eqToHom (congrArg Scheme.Opens.toScheme h) ≫ U₂.ι = U₁.ι := by
      intro U₁ U₂ h
      subst h
      simp
    exact heq _ _ hU.symm
  · intro W
    exact (u.hom ≫ j₀).app_injective W


private theorem filtered (I : Ideal A) (hI : I.FG) :
    Nonempty (Index I) ∧
      IsPreorder (Index I) (fun J K ↦ Dominates J.val K.val) ∧
      Directed (fun J K : Index I ↦ Dominates J.val K.val) id := by
  refine ⟨⟨⟨I, hI, rfl⟩⟩, { refl := ?_, trans := ?_ }, ?_⟩
  · intro J
    exact ⟨𝟙 _, Category.id_comp _⟩
  · intro J K L hJK hKL
    obtain ⟨f, hf⟩ := hJK
    obtain ⟨g, hg⟩ := hKL
    exact ⟨g ≫ f, by rw [Category.assoc, hf, hg]⟩
  · intro J K
    let L : Index I := ⟨J.val * K.val, J.property.1.mul K.property.1,
      by rw [PrimeSpectrum.zeroLocus_mul, J.property.2, K.property.2, Set.union_self]⟩
    have hrad (H : Index I) : H.val.radical = L.val.radical :=
      PrimeSpectrum.zeroLocus_eq_iff.mp (H.property.2.trans L.property.2.symm)
    refine ⟨L, ?_, ?_⟩
    · exact (AffineBlowup.exists_hom_iff_exists_pow_eq_mul_of_radical_eq
        J.val L.val J.property.1 L.property.1 (hrad J)).mpr
          ⟨1, K.val, le_rfl, K.property.1, by simp [L]⟩
    · exact (AffineBlowup.exists_hom_iff_exists_pow_eq_mul_of_radical_eq
        K.val L.val K.property.1 L.property.1 (hrad K)).mpr
          ⟨1, J.val, le_rfl, J.property.1, by simp [L, mul_comm]⟩

private theorem ker_eval (I : Ideal A) (hI : I.FG) (n : ℕ) :
    RingHom.ker (AdicCompletion.evalₐ I n).toRingHom =
      (I ^ n).map (algebraMap A (AdicCompletion I A)) := by
  ext x
  trans x ∈ (AdicCompletion.eval I A n).ker
  · have eq : I ^ n * ⊤ = I ^ n := by simp
    have hinj : Function.Injective (Ideal.Quotient.factor (le_of_eq eq)) := by
      simpa [RingHom.injective_iff_ker_eq_bot, Ideal.Quotient.factor_ker]
        using Ideal.map_mk_eq_bot_of_le (le_of_eq eq.symm)
    simpa [← AdicCompletion.factor_eval_eq_evalₐ] using map_eq_zero_iff _ hinj
  · simp [← AdicCompletion.pow_smul_top_eq_ker_eval hI]

private theorem eval_comp (I : Ideal A) (n : ℕ) :
    (AdicCompletion.evalₐ I n).toRingHom.comp (algebraMap A (AdicCompletion I A)) =
      Ideal.Quotient.mk (I ^ n) := by
  ext a
  exact AdicCompletion.evalₐ_of I n a

private theorem comap_map (I : Ideal A) (hI : I.FG) (H : Ideal A)
    (n : ℕ) (hn : I ^ n ≤ H) :
    (H.map (algebraMap A (AdicCompletion I A))).comap
      (algebraMap A (AdicCompletion I A)) = H := by
  let f := algebraMap A (AdicCompletion I A)
  let q := (AdicCompletion.evalₐ I n).toRingHom
  have hker : RingHom.ker q ≤ H.map f := (ker_eval I hI n).le.trans (Ideal.map_mono hn)
  have heq : (H.map f).comap f =
      ((H.map f).map q).comap (q.comp f) := by
    rw [← Ideal.comap_comap, Ideal.comap_map_of_surjective q
      (AdicCompletion.surjective_evalₐ I n), ← RingHom.ker_eq_comap_bot,
      sup_eq_left.mpr hker]
  rw [heq, Ideal.map_map, eval_comp, Ideal.comap_map_mk hn]

private theorem approximate (I : Ideal A) (hI : I.FG) (n : ℕ)
    (x : AdicCompletion I A) :
    ∃ a : A, x - algebraMap A (AdicCompletion I A) a ∈
      (I ^ n).map (algebraMap A (AdicCompletion I A)) := by
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ I n x)
  refine ⟨a, ?_⟩
  rw [← ker_eval I hI n]
  change AdicCompletion.evalₐ I n (x - algebraMap A (AdicCompletion I A) a) = 0
  rw [map_sub, AlgHom.commutes, Ideal.Quotient.algebraMap_eq, ha, sub_self]

private theorem map_comap (I : Ideal A) (hI : I.FG)
    (H : Ideal (AdicCompletion I A)) (n : ℕ)
    (hn : (I ^ n).map (algebraMap A (AdicCompletion I A)) ≤ H) :
    (H.comap (algebraMap A (AdicCompletion I A))).map
      (algebraMap A (AdicCompletion I A)) = H := by
  let f := algebraMap A (AdicCompletion I A)
  apply le_antisymm Ideal.map_comap_le
  intro x hx
  obtain ⟨a, ha⟩ := approximate I hI n x
  have haf : f a ∈ H := by
    simpa only [sub_sub_cancel] using H.sub_mem hx (hn ha)
  have hfa : f a ∈ (H.comap f).map f := Ideal.mem_map_of_mem f haf
  have hpow : I ^ n ≤ H.comap f := Ideal.map_le_iff_le_comap.mp hn
  have hdiff : x - f a ∈ (H.comap f).map f := (Ideal.map_mono hpow) ha
  simpa only [sub_add_cancel] using add_mem hdiff hfa

private theorem fg_comap (I : Ideal A) (hI : I.FG)
    (H : Ideal (AdicCompletion I A)) (hH : H.FG) (n : ℕ)
    (hn : (I ^ n).map (algebraMap A (AdicCompletion I A)) ≤ H) :
    (H.comap (algebraMap A (AdicCompletion I A))).FG := by
  let f := algebraMap A (AdicCompletion I A)
  let q := (AdicCompletion.evalₐ I n).toRingHom
  have hpow : I ^ n ≤ H.comap f := Ideal.map_le_iff_le_comap.mp hn
  have heq : (H.comap f).map (Ideal.Quotient.mk (I ^ n)) = H.map q := by
    rw [← eval_comp I n, ← Ideal.map_map, map_comap I hI H n hn]
  apply Ideal.fg_of_fg_map_of_fg_inf_ker_of_surjective
    (f := Ideal.Quotient.mk (I ^ n))
  · rw [heq]
    exact hH.map q
  · rw [Ideal.mk_ker, inf_eq_right.mpr hpow]
    exact hI.pow
  · exact Ideal.Quotient.mk_surjective

private theorem positive_power_le (I J : Ideal A) (hI : I.FG)
    (hrad : I.radical = J.radical) : ∃ n : ℕ, 1 ≤ n ∧ I ^ n ≤ J := by
  obtain ⟨n, hn⟩ := Ideal.exists_pow_le_of_le_radical_of_fg
    (I.le_radical.trans_eq hrad) hI
  exact ⟨n + 1, Nat.succ_pos n, (Ideal.pow_le_pow_right (Nat.le_succ n)).trans hn⟩

private theorem support_map {B : Type u} [CommRing B] (f : A →+* B)
    (I J : Ideal A)
    (h : PrimeSpectrum.zeroLocus (J : Set A) = PrimeSpectrum.zeroLocus (I : Set A)) :
    PrimeSpectrum.zeroLocus (J.map f : Set B) =
      PrimeSpectrum.zeroLocus (I.map f : Set B) := by
  simpa only [Ideal.map, PrimeSpectrum.zeroLocus_span,
    ← PrimeSpectrum.preimage_comap_zeroLocus] using
      congrArg (fun S ↦ PrimeSpectrum.comap f ⁻¹' S) h

private theorem quotient_comparison (I : Ideal A) (hI : I.FG)
    (H : Ideal A) (n : ℕ) (hn : I ^ n ≤ H) :
    ∃ e : A ⧸ H ≃+* AdicCompletion I A ⧸
        H.map (algebraMap A (AdicCompletion I A)),
      ∀ a : A, e (Ideal.Quotient.mk H a) =
        Ideal.Quotient.mk _ (algebraMap A (AdicCompletion I A) a) := by
  let f := algebraMap A (AdicCompletion I A)
  let g := Ideal.quotientMap (H.map f) f Ideal.le_comap_map
  have hinj : Function.Injective g := Ideal.quotientMap_injective'
    (comap_map I hI H n hn).le
  have hsurj : Function.Surjective g := by
    intro y
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨a, ha⟩ := approximate I hI n x
    refine ⟨Ideal.Quotient.mk H a, ?_⟩
    change Ideal.Quotient.mk (H.map f) (f a) = Ideal.Quotient.mk (H.map f) x
    apply Eq.symm
    exact Ideal.Quotient.eq.mpr (Ideal.map_mono hn ha)
  exact ⟨RingEquiv.ofBijective g ⟨hinj, hsurj⟩, fun _ ↦ rfl⟩

private noncomputable def extendIndex (I : Ideal A) :
    Index I → Index (I.map (algebraMap A (AdicCompletion I A))) :=
  fun J ↦ ⟨J.val.map (algebraMap A (AdicCompletion I A)),
    J.property.1.map _, support_map _ I J.val J.property.2⟩

private theorem index_equiv (I : Ideal A) (hI : I.FG) :
    ∃ e : Index I ≃ Index (I.map (algebraMap A (AdicCompletion I A))),
      ∀ J : Index I, (e J).val = J.val.map (algebraMap A (AdicCompletion I A)) := by
  classical
  let f := algebraMap A (AdicCompletion I A)
  have hinj : Function.Injective (extendIndex I) := by
    intro J K hJK
    obtain ⟨r, _, hr⟩ := positive_power_le I J.val hI
      (PrimeSpectrum.zeroLocus_eq_iff.mp J.property.2).symm
    obtain ⟨s, _, hs⟩ := positive_power_le I K.val hI
      (PrimeSpectrum.zeroLocus_eq_iff.mp K.property.2).symm
    apply Subtype.ext
    have heq := congrArg (fun L ↦ Ideal.comap f (Subtype.val L)) hJK
    change (J.val.map f).comap f = (K.val.map f).comap f at heq
    rwa [comap_map I hI J.val r hr, comap_map I hI K.val s hs] at heq
  have hsurj : Function.Surjective (extendIndex I) := by
    intro H
    obtain ⟨r, _, hr⟩ := positive_power_le (I.map f) H.val (hI.map f)
      (PrimeSpectrum.zeroLocus_eq_iff.mp H.property.2).symm
    have hr' : (I ^ r).map f ≤ H.val := by rwa [Ideal.map_pow]
    have hrad : (H.val.comap f).radical = I.radical := by
      rw [← Ideal.comap_radical, PrimeSpectrum.zeroLocus_eq_iff.mp H.property.2,
        Ideal.comap_radical, comap_map I hI I 1 (by simp)]
    refine ⟨⟨H.val.comap f, fg_comap I hI H.val H.property.1 r hr',
      PrimeSpectrum.zeroLocus_eq_iff.mpr hrad⟩, ?_⟩
    exact Subtype.ext (map_comap I hI H.val r hr')
  exact ⟨Equiv.ofBijective (extendIndex I) ⟨hinj, hsurj⟩, fun _ ↦ rfl⟩

private theorem domination_map_iff (I : Ideal A) (hI : I.FG) (J K : Index I) :
    Dominates J.val K.val ↔
      Dominates (J.val.map (algebraMap A (AdicCompletion I A)))
        (K.val.map (algebraMap A (AdicCompletion I A))) := by
  let f := algebraMap A (AdicCompletion I A)
  have hrad : J.val.radical = K.val.radical :=
    PrimeSpectrum.zeroLocus_eq_iff.mp (J.property.2.trans K.property.2.symm)
  have hrad' : (J.val.map f).radical = (K.val.map f).radical :=
    PrimeSpectrum.zeroLocus_eq_iff.mp
      ((support_map f I J.val J.property.2).trans
        (support_map f I K.val K.property.2).symm)
  rw [Dominates, Dominates,
    AffineBlowup.exists_hom_iff_exists_pow_eq_mul_of_radical_eq
      J.val K.val J.property.1 K.property.1 hrad,
    AffineBlowup.exists_hom_iff_exists_pow_eq_mul_of_radical_eq
      (J.val.map f) (K.val.map f) (J.property.1.map f) (K.property.1.map f) hrad']
  constructor
  · rintro ⟨n, L, hn, hL, heq⟩
    refine ⟨n, L.map f, hn, hL.map f, ?_⟩
    rw [← Ideal.map_pow, heq, Ideal.map_mul]
  · rintro ⟨n, L, hn, hL, heq⟩
    obtain ⟨r, _, hr⟩ := positive_power_le I K.val hI
      (PrimeSpectrum.zeroLocus_eq_iff.mp K.property.2).symm
    obtain ⟨s, _, hs⟩ := positive_power_le I J.val hI
      (PrimeSpectrum.zeroLocus_eq_iff.mp J.property.2).symm
    have hLpow : (I ^ (r * n)).map f ≤ L := by
      calc
        (I ^ (r * n)).map f = ((I ^ r).map f) ^ n := by
          rw [Ideal.map_pow, pow_mul, Ideal.map_pow]
        _ ≤ (K.val.map f) ^ n := pow_le_pow_left' (Ideal.map_mono hr) n
        _ = J.val.map f * L := heq
        _ ≤ L := Ideal.mul_le_right
    let L₀ := L.comap f
    have hL₀ : L₀.FG := fg_comap I hI L hL (r * n) hLpow
    have hLL : L₀.map f = L := map_comap I hI L (r * n) hLpow
    have hprod : I ^ (s + r * n) ≤ J.val * L₀ := by
      rw [pow_add]
      exact mul_le_mul' hs (Ideal.map_le_iff_le_comap.mp hLpow)
    have hKpow : I ^ (r * n) ≤ K.val ^ n := by
      rw [pow_mul]
      exact pow_le_pow_left' hr n
    have hmap : (K.val ^ n).map f = (J.val * L₀).map f := by
      rw [Ideal.map_pow, Ideal.map_mul, hLL, heq]
    have hdesc := congrArg (Ideal.comap f) hmap
    rw [comap_map I hI (K.val ^ n) (r * n) hKpow,
      comap_map I hI (J.val * L₀) (s + r * n) hprod] at hdesc
    exact ⟨n, L₀, hn, hL₀, hdesc⟩

private theorem power_quotient_comparison (I : Ideal A) (hI : I.FG)
    (L : Ideal A) (r : ℕ) (hr : I ^ r ≤ L) (m : ℕ) :
    ∃ e : powerQuotient I L m ≃+
        powerQuotient (I.map (algebraMap A (AdicCompletion I A)))
          (L.map (algebraMap A (AdicCompletion I A))) m,
      ∀ x : L, e (Submodule.Quotient.mk x) =
        Submodule.Quotient.mk
          ⟨algebraMap A (AdicCompletion I A) x.val,
            Ideal.mem_map_of_mem (algebraMap A (AdicCompletion I A)) x.property⟩ := by
  let f := algebraMap A (AdicCompletion I A)
  let p : Submodule A L := I ^ m • ⊤
  let q : Submodule (AdicCompletion I A) (L.map f) := (I.map f) ^ m • ⊤
  let g : L →ₛₗ[f] L.map f :=
    { toFun := fun x ↦ ⟨f x.val, Ideal.mem_map_of_mem f x.property⟩
      map_add' := fun x y ↦ Subtype.ext (map_add f x.val y.val)
      map_smul' := fun a x ↦ Subtype.ext (map_mul f a x.val) }
  have hp (x : L) : x ∈ p ↔ x.val ∈ I ^ m * L := by
    exact Submodule.mem_smul_top_iff (I := I ^ m) L x
  have hq (y : L.map f) : y ∈ q ↔ y.val ∈ (I ^ m * L).map f := by
    change y ∈ (I.map f) ^ m • (⊤ : Submodule _ _) ↔ _
    rw [Submodule.mem_smul_top_iff]
    change y.val ∈ (I.map f) ^ m * L.map f ↔ _
    rw [Ideal.map_mul, Ideal.map_pow]
  have hprod : I ^ (m + r) ≤ I ^ m * L := by
    rw [pow_add]
    exact mul_le_mul' le_rfl hr
  have hg : p ≤ q.comap g := by
    intro x hx
    exact (hq (g x)).mpr (Ideal.mem_map_of_mem f ((hp x).mp hx))
  let gq := p.mapQ q g hg
  have hinj : Function.Injective gq := by
    apply (injective_iff_map_eq_zero gq).mpr
    intro x hx
    induction x using Submodule.Quotient.induction_on with
    | _ x =>
      have hzero : Submodule.Quotient.mk (g x) = (0 : (L.map f) ⧸ q) := hx
      have hmem := (hq (g x)).mp ((Submodule.Quotient.mk_eq_zero q).mp hzero)
      change x.val ∈ ((I ^ m * L).map f).comap f at hmem
      rw [comap_map I hI (I ^ m * L) (m + r) hprod] at hmem
      exact (Submodule.Quotient.mk_eq_zero p).mpr ((hp x).mpr hmem)
  have hsurj : Function.Surjective gq := by
    intro y
    induction y using Submodule.Quotient.induction_on with
    | _ y =>
      obtain ⟨a, ha⟩ := approximate I hI (m + r) y.val
      have hdiff : y.val - f a ∈ (I ^ m * L).map f := Ideal.map_mono hprod ha
      have hfa : f a ∈ L.map f := by
        have hdiff' : y.val - f a ∈ L.map f :=
          Ideal.map_mono Ideal.mul_le_right hdiff
        simpa only [sub_sub_cancel] using sub_mem y.property hdiff'
      have haL : a ∈ L := by
        change a ∈ (L.map f).comap f at hfa
        rwa [comap_map I hI L r hr] at hfa
      refine ⟨Submodule.Quotient.mk ⟨a, haL⟩, ?_⟩
      change Submodule.Quotient.mk (g ⟨a, haL⟩) = Submodule.Quotient.mk y
      apply (Submodule.Quotient.eq q).mpr
      apply (hq _).mpr
      change f a - y.val ∈ (I ^ m * L).map f
      simpa only [neg_sub] using neg_mem hdiff
  exact ⟨AddEquiv.ofBijective gq.toAddMonoidHom ⟨hinj, hsurj⟩, fun _ ↦ rfl⟩

private noncomputable def reesCoeff (J : Ideal A) (n : ℕ) : reesAlgebra J →ₗ[A] A where
  toFun F := (F : Polynomial A).coeff n
  map_add' F G := Polynomial.coeff_add _ _ _
  map_smul' a F := by simp

private noncomputable def reesMono (J : Ideal A) (n : ℕ) : ↥(J ^ n) →ₗ[A] reesAlgebra J where
  toFun x := reesMonomial J x.val x.property
  map_add' x y := by
    apply Subtype.ext
    exact map_add (Polynomial.monomial n) x.val y.val
  map_smul' a x := by
    apply Subtype.ext
    simp [reesMonomial, Polynomial.smul_monomial]

private theorem mem_rees_ideal (H J : Ideal A) (F : reesAlgebra J) :
    F ∈ H.map (algebraMap A (reesAlgebra J)) ↔
      ∀ n : ℕ, (F : Polynomial A).coeff n ∈ H * J ^ n := by
  constructor
  · intro hF n
    have hF' : F ∈ H • (⊤ : Submodule A (reesAlgebra J)) := by
      rw [Ideal.smul_top_eq_map]
      exact hF
    have hle : H • (⊤ : Submodule A (reesAlgebra J)) ≤
        Submodule.comap (reesCoeff J n) (H * J ^ n) := by
      apply Submodule.smul_le.mpr
      intro a ha G _
      change (reesCoeff J n) (a • G) ∈ H * J ^ n
      rw [LinearMap.map_smul]
      exact Ideal.mul_mem_mul ha (G.property n)
    exact hle hF'
  · intro hF
    have hmono (n : ℕ) (x : ↥(J ^ n)) (hx : x.val ∈ H * J ^ n) :
        reesMono J n x ∈ H.map (algebraMap A (reesAlgebra J)) := by
      have hle : H • (⊤ : Submodule A ↥(J ^ n)) ≤
          ((H.map (algebraMap A (reesAlgebra J))).restrictScalars A).comap
            (reesMono J n) := by
        apply Submodule.smul_le.mpr
        intro a ha y _
        change reesMono J n (a • y) ∈ H.map (algebraMap A (reesAlgebra J))
        rw [LinearMap.map_smul, Algebra.smul_def]
        exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ ha)
      exact hle ((Submodule.mem_smul_top_iff H (J ^ n) x).mpr hx)
    have hsum : F = ∑ n ∈ (F : Polynomial A).support,
        reesMono J n ⟨(F : Polynomial A).coeff n, F.property n⟩ := by
      apply Subtype.ext
      simpa [reesMono, reesMonomial, Polynomial.sum_def] using
        (Polynomial.sum_monomial_eq (F : Polynomial A)).symm
    rw [hsum]
    exact Ideal.sum_mem _ fun n _ ↦ hmono n _ (hF n)

private theorem rees_quotient_comparison (I : Ideal A) (hI : I.FG)
    (J : Ideal A) (r : ℕ) (hr : I ^ r ≤ J) (m : ℕ) :
    ∃ e : reesAlgebra J ⧸ (I ^ m).map (algebraMap A (reesAlgebra J)) ≃+*
        reesAlgebra (J.map (algebraMap A (AdicCompletion I A))) ⧸
          ((I.map (algebraMap A (AdicCompletion I A))) ^ m).map
            (algebraMap (AdicCompletion I A)
              (reesAlgebra (J.map (algebraMap A (AdicCompletion I A))))),
      ∀ F : reesAlgebra J,
        e (Ideal.Quotient.mk _ F) = Ideal.Quotient.mk _
          (reesGrading.hom (algebraMap A (AdicCompletion I A)) rfl F) := by
  classical
  let B := AdicCompletion I A
  let f := algebraMap A B
  let g := (reesGrading.hom f (I := J) rfl).toRingHom
  let p := (I ^ m).map (algebraMap A (reesAlgebra J))
  let q := ((I.map f) ^ m).map (algebraMap B (reesAlgebra (J.map f)))
  have hcoeff (F : reesAlgebra J) (n : ℕ) :
      (g F : Polynomial B).coeff n = f ((F : Polynomial A).coeff n) := by
    exact Polynomial.coeff_map f n
  have hq (F : reesAlgebra (J.map f)) :
      F ∈ q ↔ ∀ n : ℕ, (F : Polynomial B).coeff n ∈ (I ^ m * J ^ n).map f := by
    rw [mem_rees_ideal]
    simp only [Ideal.map_mul, Ideal.map_pow]
  have hg : p ≤ q.comap g := by
    intro F hF
    apply (hq (g F)).mpr
    intro n
    rw [hcoeff]
    exact Ideal.mem_map_of_mem f ((mem_rees_ideal (I ^ m) J F).mp hF n)
  let gq := Ideal.quotientMap q g hg
  have hinj : Function.Injective gq := by
    apply Ideal.quotientMap_injective'
    intro F hF
    apply (mem_rees_ideal (I ^ m) J F).mpr
    intro n
    have hFn := (hq (g F)).mp hF n
    rw [hcoeff] at hFn
    change (F : Polynomial A).coeff n ∈ ((I ^ m * J ^ n).map f).comap f at hFn
    have hprod : I ^ (m + r * n) ≤ I ^ m * J ^ n := by
      rw [pow_add, pow_mul]
      exact mul_le_mul' le_rfl (pow_le_pow_left' hr n)
    rwa [comap_map I hI (I ^ m * J ^ n) (m + r * n) hprod] at hFn
  have hsurj : Function.Surjective gq := by
    intro F
    obtain ⟨F, rfl⟩ := Ideal.Quotient.mk_surjective F
    have hlift (n : ℕ) : ∃ x : ↥(J ^ n),
        f x.val - (F : Polynomial B).coeff n ∈ (I ^ m * J ^ n).map f := by
      have hJn : I ^ (r * n) ≤ J ^ n := by
        rw [pow_mul]
        exact pow_le_pow_left' hr n
      obtain ⟨e, he⟩ := power_quotient_comparison I hI (J ^ n) (r * n) hJn m
      have hF : (F : Polynomial B).coeff n ∈ (J ^ n).map f := by
        rw [Ideal.map_pow]
        exact F.property n
      obtain ⟨x, hx⟩ := e.surjective (Submodule.Quotient.mk ⟨_, hF⟩)
      obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      rw [he] at hx
      have hx' := (Submodule.Quotient.eq _).mp hx
      rw [Submodule.mem_smul_top_iff] at hx'
      refine ⟨x, ?_⟩
      change f x.val - (F : Polynomial B).coeff n ∈
        (I.map f) ^ m * (J ^ n).map f at hx'
      simpa only [Ideal.map_mul, Ideal.map_pow] using hx'
    choose x hx using hlift
    let G : reesAlgebra J := ∑ n ∈ (F : Polynomial B).support, reesMono J n (x n)
    refine ⟨Ideal.Quotient.mk p G, ?_⟩
    change Ideal.Quotient.mk q (g G) = Ideal.Quotient.mk q F
    apply Ideal.Quotient.eq.mpr
    apply (hq (g G - F)).mpr
    intro n
    change ((g G : Polynomial B) - (F : Polynomial B)).coeff n ∈ _
    rw [Polynomial.coeff_sub, hcoeff]
    by_cases hn : n ∈ (F : Polynomial B).support
    · have hGn : (G : Polynomial A).coeff n = (x n).val := by
        simp [G, reesMono, reesMonomial, Polynomial.coeff_monomial, hn]
      rw [hGn]
      exact hx n
    · have hGn : (G : Polynomial A).coeff n = 0 := by
        simp [G, reesMono, reesMonomial, Polynomial.coeff_monomial, hn]
      rw [hGn, map_zero, Polynomial.notMem_support_iff.mp hn, sub_self]
      exact zero_mem _
  exact ⟨RingEquiv.ofBijective gq ⟨hinj, hsurj⟩, fun _ ↦ rfl⟩

/-- The admissible blowup system is filtered, has schematically dense preserved opens, and
is identified by completion, including its Rees reductions and closed fibres.

Source: ILO XX §4.4, pp. 373–374 and its final Note
(blueprint: lem-per-admissible-modification-system).

Proof:
1. Equality of vanishing loci gives power containments in both directions. The ideal I
   supplies an index; identities and composition give the preorder. The product JK is an
   index dominating both J and K by the blowup domination factorization criterion.
2. The center is the unit ideal over the preserved open, so the blowup there is U. On each
   principalization chart the exceptional ideal has a regular generator a and U is D(a).
   The restriction C → C[1/a] is injective, proving schematic density on every open.
3. The canonical isomorphisms A/I^N ≅ A'/I^N A' identify ideals containing these powers.
   Lift finitely many generators to descend such ideals; extension and contraction are
   inverse and preserve the full-support condition by the power containments.
4. Domination is characterized by K^n = JL. Extension preserves this identity. Conversely,
   the factor L' after completion contains a power of I', hence descends; the quotient
   comparisons reflect the factorization. This identifies the preorders.
5. For I^r ≤ J, both J^n and I^m J^n contain powers of I. The quotient comparisons for
   A/J^n and A/I^m J^n commute with their quotient arrows. Taking kernels gives the stated
   isomorphisms of powers. For n = 0, A/J^n is zero, so no exponent-zero comparison is used.
6. All maps send a representative to its canonical image. Thus they preserve products and
   commute with reduction in m, giving the ring isomorphisms of Rees reductions. Proj base
   change at m = 1 identifies the closed fibres over the canonical residue-ring isomorphism.
-/
theorem admissibleModificationSystem (I : Ideal A) [HenselianRing A I] (hI : I.FG) :
    (Nonempty (Index I) ∧
      IsPreorder (Index I) (fun J K ↦ Dominates J.val K.val) ∧
      Directed (fun J K : Index I ↦ Dominates J.val K.val) id) ∧
    (∀ J : Index I, ∃ j : (puncturedOpen I).toScheme ⟶ AffineBlowup J.val,
      IsOpenImmersion j ∧ j ≫ AffineBlowup.toSpec J.val = (puncturedOpen I).ι ∧
      ∀ W : (AffineBlowup J.val).Opens, Function.Injective (j.app W)) ∧
    (∃ e : Index I ≃ Index (I.map (algebraMap A (AdicCompletion I A))),
      (∀ J : Index I, (e J).val = J.val.map (algebraMap A (AdicCompletion I A))) ∧
      ∀ J K : Index I, Dominates J.val K.val ↔ Dominates (e J).val (e K).val) ∧
    (∀ (J : Index I) (m : ℕ), 1 ≤ m →
      ∃ e : ∀ n : ℕ, powerQuotient I (J.val ^ n) m ≃+
          powerQuotient (I.map (algebraMap A (AdicCompletion I A)))
            ((J.val ^ n).map (algebraMap A (AdicCompletion I A))) m,
        ∀ (n : ℕ) (x : ↥(J.val ^ n)),
          e n (Submodule.Quotient.mk x) =
            Submodule.Quotient.mk
              ⟨algebraMap A (AdicCompletion I A) x.val,
                Ideal.mem_map_of_mem (algebraMap A (AdicCompletion I A)) x.property⟩) ∧
    (∀ (J : Index I) (m : ℕ), 1 ≤ m →
      ∃ e : reesQuotient I J.val m ≃+*
          reesQuotient (I.map (algebraMap A (AdicCompletion I A)))
            (J.val.map (algebraMap A (AdicCompletion I A))) m,
        ∀ F : reesAlgebra J.val,
          e (Ideal.Quotient.mk _ F) = Ideal.Quotient.mk _
            (reesGrading.hom (algebraMap A (AdicCompletion I A)) rfl F)) ∧
    (∃ e₀ : A ⧸ I ≃+*
        AdicCompletion I A ⧸ I.map (algebraMap A (AdicCompletion I A)),
      (∀ a : A, e₀ (Ideal.Quotient.mk I a) = Ideal.Quotient.mk _
        (algebraMap A (AdicCompletion I A) a)) ∧
      ∀ J : Index I,
        ∃ e : closedFiber (I.map (algebraMap A (AdicCompletion I A)))
            (J.val.map (algebraMap A (AdicCompletion I A))) ≅ closedFiber I J.val,
          e.hom ≫ pullback.fst _ _ = pullback.fst _ _ ≫
            AffineBlowup.hom (algebraMap A (AdicCompletion I A)) rfl ∧
          e.hom ≫ pullback.snd _ _ = pullback.snd _ _ ≫
            Spec.map (CommRingCat.ofHom e₀.toRingHom)) := by
  classical
  obtain ⟨e, he⟩ := index_equiv I hI
  obtain ⟨e₀, he₀⟩ := quotient_comparison I hI I 1 (by simp)
  refine ⟨filtered I hI, ?_, ⟨e, he, ?_⟩, ?_, ?_, ⟨e₀, he₀, ?_⟩⟩
  · intro J
    have hU : puncturedOpen I = puncturedOpen J.val := by
      have hmem (H : Ideal A) (x : PrimeSpectrum A) :
          x ∈ puncturedOpen H ↔ x ∉ PrimeSpectrum.zeroLocus (H : Set A) := by
        dsimp only [puncturedOpen]
        rw [TopologicalSpace.Opens.mem_iSup]
        change (∃ a : H, (a : A) ∉ x.asIdeal) ↔ ¬ (H : Set A) ⊆ x.asIdeal
        simp only [Subtype.exists, Set.subset_def, not_forall, exists_prop,
          SetLike.mem_coe]
      apply TopologicalSpace.Opens.ext
      ext x
      exact (hmem I x).trans ((J.property.2 ▸ hmem J.val x).symm)
    rw [hU]
    exact exists_dense_open J.val J.property.1
  · intro J K
    rw [he J, he K]
    exact domination_map_iff I hI J K
  · intro J m _
    obtain ⟨r, _, hr⟩ := positive_power_le I J.val hI
      (PrimeSpectrum.zeroLocus_eq_iff.mp J.property.2).symm
    have hpow (n : ℕ) : I ^ (r * n) ≤ J.val ^ n := by
      rw [pow_mul]
      exact pow_le_pow_left' hr n
    choose e he using fun n ↦ power_quotient_comparison I hI (J.val ^ n) (r * n) (hpow n) m
    exact ⟨e, he⟩
  · intro J m _
    obtain ⟨r, _, hr⟩ := positive_power_le I J.val hI
      (PrimeSpectrum.zeroLocus_eq_iff.mp J.property.2).symm
    exact rees_quotient_comparison I hI J.val r hr m
  · rintro ⟨J, hJ, hJI⟩
    obtain ⟨r, _, hr⟩ := positive_power_le I J hI
      (PrimeSpectrum.zeroLocus_eq_iff.mp hJI).symm
    have hR :
        ∃ eR : reesAlgebra J ⧸ I.map (algebraMap A (reesAlgebra J)) ≃+*
            reesAlgebra (J.map (algebraMap A (AdicCompletion I A))) ⧸
              (I.map (algebraMap A (AdicCompletion I A))).map
                (algebraMap (AdicCompletion I A)
                  (reesAlgebra (J.map (algebraMap A (AdicCompletion I A))))),
          ∀ F : reesAlgebra J, eR (Ideal.Quotient.mk _ F) =
            Ideal.Quotient.mk _
              (reesGrading.hom (algebraMap A (AdicCompletion I A)) rfl F) := by
      have h := rees_quotient_comparison I hI J r hr 1
      rw [pow_one, pow_one] at h
      exact h
    obtain ⟨eR, heR⟩ := hR
    exact AffineBlowup.exists_closedFiberIso_of_reesReduction
      (algebraMap A (AdicCompletion I A)) I J e₀ he₀ eR heR

end AlgebraicGeometry.AdmissibleModificationSystem
