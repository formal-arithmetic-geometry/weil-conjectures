/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B4
-/
module

public import WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsor
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMap
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.Algebra.Regular.SMul

public import Mathlib.AlgebraicGeometry.Normalization
public import Mathlib.AlgebraicGeometry.Noetherian

import WeilConjectures.AlgebraicGeometry.Morphisms.StrictHenselRegularDivisorQuotient
import Sheaf.AlgebraicGeometry.StrictHenselizationClosedFiberComparison
import WeilConjectures.RingTheory.ProEtale.FaithfullyFlat
import Sheaf.AlgebraicGeometry.StrictHenselizationCompatibility
import WeilConjectures.RingTheory.RootAlgebraRegularAtRoot
import WeilConjectures.RingTheory.RegularLocalLocalization
import WeilConjectures.RingTheory.RegularRingNormal
import WeilConjectures.AlgebraicGeometry.Morphisms.FiniteEtaleOpenIntegralClosure
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.LocalRing.Quotient
import WeilConjectures.Mathlib.RingTheory.RegularLocalRing.Defs

/-! # Properties of the explicit root-cover normalization
Source: Stacks Project, Tags 0EYG, 0EYH and 032L. -/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

-- Transfer the retained upstream theorem through the canonical small-colimit comparison.
private theorem small_regular_divisor_quotient
    (R : CommRingCat.{u}) [IsRegularRing R] (f : R)
    [IsRegularRing (R ⧸ Ideal.span {f})]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (barY : Spec (.of Ω) ⟶ Spec R)
    (b : R ⟶ strictHenselizationRing barY)
    (hb : Spec.map b = strictHenselizationStructuralMap barY)
    (hg : ¬ IsUnit (b.hom f)) :
    IsNoetherianRing (strictHenselizationRing barY) ∧
      IsRegularRing (strictHenselizationRing barY ⧸ Ideal.span {b.hom f}) ∧
      IsDomain (strictHenselizationRing barY ⧸ Ideal.span {b.hom f}) := by
  let e : strictHenselizationRing barY ≅ strictHenselization barY :=
    smallStrictHenselizationColimitIso barY
  have hbe : Spec.map (b ≫ e.hom) = strictLocalizationToBase barY := by
    rw [Spec.map_comp, hb, ← smallStrictHenselizationColimitIso_toBase barY]
    simp only [e, ← Category.assoc, ← Spec.map_comp, Iso.inv_hom_id, Spec.map_id,
      Category.id_comp]
  have hg' : ¬ IsUnit ((b ≫ e.hom).hom f) := by
    intro h
    apply hg
    have h' := h.map e.inv.hom
    change IsUnit (e.commRingCatIsoToRingEquiv.symm
      (e.commRingCatIsoToRingEquiv (b.hom f))) at h'
    simpa only [RingEquiv.symm_apply_apply] using h'
  obtain ⟨hN, hQ, hD⟩ :=
    strictHenselization_regular_divisor_quotient R f barY (b ≫ e.hom) hbe hg'
  let : IsNoetherianRing (strictHenselization barY) := hN
  let : IsRegularRing
      (strictHenselization barY ⧸ Ideal.span {(b ≫ e.hom).hom f}) := hQ
  let eQ : (strictHenselization barY ⧸ Ideal.span {(b ≫ e.hom).hom f}) ≃+*
      (strictHenselizationRing barY ⧸ Ideal.span {b.hom f}) :=
    Ideal.quotientEquiv _ _ e.symm.commRingCatIsoToRingEquiv (by
      rw [Ideal.map_span, Set.image_singleton]
      change Ideal.span {b.hom f} = Ideal.span {
        e.commRingCatIsoToRingEquiv.symm (e.commRingCatIsoToRingEquiv (b.hom f))}
      rw [RingEquiv.symm_apply_apply])
  exact ⟨isNoetherianRing_of_ringEquiv _ e.symm.commRingCatIsoToRingEquiv,
    IsRegularRing.of_ringEquiv eQ, eQ.toMulEquiv.isDomain_iff.mp hD⟩


set_option backward.isDefEq.respectTransparency false in
private noncomputable def root_quotient_equiv (R : Type u) [CommRing R]
    (f : R) (n : ℕ) (hn : 0 < n) :
    (AdjoinRoot ((Polynomial.X : Polynomial R) ^ n - Polynomial.C f) ⧸
      Ideal.span {AdjoinRoot.root ((Polynomial.X : Polynomial R) ^ n - Polynomial.C f)}) ≃+*
      (R ⧸ Ideal.span {f}) := by
  let P := (Polynomial.X : Polynomial R) ^ n - Polynomial.C f
  let B := AdjoinRoot P
  let t := AdjoinRoot.root P
  let I := Ideal.span ({t} : Set B)
  let J := Ideal.span ({f} : Set R)
  let v := AdjoinRoot.lift (f := P) (Ideal.Quotient.mk J) 0 (by
    simp only [P, Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X,
      Polynomial.eval₂_C, zero_pow hn.ne', zero_sub, neg_eq_zero]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self f))
  let g : B ⧸ I →+* R ⧸ J := Ideal.Quotient.lift I v (by
    intro y hy
    obtain ⟨z, rfl⟩ := Ideal.mem_span_singleton.mp hy
    rw [map_mul]
    have hv : v t = 0 := AdjoinRoot.lift_root _
    rw [hv, zero_mul])
  let w := (Ideal.Quotient.mk I).comp (AdjoinRoot.of P)
  have hw : w f = 0 := by
    change Ideal.Quotient.mk I (AdjoinRoot.of P f) = 0
    have hroot := AdjoinRoot.eval₂_root ((Polynomial.X : Polynomial R) ^ n - Polynomial.C f)
    have hroot' : AdjoinRoot.root ((Polynomial.X : Polynomial R) ^ n - Polynomial.C f) ^ n =
        AdjoinRoot.of ((Polynomial.X : Polynomial R) ^ n - Polynomial.C f) f := by
      simpa only [Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X,
        Polynomial.eval₂_C, sub_eq_zero] using hroot
    rw [← hroot', map_pow]
    have ht : Ideal.Quotient.mk I t = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self t)
    change (Ideal.Quotient.mk I t) ^ n = 0
    rw [ht, zero_pow hn.ne']
  let h : R ⧸ J →+* B ⧸ I := Ideal.Quotient.lift J w (by
    intro y hy
    obtain ⟨z, rfl⟩ := Ideal.mem_span_singleton.mp hy
    rw [map_mul, hw, zero_mul])
  apply RingEquiv.ofRingHom g h
  · apply Ideal.Quotient.ringHom_ext
    ext r
    change v (AdjoinRoot.of P r) = Ideal.Quotient.mk J r
    exact AdjoinRoot.lift_of _
  · apply Ideal.Quotient.ringHom_ext
    apply AdjoinRoot.ringHom_ext
    · ext r
      change h (g (Ideal.Quotient.mk I (AdjoinRoot.of P r))) =
        Ideal.Quotient.mk I (AdjoinRoot.of P r)
      change h (v (AdjoinRoot.of P r)) = _
      rw [show v (AdjoinRoot.of P r) = Ideal.Quotient.mk J r from AdjoinRoot.lift_of _]
      rfl
    · change h (g (Ideal.Quotient.mk I t)) = Ideal.Quotient.mk I t
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self t)]
      rw [map_zero, map_zero]

set_option backward.isDefEq.respectTransparency false in
private theorem finite_normalization_of_normal_open
    {N : Scheme.{u}} [IsNoetherian N] [IsIntegral N]
    (hn : ∀ z : N, IsIntegrallyClosed (N.presheaf.stalk z))
    (V : N.Opens) {X : Scheme.{u}} (p : X ⟶ V.toScheme) [IsFinite p] [Etale p] :
    IsFinite (p ≫ V.ι).fromNormalization := by
  let Q : V.toScheme.FiniteEtale :=
    ⟨MorphismProperty.Over.mk ⊤ p inferInstance, (show IsFinite p from inferInstance)⟩
  let a := p ≫ V.ι
  refine { finite_app := ?_ }
  intro B hB
  let : Algebra Γ(N, B) Γ(X, a ⁻¹ᵁ B) := (a.app B).hom.toAlgebra
  have hfin : Module.Finite Γ(N, B) (integralClosure Γ(N, B) Γ(X, a ⁻¹ᵁ B)) :=
    finiteEtale_open_integralClosure_finite hn V Q B hB
  rw [Scheme.Hom.fromNormalization_app a hB]
  exact (RingHom.finite_respectsIso.cancel_right_isIso
    (CommRingCat.ofHom (algebraMap _ _))
    (Scheme.Hom.normalizationObjIso a hB).inv).2 (RingHom.finite_algebraMap.2 hfin)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The explicit relative normalization of the punctured root cover is finite.
Source: Stacks Project, Tag 0EYG, root-algebra paragraph, Tag 0EYH, local
regularity verification, and Tag 032L (finite separable integral closure).
(blueprint: lem-sbc-strict-hensel-root-normalization-finite)

Proof: StrictHenselizationLocalStructure gives the local-ring structure of H.
The regular-divisor quotient theorem supplies Noetherianness of H and regularity
of H/(g), while flatness of the structural map makes g regular. The monic root
algebra A is finite free over H. Its root t satisfies t^|G|=g, and the explicitly
constructed quotient equivalence identifies A/(t) with the local ring H/(g).
Every maximal ideal M of A contracts to the maximal ideal of H by integrality.
Thus g belongs to M, hence t belongs to M. The maximal ideals of A therefore
correspond to those of A/(t); the latter ring is local, so A is local. Apply
RootAlgebraRegularAtRoot at its maximal ideal and identify that localization
with A (all denominators are units). A is regular local. RegularLocalLocalization
makes A regular, and RegularRingNormal gives integrally closed domain stalks
of N=Spec A. In particular N is integral and Noetherian.

Package the supplied finite etale punctured projection as a finite etale object.
FiniteEtaleOpenIntegralClosure applies on each affine open B of N: its generic
algebra is a finite product of separable function-field extensions, whose integral
closures are finite by the trace-dual-lattice argument of 032L; the closure in
sections injects into that finite module. Mathlib fromNormalization_app and
normalizationObjIso identify the section map of the explicit normalization with
this finite algebra map followed by a ring isomorphism. These finite affine
section maps prove finiteness. This part uses neither the unit group-order
hypothesis nor the projection equation for beta; ramification is only needed
for the separate generic-etaleness statement. No normalization witness is chosen. -/
theorem GaloisCover.strict_hensel_root_normalization_finite
    {L U : Scheme.{u}} (i : U ⟶ L)
    (G : Type (u + 1)) [Group G] [Finite G] (W : GaloisCover G U)
    (R : CommRingCat.{u}) (φ : Spec R ⟶ L) (f : R)
    (_hG : IsUnit (Nat.card G : R))
    [IsRegularRing R] (hf : IsSMulRegular R f)
    [IsRegularRing (R ⧸ Ideal.span {f})]
    (β : pullback i φ ≅ Scheme.Opens.toScheme (X := Spec R) (PrimeSpectrum.basicOpen f))
    (_hβ : β.hom ≫ Scheme.Opens.ι (X := Spec R) (PrimeSpectrum.basicOpen f) = pullback.snd i φ)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (barY : Spec (.of Ω) ⟶ Spec R)
    (b : R ⟶ strictHenselizationRing barY)
    (hb : Spec.map b = strictHenselizationStructuralMap barY) :
    let H := strictHenselizationRing barY
    let g := b.hom f
    let A := AdjoinRoot ((Polynomial.X : Polynomial H) ^ Nat.card G - Polynomial.C g)
    let N := Spec (CommRingCat.of A)
    let q := Spec.map (CommRingCat.ofHom (algebraMap H A))
    let V : N.Opens := PrimeSpectrum.basicOpen (algebraMap H A g)
    ¬ IsUnit g → ∀ (hN : IsLocallyNoetherian N),
    letI := hN
    let p := pullback.snd (W.π ≫ i) (V.ι ≫ q ≫ Spec.map b ≫ φ)
    ∀ (hp : IsFinite p),
    letI := hp
    let a := p ≫ V.ι
    Etale p → IsFinite a.fromNormalization := by
  classical
  dsimp only
  intro hg hN hp hep
  let H := strictHenselizationRing barY
  let g := b.hom f
  let P := (Polynomial.X : Polynomial H) ^ Nat.card G - Polynomial.C g
  let A := AdjoinRoot P
  let t := AdjoinRoot.root P
  let I := Ideal.span ({t} : Set A)
  let N := Spec (CommRingCat.of A)
  let q := Spec.map (CommRingCat.ofHom (algebraMap H A))
  let V : N.Opens := PrimeSpectrum.basicOpen (algebraMap H A g)
  let p := pullback.snd (W.π ≫ i) (V.ι ≫ q ≫ Spec.map b ≫ φ)
  have : IsFinite p := hp
  have : Etale p := hep
  obtain ⟨hlocal, -⟩ := AlgebraicGeometry.strictHenselizationLocalStructure barY
  let : IsLocalRing H := hlocal
  obtain ⟨hH, hQ, hQD⟩ := small_regular_divisor_quotient R f barY b hb hg
  have : IsNoetherianRing H := hH
  have : IsRegularRing (H ⧸ Ideal.span {g}) := hQ
  have : IsDomain (H ⧸ Ideal.span {g}) := hQD
  have hm : P.Monic := Polynomial.monic_X_pow_sub_C g (Nat.card_pos (α := G)).ne'
  have : Module.Finite H A := hm.finite_adjoinRoot
  have : Module.Free H A := hm.free_adjoinRoot
  let : Algebra R H := b.hom.toAlgebra
  have : Module.Flat R H := by
    have := (strictHenselization_properties barY).2.1
    let J := SmallModel.{u} (strictHenselizationNeighbourhoods barY)
    let F := (equivSmallModel.{u} (strictHenselizationNeighbourhoods barY)).inverse
    let ψ (j : J) := ((AffineEtale.Spec (Spec R)).obj (F.obj j).1).hom
    let τ : (Functor.const Jᵒᵖ).obj R ⟶ strictHenselizationAffineDiagram barY :=
      { app := fun j ↦ (ΓSpecIso R).inv ≫ (ψ j.unop).appTop
        naturality := fun j k a ↦ by
          dsimp only [Functor.const_obj_map, Functor.const_obj_obj]
          rw [Category.id_comp]
          symm
          change ((ΓSpecIso R).inv ≫ (ψ j.unop).appTop) ≫
            (Spec.map (F.map a.unop).1.left.unop).appTop =
              (ΓSpecIso R).inv ≫ (ψ k.unop).appTop
          rw [Category.assoc, ← Scheme.Hom.comp_appTop]
          exact congrArg (fun l ↦ (ΓSpecIso R).inv ≫ l.appTop) (F.map a.unop).1.w }
    apply RingHom.Flat.of_isColimit b Jᵒᵖ (strictHenselizationAffineDiagram barY)
      (t := τ) (c := (colimit.cocone (strictHenselizationAffineDiagram barY)).ι)
      (colimit.isColimit (strictHenselizationAffineDiagram barY))
    intro j
    constructor
    · have : Etale (ψ j.unop) := inferInstance
      have : IsAffine ((AffineEtale.Spec (Spec R)).obj (F.obj j.unop).1).left := by
        change IsAffine (Spec (F.obj j.unop).1.left.unop)
        infer_instance
      exact (RingHom.Flat.of_bijective
        (ConcreteCategory.bijective_of_isIso (ΓSpecIso R).inv)).comp
          (Scheme.Hom.flat_appTop (f := ψ j.unop)
            (X := Spec (F.obj j.unop).1.left.unop) (Y := Spec R))
    · have h := (exists_strictHenselizationStructuralMap barY).choose_spec j.unop
      apply Spec.map_injective
      rw [hb]
      change Spec.map ((ΓSpecIso R).inv ≫ (ψ j.unop).appTop ≫
        colimit.ι (strictHenselizationAffineDiagram barY) j) = _
      have hτ : (ΓSpecIso R).inv ≫ (ψ j.unop).appTop =
          Spec.preimage (ψ j.unop) ≫ (ΓSpecIso (F.obj j.unop).1.left.unop).inv := by
        rw [ΓSpecIso_inv_naturality, Spec.map_preimage]
      rw [← Category.assoc, hτ, Category.assoc, Spec.map_comp, Spec.map_comp,
        Spec.map_preimage]
      exact h
  have hgH : IsSMulRegular H g := hf.of_flat
  have : IsLocalRing (H ⧸ Ideal.span {g}) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk (Ideal.span {g}))
      Ideal.Quotient.mk_surjective
  let e := root_quotient_equiv H g (Nat.card G) (Nat.card_pos (α := G))
  have : IsLocalRing (A ⧸ I) := e.symm.isLocalRing
  let v := Ideal.Quotient.mk I
  let m := IsLocalRing.maximalIdeal (A ⧸ I)
  have hmA : (m.comap v).IsMaximal :=
    Ideal.comap_isMaximal_of_surjective v Ideal.Quotient.mk_surjective
  have hlocalA : IsLocalRing A := by
    apply IsLocalRing.of_unique_max_ideal
    refine ⟨m.comap v, hmA, ?_⟩
    intro M hM
    have : M.IsMaximal := hM
    have hMH : (M.comap (algebraMap H A)).IsMaximal :=
      Ideal.isMaximal_comap_of_isIntegral_of_isMaximal M
    have hgM : algebraMap H A g ∈ M := by
      change g ∈ M.comap (algebraMap H A)
      rw [IsLocalRing.eq_maximalIdeal hMH]
      exact (IsLocalRing.mem_maximalIdeal g).mpr hg
    have htM : t ∈ M := by
      apply (Ideal.IsMaximal.isPrime hM).mem_of_pow_mem (Nat.card G)
      have hroot := AdjoinRoot.eval₂_root
        ((Polynomial.X : Polynomial H) ^ Nat.card G - Polynomial.C g)
      have hroot' : t ^ Nat.card G = algebraMap H A g := by
        have hh : AdjoinRoot.root ((Polynomial.X : Polynomial H) ^ Nat.card G -
            Polynomial.C g) ^ Nat.card G =
            AdjoinRoot.of ((Polynomial.X : Polynomial H) ^ Nat.card G -
              Polynomial.C g) g := by
          rw [Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X] at hroot
          rw [Polynomial.eval₂_C] at hroot
          exact sub_eq_zero.mp hroot
        exact hh
      rw [hroot']
      exact hgM
    have hIM : I ≤ M := Ideal.span_le.mpr (by rintro x rfl; exact htM)
    have hker : RingHom.ker v ≤ M := by simpa only [v, Ideal.mk_ker] using hIM
    have hmap : (M.map v).IsMaximal :=
      Ideal.IsMaximal.map_of_surjective_of_ker_le Ideal.Quotient.mk_surjective hker
    have heq : M.map v = m := IsLocalRing.eq_maximalIdeal hmap
    have hc := congrArg (Ideal.comap v) heq
    rw [Ideal.comap_map_of_surjective v Ideal.Quotient.mk_surjective,
      ← RingHom.ker_eq_comap_bot, sup_eq_left.mpr hker] at hc
    exact hc
  let : IsLocalRing A := hlocalA
  have htmax : t ∈ IsLocalRing.maximalIdeal A := by
    have hI : I ≤ m.comap v := by
      intro x hx
      change v x ∈ m
      rw [show v x = 0 from Ideal.Quotient.eq_zero_iff_mem.mpr hx]
      exact m.zero_mem
    rw [← IsLocalRing.eq_maximalIdeal hmA]
    exact hI (Ideal.mem_span_singleton_self t)
  have hreg := AdjoinRoot.isRegularLocalRing_atPrime_of_root_mem H g hgH
    (Nat.card G) (Nat.card_pos (α := G)) (IsLocalRing.maximalIdeal A) htmax
  have : IsRegularLocalRing (Localization.AtPrime (IsLocalRing.maximalIdeal A)) := hreg
  let em : A ≃ₐ[A] Localization.AtPrime (IsLocalRing.maximalIdeal A) :=
    IsLocalization.atUnits A (IsLocalRing.maximalIdeal A).primeCompl
      (fun x ↦ by simpa using! fun a ↦ a)
  have : IsRegularLocalRing A := IsRegularLocalRing.of_ringEquiv em.toRingEquiv.symm
  have : IsRegularRing A :=
    (IsRegularLocalRing.localization_at_prime_and_isRegularRing
      (IsLocalRing.maximalIdeal A)).2
  have : IsDomain A := inferInstance
  have : IsIntegral N := inferInstance
  have : IsLocallyNoetherian N := hN
  have : IsNoetherian N := inferInstance
  have hn : ∀ z : N, IsIntegrallyClosed (N.presheaf.stalk z) := by
    intro z
    obtain ⟨_, hnormal⟩ := IsRegularRing.isNormalRing A z.asIdeal
    exact IsIntegrallyClosed.of_equiv
      (Spec.stalkIso (CommRingCat.of A) z).commRingCatIsoToRingEquiv.symm
  simpa only using finite_normalization_of_normal_open hn V p

end AlgebraicGeometry.Scheme
