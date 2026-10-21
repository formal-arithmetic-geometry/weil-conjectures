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

public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.EffectiveCartier
public import WeilConjectures.AlgebraicGeometry.Regular

public import Mathlib.AlgebraicGeometry.Normalization
public import Mathlib.AlgebraicGeometry.Noetherian

import WeilConjectures.AlgebraicGeometry.Morphisms.StrictHenselRegularDivisorQuotient
import Sheaf.AlgebraicGeometry.StrictHenselizationClosedFiberComparison
import Sheaf.AlgebraicGeometry.SmallStrictHenselizationIndEtale
import WeilConjectures.RingTheory.RootAlgebraRegularAtRoot
import WeilConjectures.AlgebraicGeometry.Morphisms.RootNormalizationGenericSourceEtale

/-! # Properties of the explicit root-cover normalization
Source: Stacks Project, Tags 09EB, 0BRM, 0EYG and 0EYH. -/

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


-- Apply the existing affine-chart theorem to the identity chart of Spec R.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem small_strictHenselization_structural_flat
    (R : CommRingCat.{u})
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (barY : Spec (.of Ω) ⟶ Spec R)
    (b : R ⟶ strictHenselizationRing barY)
    (hb : Spec.map b = strictHenselizationStructuralMap barY) :
    RingHom.Flat b.hom := by
  let : Algebra R (strictHenselizationRing barY) := b.hom.toAlgebra
  have he : Algebra.IndEtale R (strictHenselizationRing barY) :=
    smallStrictHenselization_indEtale_of_affine_chart
      (A := strictHenselizationRing barY) barY R (𝟙 _)
      ⟨barY (IsLocalRing.closedPoint Ω), rfl⟩ (Iso.refl _) b.hom
      (by
        change Spec.map b ≫ 𝟙 _ = 𝟙 _ ≫ strictHenselizationStructuralMap barY
        simpa only [Category.comp_id, Category.id_comp] using hb)
  obtain ⟨J, _, _, P, hP⟩ := he.exists_colimitPresentation
  exact ModuleCat.flat_of_colimitPresentation
    (P.map (forget₂ _ (AlgCat R) ⋙ forget₂ _ (ModuleCat R))) fun j ↦ by
      change Module.Flat R (P.diag.obj j)
      have := hP j
      infer_instance

-- Finiteness lets source-local etaleness around the whole fibre give a target open.
private theorem etale_shrink_of_fibre_source_opens {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsFinite f] (y : Y)
    (h : ∀ x : X, f x = y → ∃ V : X.Opens, x ∈ V ∧ Etale (V.ι ≫ f)) :
    ∃ W : Y.Opens, y ∈ W ∧ Etale (f ∣_ W) := by
  classical
  let E : X.Opens := ⨆ V : {V : X.Opens // Etale (V.ι ≫ f)}, V.val
  let W : Y.Opens := ⟨(f '' (E : Set X)ᶜ)ᶜ,
    (f.isClosedMap _ E.isOpen.isClosed_compl).isOpen_compl⟩
  have hy : y ∈ W := by
    rintro ⟨x, hx, hxy⟩
    obtain ⟨V, hxV, hV⟩ := h x hxy
    apply hx
    exact (le_iSup (fun V : {V : X.Opens // Etale (V.ι ≫ f)} ↦ V.val)
      ⟨V, hV⟩) hxV
  have hle : f ⁻¹ᵁ W ≤ E := by
    intro x hx
    by_contra hxE
    exact hx ⟨x, hxE, rfl⟩
  let g := f ∣_ W
  have hlocal (x : (f ⁻¹ᵁ W).toScheme) :
      ∃ V : (f ⁻¹ᵁ W).toScheme.Opens, x ∈ V ∧ Etale (V.ι ≫ g) := by
    have hxE : (f ⁻¹ᵁ W).ι x ∈ E := hle x.property
    obtain ⟨V, hxV⟩ := (TopologicalSpace.Opens.mem_iSup.mp hxE)
    let T := (f ⁻¹ᵁ W).ι ⁻¹ᵁ V.val
    have hT : Etale (T.ι ≫ (f ⁻¹ᵁ W).ι ≫ f) := by
      have hcomp : T.ι ≫ (f ⁻¹ᵁ W).ι ≫ f =
          ((f ⁻¹ᵁ W).ι ∣_ V.val) ≫ V.val.ι ≫ f := by
        simp only [← Category.assoc, morphismRestrict_ι]
        rfl
      rw [hcomp]
      let : Etale (V.val.ι ≫ f) := V.property
      infer_instance
    have hT' : Etale ((T.ι ≫ g) ≫ W.ι) := by
      simpa only [Category.assoc, g, morphismRestrict_ι] using hT
    let := hT'
    exact ⟨T, hxV, AlgebraicGeometry.Etale.of_comp (T.ι ≫ g) W.ι⟩
  choose V hxV hV using hlocal
  have htop : (⨆ x, V x) = ⊤ := by
    apply top_le_iff.mp
    intro x _
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hxV x⟩
  exact ⟨W, hy, IsZariskiLocalAtSource.of_iSup_eq_top V htop hV⟩

/-- Abhyankar's lemma gives an etale neighborhood of the divisor generic point
for the already finite, explicitly constructed relative normalization.
Source: Stacks Project, Tags 09EB, 0BRM and 0EYG, root-extension paragraph.
(blueprint: lem-sbc-strict-hensel-root-normalization-generic-etale)

Proof: The strict henselization quotient by g is a regular local domain and g
is regular. In the root algebra the coordinate t is regular, its quotient is
H/(g), and t^|G|=g. Its height-one local ring at the root divisor is therefore
a DVR and the root extension has ramification index |G|. Generic components of
the original torsor are Galois for stabilizer subgroups of G. By 09EB their
ramification and residue degrees divide the invertible group order; hence the
extensions are tame. Apply 0BRM: every ramification index becomes one after
adjoining the group-order root, and residue extensions remain separable.
Consequently the relative normalization is etale above the generic point of
the root divisor. The supplied integral regular Cartier divisor is reduced
and has exactly the same support, so its generic point has that same image.
The assumed finite normalization is finitely presented over the Noetherian N.
Its nonetale locus is closed. Its image is closed under the finite structural
map and misses j(eta). Its complement is the required open O, on which the
whole normalization morphism is etale. No assertion of global etaleness or
purity is used, and the finiteness assertion is a separate input. -/
theorem GaloisCover.strict_hensel_root_normalization_generic_etale
    {L U : Scheme.{u}} (i : U ⟶ L)
    (G : Type (u + 1)) [Group G] [Finite G] (W : GaloisCover G U)
    (R : CommRingCat.{u}) (φ : Spec R ⟶ L) (f : R)
    (hG : IsUnit (Nat.card G : R))
    [IsRegularRing R] (hf : IsSMulRegular R f)
    [IsRegularRing (R ⧸ Ideal.span {f})]
    (β : pullback i φ ≅ Scheme.Opens.toScheme (X := Spec R) (PrimeSpectrum.basicOpen f))
    (hβ : β.hom ≫ Scheme.Opens.ι (X := Spec R) (PrimeSpectrum.basicOpen f) = pullback.snd i φ)
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
    Etale p → IsFinite a.fromNormalization →
    ∀ (D : Scheme.{u}) (j : D ⟶ N),
      IsRegular D → IsIntegral D → IsEffectiveCartierCenter j →
      (∀ z : N, z ∈ V ↔ z ∉ Set.range j) →
      ∀ (η : D), IsGenericPoint η Set.univ →
      ∃ (O : N.Opens), j η ∈ O ∧ Etale (a.fromNormalization ∣_ O) := by
  dsimp only
  intro hg hN hp he hn D j hD hDi hj hV η hη
  have hQ := small_regular_divisor_quotient R f barY b hb hg
  have : IsNoetherianRing (strictHenselizationRing barY) := hQ.1
  have : IsRegularRing (strictHenselizationRing barY ⧸ Ideal.span {b.hom f}) := hQ.2.1
  have : IsDomain (strictHenselizationRing barY ⧸ Ideal.span {b.hom f}) := hQ.2.2
  let : Algebra R (strictHenselizationRing barY) := b.hom.toAlgebra
  have : Module.Flat R (strictHenselizationRing barY) :=
    small_strictHenselization_structural_flat R barY b hb
  have hgreg : IsSMulRegular (strictHenselizationRing barY) (b.hom f) := hf.of_flat
  have hG' : IsUnit (Nat.card G : strictHenselizationRing barY) := by
    simpa only [map_natCast] using hG.map b.hom
  have hroot (Q : Ideal (AdjoinRoot
      ((Polynomial.X : Polynomial (strictHenselizationRing barY)) ^ Nat.card G -
        Polynomial.C (b.hom f)))) (hQp : Q.IsPrime) :
      AdjoinRoot.root ((Polynomial.X : Polynomial (strictHenselizationRing barY)) ^
        Nat.card G - Polynomial.C (b.hom f)) ∈ Q →
      IsRegularLocalRing (Localization.AtPrime Q) := by
    have := hQp
    exact AdjoinRoot.isRegularLocalRing_atPrime_of_root_mem
      (strictHenselizationRing barY) (b.hom f) hgreg (Nat.card G)
      (Nat.card_pos) Q
  have := hN
  have := hp
  have := hn
  apply etale_shrink_of_fibre_source_opens _ (j η)
  exact W.root_normalization_generic_source_etale i G R φ f β hβ
    (strictHenselizationRing barY) b hG' hgreg hroot hN hp he hn D j hD hDi hj hV η hη


end AlgebraicGeometry.Scheme
