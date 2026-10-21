/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.Algebra.Regular.SMul
public import WeilConjectures.RingTheory.ProEtale.IndEtale
public import WeilConjectures.Mathlib.RingTheory.Henselian
import WeilConjectures.AlgebraicGeometry.Morphisms.StrictHenselRegularDivisorQuotient
import Sheaf.AlgebraicGeometry.StrictHenselizationClosedFiberComparison
import Sheaf.AlgebraicGeometry.SmallStrictHenselizationIndEtale
import WeilConjectures.AlgebraicGeometry.StrictHenselizationFunctoriality
import Sheaf.AlgebraicGeometry.StrictHenselizationCompatibility
import WeilConjectures.RingTheory.ProEtale.IndWeaklyEtale

/-! # Strict local limits of regular divisors

Source: Stacks Project, Tag 0EYG, strict henselization paragraph; Tags 04GP, 04HX, 06LN and 05WS.
(blueprint: lem-sbc-regular-divisor-strict-local-limit)
-/

@[expose] public section

universe u
set_option autoImplicit false
open CategoryTheory
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


-- Preserve the original existential instance binder name `hH`.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option linter.unusedVariables false in
/-- A regular divisor has a pointed regular strict local ind-etale limit.

Source: Stacks Project, Tag 0EYG, strict henselization paragraph; Tags 04GP,
04HX, 06LN and 05WS for strict henselization and passage to the quotient.
(blueprint: lem-sbc-regular-divisor-strict-local-limit)

Proof: Localize R at y, choose a separable closure of its residue field, and
form its strict henselization H as the filtered colimit of pointed etale
neighbourhood algebras. Its structural map from R is ind-etale (localization
is ind-etale, and so is this filtered etale colimit). H is strictly henselian
local, and the contraction of its maximal ideal is y; take x to be its
closed point. The local ring of R at y is regular, so H is regular local
by Tag 06LN. Flatness of R to H preserves injective multiplication by g.
Because g belongs to y, its image lies in the maximal ideal of H. The
quotient H/(g) is the strict henselization of the localization of R/(g)
at the image of y (Tag 05WS); it is regular local by Tag 06LN. These
constructions all stay in the universe of R using small representatives.
Edge cases: y excludes the zero ring, and hy excludes a unit g. A regular
g=0 can occur only in the zero ring, so cannot satisfy these hypotheses. -/
theorem regular_divisor_strict_local_limit
    (R : CommRingCat.{u}) (g : R) [IsRegularRing R]
    (hg : IsSMulRegular R g) [IsRegularRing (R ⧸ Ideal.span {g})]
    (y : Spec R) (hy : g ∈ y.asIdeal) :
    ∃ (H : CommRingCat.{u}) (ι : R →+* H),
      ι.IndEtale ∧
      ∃ (hH : IsStrictlyHenselianLocalRing H),
        IsRegularLocalRing H ∧ IsRegularLocalRing (H ⧸ Ideal.span {ι g}) ∧
        IsSMulRegular H (ι g) ∧
        ι g ∈ IsLocalRing.maximalIdeal H ∧
        ∃ x : Spec H, (Spec.map (CommRingCat.ofHom ι)) x = y := by
  classical
  let Ω := AlgebraicClosure ((Spec R).residueField y)
  let barY : Spec (.of Ω) ⟶ Spec R :=
    Spec.map (CommRingCat.ofHom (algebraMap ((Spec R).residueField y) Ω)) ≫
      (Spec R).fromSpecResidueField y
  have hbarY : barY (IsLocalRing.closedPoint Ω) = y :=
    (Spec R).fromSpecResidueField_apply y _
  let : Algebra ((Spec R).residueField (barY (IsLocalRing.closedPoint Ω))) Ω :=
    (descResidueField (stalkClosedPointTo barY)).hom.toAlgebra
  obtain ⟨hfullLocal, _, hfull, _⟩ := AlgebraicGeometry.strictHenselizationResidue barY rfl
  let : IsLocalRing (strictHenselization barY) := hfullLocal
  obtain ⟨hlocal, hstrict⟩ := AlgebraicGeometry.strictHenselizationLocalStructure barY
  let H := strictHenselizationRing barY
  have : IsLocalRing H := hlocal
  have hx : strictHenselizationStructuralMap barY (IsLocalRing.closedPoint H) =
      barY (IsLocalRing.closedPoint Ω) := by
    have hp : Spec.map (smallStrictHenselizationColimitIso barY).inv
        (IsLocalRing.closedPoint H) =
        IsLocalRing.closedPoint (strictHenselization barY) :=
      @AlgebraicGeometry.Spec_closedPoint (strictHenselization barY)
        (strictHenselizationRing barY) hfullLocal hlocal
        (smallStrictHenselizationColimitIso barY).inv inferInstance
    have hc := congrArg (fun k : Spec H ⟶ Spec R ↦ k (IsLocalRing.closedPoint H))
      (smallStrictHenselizationColimitIso_toBase barY)
    exact hc.symm.trans ((congrArg (fun x ↦ strictLocalizationToBase barY x) hp).trans hfull)
  let b : R ⟶ H := Spec.preimage (strictHenselizationStructuralMap barY)
  have hb : Spec.map b = strictHenselizationStructuralMap barY := Spec.map_preimage _
  have hi : b.hom.IndEtale := by
    have h := smallStrictHenselization_indEtale_of_affine_chart barY R (𝟙 (Spec R))
      (by simp) (Iso.refl _) b.hom (by
        change Spec.map b ≫ 𝟙 (Spec R) = strictHenselizationStructuralMap barY
        rw [Category.comp_id]
        exact hb)
    exact h
  have hpoint : (Spec.map b) (IsLocalRing.closedPoint H) = y := by
    rw [hb]
    exact hx.trans hbarY
  have hgm : b.hom g ∈ IsLocalRing.maximalIdeal H := by
    have h := congrArg PrimeSpectrum.asIdeal hpoint
    change (IsLocalRing.maximalIdeal H).comap b.hom = y.asIdeal at h
    change g ∈ (IsLocalRing.maximalIdeal H).comap b.hom
    rw [h]
    exact hy
  have hnunit : ¬ IsUnit (b.hom g) :=
    (IsLocalRing.mem_maximalIdeal _).mp hgm
  obtain ⟨_, hquot, hdomain⟩ :=
    small_regular_divisor_quotient R g barY b hb hnunit
  have : IsRegularRing (H ⧸ Ideal.span {b.hom g}) := hquot
  have : IsDomain (H ⧸ Ideal.span {b.hom g}) := hdomain
  have : IsLocalRing (H ⧸ Ideal.span {b.hom g}) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
  have hquotLocal : IsRegularLocalRing (H ⧸ Ideal.span {b.hom g}) :=
    IsRegularLocalRing.of_isRegularRing_of_isLocalRing _
  -- The existing quotient comparison also handles zero, giving ambient regularity.
  have : IsRegularRing (R ⧸ Ideal.span {(0 : R)}) :=
    IsRegularRing.of_ringEquiv ((RingEquiv.quotientBot R).symm.trans
      (Ideal.quotEquivOfEq (Ideal.span_singleton_zero (α := R))).symm)
  obtain ⟨_, hzero, _⟩ :=
    small_regular_divisor_quotient R 0 barY b hb (by simp)
  have : IsRegularRing (H ⧸ Ideal.span {b.hom (0 : R)}) := hzero
  let e0 : (H ⧸ Ideal.span {b.hom (0 : R)}) ≃+* H :=
    (Ideal.quotEquivOfEq (by rw [map_zero, Ideal.span_singleton_zero])).trans
      (RingEquiv.quotientBot H)
  have : IsRegularRing H := IsRegularRing.of_ringEquiv e0
  have hreg : IsRegularLocalRing H :=
    IsRegularLocalRing.of_isRegularRing_of_isLocalRing _
  let : Algebra R H := b.hom.toAlgebra
  have : Algebra.IndEtale R H := hi
  have hsmul : IsSMulRegular H (b.hom g) := hg.of_flat
  exact ⟨H, b.hom, hi, hstrict, hreg, hquotLocal, hsmul, hgm,
    IsLocalRing.closedPoint H, hpoint⟩

end AlgebraicGeometry.Scheme
