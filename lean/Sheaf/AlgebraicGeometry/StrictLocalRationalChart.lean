/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C2
-/
module

public import WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMap
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationExtension
public import Mathlib.AlgebraicGeometry.Over
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.RingTheory.AlgebraicIndependent.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import WeilConjectures.ZetaSeries
import Sheaf.AlgebraicGeometry.FiniteTypeResidueTrdeg
import Sheaf.Paper.StrictHenselizationFunctoriality
import Mathlib.FieldTheory.FinTrdeg
import Mathlib.RingTheory.Localization.Algebra
import WeilConjectures.PointCount
import Mathlib.RingTheory.Localization.Integral

/-!
# Rational chart inside a strict localization

Source: Stacks Project, Tags 0F0U and 0F0X
(blueprint: lem-kun-strict-local-rational-chart).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme
open Opposite

private theorem spec_preimage_formula {R S : CommRingCat.{u}} (f : Spec S ⟶ Spec R) :
    Spec.preimage f = (ΓSpecIso R).inv ≫ f.appTop ≫ (ΓSpecIso S).hom := by
  apply Spec.map_injective
  rw [Spec.map_preimage]
  have h := Scheme.toSpecΓ_naturality f
  have hh := congrArg (fun z ↦ z ≫ Spec.map (ΓSpecIso R).inv) h
  simp only [← SpecMap_ΓSpecIso_hom, Category.assoc] at hh
  have hc : Spec.map (ΓSpecIso R).hom ≫ Spec.map (ΓSpecIso R).inv = 𝟙 _ := by
    rw [← Spec.map_comp, Iso.inv_hom_id, Spec.map_id]
  simpa only [Spec.map_comp, Category.assoc, hc, Category.comp_id] using hh

private theorem chart_evaluation_scalars
    {K : Type u} [Field K] (Y : Scheme.{u}) (f : Y ⟶ Spec (.of K))
    (U : Y.Opens) (hU : IsAffineOpen U) (y : Y) (hy : y ∈ U) :
    Spec.preimage (hU.fromSpec ≫ f) ≫ Y.evaluation U y hy =
      CommRingCat.ofHom (f.residueFieldAlgebraMap y) := by
  apply Spec.map_injective
  rw [Spec.map_comp, Spec.map_preimage, f.specMap_residueFieldAlgebraMap]
  have he : Spec.map (Y.evaluation U y hy) ≫ hU.fromSpec =
      Y.fromSpecResidueField y := by
    rw [← Scheme.germ_residue, Spec.map_comp, Category.assoc,
      ← IsAffineOpen.fromSpecStalk, hU.fromSpecStalk_eq_fromSpecStalk]
    rfl
  simpa only [Category.assoc] using congrArg (fun z ↦ z ≫ f) he

private theorem chart_scalar_formula
    {K : Type u} [Field K] (Y : Scheme.{u}) (f : Y ⟶ Spec (.of K))
    (U : Y.Opens) (hU : IsAffineOpen U) :
    Spec.preimage (hU.fromSpec ≫ f) =
      (ΓSpecIso (.of K)).inv ≫ (U.ι ≫ f).appTop ≫ U.topIso.hom := by
  rw [spec_preimage_formula]
  simp only [IsAffineOpen.fromSpec, Scheme.Hom.comp_appTop,
    hU.isoSpec_inv_appTop, Category.assoc, Iso.inv_hom_id, Category.comp_id]

private theorem exists_affine_residue_lifts
    (Y : Scheme.{u}) (y : Y) (ι : Type u) [Finite ι]
    (v : ι → Y.residueField y) :
    ∃ (U : Y.Opens) (_ : IsAffineOpen U) (hy : y ∈ U)
      (t : ι → Γ(Y, U)), ∀ i, Y.evaluation U y hy (t i) = v i := by
  classical
  let := Fintype.ofFinite ι
  choose a ha using fun i ↦ Y.residue_surjective y (v i)
  choose V hyV t ht using fun i ↦ Y.presheaf.exists_germ_eq (a i)
  let W : Y.Opens := ⨅ i, V i
  have hyW : y ∈ W := by
    change y ∈ ((⨅ i, V i : Y.Opens) : Set Y)
    rw [TopologicalSpace.Opens.coe_iInf]
    exact Set.mem_iInter.mpr hyV
  obtain ⟨U, hU, hyU, hUW⟩ := exists_isAffineOpen_mem_and_subset hyW
  have hUV (i : ι) : U ≤ V i := hUW.trans (iInf_le V i)
  refine ⟨U, hU, hyU, fun i ↦ Y.presheaf.map (homOfLE (hUV i)).op (t i), ?_⟩
  intro i
  change Y.residue y (Y.presheaf.germ U y hyU
    (Y.presheaf.map (homOfLE (hUV i)).op (t i))) = v i
  rw [TopCat.Presheaf.germ_res_apply, ht i, ha i]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- A finite transcendence basis can be lifted to an affine chart, and its rational
function field embeds in the strict-local ring with the canonical K-scalar map.

Source: Stacks Project, Tag 0F0U, proof before the compatible-model footnote, and Tag 0F0X,
second paragraph (blueprint: lem-kun-strict-local-rational-chart).

Proof: the residue field at y has finite transcendence degree over K. Choose a finite
transcendence basis and lift its elements to stalk elements, then to regular functions
on a common affine neighbourhood U of y. This is possible because the stalk is the
colimit over neighbourhoods and there are only finitely many functions. Let R be the
polynomial ring over K on these lifts. Its map to the residue field is injective by
algebraic independence. The structural map Spec B to Y factors through U: B is local,
its closed point maps to y, and every point generalizes the closed point. Full faithfulness
of Spec gives a:Gamma(U) to B. For every nonzero polynomial its residue at y is nonzero,
hence its image in the local ring B is a unit. The localization universal property
therefore extends R to FractionRing R in B. Both displayed scalar equalities follow
from that universal property and from the definition of the polynomial evaluation.
The number of variables computes the transcendence degree of FractionRing R and of
the residue field. With an empty basis take R=K; no variables or denominators are needed.
Nontriviality of B follows from its geometric residue map.
-/
theorem exists_strictLocal_rational_chart
    {K : Type u} [Field K] (Y : Scheme.{u}) [Y.Over (Spec (.of K))]
    [LocallyOfFiniteType (Y ↘ Spec (.of K))] [QuasiCompact (Y ↘ Spec (.of K))]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ Y) :
    ∃ U : Y.Opens, s (IsLocalRing.closedPoint Ω) ∈ U ∧
      ∃ hU : IsAffineOpen U,
      ∃ (R : Type u) (_ : CommRing R) (_ : IsDomain R) (_ : Algebra K R)
        (r : CommRingCat.of R ⟶ Γ(U.toScheme, ⊤))
        (a : Γ(U.toScheme, ⊤) ⟶ strictHenselizationRing s)
        (_ : Algebra (FractionRing R) (strictHenselizationRing s)),
        Nontrivial (strictHenselizationRing s) ∧
        Spec.map a ≫ (@Scheme.isoSpec U.toScheme hU).inv ≫ U.ι =
          strictHenselizationStructuralMap s ∧
        (r ≫ a).hom = (algebraMap (FractionRing R) (strictHenselizationRing s)).comp
          (algebraMap R (FractionRing R)) ∧
        ((ΓSpecIso (.of K)).inv ≫ (U.ι ≫ (Y ↘ Spec (.of K))).appTop ≫ a).hom =
          (algebraMap (FractionRing R) (strictHenselizationRing s)).comp
            (algebraMap K (FractionRing R)) ∧
        Algebra.trdeg K (FractionRing R) =
          @Algebra.trdeg K (Y.residueField (s (IsLocalRing.closedPoint Ω))) _ _
            (((Y ↘ Spec (.of K)).residueFieldAlgebraMap
              (s (IsLocalRing.closedPoint Ω))).toAlgebra) := by
  classical
  let y := s (IsLocalRing.closedPoint Ω)
  let f := Y ↘ Spec (.of K)
  let κ := Y.residueField y
  let : Algebra K κ := (f.residueFieldAlgebraMap y).toAlgebra
  let : FinTrdeg K κ := finTrdeg_iff_trdeg.mpr (AlgebraicGeometry.finite_trdeg_residueField
    (K := K) y)
  obtain ⟨t, ht⟩ := exists_finset_isTranscendenceBasis K κ
  obtain ⟨U, hU, hy, v, hv⟩ := exists_affine_residue_lifts Y y t Subtype.val
  let : IsAffine U.toScheme := hU
  let B := strictHenselizationRing s
  let : Algebra κ Ω := (descResidueField (stalkClosedPointTo s)).hom.toAlgebra
  obtain ⟨hl, hstrict, hclosed, -⟩ := AlgebraicGeometry.strictHenselizationResidue s rfl
  let : IsLocalRing B := hl
  let : IsStrictlyHenselianLocalRing B := hstrict
  let g := strictHenselizationStructuralMap s
  have hUB : Set.range g ⊆ Set.range U.ι := by
    rintro _ ⟨x, rfl⟩
    apply ((IsLocalRing.specializes_closedPoint x).map g.continuous).mem_open
      U.ι.opensRange.isOpen
    exact ⟨⟨y, hy⟩, hclosed.symm⟩
  let gU := IsOpenImmersion.lift U.ι g hUB
  let A := Γ(Y, U)
  let aA : A ⟶ B := Spec.preimage (gU ≫ hU.isoSpec.hom)
  have haA : Spec.map aA ≫ hU.fromSpec = g := by
    rw [Spec.map_preimage]
    simp only [IsAffineOpen.fromSpec, Category.assoc, Iso.hom_inv_id_assoc]
    exact IsOpenImmersion.lift_fac U.ι g hUB
  let kA := Spec.preimage (hU.fromSpec ≫ f)
  let : Algebra K A := kA.hom.toAlgebra
  let : Algebra K B := (kA ≫ aA).hom.toAlgebra
  let aa : A →ₐ[K] B := { aA.hom with commutes' _ := rfl }
  let ρ : A →ₐ[K] κ :=
    { (Y.evaluation U y hy).hom with
      commutes' x := ConcreteCategory.congr_hom (chart_evaluation_scalars Y f U hU y hy) x }
  let R := MvPolynomial t K
  let ev : R →ₐ[K] A := MvPolynomial.aeval v
  let bb : R →ₐ[K] B := aa.comp ev
  have hev : ρ.comp ev = MvPolynomial.aeval (fun i : t ↦ (i : κ)) := by
    ext i
    simp only [AlgHom.comp_apply, ev, MvPolynomial.aeval_X]
    change (Y.evaluation U y hy).hom (v i) = (i : κ)
    exact hv i
  have hpoint : Spec.map aA (IsLocalRing.closedPoint B) = hU.primeIdealOf ⟨y, hy⟩ := by
    apply hU.fromSpec.isOpenEmbedding.injective
    rw [hU.fromSpec_primeIdealOf]
    exact (congrArg (fun z : Spec B ⟶ Y ↦ z (IsLocalRing.closedPoint B)) haA).trans hclosed
  have hunits (p : nonZeroDivisors R) : IsUnit (bb p) := by
    by_contra hn
    have hm : bb p ∈ IsLocalRing.maximalIdeal B := by
      simpa only [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] using hn
    have hm' : ev p ∈ (Spec.map aA (IsLocalRing.closedPoint B)).asIdeal := hm
    rw [hpoint, hU.primeIdealOf_eq_map_closedPoint] at hm'
    have hz : ρ (ev p) = 0 := by
      exact (IsLocalRing.residue_eq_zero_iff _).mpr hm'
    have hp : MvPolynomial.aeval (fun i : t ↦ (i : κ)) (p : R) = 0 := by
      rw [← hev]
      exact hz
    exact (mem_nonZeroDivisors_iff_ne_zero.mp p.property)
      ((algebraicIndependent_iff_injective_aeval.mp ht.1) (by simpa using hp))
  let φ : FractionRing R →ₐ[K] B := IsLocalization.liftAlgHom hunits
  let : Algebra (FractionRing R) B := φ.toRingHom.toAlgebra
  let a : Γ(U.toScheme, ⊤) ⟶ B := U.topIso.hom ≫ aA
  let r : CommRingCat.of R ⟶ Γ(U.toScheme, ⊤) :=
    CommRingCat.ofHom ev.toRingHom ≫ U.topIso.inv
  have ha : Spec.map a ≫ U.toScheme.isoSpec.inv ≫ U.ι = g := by
    simpa only [a, Spec.map_comp, IsAffineOpen.fromSpec,
      IsAffineOpen.isoSpec_inv, Scheme.Opens.topIso_hom, Category.assoc] using haA
  have hr : r ≫ a = CommRingCat.ofHom bb.toRingHom := by
    simp only [r, a, Category.assoc, Iso.inv_hom_id_assoc]
    rfl
  have hk : (ΓSpecIso (.of K)).inv ≫ (U.ι ≫ f).appTop ≫ a = kA ≫ aA := by
    simpa only [a, Category.assoc] using congrArg
      (fun z : CommRingCat.of K ⟶ A ↦ z ≫ aA) (chart_scalar_formula Y f U hU).symm
  refine ⟨U, hy, hU, R, inferInstance, inferInstance, inferInstance, r, a,
    inferInstance, inferInstance, ha, ?_, ?_, ?_⟩
  · rw [hr]
    apply RingHom.ext
    intro x
    change bb x = IsLocalization.lift hunits (algebraMap R (FractionRing R) x)
    exact (IsLocalization.lift_eq hunits x).symm
  · rw [hk]
    ext x
    exact (φ.commutes x).symm
  · let : Algebra.IsAlgebraic R (FractionRing R) :=
      IsFractionRing.comap_isAlgebraic_iff.mpr
        (inferInstance : Algebra.IsAlgebraic (FractionRing R) (FractionRing R))
    have hd := trdeg_add_eq K R (A := FractionRing R)
    rw [trdeg_eq_zero (R := R) (A := FractionRing R), add_zero] at hd
    rw [← hd]
    simpa only [R, MvPolynomial.trdeg_of_isDomain, Cardinal.lift_id] using
      ht.cardinalMk_eq_trdeg

end AlgebraicGeometry.Scheme
