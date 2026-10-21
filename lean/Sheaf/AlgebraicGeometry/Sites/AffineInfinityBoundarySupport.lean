/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Line
public import Mathlib.AlgebraicGeometry.AffineSpace
public import WeilConjectures.AlgebraicGeometry.Sites.TorsionCohomologicalDimension
public import WeilConjectures.AlgebraicGeometry.Sites.SupportDimension
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.Topology.KrullDimension
public import Mathlib.FieldTheory.IsAlgClosed.Basic

import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselizationLocal
import WeilConjectures.AlgebraicGeometry.Sites.FieldCohomologicalDimension
import Sheaf.AlgebraicGeometry.Sites.PuncturedCoefficientFieldCohomologicalDimension
import all Sheaf.AlgebraicGeometry.Sites.AffineLineInfinityStrictLocalModel
import all Sheaf.AlgebraicGeometry.Sites.AffineLineProjectionStalkBound
import all Sheaf.AlgebraicGeometry.Sites.FieldHigherDirectImageStalk
import Sheaf.AlgebraicGeometry.SmoothStrictLocalFieldModel
import Sheaf.AlgebraicGeometry.StrictHenselizationCompatibility
import WeilConjectures.Mathlib.AlgebraicGeometry.ResidueField
import WeilConjectures.AlgebraicGeometry.StrictHenselizationAffineChartIndEtale
import Sheaf.AlgebraicGeometry.StrictHenselizationClosedFiberComparison
import WeilConjectures.RingTheory.ProEtale.FaithfullyFlat
import Mathlib.RingTheory.Flat.Basic

/-! # The local infinity-boundary calculation

Source: blueprint thm-sc-affine-torsion-cd, punctured strict localizations.
(blueprint: lem-sc-affine-infinity-boundary-support)
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
universe u
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme

private instance strict_local_ring
    {Y : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ Y) :
    IsLocalRing (strictHenselizationRing s) :=
  (AlgebraicGeometry.strictHenselizationLocalStructure s).choose

private instance strict_local_nontrivial
    {Y : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ Y) :
    Nontrivial (strictHenselizationRing s) :=
  (show strictHenselizationRing s ≃+* strictHenselization s from
    (smallStrictHenselizationColimitIso s).commRingCatIsoToRingEquiv).symm.injective.nontrivial

private theorem infinity_strictLocal_principalOpen
    (A : Type u) [CommRing A] {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ Spec (.of A)) :
    let B := Spec (.of A)
    let t := s ≫ ProjectiveLine.infinity B
    ∃ h : strictHenselizationRing t, h ∈ IsLocalRing.maximalIdeal _ ∧ h ≠ 0 ∧
      Nonempty (pullback (ProjectiveLine.affineChart B) (strictHenselizationStructuralMap t) ≅
        Spec (.of (Localization.Away h))) := by
  classical
  let B := Spec (.of A)
  let C := MvPolynomial PUnit.{u + 1} A
  let Y := AlgebraicGeometry.ProjectiveLine B
  let ε := AffineSpace.SpecIso PUnit.{u + 1} (.of A)
  let c : Spec (.of C) ⟶ Y := ε.inv ≫ ProjectiveLine.infinityChart B
  let t := s ≫ ProjectiveLine.infinity B
  let R := strictHenselizationRing t
  let ρ : Spec R ⟶ Y := strictHenselizationStructuralMap t
  let τ : Spec (.of Ω) ⟶ Spec R := Spec.map (strictHenselizationEval t) ≫
    Spec.map (smallStrictHenselizationColimitIso t).hom
  have hτρ : τ ≫ ρ = t := by
    change (Spec.map (strictHenselizationEval t) ≫
      Spec.map (smallStrictHenselizationColimitIso t).hom) ≫ _ = _
    rw [Category.assoc, Etale.strictHenselizationComparison_over]
    exact spec_map_strictHenselizationEval_comp_strictLocalizationToBase t
  have hτ : τ (IsLocalRing.closedPoint Ω) = IsLocalRing.closedPoint R := by
    apply PrimeSpectrum.ext
    change ((IsLocalRing.maximalIdeal Ω).comap (strictHenselizationEval t).hom).comap
      (smallStrictHenselizationColimitIso t).hom.hom = _
    rw [IsLocalRing.maximalIdeal_eq_bot]
    change (RingHom.ker (strictHenselizationEval t).hom).comap
      (smallStrictHenselizationColimitIso t).hom.hom = IsLocalRing.maximalIdeal R
    rw [← maximalIdeal_strictHenselization (s := t)]
    let E : R ≃+* strictHenselization t :=
      (smallStrictHenselizationColimitIso t).commRingCatIsoToRingEquiv
    let : IsLocalHom E.toRingHom := IsLocalHom.of_surjective E.toRingHom E.surjective
    exact IsLocalRing.maximalIdeal_comap E.toRingHom
  have htc : t (IsLocalRing.closedPoint Ω) ∈ Set.range c := by
    refine ⟨(s ≫ AffineSpace.zeroSection PUnit.{u + 1} B ≫ ε.hom)
      (IsLocalRing.closedPoint Ω), ?_⟩
    change ((s ≫ AffineSpace.zeroSection PUnit.{u + 1} B ≫ ε.hom) ≫ c) _ = _
    simp only [c, Category.assoc, Iso.hom_inv_id_assoc]
    rfl
  have hρ : Set.range ρ ⊆ Set.range c := by
    rintro _ ⟨x, rfl⟩
    apply ((IsLocalRing.specializes_closedPoint x).map ρ.continuous).mem_open c.opensRange.2
    rw [← hτ, ← Hom.comp_apply, hτρ]
    exact htc
  let l : Spec R ⟶ Spec (.of C) := IsOpenImmersion.lift c ρ hρ
  have hl : l ≫ c = ρ := IsOpenImmersion.lift_fac c ρ hρ
  let α : C →+* R := (Spec.preimage l).hom
  have hα : Spec.map (CommRingCat.ofHom α) ≫ c = ρ := by
    change Spec.map (Spec.preimage l) ≫ c = ρ
    rw [Spec.map_preimage]
    exact hl
  letI : Algebra C R := α.toAlgebra
  let eR : Spec (.of R) ≅ strictLocalization t :=
    { hom := Spec.map (smallStrictHenselizationColimitIso t).inv
      inv := Spec.map (smallStrictHenselizationColimitIso t).hom
      hom_inv_id := by rw [← Spec.map_comp, Iso.hom_inv_id, Spec.map_id]
      inv_hom_id := by rw [← Spec.map_comp, Iso.inv_hom_id, Spec.map_id] }
  have hind : Algebra.IndEtale C R := strictHenselization_indEtale_of_affine_chart t
    (.of C) c htc eR α (by
      rw [hα]
      exact (smallStrictHenselizationColimitIso_toBase t).symm)
  have hflat : Module.Flat C R := by
    change CommAlgCat.flat C (CommAlgCat.of C R)
    rw [← CommAlgCat.ind_flat]
    obtain ⟨I, hcat, hfilt, P, hP⟩ := hind.exists_colimitPresentation
    letI := hcat
    letI := hfilt
    refine ⟨I, hcat, hfilt, P, fun i ↦ ?_⟩
    have := hP i
    exact inferInstanceAs (Module.Flat C (P.diag.obj i))
  let h : R := α (MvPolynomial.X PUnit.unit)
  have hreg : IsSMulRegular R h := (MvPolynomial.isRegular_X (R := A)
    (n := PUnit.unit)).1.isSMulRegular.of_flat
  have hh0 : h ≠ 0 := by
    intro hh
    have hmul := hreg (a₁ := (1 : R)) (a₂ := 0)
    simp only [hh, zero_smul] at hmul
    exact one_ne_zero (hmul trivial)
  have hopen : ρ ⁻¹ᵁ (ProjectiveLine.affineChart B).opensRange =
      PrimeSpectrum.basicOpen h := by
    have hc : c ⁻¹ᵁ (ProjectiveLine.affineChart B).opensRange =
        PrimeSpectrum.basicOpen (MvPolynomial.X PUnit.unit : C) := by
      dsimp only [c]
      rw [Hom.comp_preimage, ProjectiveLine.infinityChart_preimage_opensRange_affineChart]
      rw [Scheme.preimage_basicOpen_top, AffineSpace.SpecIso_inv_appTop_coord]
      exact basicOpen_eq_of_affine _
    rw [← hl, Hom.comp_preimage, hc]
    have hl' : Spec.map (CommRingCat.ofHom α) = l := Spec.map_preimage l
    rw [← hl']
    exact PrimeSpectrum.comap_basicOpen α (MvPolynomial.X PUnit.unit)
  have hhm : h ∈ IsLocalRing.maximalIdeal R := by
    by_contra hn
    have hx : IsLocalRing.closedPoint R ∈ PrimeSpectrum.basicOpen h := hn
    rw [← hopen] at hx
    have ht' : t (IsLocalRing.closedPoint Ω) ∈
        (ProjectiveLine.affineChart B).opensRange := by
      change ρ (IsLocalRing.closedPoint R) ∈
        (ProjectiveLine.affineChart B).opensRange at hx
      rwa [← hτ, ← Hom.comp_apply, hτρ] at hx
    exact ((ProjectiveLine.range_infinity B).le
      ⟨s (IsLocalRing.closedPoint Ω), rfl⟩) ht' 
  refine ⟨h, hhm, hh0, ⟨?_⟩⟩
  apply IsOpenImmersion.isoOfRangeEq
    (pullback.snd (ProjectiveLine.affineChart B) ρ)
    (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away h))))
  rw [IsOpenImmersion.range_pullbackSnd, hopen]
  exact (PrimeSpectrum.localization_away_comap_range (Localization.Away h) h).symm

private theorem affineLine_infinity_strictLocal_model
    (K : Type u) [Field K] [IsAlgClosed K] (n : ℕ)
    (e : Spec (.of (MvPolynomial (Fin (n + 2)) K)) ≅
      AffineSpace PUnit.{u + 1} (Spec (.of (MvPolynomial (Fin (n + 1)) K))))
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ Spec (.of (MvPolynomial (Fin (n + 1)) K))) :
    let B := Spec (.of (MvPolynomial (Fin (n + 1)) K))
    let b := Spec.map (CommRingCat.ofHom (algebraMap K (MvPolynomial (Fin (n + 1)) K)))
    let Y := AlgebraicGeometry.ProjectiveLine B
    let g := Y ↘ B
    let j := e.hom ≫ ProjectiveLine.affineChart B
    let t := s ≫ ProjectiveLine.infinity B
    let y := t (IsLocalRing.closedPoint Ω)
    letI : Algebra K (Y.residueField y) := ((g ≫ b).residueFieldAlgebraMap y).toAlgebra
    ∃ a : ℕ, a < n + 2 ∧
      residueFieldTrdeg b (s (IsLocalRing.closedPoint Ω)) = (a : Cardinal.{u}) ∧
      Algebra.trdeg K (Y.residueField y) = (a : Cardinal.{u}) ∧
      ∃ h : strictHenselizationRing t, h ∈ IsLocalRing.maximalIdeal _ ∧ h ≠ 0 ∧
        Nonempty (pullback j (strictHenselizationStructuralMap t) ≅
          Spec (.of (Localization.Away h))) := by
  dsimp only
  let B := Spec (.of (MvPolynomial (Fin (n + 1)) K))
  let b : B ⟶ Spec (.of K) :=
    Spec.map (CommRingCat.ofHom (algebraMap K (MvPolynomial (Fin (n + 1)) K)))
  let t := s ≫ ProjectiveLine.infinity B
  obtain ⟨a, ha, htr⟩ := polynomial_residue_trdeg_le K (n + 1)
    (s (IsLocalRing.closedPoint Ω))
  refine ⟨a, by omega, htr, ?_, ?_⟩
  · exact (infinity_residue_trdeg K b (s (IsLocalRing.closedPoint Ω))).trans htr
  · obtain ⟨h, hhm, hh0, ⟨eh⟩⟩ := infinity_strictLocal_principalOpen
      (MvPolynomial (Fin (n + 1)) K) s
    refine ⟨h, hhm, hh0, ⟨?_⟩⟩
    have hp := IsPullback.of_hasPullback (ProjectiveLine.affineChart B)
      (strictHenselizationStructuralMap t)
    have hp' : IsPullback
        (pullback.fst (ProjectiveLine.affineChart B) (strictHenselizationStructuralMap t) ≫
          e.inv)
        (pullback.snd (ProjectiveLine.affineChart B) (strictHenselizationStructuralMap t))
        (e.hom ≫ ProjectiveLine.affineChart B) (strictHenselizationStructuralMap t) := by
      apply hp.of_iso (Iso.refl _) e.symm (Iso.refl _) (Iso.refl _)
      · simp
      · simp
      · simp
      · simp
    exact hp'.isoPullback.symm ≪≫ eh

/-- The local compactification calculation at the infinity section.

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-prop-sf-cbc/
thm-sc-affine-torsion-cd.proof.md, local calculation and passage to affine space.
(blueprint: lem-sc-affine-infinity-boundary-support)

Proof: Let d=n+2. At the chosen infinity point y of P^1 over A^(d-1), the residue
transcendence degree a equals that of the corresponding base point and satisfies a<d.
The smooth strict-local field model constructs a separably closed coefficient field F in
R=O^sh_y, whose fraction field has transcendence degree d-a over F. The infinity divisor
is a nonzero equation h in the maximal ideal of this local domain. Its complement after
strict localization is Spec R[1/h], independently of the affine-line identification e.
For each nonzero polynomial P over F, write P(h)=h^r times a polynomial with nonzero
constant term. The latter is a unit by reduction to the residue field. Thus F(T) embeds
in R[1/h]. Each finitely generated F(T)-subalgebra has dimension at most d-a-1<d.
Apply hIH to these affine spectra with the field bound one for F(T), and use affine-limit
cohomology to obtain torsion cohomological dimension at most d-a for Spec R[1/h].
The cardinal inequality in the statement is equivalent to q>d-a. The strict-local stalk
comparison for the quasi-compact separated open immersion j identifies the given stalk
with degree-q cohomology of this punctured spectrum. Pullback preserves the annihilator N
and hence torsion; the dimension bound makes that cohomology, and therefore the stalk, zero.
This is a local boundary calculation only; the projective-line row, mixed terms, and Leray
assembly are proved separately. -/
theorem isZero_stalk_infinityBoundary_of_lowerDimension
    (K : Type u) [Field K] [IsAlgClosed K] (n : ℕ)
    (hIH : ∀ (L : Type u) [Field L] (m c : ℕ), m < n + 2 →
      (Spec (.of L)).HasTorsionCohomologicalDimensionLE c →
      ∀ (X : Scheme.{u}) [IsAffine X] (a : X ⟶ Spec (.of L))
        [LocallyOfFiniteType a] [QuasiCompact a],
        topologicalKrullDim X ≤ (m : WithBot ℕ∞) →
          X.HasTorsionCohomologicalDimensionLE (m + c))
    (e : Spec (.of (MvPolynomial (Fin (n + 2)) K)) ≅
      AffineSpace PUnit.{u + 1} (Spec (.of (MvPolynomial (Fin (n + 1)) K))))
    (M : Sheaf (Spec (.of (MvPolynomial (Fin (n + 2)) K))).smallEtaleTopology
      AddCommGrpCat.{u + 1}) (N : ℕ) (hN : 0 < N) (hM : N • 𝟙 M = 0)
    (q : ℕ) (_hq : 2 < q) :
    let B := Spec (.of (MvPolynomial (Fin (n + 1)) K))
    let b := Spec.map (CommRingCat.ofHom (algebraMap K (MvPolynomial (Fin (n + 1)) K)))
    let j := e.hom ≫ ProjectiveLine.affineChart B
    ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ B),
      ((n + 2 : ℕ) : Cardinal.{u}) < (q : Cardinal.{u}) +
          residueFieldTrdeg b (s (IsLocalRing.closedPoint Ω)) →
        IsZero ((pointSmallEtale (s ≫ ProjectiveLine.infinity B)).sheafFiber.obj
          (((Etale.lowerStar AddCommGrpCat.{u + 1} j).rightDerived q).obj M)) := by
  classical
  dsimp only
  intro Ω _ _ s hs
  let X := Spec (.of (MvPolynomial (Fin (n + 2)) K))
  let B := Spec (.of (MvPolynomial (Fin (n + 1)) K))
  let b : B ⟶ Spec (.of K) :=
    Spec.map (CommRingCat.ofHom (algebraMap K (MvPolynomial (Fin (n + 1)) K)))
  let Y := AlgebraicGeometry.ProjectiveLine B
  let g : Y ⟶ B := Y ↘ B
  let j : X ⟶ Y := e.hom ≫ ProjectiveLine.affineChart B
  have : QuasiCompact j := inferInstance
  have : QuasiSeparated j := inferInstance
  obtain ⟨hint, hsm, hlft, hqc, hd⟩ := projectiveLine_polynomial_geometry K (n + 1)
  change IsIntegral Y at hint
  change Smooth (g ≫ b) at hsm
  change LocallyOfFiniteType (g ≫ b) at hlft
  change QuasiCompact (g ≫ b) at hqc
  change topologicalKrullDim Y = ((n + 2 : ℕ) : WithBot ℕ∞) at hd
  let v := s ≫ ProjectiveLine.infinity B
  let y := v (IsLocalRing.closedPoint Ω)
  let : Algebra K (Y.residueField y) := ((g ≫ b).residueFieldAlgebraMap y).toAlgebra
  obtain ⟨a, ha, htr, htry, h, hhm, hh0, ⟨eh⟩⟩ :=
    affineLine_infinity_strictLocal_model K n e s
  have hqa : n + 2 - a < q := by
    have hnat : n + 2 < q + a := by
      have hs' : ((n + 2 : ℕ) : Cardinal.{u}) < (q : Cardinal.{u}) + a := by
        rw [← htr]
        exact hs
      exact_mod_cast hs'
    omega
  let χ := (SpecToEquivOfField Ω Y v).2
  let : Algebra (Y.residueField y) Ω := χ.hom.toAlgebra
  have hΩ : Spec.map (CommRingCat.ofHom
      (algebraMap (Y.residueField y) Ω)) ≫ Y.fromSpecResidueField y = v :=
    (SpecToEquivOfField Ω Y).symm_apply_apply v
  let α := Spec.preimage (strictHenselizationStructuralMap v ≫ (g ≫ b))
  let : Algebra K (strictHenselizationRing v) := α.hom.toAlgebra
  have hK : Spec.map (CommRingCat.ofHom (algebraMap K (strictHenselizationRing v))) =
      strictHenselizationStructuralMap v ≫ (g ≫ b) := Spec.map_preimage _
  have hκ : Spec.map (CommRingCat.ofHom (algebraMap K (Y.residueField y))) =
      Y.fromSpecResidueField y ≫ (g ≫ b) := by
    change Spec.map (CommRingCat.ofHom ((g ≫ b).residueFieldAlgebraMap y)) = _
    unfold Hom.residueFieldAlgebraMap
    rw [CommRingCat.ofHom_hom, Spec.map_comp, Spec.map_comp, Category.assoc,
      Spec.map_residueFieldIso_inv_eq_fromSpecResidueField,
      Hom.SpecMap_residueFieldMap_fromSpecResidueField]
  obtain ⟨hreg, hlocal, hdomain, hdim, ε, hε, i, hi, halg,
    F, hF, hKF, φ, hsep, hbij, htrF, htrQ⟩ :=
    smooth_strict_local_field_model K Y (g ≫ b) (n + 2) a hd Ω v y rfl
      hκ hΩ htry hK
  let := hlocal
  let := hdomain
  let := hF
  let := hsep
  let : Algebra F (strictHenselizationRing v) := φ.toRingHom.toAlgebra
  have hcd := hasTorsionCohomologicalDimensionLE_punctured_of_coefficientField n hIH
    F (strictHenselizationRing v) hbij (n + 2 - a) (by omega) (by omega)
    htrQ h hhm hh0
  have hcd' := hcd.of_isUniversalHomeomorphism eh.inv
  have hMt : M.IsTorsion := isTorsion_of_nsmul_id_eq_zero hN hM
  obtain ⟨E⟩ := Etale.nonempty_addEquiv_strictLocalization j Ω v M hMt q
  have : Subsingleton (Sheaf.H
      ((Etale.upperStar AddCommGrpCat.{u + 1}
        (pullback.fst j (strictHenselizationStructuralMap v))).obj M) q) :=
    hcd' _ (Etale.isTorsion_upperStar _ hMt) q hqa
  have : Subsingleton (((pointSmallEtale v).sheafFiber
      (A := AddCommGrpCat.{u + 1})).obj
        (((Etale.lowerStar AddCommGrpCat.{u + 1} j).rightDerived q).obj M)) :=
    E.injective.subsingleton
  exact (AddCommGrpCat.isZero_iff_subsingleton).mpr inferInstance

end AlgebraicGeometry.Scheme
