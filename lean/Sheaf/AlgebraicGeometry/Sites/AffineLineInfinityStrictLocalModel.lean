/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C4
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Line
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMap
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationExtension
public import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselizationLocal
public import WeilConjectures.AlgebraicGeometry.Sites.SupportDimension
public import WeilConjectures.ZetaSeries
import Sheaf.AlgebraicGeometry.ClosedIrreducibleDimensionTrdeg
import WeilConjectures.PointCount
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.KrullDimension.Field
import WeilConjectures.Mathlib.AlgebraicGeometry.ResidueField
import Sheaf.AlgebraicGeometry.ClosedImmersionResidueFieldIso
import Sheaf.AlgebraicGeometry.SmallStrictHenselizationIndEtale
import WeilConjectures.RingTheory.ProEtale.FaithfullyFlat
import Mathlib.RingTheory.Flat.Basic

/-! # The strict-local principal open at infinity

Source: blueprint `thm-sc-affine-torsion-cd`, compactification and local calculation.
-/

@[expose] public section

-- The public statement is taken out below; the retained helpers are intentionally private.
set_option linter.privateModule false
set_option autoImplicit false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false

universe u
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme

private theorem residueFieldHomOfOver_eq (K : Type u) [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) (x : X) :
    residueFieldHomOfOver f x = f.residueFieldAlgebraMap x := by
  unfold residueFieldHomOfOver Hom.residueFieldAlgebraMap
  congr 1
  rw [Spec.algebraMap_residueFieldIso_inv_assoc, Scheme.residue_residueFieldMap,
    Scheme.Hom.germ_stalkMap_assoc]
  rfl

private theorem polynomial_residue_trdeg_le
    (K : Type u) [Field K] (m : ℕ) (x : Spec (.of (MvPolynomial (Fin m) K))) :
    ∃ a : ℕ, a ≤ m ∧ residueFieldTrdeg
      (Spec.map (CommRingCat.ofHom (algebraMap K (MvPolynomial (Fin m) K)))) x =
        (a : Cardinal.{u}) := by
  let B := Spec (.of (MvPolynomial (Fin m) K))
  let b : B ⟶ Spec (.of K) :=
    Spec.map (CommRingCat.ofHom (algebraMap K (MvPolynomial (Fin m) K)))
  letI : B.Over (Spec (.of K)) := ⟨b⟩
  have hlft : LocallyOfFiniteType (B ↘ Spec (.of K)) := by
    change LocallyOfFiniteType b
    rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
    exact RingHom.finiteType_algebraMap.2 inferInstance
  obtain ⟨a, hdim, htr⟩ := topologicalKrullDim_closed_irreducible_eq_trdeg (K := K)
    (closure ({x} : Set B)) isClosed_closure (isIrreducible_singleton.closure)
      x (subset_closure (Set.mem_singleton x)) rfl
  have hdB : topologicalKrullDim B = (m : WithBot ℕ∞) := by
    change topologicalKrullDim (PrimeSpectrum (MvPolynomial (Fin m) K)) = _
    rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim,
      MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]
    simp
  refine ⟨a, ?_, ?_⟩
  · have hle := topologicalKrullDim_subspace_le B (closure ({x} : Set B))
    rw [hdim, hdB] at hle
    exact_mod_cast hle
  · change @Algebra.trdeg K (B.residueField x) _ _
      (residueFieldHomOfOver b x).toAlgebra = _
    rw [residueFieldHomOfOver_eq]
    exact htr

private theorem infinity_residue_trdeg
    (K : Type u) [Field K] {B : Scheme.{u}} (b : B ⟶ Spec (.of K)) (x : B) :
    let Y := AlgebraicGeometry.ProjectiveLine B
    let i := ProjectiveLine.infinity B
    let g := Y ↘ B
    letI : Algebra K (Y.residueField (i x)) := ((g ≫ b).residueFieldAlgebraMap (i x)).toAlgebra
    Algebra.trdeg K (Y.residueField (i x)) = residueFieldTrdeg b x := by
  let Y := AlgebraicGeometry.ProjectiveLine B
  let i : B ⟶ Y := ProjectiveLine.infinity B
  let g : Y ⟶ B := Y ↘ B
  letI : Algebra K (Y.residueField (i x)) := ((g ≫ b).residueFieldAlgebraMap (i x)).toAlgebra
  letI : Algebra K (B.residueField x) := (b.residueFieldAlgebraMap x).toAlgebra
  have hi : IsClosedImmersion i := by
    have : IsClosedImmersion (i ≫ g) := by
      rw [ProjectiveLine.infinity_over]
      infer_instance
    exact IsClosedImmersion.of_comp i g
  have : IsIso (i.residueFieldMap x) := Hom.isIso_residueFieldMap_of_isClosedImmersion i x
  let ε : Y.residueField (i x) ≃ₐ[K] B.residueField x :=
    { __ := (asIso (i.residueFieldMap x)).commRingCatIsoToRingEquiv
      commutes' := by
        intro k
        have hh := Hom.residueFieldAlgebraMap_comp i (g ≫ b) x
        rw [← Category.assoc, ProjectiveLine.infinity_over, Category.id_comp] at hh
        exact (RingHom.congr_fun hh k).symm }
  change Algebra.trdeg K (Y.residueField (i x)) =
    @Algebra.trdeg K (B.residueField x) _ _ (residueFieldHomOfOver b x).toAlgebra
  rw [residueFieldHomOfOver_eq]
  exact ε.trdeg_eq

/- TAKEN OUT at the upstream sync e47efb5a5 (2026-10-17): does not compile against the source;
returned as a stage-3 repair item.
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
  let τ : Spec (.of Ω) ⟶ Spec R := Spec.map (strictHenselizationEval t)
  have hτρ : τ ≫ ρ = t :=
    spec_map_strictHenselizationEval_comp_strictLocalizationToBase t
  have hτ : τ (IsLocalRing.closedPoint Ω) = IsLocalRing.closedPoint R := by
    apply PrimeSpectrum.ext
    change (IsLocalRing.maximalIdeal Ω).comap (strictHenselizationEval t).hom = _
    rw [IsLocalRing.maximalIdeal_eq_bot]
    exact (maximalIdeal_strictHenselization (s := t)).symm
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
  have hind : Algebra.IndEtale C R := smallStrictHenselization_indEtale_of_affine_chart t
    (.of C) c htc (Iso.refl _) α (by simpa only [Iso.refl_hom, Category.id_comp] using hα)
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
-/

/- TAKEN OUT at the upstream sync e47efb5a5 (2026-10-17): does not compile against the source;
returned as a stage-3 repair item.
/ -- The complement of infinity in a strict localization of the relative projective line
is a principal open cut out by a nonzero element of the maximal ideal. Its residue
transcendence degree agrees with that of the base point and is less than the total dimension.
Source: blueprint `thm-sc-affine-torsion-cd`, proof steps 4--6.
(blueprint: lem-sc-affine-line-infinity-strict-local-model)

Proof: use the infinity chart with coordinate z. The infinity section is z=0 and the
ordinary affine chart meets it in D(z). Since the closed point of the strict localization
lies in the infinity chart, its whole spectrum maps into that chart. Pull z back to h.
Its evaluation at the geometric point is zero, so h lies in the maximal ideal. The
strict localization is ind-etale, hence flat, over this smooth affine chart. The chart
coordinate is a nonzerodivisor; flatness preserves that property, and the strict-local
ring is nonzero, so h is nonzero. Base change of the chart intersection identifies the
open complement with D(h)=Spec R[1/h]. The infinity section induces an isomorphism of
residue fields over K, so its transcendence degree equals that of the base point. It
is a finite natural number a at most n+1: the closed-irreducible dimension theorem
identifies a with the dimension of the base point's closure, which is at most the
dimension n+1 of polynomial affine space. Hence a<n+2. This argument
also applies at n=0 and at nonclosed base points; no closed-point assumption is made. - /
theorem affineLine_infinity_strictLocal_model
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
-/

end AlgebraicGeometry.Scheme
