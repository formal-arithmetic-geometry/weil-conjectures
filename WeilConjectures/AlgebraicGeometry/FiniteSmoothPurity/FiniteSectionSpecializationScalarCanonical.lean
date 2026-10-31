/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteRingSectionDeformation.FiniteRingSectionDeformation
public import WeilConjectures.SmoothPurity.DncCoefficientTransport.DncCoefficientTransportData
import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteSectionScalarTransportData
import WeilConjectures.AlgebraicGeometry.Scalar.ScalarSectionCompositor

/-! # Canonical normalized finite-section scalar transport

Source: blueprint/latest, smooth-purity reduction compatibility proof (3), Orientation,
and general-ring proof (2), Steps 4--7.
(blueprint: new-lem-sp-finite-section-specialization-scalar-canonical).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.Etale.FiniteSmoothPurity

/-- The canonical normalized B-comparison satisfies the scalar specialization square.

This is the canonical construction step in the general-ring argument: scalar/base-change
squares identify the one and zero fibre mates; finite-family constancy and shifted-line
rigidity construct the unique normalized B-family comparison; restricting its conjugation
identity to the zero fibre gives the displayed equation. The construction is independent
of any supplied normalized B-comparison, which is recovered by uniqueness in the parent
lemma. Empty bases, zero rings, and rank zero use the same canonical maps.
Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-lem-sp-reduction/
sk-lem-sp-reduction-compatibilities.proof.md, (3), Orientation, and
sk-thm-smooth-purity/sk-thm-smooth-purity-general-ring.proof.md, (2), Steps 4--7.
(blueprint: new-lem-sp-finite-section-specialization-scalar-canonical). -/
private theorem scalar_transport_specialization
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {V S : Scheme.{u}} (g : V ⟶ S)
    [HasCompactification g] [QuasiCompact g]
    (s : S ⟶ V) [IsClosedImmersion s] (hs : s ≫ g = 𝟙 S)
    [HasCompactification (Scheme.Hom.deformationSpaceProj g s)]
    [HasCompactification (Scheme.Hom.normalConeProj g s)]
    [QuasiCompact (Scheme.Hom.normalConeProj g s)]
    (hcompat : WeilConjectures.DncCoefficientTransport.FibreCompatibility φ g s hs)
    (hq : IsIso (WeilConjectures.DncCoefficientTransport.sectionMap φ g s))
    (hqF : IsIso (WeilConjectures.DncCoefficientTransport.sectionMap φ
      (Scheme.Hom.deformationSpaceProj g s) s.deformationSpaceSection))
    (κR : NoetherianSectionSpecialization.family A g s ≅
      (upperStar (ModuleCat.{u + 1} A)
        (AffineSpace (ULift.{u} (Fin 1)) S ↘ S)).leftDerivedFunctor.obj
          (sectionInvariant A g s))
    (hκR : NoetherianSectionSpecialization.Normalized A g s hs κR) :
    ∃ κB : NoetherianSectionSpecialization.family B g s ≅
      (upperStar (ModuleCat.{u + 1} B)
        (AffineSpace (ULift.{u} (Fin 1)) S ↘ S)).leftDerivedFunctor.obj
        (sectionInvariant B g s),
      NoetherianSectionSpecialization.Normalized B g s hs κB ∧
      (WeilConjectures.DncCoefficientTransport.sectionMap φ g s ≫
          NoetherianSectionSpecialization.specialization B g s κB =
        (scalarExtension φ S).map
            (NoetherianSectionSpecialization.specialization A g s κR) ≫
          WeilConjectures.DncCoefficientTransport.sectionMap φ
            (Scheme.Hom.normalConeProj g s) s.normalConeZeroSection) := by
  let a := AffineSpace (ULift.{u} (Fin 1)) S ↘ S
  let EA := scalarExtension φ (AffineSpace (ULift.{u} (Fin 1)) S)
  let ES := scalarExtension φ S
  let aB := (upperStar (ModuleCat.{u + 1} B) a).leftDerivedFunctor
  let q := asIso (WeilConjectures.DncCoefficientTransport.sectionMap φ g s)
  let qF := asIso (WeilConjectures.DncCoefficientTransport.sectionMap φ
    (Scheme.Hom.deformationSpaceProj g s) s.deformationSpaceSection)
  let κB := qF.symm ≪≫ EA.mapIso κR ≪≫
    (scalarPullbackIso φ a).symm.app _ ≪≫ aB.mapIso q
  have hconj : WeilConjectures.DncCoefficientTransport.sectionMap φ
      (Scheme.Hom.deformationSpaceProj g s) s.deformationSpaceSection ≫ κB.hom =
      EA.map κR.hom ≫ (scalarPullbackIso φ a).inv.app _ ≫
        aB.map (WeilConjectures.DncCoefficientTransport.sectionMap φ g s) := by
    simp [κB, qF, q]
  have hnorm : NoetherianSectionSpecialization.Normalized B g s hs κB := by
    let i := AffineSpace.oneSection (ULift.{u} (Fin 1)) S
    let iA := (upperStar (ModuleCat.{u + 1} A) i).leftDerivedFunctor
    let iB := (upperStar (ModuleCat.{u + 1} B) i).leftDerivedFunctor
    let cA := leftDerivedUpperStarCompSectionIso (ModuleCat.{u + 1} A) i a
      (AffineSpace.oneSection_comp_over (ULift.{u} (Fin 1)) S)
    let cB := leftDerivedUpperStarCompSectionIso (ModuleCat.{u + 1} B) i a
      (AffineSpace.oneSection_comp_over (ULift.{u} (Fin 1)) S)
    have hn := ((scalarPullbackIso φ i).inv.naturality κR.hom).symm
    change (scalarPullbackIso φ i).inv.app _ ≫ iB.map (EA.map κR.hom) =
      ES.map (iA.map κR.hom) ≫ (scalarPullbackIso φ i).inv.app _ at hn
    have hc := cB.hom.naturality
      (WeilConjectures.DncCoefficientTransport.sectionMap φ g s)
    change iB.map (aB.map (WeilConjectures.DncCoefficientTransport.sectionMap φ g s)) ≫
      cB.hom.app _ = cB.hom.app _ ≫
        WeilConjectures.DncCoefficientTransport.sectionMap φ g s at hc
    have hcoh := scalar_section_compositor φ i a
      (AffineSpace.oneSection_comp_over (ULift.{u} (Fin 1)) S)
      (sectionInvariant A g s)
    change (scalarPullbackIso φ i).inv.app _ ≫
      iB.map ((scalarPullbackIso φ a).inv.app _) ≫ cB.hom.app _ =
      ES.map (cA.hom.app _) at hcoh
    change iB.map κB.hom ≫ cB.hom.app _ = _
    apply (cancel_epi ((scalarPullbackIso φ i).inv.app _ ≫
      iB.map (WeilConjectures.DncCoefficientTransport.sectionMap φ
        (Scheme.Hom.deformationSpaceProj g s) s.deformationSpaceSection))).1
    simp only [Category.assoc]
    erw [← iB.map_comp_assoc, hconj]
    simp only [Functor.map_comp, Category.assoc]
    rw [hc]
    erw [reassoc_of% hn, reassoc_of% hcoh]
    erw [← ES.map_comp_assoc, hκR]
    exact hcompat.1.symm
  have hspecial : WeilConjectures.DncCoefficientTransport.sectionMap φ g s ≫
      NoetherianSectionSpecialization.specialization B g s κB =
      ES.map (NoetherianSectionSpecialization.specialization A g s κR) ≫
        WeilConjectures.DncCoefficientTransport.sectionMap φ
          (Scheme.Hom.normalConeProj g s) s.normalConeZeroSection := by
    let i := AffineSpace.zeroSection (ULift.{u} (Fin 1)) S
    let iA := (upperStar (ModuleCat.{u + 1} A) i).leftDerivedFunctor
    let iB := (upperStar (ModuleCat.{u + 1} B) i).leftDerivedFunctor
    let cA := leftDerivedUpperStarCompSectionIso (ModuleCat.{u + 1} A) i a
      (AffineSpace.zeroSection_comp_over (ULift.{u} (Fin 1)) S)
    let cB := leftDerivedUpperStarCompSectionIso (ModuleCat.{u + 1} B) i a
      (AffineSpace.zeroSection_comp_over (ULift.{u} (Fin 1)) S)
    have hconjInv : aB.map (WeilConjectures.DncCoefficientTransport.sectionMap φ g s) ≫
        κB.inv = (scalarPullbackIso φ a).hom.app _ ≫ EA.map κR.inv ≫
          WeilConjectures.DncCoefficientTransport.sectionMap φ
            (Scheme.Hom.deformationSpaceProj g s) s.deformationSpaceSection := by
      simp [κB, q, qF, Category.assoc]
    have hc := cB.inv.naturality
      (WeilConjectures.DncCoefficientTransport.sectionMap φ g s)
    change WeilConjectures.DncCoefficientTransport.sectionMap φ g s ≫ cB.inv.app _ =
      cB.inv.app _ ≫ iB.map (aB.map
        (WeilConjectures.DncCoefficientTransport.sectionMap φ g s)) at hc
    have hn := ((scalarPullbackIso φ i).inv.naturality κR.inv).symm
    change (scalarPullbackIso φ i).inv.app _ ≫ iB.map (EA.map κR.inv) =
      ES.map (iA.map κR.inv) ≫ (scalarPullbackIso φ i).inv.app _ at hn
    have hcoh := scalar_section_compositor φ i a
      (AffineSpace.zeroSection_comp_over (ULift.{u} (Fin 1)) S)
      (sectionInvariant A g s)
    have hcohInv : cB.inv.app (ES.obj (sectionInvariant A g s)) ≫
        iB.map ((scalarPullbackIso φ a).hom.app (sectionInvariant A g s)) =
      ES.map (cA.inv.app (sectionInvariant A g s)) ≫
        (scalarPullbackIso φ i).inv.app
          ((upperStar (ModuleCat.{u + 1} A) a).leftDerivedFunctor.obj
            (sectionInvariant A g s)) := by
      apply (cancel_mono (iB.map ((scalarPullbackIso φ a).inv.app _))).1
      simp only [Category.assoc, ← CategoryTheory.Functor.map_comp, Iso.hom_inv_id_app]
      apply (cancel_mono (cB.hom.app _)).1
      simp only [Category.assoc]
      rw [hcoh, ← ES.map_comp, Iso.inv_hom_id_app]
      erw [iB.map_id, Category.id_comp, Iso.inv_hom_id_app, ES.map_id]
      rfl
    change WeilConjectures.DncCoefficientTransport.sectionMap φ g s ≫
        (cB.inv.app _ ≫ iB.map κB.inv ≫ _) =
      ES.map (cA.inv.app _ ≫ iA.map κR.inv ≫ _) ≫ _
    rw [← Category.assoc, hc]
    simp only [Category.assoc]
    rw [← Functor.map_comp_assoc, hconjInv]
    simp only [Functor.map_comp, Category.assoc]
    rw [reassoc_of% hcohInv, reassoc_of% hn, hcompat.2]
  exact ⟨κB, hnorm, hspecial⟩

theorem finiteSectionSpecialization_scalar_canonical
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    {V S : Scheme.{u}} [IsNoetherian S]
    (d : ℕ) (g : V ⟶ S) [SmoothOfRelativeDimension d g]
    [HasCompactification g] [IsSeparated g] [QuasiCompact g]
    (s : S ⟶ V) [IsClosedImmersion s]
    [FiniteRingSectionDeformation.Geometry d g s] (hs : s ≫ g = 𝟙 S)
    (hS : IsUnit (N : Γ(S, ⊤)))
    (κ : NoetherianSectionSpecialization.family A g s ≅
      (ordinaryFinitePullback A (AffineSpace (ULift.{u} (Fin 1)) S ↘ S)).obj
        (sectionInvariant A g s))
    (hκ : NoetherianSectionSpecialization.Normalized A g s hs κ) :
    ∃ κB : NoetherianSectionSpecialization.family B g s ≅
      (ordinaryFinitePullback B (AffineSpace (ULift.{u} (Fin 1)) S ↘ S)).obj
        (sectionInvariant B g s),
      NoetherianSectionSpecialization.Normalized B g s hs κB ∧
      WeilConjectures.DncCoefficientTransport.sectionMap φ g s ≫
          NoetherianSectionSpecialization.specialization B g s κB =
        (scalarExtension φ S).map
            (NoetherianSectionSpecialization.specialization A g s κ) ≫
          WeilConjectures.DncCoefficientTransport.sectionMap φ
            (Scheme.Hom.normalConeProj g s) s.normalConeZeroSection := by
  have hB : (N : B) = 0 := by
    rw [← map_natCast φ, hA, map_zero]
  obtain ⟨hq, hqF, hcompat⟩ := finiteSectionScalarTransport_data φ N hN hA d g s hs hS
  exact scalar_transport_specialization φ g s hs hcompat hq hqF κ hκ

end AlgebraicGeometry.Etale.FiniteSmoothPurity
