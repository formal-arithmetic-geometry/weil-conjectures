/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteRingSectionDeformation.FiniteRingSectionDeformation
public import WeilConjectures.SmoothPurity.DncCoefficientTransport.DncCoefficientTransportData
import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryChartExceptionalScalar
import WeilConjectures.SixFunctors.Etale.Derived.SmoothDuality.Local
import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
import WeilConjectures.SixFunctors.OpenClosed.Conservative
import WeilConjectures.SixFunctors.DncCoefficientTransport.SectionScalarBaseChange

/-! # Coefficient transport data for finite section specialization

The coefficient maps and the two fibre squares are the input data for the
canonical scalar transport argument. Their construction is the coefficient
comparison step in the smooth-purity reduction proof.
(blueprint: new-lem-sp-finite-section-specialization-scalar-canonical-data)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme
open CategoryTheory.MonoidalCategory
namespace AlgebraicGeometry.Etale

/-- Smooth coordinates in the ordered affine-trace model, as in the private chart
construction of `FiniteSmoothDualizingScalar`. The chart at x contains x. -/
private theorem ordinary_smooth_coordinate_chart
    {V S : Scheme.{u}} [IsNoetherian V] [IsNoetherian S]
    (g : V ⟶ S) [IsSeparated g] (d : ℕ) [SmoothOfRelativeDimension d g] (x : V) :
    ∃ (W : V.Opens) (_ : x ∈ W) (e : W.toScheme ⟶ affineTraceTower S d),
      AlgebraicGeometry.Etale e ∧ IsSeparated e ∧ LocallyOfFiniteType e ∧
        QuasiCompact e ∧ W.ι ≫ g = e ≫ affineTraceProjection S d := by
  obtain ⟨T, W, hT, hW, _, hx, hWT, e₀, he₀, he₀g⟩ :=
    Smooth.exists_etale_to_affineSpace g d x
  have : IsAffine W.toScheme := hW
  have : AlgebraicGeometry.Etale e₀ := he₀
  have : IsOpenImmersion (AffineSpace.map (ULift.{u} (Fin d)) T.ι) :=
    MorphismProperty.of_isPullback
      (AffineSpace.isPullback_map (n := ULift.{u} (Fin d)) T.ι).flip
      (inferInstance : IsOpenImmersion T.ι)
  let a := e₀ ≫ AffineSpace.map (ULift.{u} (Fin d)) T.ι
  have ha : W.ι ≫ g = a ≫ (AffineSpace (ULift.{u} (Fin d)) S ↘ S) := by
    dsimp only [a]
    rw [Category.assoc, AffineSpace.map_over, ← Category.assoc, he₀g,
      Scheme.Hom.resLE_comp_ι]
  have : IsSeparated a := inferInstance
  let e := a ≫ (affineTraceAffineSpaceIso S d).inv
  have : AlgebraicGeometry.Etale e := inferInstance
  have : IsSeparated e := inferInstance
  have : LocallyOfFiniteType e := inferInstance
  have : QuasiCompact e := inferInstance
  refine ⟨W, hx, e, inferInstance, inferInstance, inferInstance, inferInstance, ?_⟩
  have hp : affineTraceToAffineSpace S d ≫
      (AffineSpace (ULift.{u} (Fin d)) S ↘ S) = affineTraceProjection S d :=
    AffineSpace.homOfVector_over _ _
  rw [ha, ← hp]
  change a ≫ _ = a ≫ (affineTraceAffineSpaceIso S d).inv ≫
    (affineTraceAffineSpaceIso S d).hom ≫ _
  rw [Iso.inv_hom_id_assoc]

/-- The unit case of the ordinary chart coefficient equation detects invertibility
on a covering family. The existing prime-power argument only uses positivity of
its exponent here; the ordinary P1 input works for any positive annihilator. -/
private theorem finite_smooth_dualizing_iso
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (N : ℕ) (hN : 0 < N)
    (hA : (N : A) = 0) (hB : (N : B) = 0)
    {V S : Scheme.{u}} [IsNoetherian V] [IsNoetherian S]
    (hS : IsUnit (N : Γ(S, ⊤))) (g : V ⟶ S) [HasCompactification g]
    [IsSeparated g] [QuasiCompact g] (d : ℕ) [SmoothOfRelativeDimension d g] :
    IsIso (WeilConjectures.DncCoefficientTransport.dualizingMap φ g) := by
  classical
  have hchart {U : Scheme.{u}} [IsNoetherian U]
      (i : U ⟶ V) [IsOpenImmersion i]
      (e : U ⟶ affineTraceTower S d) [AlgebraicGeometry.Etale e]
      [IsSeparated e] [LocallyOfFiniteType e] [QuasiCompact e]
      (he : i ≫ g = e ≫ affineTraceProjection S d)
      (MA : EtaleCompactSupportNormalization A) (MB : EtaleCompactSupportNormalization B)
      (tA : OrdinaryFiniteTwistTransport A N hA)
      (tB : OrdinaryFiniteTwistTransport B N hB)
      (PA : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (N : Γ(T, ⊤))),
        OrdinaryFiniteP1Datum A N hA tA T hT)
      (PB : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (N : Γ(T, ⊤))),
        OrdinaryFiniteP1Datum B N hB tB T hT) :
      (scalarExtension φ U).map
          ((ProEtale.reductionEtaleChartRightIso A MA g i d e he
            (HasCompactification.compactification g)
            (rightDerivedUpperShriek A g)
            (rightDerivedUpperShriekAdjunction A g)
            N hA tA PA hS).hom.app (𝟙_ _)) ≫
        (ProEtale.reductionEtaleChartScalarIso φ N hA hB hS d e (𝟙_ _)).hom ≫
        (affineTraceRight B N hB S d ⋙ ordinaryFinitePullback B e).map
          (ExceptionalCoefficients.unitIso φ S).hom =
      (scalarPullbackIso φ i).inv.app (dualizingComplex A g) ≫
        (ordinaryFinitePullback B i).map
          (WeilConjectures.DncCoefficientTransport.dualizingMap φ g) ≫
        (ProEtale.reductionEtaleChartRightIso B MB g i d e he
          (HasCompactification.compactification g)
          (rightDerivedUpperShriek B g)
          (rightDerivedUpperShriekAdjunction B g)
          N hB tB PB hS).hom.app (𝟙_ _) := by
    let RB := ProEtale.reductionEtaleChartRightIso B MB g i d e he
      (HasCompactification.compactification g)
      (rightDerivedUpperShriek B g)
      (rightDerivedUpperShriekAdjunction B g)
      N hB tB PB hS
    have h := ordinary_chart_exceptional_scalar φ N hN hA hB hS g i d e he
      MA MB tA tB PA PB (𝟙_ _)
    have hn := RB.hom.naturality (ExceptionalCoefficients.unitIso φ S).hom
    rw [← Category.assoc, h, Category.assoc, Category.assoc, ← hn]
    simp only [WeilConjectures.DncCoefficientTransport.dualizingMap, Functor.map_comp,
      Functor.comp_map, Category.assoc]
    simp only [RB, dualizingComplex]
  obtain ⟨MA⟩ := nonempty_etaleCompactSupportNormalization A
  obtain ⟨MB⟩ := nonempty_etaleCompactSupportNormalization B
  obtain ⟨tA, PA, _⟩ := exists_ordinaryFiniteP1Adjunction N hN A hA
  obtain ⟨tB, PB, _⟩ := exists_ordinaryFiniteP1Adjunction N hN B hB
  choose W hx e he hs hft hqc hg using ordinary_smooth_coordinate_chart g d
  have hlocal (x : V) :
      IsIso ((ordinaryFinitePullback B (W x).ι).map
        (WeilConjectures.DncCoefficientTransport.dualizingMap φ g)) := by
    have : IsLocallyNoetherian (W x).toScheme := inferInstance
    have : TopologicalSpace.NoetherianSpace (W x).toScheme :=
      (W x).ι.isOpenEmbedding.isInducing.noetherianSpace
    have : CompactSpace (W x).toScheme := TopologicalSpace.NoetherianSpace.compactSpace _
    have : IsNoetherian (W x).toScheme := ⟨⟩
    have : AlgebraicGeometry.Etale (e x) := he x
    have : IsSeparated (e x) := hs x
    have : LocallyOfFiniteType (e x) := hft x
    have : QuasiCompact (e x) := hqc x
    let RB := ProEtale.reductionEtaleChartRightIso B MB g (W x).ι d (e x) (hg x)
      (HasCompactification.compactification g)
      (rightDerivedUpperShriek B g)
      (rightDerivedUpperShriekAdjunction B g)
      N hB tB PB hS
    have H : IsIso
        ((scalarPullbackIso φ (W x).ι).inv.app
            (dualizingComplex A g) ≫
          (ordinaryFinitePullback B (W x).ι).map
            (WeilConjectures.DncCoefficientTransport.dualizingMap φ g) ≫
          RB.hom.app (𝟙_ _)) := by
      rw [← hchart (W x).ι (e x) (hg x) MA MB tA tB PA PB]
      infer_instance
    have := IsIso.of_isIso_comp_left
      ((scalarPullbackIso φ (W x).ι).inv.app
        (dualizingComplex A g))
      ((ordinaryFinitePullback B (W x).ι).map
        (WeilConjectures.DncCoefficientTransport.dualizingMap φ g) ≫ RB.hom.app (𝟙_ _))
    exact IsIso.of_isIso_comp_right _ (RB.hom.app (𝟙_ _))
  exact isIso_of_isIso_leftDerivedUpperStar_map_of_jointlySurjective B
      (fun x ↦ (W x).ι) (fun x ↦ ⟨x, ⟨x, hx x⟩, rfl⟩)
      (WeilConjectures.DncCoefficientTransport.dualizingMap φ g) hlocal

end AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Etale.FiniteSmoothPurity

/-- The section coefficient maps are invertible and satisfy both canonical fibre
squares.  This is the coefficient/base-change part of the scalar transport proof.
Source: literature/blueprint/latest/blueprint/sec-smooth-purity/
sk-lem-sp-reduction/sk-lem-sp-reduction-compatibilities.proof.md, (3),
and sk-thm-smooth-purity/sk-thm-smooth-purity-general-ring.proof.md, (2), Steps 1--3.
The maps are obtained by the finite coefficient comparison for the exceptional
right adjoint; the two displayed fibre equations are the specialization of the
section scalar/base-change theorem to the one and zero sections.  The argument
uses only finiteness and the common annihilator and includes zero rings and rank
zero.
(blueprint: new-lem-sp-finite-section-specialization-scalar-canonical-data). -/
theorem finiteSectionScalarTransport_data
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    {V S : Scheme.{u}} [IsNoetherian S]
    (d : ℕ) (g : V ⟶ S) [SmoothOfRelativeDimension d g]
    [HasCompactification g] [IsSeparated g] [QuasiCompact g]
    (s : S ⟶ V) [IsClosedImmersion s]
    [FiniteRingSectionDeformation.Geometry d g s] (hs : s ≫ g = 𝟙 S)
    (hS : IsUnit (N : Γ(S, ⊤))) :
    IsIso (WeilConjectures.DncCoefficientTransport.sectionMap φ g s) ∧
      IsIso (WeilConjectures.DncCoefficientTransport.sectionMap φ
        (Scheme.Hom.deformationSpaceProj g s) s.deformationSpaceSection) ∧
      WeilConjectures.DncCoefficientTransport.FibreCompatibility φ g s hs := by
  have hB : (N : B) = 0 := by
    simpa only [map_natCast, map_zero] using congrArg φ hA
  have hline : IsUnit (N : Γ(AffineSpace (ULift.{u} (Fin 1)) S, ⊤)) := by
    simpa only [map_natCast] using
      hS.map (AffineSpace (ULift.{u} (Fin 1)) S ↘ S).appTop.hom
  have hq := finite_smooth_dualizing_iso φ N hN hA hB hS g d
  have hqF := finite_smooth_dualizing_iso φ N hN hA hB hline
    (Scheme.Hom.deformationSpaceProj g s) d
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold WeilConjectures.DncCoefficientTransport.sectionMap
    infer_instance
  · unfold WeilConjectures.DncCoefficientTransport.sectionMap
    infer_instance
  · exact (WeilConjectures.DncCoefficientTransport.section_scalar_base_change
      φ N hN hA hB hline (Scheme.Hom.deformationSpaceProj g s) d).2
      g (AffineSpace.oneSection (ULift.{u} (Fin 1)) S)
      (Scheme.Hom.deformationSpaceOneFibre g s)
      (Scheme.Hom.isPullback_deformationSpaceOneFibre g s)
      s.deformationSpaceSection s (Scheme.Hom.comp_deformationSpaceOneFibre hs)
  · exact (WeilConjectures.DncCoefficientTransport.section_scalar_base_change
      φ N hN hA hB hline (Scheme.Hom.deformationSpaceProj g s) d).2
      (Scheme.Hom.normalConeProj g s) (AffineSpace.zeroSection (ULift.{u} (Fin 1)) S)
      s.ker.normalConeToDeformationSpace
      (Scheme.Hom.isPullback_normalConeToDeformationSpace g s)
      s.deformationSpaceSection s.normalConeZeroSection
      Scheme.Hom.normalConeZeroSection_comp_normalConeToDeformationSpace

end AlgebraicGeometry.Etale.FiniteSmoothPurity
