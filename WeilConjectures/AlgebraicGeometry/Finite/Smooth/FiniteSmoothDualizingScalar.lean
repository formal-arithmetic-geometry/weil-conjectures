/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.DncCoefficientTransport.DncCoefficientTransportData
import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryChartExceptionalScalar
import WeilConjectures.SixFunctors.Etale.Derived.SmoothDuality.Local
import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
import WeilConjectures.SixFunctors.OpenClosed.Conservative

/-! # Smooth dualizing coefficient comparison in ordinary etale coordinates -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

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

/-- Invertibility and the counit-normalized chart value of the ordinary dualizing
coefficient map for finite rings killed by a positive prime power invertible on the base.
Source: blueprint/latest, sec-smooth-purity/sk-lem-sp-reduction/
sk-lem-sp-reduction-exceptional.proof.md, etale chart argument, and
sk-thm-smooth-purity-general-ring.proof.md, Proof (2), first sentences
(blueprint: lem-pur-finite-smooth-dualizing-scalar).
Proof: identify the intrinsic constructible right adjoints in reductionExceptional_isIso
with the ordinary rightDerivedUpperShriek by their counits, using its realization
clauses. Evaluate at the free rank-one coefficient unit and use the scalar-unit
isomorphism. The result is precisely dualizingScalarMap, since adjunction transposition
is injective. On a chart the same counit is etale summation followed by the ordered
affine trace. The chart clause therefore identifies the map with the specified
root-normalized Tate reassociation. The ordinary coefficient unit is bounded
constructible of finite Tor dimension, so every use of the intrinsic theorem is
on its asserted domain. The free-line calculation uses no flatness of B over A.
Isomorphism detection on the etale chart cover gives the global assertion. -/
theorem finite_smooth_dualizing_scalar
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (ell n : ℕ) [Fact ell.Prime] (hn : 1 ≤ n)
    (hA : ((ell ^ n : ℕ) : A) = 0) (hB : ((ell ^ n : ℕ) : B) = 0)
    {V S : Scheme.{u}} [IsNoetherian V] [IsNoetherian S]
    (hS : IsUnit ((ell ^ n : ℕ) : Γ(S, ⊤))) (g : V ⟶ S) [HasCompactification g]
    [IsSeparated g] [QuasiCompact g] (d : ℕ) [SmoothOfRelativeDimension d g] :
    IsIso (ExceptionalCoefficients.dualizingScalarMap φ g) ∧
    ∀ {U : Scheme.{u}} [IsNoetherian U] (i : U ⟶ V) [IsOpenImmersion i]
      (e : U ⟶ affineTraceTower S d) [AlgebraicGeometry.Etale e]
      [IsSeparated e] [LocallyOfFiniteType e] [QuasiCompact e]
      (he : i ≫ g = e ≫ affineTraceProjection S d)
      (MA : EtaleCompactSupportNormalization A)
      (MB : EtaleCompactSupportNormalization B)
      (tA : OrdinaryFiniteTwistTransport A (ell ^ n) hA)
      (tB : OrdinaryFiniteTwistTransport B (ell ^ n) hB)
      (PA : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit ((ell ^ n : ℕ) : Γ(T, ⊤))),
        OrdinaryFiniteP1Datum A (ell ^ n) hA tA T hT)
      (PB : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit ((ell ^ n : ℕ) : Γ(T, ⊤))),
        OrdinaryFiniteP1Datum B (ell ^ n) hB tB T hT),
      (scalarExtension φ U).map
          ((ProEtale.reductionEtaleChartRightIso A MA g i d e he
            (HasCompactification.compactification g)
            (rightDerivedUpperShriek A g)
            (rightDerivedUpperShriekAdjunction A g)
            (ell ^ n) hA tA PA hS).hom.app (𝟙_ _)) ≫
        (ProEtale.reductionEtaleChartScalarIso φ (ell ^ n) hA hB hS d e (𝟙_ _)).hom ≫
        (affineTraceRight B (ell ^ n) hB S d ⋙ ordinaryFinitePullback B e).map
          (ExceptionalCoefficients.unitIso φ S).hom =
      (scalarPullbackIso φ i).inv.app (dualizingComplex A g) ≫
        (ordinaryFinitePullback B i).map
          (WeilConjectures.DncCoefficientTransport.dualizingMap φ g) ≫
        (ProEtale.reductionEtaleChartRightIso B MB g i d e he
          (HasCompactification.compactification g)
          (rightDerivedUpperShriek B g)
          (rightDerivedUpperShriekAdjunction B g)
          (ell ^ n) hB tB PB hS).hom.app (𝟙_ _) := by
  classical
  have _hn := hn
  have hN : 0 < ell ^ n := pow_pos (Fact.out : ell.Prime).pos n
  have hchart {U : Scheme.{u}} [IsNoetherian U]
      (i : U ⟶ V) [IsOpenImmersion i]
      (e : U ⟶ affineTraceTower S d) [AlgebraicGeometry.Etale e]
      [IsSeparated e] [LocallyOfFiniteType e] [QuasiCompact e]
      (he : i ≫ g = e ≫ affineTraceProjection S d)
      (MA : EtaleCompactSupportNormalization A) (MB : EtaleCompactSupportNormalization B)
      (tA : OrdinaryFiniteTwistTransport A (ell ^ n) hA)
      (tB : OrdinaryFiniteTwistTransport B (ell ^ n) hB)
      (PA : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit ((ell ^ n : ℕ) : Γ(T, ⊤))),
        OrdinaryFiniteP1Datum A (ell ^ n) hA tA T hT)
      (PB : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit ((ell ^ n : ℕ) : Γ(T, ⊤))),
        OrdinaryFiniteP1Datum B (ell ^ n) hB tB T hT) :
      (scalarExtension φ U).map
          ((ProEtale.reductionEtaleChartRightIso A MA g i d e he
            (HasCompactification.compactification g)
            (rightDerivedUpperShriek A g)
            (rightDerivedUpperShriekAdjunction A g)
            (ell ^ n) hA tA PA hS).hom.app (𝟙_ _)) ≫
        (ProEtale.reductionEtaleChartScalarIso φ (ell ^ n) hA hB hS d e (𝟙_ _)).hom ≫
        (affineTraceRight B (ell ^ n) hB S d ⋙ ordinaryFinitePullback B e).map
          (ExceptionalCoefficients.unitIso φ S).hom =
      (scalarPullbackIso φ i).inv.app (dualizingComplex A g) ≫
        (ordinaryFinitePullback B i).map
          (WeilConjectures.DncCoefficientTransport.dualizingMap φ g) ≫
        (ProEtale.reductionEtaleChartRightIso B MB g i d e he
          (HasCompactification.compactification g)
          (rightDerivedUpperShriek B g)
          (rightDerivedUpperShriekAdjunction B g)
          (ell ^ n) hB tB PB hS).hom.app (𝟙_ _) := by
    let RB := ProEtale.reductionEtaleChartRightIso B MB g i d e he
      (HasCompactification.compactification g)
      (rightDerivedUpperShriek B g)
      (rightDerivedUpperShriekAdjunction B g)
      (ell ^ n) hB tB PB hS
    have h := ordinary_chart_exceptional_scalar φ (ell ^ n) hN hA hB hS g i d e he
      MA MB tA tB PA PB (𝟙_ _)
    have hn := RB.hom.naturality (ExceptionalCoefficients.unitIso φ S).hom
    rw [← Category.assoc, h, Category.assoc, Category.assoc, ← hn]
    simp only [WeilConjectures.DncCoefficientTransport.dualizingMap, Functor.map_comp,
      Functor.comp_map, Category.assoc]
    simp only [RB, dualizingComplex]
  refine ⟨?_, ?_⟩
  swap
  · intro U _ i _ e _ _ _ _ he MA MB tA tB PA PB
    exact hchart i e he MA MB tA tB PA PB
  obtain ⟨MA⟩ := nonempty_etaleCompactSupportNormalization A
  obtain ⟨MB⟩ := nonempty_etaleCompactSupportNormalization B
  obtain ⟨tA, PA, _⟩ := exists_ordinaryFiniteP1Adjunction (ell ^ n) hN A hA
  obtain ⟨tB, PB, _⟩ := exists_ordinaryFiniteP1Adjunction (ell ^ n) hN B hB
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
    let RA := ProEtale.reductionEtaleChartRightIso A MA g (W x).ι d (e x) (hg x)
      (HasCompactification.compactification g)
      (rightDerivedUpperShriek A g)
      (rightDerivedUpperShriekAdjunction A g)
      (ell ^ n) hA tA PA hS
    let RB := ProEtale.reductionEtaleChartRightIso B MB g (W x).ι d (e x) (hg x)
      (HasCompactification.compactification g)
      (rightDerivedUpperShriek B g)
      (rightDerivedUpperShriekAdjunction B g)
      (ell ^ n) hB tB PB hS
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
  have H : IsIso (WeilConjectures.DncCoefficientTransport.dualizingMap φ g) :=
    isIso_of_isIso_leftDerivedUpperStar_map_of_jointlySurjective B
      (fun x ↦ (W x).ι) (fun x ↦ ⟨x, ⟨x, hx x⟩, rfl⟩)
      (WeilConjectures.DncCoefficientTransport.dualizingMap φ g) hlocal
  simpa only [WeilConjectures.DncCoefficientTransport.dualizingMap,
    ExceptionalCoefficients.dualizingScalarMap] using H

end AlgebraicGeometry.Etale
