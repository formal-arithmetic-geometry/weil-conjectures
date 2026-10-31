/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CoordinateCounitArrows
public import WeilConjectures.AlgebraicGeometry.SectionCentredChartData
import WeilConjectures.AlgebraicGeometry.SectionCoordinateChartRestriction
import WeilConjectures.AlgebraicGeometry.StandardAffineSectionOrientation

/-! # The fibre square for the two specified chart orientations

Source: blueprint sk-thm-dnc, Local construction, and orientation-charts Step 3.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale
open SectionComparisonArrows SectionLocalDualizingComparisons

private theorem affineSectionIso_transport
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (N : Γ(T, ⊤))) (d : ℕ)
    (r r' : T ⟶ AffineSpace (ULift.{u} (Fin d)) T) (h : r = r')
    (adj : rightDerivedLowerShriek (ModuleCat.{u + 1} A)
      (AffineSpace (ULift.{u} (Fin d)) T ↘ T) ⊣ affineRight A N hA T d) :
    (affineSectionIso A N hN hA T hT d r adj).hom =
      eqToHom (congrArg (sectionInvariant A (AffineSpace (ULift.{u} (Fin d)) T ↘ T)) h) ≫
        (affineSectionIso A N hN hA T hT d r' adj).hom := by
  subst r'
  simp only [eqToHom_refl, Category.id_comp]

private theorem chartMap_factor
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    {X T : Scheme.{u}} [IsNoetherian X] [IsNoetherian T]
    (hT : IsUnit (N : Γ(T, ⊤))) (d : ℕ) (f : X ⟶ T) [HasCompactification f]
    (r : T ⟶ X) (e : X ⟶ AffineSpace (ULift.{u} (Fin d)) T)
    [Etale e] [IsSeparated e] [LocallyOfFiniteType e] [QuasiCompact e]
    (w : e ≫ (AffineSpace (ULift.{u} (Fin d)) T ↘ T) = f)
    (he : r ≫ e = AffineSpace.zeroSection (ULift.{u} (Fin d)) T)
    (adj : rightDerivedLowerShriek (ModuleCat.{u + 1} A)
      (AffineSpace (ULift.{u} (Fin d)) T ↘ T) ⊣ affineRight A N hA T d) :
    chartMap A N hN hA hT d f r e w adj =
      SectionCoordinateChartMaps.toStandard A d f r e w he ≫
        (affineSectionIso A N hN hA T hT d
          (AffineSpace.zeroSection (ULift.{u} (Fin d)) T) adj).hom := by
  unfold chartMap SectionCoordinateChartMaps.toStandard
  rw [affineSectionIso_transport A N hN hA T hT d (r ≫ e) _ he adj]
  simp only [Category.assoc]

/-- The actual source and family orientation maps form a commuting square at one,
before either orientation is inverted.

Source: sk-thm-dnc, Local construction, standard model; orientation-charts Step 3
(blueprint: lem-trf-section-coordinate-orientation-square).

Proof: uniqueness of normalized projective-line data supplies base change for the
specified family D. Transpose the pullback of the ordered affine counit through compact-support
exchange. Naturality of exchange and the defining exceptional mate identity identify
its transpose with the pullback trace. The arbitrary-base-change trace equation
identifies this with the trace over the new base; injectivity of the adjunction
bijection identifies the two adjuncts. Pull to the zero section and use the canonical
Tate pullback and section compositors. In the standard Rees coordinates x_j=t*u_j,
the fibre at one is the original ordered coordinate chart. This proves the square for
the standard pair. For a centred chart apply exceptional fibre coherence to the two
etale Rees maps c.reesCoordinates and c.reesOpen, and to c.reesBase. The first two
squares commute with the counit-normalized locality maps; the last identifies the
base-restricted fibre map with restrictedTheta. Paste the three squares with the
standard square. The resulting two orientations are exactly localSourceMap and
localFamilyMap. Naturality of the section compositor gives the displayed equation.
The identity tower proves the same equation for d=0; no cancellation of coefficients,
nonemptiness, flatness of the base change, or inversion of t is used.
-/
theorem sectionCoordinateOrientation_square (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA)
    (D : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (N : Γ(T, ⊤))),
      OrdinaryFiniteP1Datum A N hA t T hT)
    {V S : Scheme.{u}} [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ)
    (g : V ⟶ S) [SmoothOfRelativeDimension d g] [IsSeparated g]
    [QuasiCompact g] [HasCompactification g] (s : S ⟶ V) [IsClosedImmersion s]
    (hs : s ≫ g = 𝟙 S)
    [HasCompactification (Scheme.Hom.deformationSpaceProj g s)]
    (c : Chart d g s hs)
    (adjC : rightDerivedLowerShriek (ModuleCat.{u + 1} A)
      (AffineSpace (ULift.{u} (Fin d)) c.T ↘ c.T) ⊣ affineRight A N hA c.T d)
    (adjF : rightDerivedLowerShriek (ModuleCat.{u + 1} A)
      (AffineSpace (ULift.{u} (Fin d)) (AffineSpace (ULift.{u} (Fin 1)) c.T) ↘ _) ⊣
        affineRight A N hA (AffineSpace (ULift.{u} (Fin 1)) c.T) d)
    (hC : @CoordinateCounitArrows.IsNormalized N hN A _ _ hA t D c.T
      (chartGeometry d g s hs c).noethT (invertibleOnSource N c.b hS) d adjC)
    (hF : @CoordinateCounitArrows.IsNormalized N hN A _ _ hA t D
      (AffineSpace (ULift.{u} (Fin 1)) c.T) (chartGeometry d g s hs c).noethLine
      (invertibleOnSource N (AffineSpace (ULift.{u} (Fin 1)) c.T ↘ c.T)
        (invertibleOnSource N c.b hS)) d adjF) :
    (upperStar (ModuleCat.{u + 1} A)
      (AffineSpace.oneSection (ULift.{u} (Fin 1)) c.T)).leftDerivedFunctor.map
        (localFamilyMap A N hN hA hS d g s hs c adjF) ≫
      (upperStar (ModuleCat.{u + 1} A)
        (AffineSpace.oneSection (ULift.{u} (Fin 1)) c.T)).leftDerivedFunctor.map
          (tatePullback A N hN hA (AffineSpace (ULift.{u} (Fin 1)) c.T ↘ c.T)
            (invertibleOnSource N c.b hS)
            (invertibleOnSource N (AffineSpace (ULift.{u} (Fin 1)) c.T ↘ c.T)
              (invertibleOnSource N c.b hS)) d).inv ≫
      (leftDerivedUpperStarCompSectionIso (ModuleCat.{u + 1} A)
        (AffineSpace.oneSection (ULift.{u} (Fin 1)) c.T)
        (AffineSpace (ULift.{u} (Fin 1)) c.T ↘ c.T)
        (AffineSpace.oneSection_comp_over (ULift.{u} (Fin 1)) c.T)).hom.app
          (SectionLocalDualizingComparisons.tateObject A N hA c.T d) =
      restrictedTheta A g s hs c.b ≫ localSourceMap A N hN hA hS d g s hs c adjC := by
  let := chartGeometry d g s hs c
  have hsource : localSourceMap A N hN hA hS d g s hs c adjC =
      SectionCoordinateChartMaps.sourceMap A d g s hs c ≫
        (affineSectionIso A N hN hA c.T (invertibleOnSource N c.b hS) d
          (AffineSpace.zeroSection (ULift.{u} (Fin d)) c.T) adjC).hom := by
    unfold localSourceMap SectionCoordinateChartMaps.sourceMap
    rw [chartMap_factor A N hN hA _ _ _ _ _ _
      (SectionCoordinateChartMaps.sourceCentre c) adjC]
    simp only [Category.assoc]
  have hfamily : localFamilyMap A N hN hA hS d g s hs c adjF =
      SectionCoordinateChartMaps.familyMap A d g s hs c ≫
        (affineSectionIso A N hN hA (AffineSpace (ULift.{u} (Fin 1)) c.T)
          (invertibleOnSource N (AffineSpace (ULift.{u} (Fin 1)) c.T ↘ c.T)
            (invertibleOnSource N c.b hS)) d
          (AffineSpace.zeroSection (ULift.{u} (Fin d)) _) adjF).hom := by
    unfold localFamilyMap SectionCoordinateChartMaps.familyMap
    rw [chartMap_factor A N hN hA _ _ _ _ _ _
      (SectionCoordinateChartMaps.familyCentre d g s hs c) adjF]
    simp only [Category.assoc]
  have hstd := standardAffineSectionOrientation_one N hN A hA t D c.T
    (invertibleOnSource N c.b hS) d adjC adjF hC hF
  rw [hsource, hfamily, Functor.map_comp]
  simp only [Category.assoc]
  rw [hstd, ← Category.assoc, sectionCoordinateChart_restriction A d g s hs c,
    Category.assoc]

end AlgebraicGeometry.Etale
