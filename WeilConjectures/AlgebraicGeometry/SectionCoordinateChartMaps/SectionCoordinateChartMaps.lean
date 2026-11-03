/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SectionLocalDualizingComparisons.SectionCentredChartData
import WeilConjectures.AlgebraicGeometry.SectionReesBaseChange.SectionReesBaseChangeEtale

/-! # Chart comparison maps before choosing an affine orientation

Source: sk-thm-dnc, Local construction, standard model and etale locality.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale.SectionCoordinateChartMaps
open SectionComparisonArrows SectionLocalDualizingComparisons

/-- The chart sends its centre to the standard zero section.
Source: sk-thm-dnc, Local construction (blueprint: def-trf-section-coordinate-chart-maps).
Proof: use the commutativity of the Cartesian centre square and the identity law. -/
theorem sourceCentre {V S : Scheme.{u}} {d : ℕ} {g : V ⟶ S} {s : S ⟶ V}
    {hs : s ≫ g = 𝟙 S} (c : Chart d g s hs) :
    c.r ≫ c.e = AffineSpace.zeroSection (ULift.{u} (Fin d)) c.T := by
  simpa only [Category.id_comp] using c.centres.w

/-- The augmented Rees chart sends the family centre to the standard zero section.
Source: sk-thm-dnc, Local construction (blueprint: def-trf-section-coordinate-chart-maps).
Proof: the etale pair-map theorem preserves the augmentation. Compose with the
standard Rees coordinate isomorphism, whose section equation is already proved.
The identity base map acts as the identity on the affine line, also when d=0. -/
theorem familyCentre {V S : Scheme.{u}} [IsNoetherian S] (d : ℕ) (g : V ⟶ S)
    [SmoothOfRelativeDimension d g] [IsSeparated g] [QuasiCompact g]
    (s : S ⟶ V) [IsClosedImmersion s] (hs : s ≫ g = 𝟙 S) (c : Chart d g s hs) :
    c.r.deformationSpaceSection ≫ c.reesCoordinates =
      AffineSpace.zeroSection (ULift.{u} (Fin d)) (AffineSpace (ULift.{u} (Fin 1)) c.T) := by
  let := chartGeometry d g s hs c
  have : SmoothOfRelativeDimension d
      (AffineSpace (ULift.{u} (Fin d)) c.T ↘ c.T) := by
    simpa using AffineSpace.smoothOfRelativeDimension_over (ULift.{u} (Fin d)) c.T
  have hr : c.r ≫ (c.e ≫ (AffineSpace (ULift.{u} (Fin d)) c.T ↘ c.T)) = 𝟙 c.T := by
    rw [← Category.assoc, sourceCentre c, AffineSpace.zeroSection_comp_over]
  have hc := (SectionReesBaseChange.etale d
    (AffineSpace (ULift.{u} (Fin d)) c.T ↘ c.T)
    (AffineSpace.zeroSection (ULift.{u} (Fin d)) c.T)
    (AffineSpace.zeroSection_comp_over _ _) c.e c.r hr c.centres.w c.centres).2.2.1.2.1
  have hm : SectionReesBaseChange.pairMap
      (AffineSpace.zeroSection (ULift.{u} (Fin d)) c.T) c.r c.e (𝟙 c.T) c.centres.w ≫
      Scheme.Hom.deformationSpaceToAffineSpace (ULift.{u} (Fin d)) c.T =
        c.reesCoordinates := by
    unfold Chart.reesCoordinates SectionReesBaseChange.pairMap
    rfl
  rw [← hm, ← Category.assoc, hc, AffineSpace.map_id, Category.id_comp]
  exact Scheme.Hom.deformationSpaceSection_comp_deformationSpaceToAffineSpace _ _

/-- The orientation-free chart map into the standard zero-section invariant.
Source: sk-thm-dnc, Local construction (blueprint: def-trf-section-coordinate-chart-maps). -/
@[irreducible]
def toStandard (A : Type (u + 1)) [CommRing A] [Finite A]
    {X T : Scheme.{u}} [IsNoetherian X] [IsNoetherian T]
    (d : ℕ) (f : X ⟶ T) [HasCompactification f]
    (r : T ⟶ X) (e : X ⟶ AffineSpace (ULift.{u} (Fin d)) T)
    [Etale e] [IsSeparated e] [LocallyOfFiniteType e] [QuasiCompact e]
    (w : e ≫ (AffineSpace (ULift.{u} (Fin d)) T ↘ T) = f)
    (he : r ≫ e = AffineSpace.zeroSection (ULift.{u} (Fin d)) T) :
    sectionInvariant A f r ⟶
      sectionInvariant A (AffineSpace (ULift.{u} (Fin d)) T ↘ T)
        (AffineSpace.zeroSection (ULift.{u} (Fin d)) T) :=
  letI : IsNoetherian (AffineSpace (ULift.{u} (Fin d)) T) :=
    noetherianSource (AffineSpace (ULift.{u} (Fin d)) T ↘ T)
  (sectionLocality A e (AffineSpace (ULift.{u} (Fin d)) T ↘ T) f w
    (r ≫ e) r rfl).inv ≫
      eqToHom (congrArg (sectionInvariant A (AffineSpace (ULift.{u} (Fin d)) T ↘ T)) he)

/-- Base restriction and the two source locality comparisons, before the Tate orientation.
Source: sk-thm-dnc, Local construction (blueprint: def-trf-section-coordinate-chart-maps). -/
@[irreducible]
def sourceMap (A : Type (u + 1)) [CommRing A] [Finite A]
    {V S : Scheme.{u}} [IsNoetherian S] (d : ℕ) (g : V ⟶ S)
    [SmoothOfRelativeDimension d g] [IsSeparated g] [QuasiCompact g]
    [HasCompactification g] (s : S ⟶ V) [IsClosedImmersion s]
    (hs : s ≫ g = 𝟙 S) (c : Chart d g s hs) :
    (upperStar (ModuleCat.{u + 1} A) c.b).leftDerivedFunctor.obj (sectionInvariant A g s) ⟶
      sectionInvariant A (AffineSpace (ULift.{u} (Fin d)) c.T ↘ c.T)
        (AffineSpace.zeroSection (ULift.{u} (Fin d)) c.T) :=
  letI := chartGeometry d g s hs c
  sectionMap A g (pullback.snd g c.b) c.b (pullback.fst g c.b)
      (IsPullback.of_hasPullback g c.b) s (Scheme.Hom.baseChangeSection g s hs c.b)
      (Scheme.Hom.baseChangeSection_fst g s hs c.b) ≫
    (sectionLocality A c.j (pullback.snd g c.b) (c.j ≫ pullback.snd g c.b) rfl
      (Scheme.Hom.baseChangeSection g s hs c.b) c.r c.section_eq).hom ≫
    toStandard A d (c.j ≫ pullback.snd g c.b) c.r c.e c.overE (sourceCentre c)

/-- The same orientation-free comparison on the actual extended-Rees family.
Source: sk-thm-dnc, Local construction (blueprint: def-trf-section-coordinate-chart-maps). -/
@[irreducible]
def familyMap (A : Type (u + 1)) [CommRing A] [Finite A]
    {V S : Scheme.{u}} [IsNoetherian S] (d : ℕ) (g : V ⟶ S)
    [SmoothOfRelativeDimension d g] [IsSeparated g] [QuasiCompact g]
    (s : S ⟶ V) [IsClosedImmersion s] (hs : s ≫ g = 𝟙 S)
    [HasCompactification (Scheme.Hom.deformationSpaceProj g s)] (c : Chart d g s hs) :
    (upperStar (ModuleCat.{u + 1} A)
      (AffineSpace.map (ULift.{u} (Fin 1)) c.b)).leftDerivedFunctor.obj (family A g s) ⟶
      sectionInvariant A
        (AffineSpace (ULift.{u} (Fin d)) (AffineSpace (ULift.{u} (Fin 1)) c.T) ↘ _)
        (AffineSpace.zeroSection (ULift.{u} (Fin d)) (AffineSpace (ULift.{u} (Fin 1)) c.T)) :=
  letI := chartGeometry d g s hs c
  sectionMap A (Scheme.Hom.deformationSpaceProj g s)
      (Scheme.Hom.deformationSpaceProj (pullback.snd g c.b)
        (Scheme.Hom.baseChangeSection g s hs c.b))
      (AffineSpace.map (ULift.{u} (Fin 1)) c.b) c.reesBase (Chart.Geometry.baseSquare)
      s.deformationSpaceSection (Scheme.Hom.baseChangeSection g s hs c.b).deformationSpaceSection
      (Chart.Geometry.baseSections) ≫
    (sectionLocality A c.reesOpen
      (Scheme.Hom.deformationSpaceProj (pullback.snd g c.b)
        (Scheme.Hom.baseChangeSection g s hs c.b))
      (Scheme.Hom.deformationSpaceProj (c.j ≫ pullback.snd g c.b) c.r)
      (Chart.Geometry.openOver) (Scheme.Hom.baseChangeSection g s hs c.b).deformationSpaceSection
      c.r.deformationSpaceSection (Chart.Geometry.openSections)).hom ≫
    toStandard A d (Scheme.Hom.deformationSpaceProj (c.j ≫ pullback.snd g c.b) c.r)
      c.r.deformationSpaceSection c.reesCoordinates (Chart.Geometry.coordinatesOver)
      (familyCentre d g s hs c)

end AlgebraicGeometry.Etale.SectionCoordinateChartMaps
