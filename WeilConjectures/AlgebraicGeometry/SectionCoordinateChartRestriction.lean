/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SectionCoordinateChartMaps

/-! # The one-fibre square for chart locality, before affine orientations

Source: sk-thm-dnc, Local construction, etale maps of pairs.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Etale
open SectionComparisonArrows SectionLocalDualizingComparisons

/-- The orientation-free source and Rees chart maps respect the actual fibre at one.
Source: sk-thm-dnc, Local construction, etale maps of pairs and fibre restriction
(blueprint: lem-trf-section-coordinate-chart-restriction).

Proof: apply exceptional base-change transitivity to the Cartesian square defined by
c.reesBase and the one-fibre inclusions. The two composites of the upper scheme maps
agree by functoriality of the extended-Rees construction at one. Pull to the compatible
sections; the inverse-image compositors identify the outer map with restrictedTheta.
For c.reesOpen apply the counit-normalized etale locality/base-change square at one.
Apply the same square to c.reesCoordinates and c.e. In the standard Rees isomorphism
x_j=t*u_j the map at t=1 is the identity on the ordered coordinates. The augmentation
identities identify the two centre sections with the standard zero sections. Paste the
base-change and open-locality squares with the inverse coordinate-locality square.
The inner locality isomorphisms cancel. Inverse-image composition coherence regroups
the outer arrows as exactly familyMap, standardFibreMap, restrictedTheta and sourceMap.
This uses no affine adjunction or Tate orientation. For d=0 the coordinate isomorphism
and its fibre map are the identity; empty schemes and zero coefficient rings obey the
same functorial and mate equations.
-/
theorem sectionCoordinateChart_restriction (A : Type (u + 1)) [CommRing A] [Finite A]
    {V S : Scheme.{u}} [IsNoetherian S] (d : ℕ) (g : V ⟶ S)
    [SmoothOfRelativeDimension d g] [IsSeparated g] [QuasiCompact g]
    [HasCompactification g] (s : S ⟶ V) [IsClosedImmersion s]
    (hs : s ≫ g = 𝟙 S)
    [HasCompactification (Scheme.Hom.deformationSpaceProj g s)] (c : Chart d g s hs) :
    (upperStar (ModuleCat.{u + 1} A)
      (AffineSpace.oneSection (ULift.{u} (Fin 1)) c.T)).leftDerivedFunctor.map
        (SectionCoordinateChartMaps.familyMap A d g s hs c) ≫
      SectionCoordinateChartMaps.standardFibreMap A c.T d =
    restrictedTheta A g s hs c.b ≫ SectionCoordinateChartMaps.sourceMap A d g s hs c := by
  sorry

end AlgebraicGeometry.Etale
