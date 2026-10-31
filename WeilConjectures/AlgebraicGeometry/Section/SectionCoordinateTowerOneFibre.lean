/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CoordinateCounitArrows.CoordinateCounitArrows
public import WeilConjectures.AlgebraicGeometry.NoetherianSectionSpecialization.NoetherianEtaleSectionSpecialization
public import WeilConjectures.AlgebraicGeometry.SectionReesBaseChange.SectionReesBaseChangeEtale
public import WeilConjectures.AlgebraicGeometry.Vector.VectorBundleIntegrationCharts
import WeilConjectures.AlgebraicGeometry.Ordered.OrderedTateSectionPullback
import WeilConjectures.AlgebraicGeometry.Section.SectionReesOneCoordinates
import WeilConjectures.AlgebraicGeometry.Section.SectionTowerCounitBaseChange
import WeilConjectures.AlgebraicGeometry.Section.SectionLocalityBaseChange
import all WeilConjectures.AlgebraicGeometry.SectionReesBaseChange.SectionReesBaseChangeEtale
import all WeilConjectures.AlgebraicGeometry.Vector.VectorIntegrationOverlapCoordinates

/-! # The fibre at one of the ordered coordinate-counit orientations

Source: sk-thm-dnc, Local construction, and orientation-charts Step 3.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.all false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale
open NoetherianSectionSpecialization

attribute [local irreducible] upperStar Functor.leftDerivedFunctor Functor.rightDerivedFunctor
  rightDerivedUpperShriek rightDerivedUpperShriekAdjunction

attribute [local instance 100000] DerivedCategoryModule._proof_1 DerivedCategoryModule._proof_2

set_option maxHeartbeats 1000000

/-- The two prescribed coordinate orientations commute with the actual exceptional
fibre map at one. This is a fibre equation, before constructing or comparing any
normalized isomorphism over the affine line.

Source: sk-thm-dnc, Local construction, standard model; orientation-charts Step 3
(blueprint: lem-trf-section-coordinate-tower-one-fibre).

Proof: On the standard pair the Rees coordinates satisfy x_j=t*u_j, so restriction
at one is the original ordered coordinate map. Transpose base change of the ordered
Kummer-normalized trace through the compact-support comparison. The counit identity
for the exceptional mate and naturality of compact-support exchange give the same
transpose, so injectivity of the adjunction bijection identifies the two ambient
adjoints. The ordered Tate coefficient pullback comparisons compose to the section
compositor for i1 followed by the affine-line projection. Restrict the ambient square
to the zero sections. For e use the counit-normalized etale locality isomorphisms;
exceptional base-change/locality coherence commutes them with the one-fibre map.
The inverse-image composition and section pasting laws give exactly the equation
below. The map v is constrained to be the actual extended-Rees coordinate map, not
an independently chosen orientation. Rank zero uses the identity tower; empty
schemes and the zero ring satisfy the same functorial equations.
-/
theorem coordinateTowerSection_oneFibre (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA)
    (D : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (N : Γ(T, ⊤))),
      OrdinaryFiniteP1Datum A N hA t T hT)
    {X S : Scheme.{u}} [IsNoetherian S] [IsNoetherian X]
    [IsNoetherian (AffineSpace (ULift.{u} (Fin 1)) S)]
    (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ)
    (g : X ⟶ S) [HasCompactification g] [QuasiCompact g]
    (s : S ⟶ X) [IsClosedImmersion s] (hs : s ≫ g = 𝟙 S)
    [IsNoetherian s.ker.deformationSpace]
    [HasCompactification (Scheme.Hom.deformationSpaceProj g s)]
    [QuasiCompact (Scheme.Hom.deformationSpaceProj g s)]
    (e : X ⟶ AffineSpace (ULift.{u} (Fin d)) S) [Etale e] [IsSeparated e]
    [LocallyOfFiniteType e] [QuasiCompact e]
    (w : e ≫ (AffineSpace (ULift.{u} (Fin d)) S ↘ S) = g)
    (sq : IsPullback s (𝟙 S) e (AffineSpace.zeroSection (ULift.{u} (Fin d)) S))
    (v : s.ker.deformationSpace ⟶
      affineTraceTower (AffineSpace (ULift.{u} (Fin 1)) S) d)
    [Etale v] [IsSeparated v] [LocallyOfFiniteType v] [QuasiCompact v]
    (hv : v = SectionReesBaseChange.pairMap
      (AffineSpace.zeroSection (ULift.{u} (Fin d)) S) s e (𝟙 S) sq.w ≫
        Scheme.Hom.deformationSpaceToAffineSpace (ULift.{u} (Fin d)) S ≫
          (affineTraceAffineSpaceIso (AffineSpace (ULift.{u} (Fin 1)) S) d).inv)
    (overV : v ≫ affineTraceProjection (AffineSpace (ULift.{u} (Fin 1)) S) d =
      Scheme.Hom.deformationSpaceProj g s) :
    letI := affineTraceNoetherian S d
    letI := affineTraceNoetherian (AffineSpace (ULift.{u} (Fin 1)) S) d
    let eC := e ≫ (affineTraceAffineSpaceIso S d).inv
    let overC : eC ≫ affineTraceProjection S d = g := by
      rw [Category.assoc, (CoordinateCounitArrows.standardSquare S d).w,
        Category.comp_id, w]
    let C := affineLinearBaseCoefficient A N hA S d
    let a := AffineSpace (ULift.{u} (Fin 1)) S ↘ S
    let hLine := affineTracePullbackInvertible N a hS
    let oC :=
      ((leftDerivedUpperStarCompSectionIso (ModuleCat.{u + 1} A) (s ≫ eC)
        (affineTraceProjection S d) (by rw [Category.assoc, overC, hs])).inv.app C ≫
      (ordinaryFinitePullback A (s ≫ eC)).map
        ((affineLinearCoefficientDescent A N hA t S hS d).inv ≫
          CoordinateCounitArrows.towerAdjoint N hN A hA t D S hS d)) ≫
      (SectionLocalDualizingComparisons.sectionLocality A eC (affineTraceProjection S d)
        g overC (s ≫ eC) s rfl).hom
    let oF := (vectorIntegrationBaseCoefficientPullback A N hA t a hS d).hom ≫
      (((leftDerivedUpperStarCompSectionIso (ModuleCat.{u + 1} A)
        (s.deformationSpaceSection ≫ v)
        (affineTraceProjection (AffineSpace (ULift.{u} (Fin 1)) S) d)
        (by rw [Category.assoc, overV];
            exact Scheme.Hom.deformationSpaceSection_deformationSpaceProj hs)).inv.app _ ≫
      (ordinaryFinitePullback A (s.deformationSpaceSection ≫ v)).map
        ((affineLinearCoefficientDescent A N hA t
          (AffineSpace (ULift.{u} (Fin 1)) S) hLine d).inv ≫
          CoordinateCounitArrows.towerAdjoint N hN A hA t D
            (AffineSpace (ULift.{u} (Fin 1)) S) hLine d)) ≫
      (SectionLocalDualizingComparisons.sectionLocality A v
        (affineTraceProjection (AffineSpace (ULift.{u} (Fin 1)) S) d)
        (Scheme.Hom.deformationSpaceProj g s) overV
        (s.deformationSpaceSection ≫ v) s.deformationSpaceSection rfl).hom)
    (ordinaryFinitePullback A (AffineSpace.oneSection (ULift.{u} (Fin 1)) S)).map oF ≫
        atOne A g s hs =
      (leftDerivedUpperStarCompSectionIso (ModuleCat.{u + 1} A)
        (AffineSpace.oneSection (ULift.{u} (Fin 1)) S) a
        (AffineSpace.oneSection_comp_over (ULift.{u} (Fin 1)) S)).hom.app C ≫ oC := by
  letI := affineTraceNoetherian S d
  letI := affineTraceNoetherian (AffineSpace (ULift.{u} (Fin 1)) S) d
  let L := AffineSpace (ULift.{u} (Fin 1)) S
  let a := L ↘ S
  let i := AffineSpace.oneSection (ULift.{u} (Fin 1)) S
  let eC := e ≫ (affineTraceAffineSpaceIso S d).inv
  let pC := affineTraceProjection S d
  let pF := affineTraceProjection L d
  let q := Scheme.Hom.deformationSpaceProj g s
  let r := Scheme.Hom.deformationSpaceOneFibre g s
  let zC := s ≫ eC
  let zF := s.deformationSpaceSection ≫ v
  let hL := affineTracePullbackInvertible N a hS
  have overC : eC ≫ pC = g := by
    dsimp only [eC, pC]
    rw [Category.assoc, (CoordinateCounitArrows.standardSquare S d).w,
      Category.comp_id, w]
  have hzC : zC ≫ pC = 𝟙 S := by rw [Category.assoc, overC, hs]
  have hzF : zF ≫ pF = 𝟙 L := by
    rw [Category.assoc, overV]
    exact Scheme.Hom.deformationSpaceSection_deformationSpaceProj hs
  have hOne : r ≫ v = eC ≫ affineTraceMap i d := by
    apply (cancel_mono (affineTraceAffineSpaceIso L d).hom).mp
    dsimp only [eC, L]
    simp only [Category.assoc, tower_map_iso, Iso.inv_hom_id_assoc]
    rw [hv]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [← Category.assoc r, SectionReesBaseChange.pairMap_oneFibre
      (AffineSpace (ULift.{u} (Fin d)) S ↘ S) g
      (AffineSpace.zeroSection (ULift.{u} (Fin d)) S) s e (𝟙 S) sq.w,
      Category.assoc, sectionRees_oneCoordinates]
  have hz : zC ≫ affineTraceMap i d = i ≫ zF := by
    dsimp only [zC, zF]
    rw [Category.assoc, ← hOne, ← Category.assoc,
      Scheme.Hom.comp_deformationSpaceOneFibre hs, Category.assoc]
  let αC := (affineLinearCoefficientDescent A N hA t S hS d).inv ≫
    CoordinateCounitArrows.towerAdjoint N hN A hA t D S hS d
  let αF := (affineLinearCoefficientDescent A N hA t L hL d).inv ≫
    CoordinateCounitArrows.towerAdjoint N hN A hA t D L hL d
  let OC := (leftDerivedUpperStarCompSectionIso (ModuleCat.{u + 1} A)
    zC pC hzC).inv.app (affineLinearBaseCoefficient A N hA S d) ≫
      (ordinaryFinitePullback A zC).map αC
  let OF := (leftDerivedUpperStarCompSectionIso (ModuleCat.{u + 1} A)
    zF pF hzF).inv.app (affineLinearBaseCoefficient A N hA L d) ≫
      (ordinaryFinitePullback A zF).map αF
  let LC := SectionLocalDualizingComparisons.sectionLocality A eC pC g overC zC s rfl
  let LF := SectionLocalDualizingComparisons.sectionLocality A v pF q overV zF
    s.deformationSpaceSection rfl
  let bA := vectorIntegrationBaseCoefficientPullback A N hA t a hS d
  let bI := vectorIntegrationBaseCoefficientPullback A N hA t i hL d
  let I := ordinaryFinitePullback A i
  let J := leftDerivedUpperStarCompSectionIso (ModuleCat.{u + 1} A) i a
    (AffineSpace.oneSection_comp_over _ S)
  let θ := SectionComparisonArrows.sectionMap A pF pC i (affineTraceMap i d)
    (affineTraceMap_isPullback i d) zF zC hz
  have ht : I.map OF ≫ θ = bI.hom ≫ OC :=
    coordinateTowerSection_baseChange N hN A hA t D i hL d zF zC hzF hzC hz
  have sqU : IsPullback r eC v (affineTraceMap i d) := by
    have overV' : v ≫ pF = q := overV
    have ho : IsPullback r (eC ≫ pC) (v ≫ pF) i := by
      rw [overC, overV']
      exact Scheme.Hom.isPullback_deformationSpaceOneFibre g s
    exact ho.of_bot hOne (affineTraceMap_isPullback i d)
  have hsOne : s ≫ r = i ≫ s.deformationSpaceSection :=
    Scheme.Hom.comp_deformationSpaceOneFibre hs
  have hl : I.map LF.hom ≫ atOne A g s hs = θ ≫ LC.hom := by
    exact sectionLocality_baseChange A v pF eC pC q overV g overC i
      (affineTraceMap i d) r (affineTraceMap_isPullback i d) sqU
      (Scheme.Hom.isPullback_deformationSpaceOneFibre g s)
      zF zC s.deformationSpaceSection s hz hsOne rfl rfl
  have hb : I.map bA.hom ≫ bI.hom =
      J.hom.app (affineLinearBaseCoefficient A N hA S d) := by
    have hh := orderedTateSectionPullback A N hA t a i
      (AffineSpace.oneSection_comp_over _ S) hS hL d
    apply (cancel_epi (bI.inv ≫ I.map bA.inv)).mp
    simpa only [Category.assoc, ← I.map_comp_assoc, Iso.inv_hom_id,
      I.map_id, Category.id_comp, Iso.inv_hom_id_assoc] using hh.symm
  change I.map (bA.hom ≫ (OF ≫ LF.hom)) ≫ atOne A g s hs =
    J.hom.app (affineLinearBaseCoefficient A N hA S d) ≫ (OC ≫ LC.hom)
  simp only [Functor.map_comp, Category.assoc]
  rw [hl, ← Category.assoc (I.map OF), ht]
  simpa only [Category.assoc] using congrArg (fun z ↦ z ≫ OC ≫ LC.hom) hb

end AlgebraicGeometry.Etale
