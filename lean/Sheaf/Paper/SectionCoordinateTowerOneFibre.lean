/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R1
-/
module

public import Sheaf.Paper.CoordinateCounitArrows
public import Sheaf.Paper.NoetherianEtaleSectionSpecialization
public import Sheaf.Paper.SectionReesBaseChangeEtale
public import Sheaf.AlgebraicGeometry.VectorBundleIntegrationCharts

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
  sorry

end AlgebraicGeometry.Etale
