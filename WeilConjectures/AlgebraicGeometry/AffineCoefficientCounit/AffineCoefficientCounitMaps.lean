/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AffineLinePurity.AffineLinePurityComparison
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange
public import WeilConjectures.SixFunctors.Etale.Derived.Dualizing

/-! # Canonical affine coefficient counit coordinates

Source: main-20261015, sec-smooth-purity, projection-purity agreement,
finite coefficient domains and affine-line counit normalization
(blueprint: def-pur-affine-coefficient-counit-coordinate-maps).

## Main definitions
* coefficient and trace use the actual ordered affine adjunction tower.
* lineCounit and lineTrace retain the open/projective counit and restricted trace.
* finiteLineCounit and finiteLineTrace use the recorded finite Tate coordinates.
* lineSourceTransition is the normalized exponent transition through the fixed Tate line.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.AffineCoefficientCounit
open AffineLinePurity VectorIntegrationSite

/-- The recorded tower coefficient, canonically A_X(d)[2d] by coefficient descent.
Source: affine coordinate coefficient L
(blueprint: def-pur-affine-coefficient-counit-coordinate-maps). -/
@[irreducible]
def coefficient (A : Type (u + 1)) [CommRing A] (N : ℕ) (hA : (N : A) = 0)
    (Y : Scheme.{u}) (d : ℕ) : Etale.DerivedCategoryModule A (affineTraceTower Y d) :=
  (Etale.affineTraceRight A N hA Y d).obj (Etale.ordinaryFiniteUnit A Y)

/-- Integration in the standard ordered frame, using the specified compact-support
comparison and the actual composed counit. The inverse comparison changes only the
compact-support coordinates. At zero the tower adjunction is the identity adjunction.
Source: vector integration's standard frame normalization
(blueprint: def-pur-affine-coefficient-counit-coordinate-maps). -/
@[irreducible]
def trace (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    (Y : Scheme.{u}) [IsNoetherian Y] (hY : IsUnit (N : Γ(Y, ⊤))) (d : ℕ) :
    (Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A) (affineTraceProjection Y d)).obj
      (coefficient A N hA Y d) ⟶ Etale.ordinaryFiniteUnit A Y :=
  by
  unfold coefficient
  exact (Etale.affineLinearCompactComparison N hN A hA Y hY d).inv ≫
    Etale.affineTraceCounit A N hA (Etale.projectiveLineTraceTransport N hN A hA)
      (Etale.projectiveLineTraceDatum N hN A hA) Y hY d

/-- Canonical tensor source coordinates for the composed open/projective adjunction.
Source: ordinary affine-line counit display
(blueprint: def-pur-affine-coefficient-counit-coordinate-maps). -/
@[irreducible]
def lineSourceIso (A : Type (u + 1)) [CommRing A] [Finite A] (N : ℕ)
    (hA : (N : A) = 0) (Y : Scheme.{u})
    (W : Etale.DerivedCategoryModule A (AffineSpace PUnit.{u + 1} Y))
    (eW : W ≅ (Etale.ordinaryFinitePullback A (ProjectiveLine.affineChart Y)).obj
      ((Etale.ordinaryFiniteLine A N hA (ProjectiveLine Y))⟦(2 : ℤ)⟧))
    (H : Etale.DerivedCategoryModule A Y) :
    (Etale.affineTraceLineRight A N hA Y).obj H ≅
      AffineLinePurity.ordinarySourceObject A (AffineSpace PUnit.{u + 1} Y ↘ Y) W H := by
  unfold AffineLinePurity.ordinarySourceObject
  exact Etale.ordinaryFiniteTensorPullback A (ProjectiveLine.affineChart Y)
    ((Etale.ordinaryFinitePullback A (ProjectiveLine Y ↘ Y)).obj H)
    ((Etale.ordinaryFiniteLine A N hA (ProjectiveLine Y))⟦(2 : ℤ)⟧) ≪≫
    Etale.ordinaryFiniteTensorRightMapIso A (AffineSpace PUnit.{u + 1} Y)
      ((Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} A)
        (ProjectiveLine.affineChart Y) (ProjectiveLine Y ↘ Y)
        (AffineSpace PUnit.{u + 1} Y ↘ Y)
        (ProjectiveLine.affineChart_over Y).symm).symm.app H) eW.symm

/-- The actual composed counit, in the canonical tensor coordinates of its source.
Source: epsilon line in the node
(blueprint: def-pur-affine-coefficient-counit-coordinate-maps). -/
@[irreducible]
def lineCounit (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    (Y : Scheme.{u}) [IsNoetherian Y] (hY : IsUnit (N : Γ(Y, ⊤)))
    (W : Etale.DerivedCategoryModule A (AffineSpace PUnit.{u + 1} Y))
    (eW : W ≅ (Etale.ordinaryFinitePullback A (ProjectiveLine.affineChart Y)).obj
      ((Etale.ordinaryFiniteLine A N hA (ProjectiveLine Y))⟦(2 : ℤ)⟧))
    (H : Etale.DerivedCategoryModule A Y) :
    (Etale.affineTraceLineLeft A Y).obj
      (AffineLinePurity.ordinarySourceObject A (AffineSpace PUnit.{u + 1} Y ↘ Y) W H) ⟶ H :=
  (Etale.affineTraceLineLeft A Y).map (lineSourceIso A N hA Y W eW H).inv ≫
    (Etale.affineTraceLineAdjunction A N hA (Etale.projectiveLineTraceTransport N hN A hA)
      Y hY (Etale.projectiveLineTraceDatum N hN A hA Y hY)).counit.app H

/-- Canonical coefficient-first projection, in the fixed line compactification.
Source: inverse Pi in the line counit formula
(blueprint: def-pur-affine-coefficient-counit-coordinate-maps). -/
@[irreducible]
def lineProjection (A : Type (u + 1)) [CommRing A] [Finite A] (Y : Scheme.{u})
    (W : Etale.DerivedCategoryModule A (AffineSpace PUnit.{u + 1} Y))
    (H : Etale.DerivedCategoryModule A Y) :
    ((Etale.derivedTensor (ModuleCat.{u + 1} A) Y).obj H).obj
      ((Etale.affineTraceLineLeft A Y).obj W) ⟶
    (Etale.affineTraceLineLeft A Y).obj
      (AffineLinePurity.ordinarySourceObject A (AffineSpace PUnit.{u + 1} Y ↘ Y) W H) := by
  letI := Etale.derivedBraidedCategory A Y
  letI := Etale.derivedBraidedCategory A (AffineSpace PUnit.{u + 1} Y)
  unfold AffineLinePurity.ordinarySourceObject
  exact ((Etale.derivedTensor (ModuleCat.{u + 1} A) Y).obj H).map
    ((Etale.rightDerivedLowerShriekIso A (affineTraceLineCompactification Y)).hom.app W) ≫
    (β_ H _).hom ≫
    ((Etale.projectionMap (ModuleCat.{u + 1} A)
      (AffineSpace PUnit.{u + 1} Y ↘ Y)).app W).app H ≫
    (Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A)
      (AffineSpace PUnit.{u + 1} Y ↘ Y)).map (β_ W _).hom ≫
    (Etale.rightDerivedLowerShriekIso A (affineTraceLineCompactification Y)).inv.app _

/-- Transport a counit along a specified source isomorphism.
Source: canonical Tate/shift source reassociation
(blueprint: def-pur-affine-coefficient-counit-coordinate-maps). -/
@[irreducible]
def transportCounit (A : Type (u + 1)) [CommRing A] (Y : Scheme.{u})
    (M M' : Etale.DerivedCategoryModule A (AffineSpace PUnit.{u + 1} Y))
    (H : Etale.DerivedCategoryModule A Y) (e : M ≅ M')
    (epsilon : (Etale.affineTraceLineLeft A Y).obj M' ⟶ H) :
    (Etale.affineTraceLineLeft A Y).obj M ⟶ H :=
  (Etale.affineTraceLineLeft A Y).map e.hom ≫ epsilon

end AlgebraicGeometry.ProEtale.AffineCoefficientCounit
