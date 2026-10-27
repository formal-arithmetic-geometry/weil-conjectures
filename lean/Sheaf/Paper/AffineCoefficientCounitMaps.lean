/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q11
-/
module

public import Sheaf.Paper.AffineLinePurityComparison
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

/-- Invertibility of any positive power of ell, from the fixed characteristic convention.
Source: finite conventions, coefficient-domain paragraph
(blueprint: def-pur-affine-coefficient-counit-coordinate-maps).
Proof: primeUnit gives invertibility of ell from its nonzero image in the fixed field.
Raise that unit to r+1 and use preservation of powers by the natural-number cast. -/
theorem modulusUnit (P : WeilConjectures.PurityFiniteSetting.{u}) (Y : Scheme.{u})
    (aY : Y ⟶ Spec (.of P.field.k)) (r : ℕ) :
    IsUnit ((P.coefficients.l ^ (r + 1) : ℕ) : Γ(Y, ⊤)) := by
  simpa only [Nat.cast_pow] using (AffineLinePurity.primeUnit P Y aY).pow (r + 1)

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

/-- The actual open-counit restriction of the normalized projective trace.
Source: I_S display (blueprint: def-pur-affine-coefficient-counit-coordinate-maps). -/
@[irreducible]
def lineTrace (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    (Y : Scheme.{u}) [IsNoetherian Y] (hY : IsUnit (N : Γ(Y, ⊤)))
    (W : Etale.DerivedCategoryModule A (AffineSpace PUnit.{u + 1} Y))
    (eW : W ≅ (Etale.ordinaryFinitePullback A (ProjectiveLine.affineChart Y)).obj
      ((Etale.ordinaryFiniteLine A N hA (ProjectiveLine Y))⟦(2 : ℤ)⟧)) :
    (Etale.affineTraceLineLeft A Y).obj W ⟶ Etale.ordinaryFiniteUnit A Y :=
  (Etale.affineTraceLineLeft A Y).map eW.hom ≫
    (Etale.ordinaryFinitePushforward A (ProjectiveLine Y ↘ Y)).map
      ((Etale.affineTraceOpenAdjunction A Y).counit.app
        ((Etale.ordinaryFiniteLine A N hA (ProjectiveLine Y))⟦(2 : ℤ)⟧)) ≫
    Etale.projectiveLineTrace N hN A hA Y hY

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
  letI := Etale.derivedBraidedCategory (ModuleCat.{u + 1} A) Y
  letI := Etale.derivedBraidedCategory (ModuleCat.{u + 1} A)
    (AffineSpace PUnit.{u + 1} Y)
  unfold AffineLinePurity.ordinarySourceObject
  exact ((Etale.derivedTensor (ModuleCat.{u + 1} A) Y).obj H).map
    ((Etale.rightDerivedLowerShriekIso A (affineTraceLineCompactification Y)).hom.app W) ≫
    (β_ H _).hom ≫
    ((Etale.projectionMap (ModuleCat.{u + 1} A)
      (AffineSpace PUnit.{u + 1} Y ↘ Y)).app W).app H ≫
    (Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A)
      (AffineSpace PUnit.{u + 1} Y ↘ Y)).map (β_ W _).hom ≫
    (Etale.rightDerivedLowerShriekIso A (affineTraceLineCompactification Y)).inv.app _

/-- Realize the actual ordinary line counit through the specified site and source
comparisons. All inputs below are instantiated with the canonical source comparisons.
Source: site comparison of the line counit
(blueprint: def-pur-affine-coefficient-counit-coordinate-maps). -/
@[irreducible]
def realizeCounit (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (c : Compactification f)
    (M : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (Z : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)))
    (H : Etale.DerivedCategoryModule A Y)
    (K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} A)))
    (eM : (comparison A X).obj M.obj ≅ Z) (eH : (comparison A Y).obj H ≅ K)
    (epsilon : (Etale.rightDerivedLowerShriekOfCompactification
      (ModuleCat.{u + 1} A) c).obj M.obj ⟶ H) :
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).obj Z ⟶ K :=
  (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).map eM.inv ≫
    (compactSupportSiteComparison A c).hom.app M ≫ (comparison A Y).map epsilon ≫ eH.hom

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

/-- The actual ordinary counit in the recorded finite-affine-line source coordinate.
Source: the line counit in the finite coefficient convention
(blueprint: def-pur-affine-coefficient-counit-coordinate-maps). -/
@[irreducible]
def finiteLineCounit (P : WeilConjectures.PurityFiniteSetting.{u}) (Y : Scheme.{u})
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    (r : ℕ) (hA : ((P.coefficients.l ^ (r + 1) : ℕ) : Ring P) = 0)
    (H : Etale.DerivedCategoryModule (Ring P) Y) :
    (Etale.affineTraceLineLeft (Ring P) Y).obj
      (AffineLinePurity.etaleSource P.coefficients.l P.extension (P.level - 1) Y r hA H) ⟶
        H :=
  letI : IsNoetherian Y := isNoetherian_of_locallyOfFiniteType aY
  transportCounit (Ring P) Y _ _ H
    (eqToIso (AffineLinePurity.etaleSource_eq P.coefficients.l P.extension
      (P.level - 1) Y r hA H))
    (lineCounit (Ring P) (P.coefficients.l ^ (r + 1))
      (pow_pos (Fact.out : P.coefficients.l.Prime).pos _) hA Y (modulusUnit P Y aY r)
      (AffineLinePurity.etaleCoefficient P.coefficients.l P.extension (P.level - 1) Y r hA)
      (eqToIso (AffineLinePurity.etaleCoefficient_eq P.coefficients.l P.extension
        (P.level - 1) Y r hA)) H)

/-- The restricted projective trace at the recorded shifted coefficient.
Source: I_S in the finite coefficient convention
(blueprint: def-pur-affine-coefficient-counit-coordinate-maps). -/
@[irreducible]
def finiteLineTrace (P : WeilConjectures.PurityFiniteSetting.{u}) (Y : Scheme.{u})
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    (r : ℕ) (hA : ((P.coefficients.l ^ (r + 1) : ℕ) : Ring P) = 0) :
    (Etale.affineTraceLineLeft (Ring P) Y).obj
      (AffineLinePurity.etaleCoefficient P.coefficients.l P.extension (P.level - 1) Y r hA) ⟶
        Etale.ordinaryFiniteUnit (Ring P) Y :=
  letI : IsNoetherian Y := isNoetherian_of_locallyOfFiniteType aY
  lineTrace (Ring P) (P.coefficients.l ^ (r + 1))
    (pow_pos (Fact.out : P.coefficients.l.Prime).pos _) hA Y (modulusUnit P Y aY r)
    (AffineLinePurity.etaleCoefficient P.coefficients.l P.extension (P.level - 1) Y r hA)
    (eqToIso (AffineLinePurity.etaleCoefficient_eq P.coefficients.l P.extension
      (P.level - 1) Y r hA))

/-- Tensor the canonical coefficient transition with the actual inverse image of K.
Source: independence of annihilating exponent
(blueprint: def-pur-affine-coefficient-counit-coordinate-maps). -/
@[irreducible]
def sourceChange (A : Type (u + 1)) [CommRing A] {X Y : Scheme.{u}} (f : X ⟶ Y)
    (W W' : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X)
      (ModuleCat.{u + 1} A)))
    (K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology Y)
      (ModuleCat.{u + 1} A))) (e : W ≅ W') :
    AffineLinePurity.projectionSourceObject A f W K ≅
      AffineLinePurity.projectionSourceObject A f W' K := by
  unfold AffineLinePurity.projectionSourceObject
  exact ((derivedTensor (ModuleCat.{u + 1} A) X).obj
    ((upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor.obj K)).mapIso e

/-- Source transition through the specified common pro-etale Tate line, with no choice
of orientation. Source: the exponent-independence clause
(blueprint: def-pur-affine-coefficient-counit-coordinate-maps). -/
@[irreducible]
def lineSourceTransition (P : WeilConjectures.PurityFiniteSetting.{u}) (Y : Scheme.{u})
    (aY : Y ⟶ Spec (.of P.field.k)) (r r' : ℕ)
    (hA : ((P.coefficients.l ^ (r + 1) : ℕ) : Ring P) = 0)
    (hA' : ((P.coefficients.l ^ (r' + 1) : ℕ) : Ring P) = 0)
    (K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology Y)
      (ModuleCat.{u + 1} (Ring P)))) :
    AffineLinePurity.source P.coefficients.l P.extension (P.level - 1) Y r hA K ≅
      AffineLinePurity.source P.coefficients.l P.extension (P.level - 1) Y r' hA' K :=
  sourceChange (Ring P) (AffineSpace PUnit.{u + 1} Y ↘ Y) _ _ K
    (AffineLinePurity.coefficientTwistIso P.coefficients.l P.extension (P.level - 1)
      Y r hA (AffineLinePurity.primeUnit P (ProjectiveLine Y) ((ProjectiveLine Y ↘ Y) ≫ aY))
      (AffineLinePurity.primeUnit P (AffineSpace PUnit.{u + 1} Y)
        ((AffineSpace PUnit.{u + 1} Y ↘ Y) ≫ aY)) ≪≫
    (AffineLinePurity.coefficientTwistIso P.coefficients.l P.extension (P.level - 1)
      Y r' hA'
      (AffineLinePurity.primeUnit P (ProjectiveLine Y) ((ProjectiveLine Y ↘ Y) ≫ aY))
      (AffineLinePurity.primeUnit P (AffineSpace PUnit.{u + 1} Y)
        ((AffineSpace PUnit.{u + 1} Y ↘ Y) ≫ aY))).symm)


end AlgebraicGeometry.ProEtale.AffineCoefficientCounit
