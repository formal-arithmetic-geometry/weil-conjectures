/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AffineZeroPurity.CoordinateSectionArrows
public import WeilConjectures.AlgebraicGeometry.CoordinateSectionNormalization.TwistedCoordinateSectionMaps
public import WeilConjectures.SixFunctors.AdicSmoothDualizing.AdicSmoothDualizingFinitePowers
public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriekLocality

/-! # Canonical Tate coordinates for the last coordinate section

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-prop-an/
cor-pur-affine-space-zero-section-purity.proof.md, even-twist and finite-site
transport sentences (blueprint: def-pur-coordinate-section-tate-coordinates).

All identifications below are composites of the published root comparison,
ordered tensor presentation and adjunction-preserving closed comparison.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
set_option maxRecDepth 2048
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry WeilConjectures
namespace AlgebraicGeometry.ProEtale.CoordinateSectionCoordinates
open AffineZeroPurity AffineSpacePurity AffineLinePurity VectorIntegrationSite

/-- The exact site/single comparison at the coefficient unit.
Source: even-twist and finite-site transport sentences
(blueprint: def-pur-coordinate-section-tate-coordinates). -/
def unitComparison (P : PurityFiniteSetting.{u}) (n : ℕ) (X : Scheme.{u}) :
    (comparison (setting P n).Coefficient X).obj
      (Etale.ordinaryFiniteUnit (setting P n).Coefficient X) ≅ unit P n X :=
  (Functor.mapDerivedCategorySingleFunctor
    (comparisonUpperStar (ModuleCat.{u + 1} (setting P n).Coefficient) X) 0).app
      ((setting P n).constantEtale X) ≪≫ (eqToIso (unit_single_eq P n X)).symm

set_option maxHeartbeats 800000 in
-- Comparing the two root exponents unfolds the finite coefficient presentation.
/-- Identify the two root exponents through their common inverse-limit line.
Source: even-twist and finite-site transport sentences
(blueprint: def-pur-coordinate-section-tate-coordinates). -/
def lineTargetComparison (P : PurityFiniteSetting.{u}) (n : ℕ) (X : Scheme.{u})
    (aX : X ⟶ Spec (.of P.field.k)) :
    (comparison (setting P n).Coefficient X).obj
      ((Etale.ordinaryFiniteLine (setting P n).Coefficient (setting P n).diagonalExponent
        (setting P n).diagonalExponent_annihilates X)⟦(2 : ℤ)⟧) ≅
      AffineSpacePurity.shiftedLine (setting P n) X :=
  let Q := setting P n
  let hX := AffineLinePurity.primeUnit Q X aX
  twistDerived P.coefficients.l P.extension n X hX n Q.diagonalExponent_annihilates 1 2 ≪≫
    (twistDerived P.coefficients.l P.extension n X hX (n + 1)
      (AffineSpacePurity.annihilates Q) 1 2).symm

/-- Apply the monoidal comparison along the ordered tensor recursion.
Source: even-twist and finite-site transport sentences
(blueprint: def-pur-coordinate-section-tate-coordinates). -/
def orderedTargetComparison (P : PurityFiniteSetting.{u}) (n : ℕ) (X : Scheme.{u})
    (aX : X ⟶ Spec (.of P.field.k)) : (c : ℕ) →
    (comparison (setting P n).Coefficient X).obj
      ((setting P n).diagonalTwistEtale X c) ≅ target P n X c
  | 0 => unitComparison P n X
  | c + 1 => tensorComparison (setting P n).Coefficient X _ _ ≪≫
      AffineSpacePurity.tensorIso (setting P n).Coefficient X
        (orderedTargetComparison P n X aX c) (lineTargetComparison P n X aX)

/-- Compare the positive Tate target using the normalized finite-power presentation.
Source: even-twist and finite-site transport sentences
(blueprint: def-pur-coordinate-section-tate-coordinates). -/
def positiveTargetComparison (P : PurityFiniteSetting.{u}) (n : ℕ) (X : Scheme.{u})
    (aX : X ⟶ Spec (.of P.field.k)) (c : ℕ) :
    (comparison (setting P n).Coefficient X).obj
      ((setting P n).functorialCupTarget false X (2 * (c : ℤ)) c) ≅ target P n X c :=
  (comparison (setting P n).Coefficient X).mapIso
    (AdicSmoothDualizing.etalePowerComparison (setting P n) X
      ((setting P n).diagonalExponent_isUnit aX) c).symm ≪≫
    orderedTargetComparison P n X aX c

/-- The literal Tate input used by the existing rank-one normalization.
Source: even-twist sentence
(blueprint: def-pur-coordinate-section-tate-coordinates). -/
abbrev input (P : PurityFiniteSetting.{u}) (n : ℕ) (T : Scheme.{u}) (r : ℕ) :=
  Etale.SectionLocalDualizingComparisons.tateObject (setting P n).Coefficient
    (P.coefficients.l ^ ((setting P n).level + 1)) (annihilates (setting P n)) T r

/-- Compare two ordinary finite Tate exponents via the common inverse-limit
Tate object, before specializing the coefficient presentation.
Source: finite-site transport sentence
(blueprint: def-pur-coordinate-section-tate-coordinates). -/
def twistExponentComparison (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (n : ℕ)
    (T : Scheme.{u}) (hT : IsUnit (l : Γ(T, ⊤))) (b b' : ℕ)
    (hA : ((l ^ (b + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0)
    (hA' : ((l ^ (b' + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0) (r : ℕ) :
    (comparison (Scheme.finiteTateCoefficient l E n) T).obj
      (Etale.SectionLocalDualizingComparisons.tateObject
        (Scheme.finiteTateCoefficient l E n) (l ^ (b + 1)) hA T r) ≅
    (comparison (Scheme.finiteTateCoefficient l E n) T).obj
      (Etale.SectionLocalDualizingComparisons.tateObject
        (Scheme.finiteTateCoefficient l E n) (l ^ (b' + 1)) hA' T r) :=
  twistDerived l E n T hT b hA r (2 * (r : ℤ)) ≪≫
    (twistDerived l E n T hT b' hA' r (2 * (r : ℤ))).symm

set_option maxHeartbeats 1200000 in
-- Specializing the finite coefficient presentation makes the exponent comparison expensive.
set_option allowUnsafeReducibility true in
attribute [local irreducible] DerivedCategory.singleFunctor shiftFunctor in
/-- Compare the literal Tate input with the ordered target through the common
inverse-limit twist. Source: finite-site transport sentence
(blueprint: def-pur-coordinate-section-tate-coordinates). -/
def tateComparison (P : PurityFiniteSetting.{u}) (n : ℕ) (T : Scheme.{u})
    (aT : T ⟶ Spec (.of P.field.k)) (r : ℕ) :
    (comparison (setting P n).Coefficient T).obj (input P n T r) ≅ target P n T r :=
  twistExponentComparison P.coefficients.l P.extension n T
    (primeUnit (setting P n) T aT) (setting P n).level n
    (annihilates (setting P n)) (setting P n).diagonalExponent_annihilates r ≪≫
    positiveTargetComparison P n T aT r

/-- Uniqueness of right adjoints, with the canonical proper compact-support
comparison on the left. Source: finite-site transport sentence
(blueprint: def-pur-coordinate-section-tate-coordinates). -/
def ordinaryClosedComparison (A : Type (u + 1)) [CommRing A] [Finite A]
    (T : Scheme.{u}) :
    Etale.rightDerivedUpperShriek A (CoordinateSectionNormalization.sectionMap T) ≅
      (CoordinateSectionNormalization.closedImage A T).rightAdjoint :=
  (Etale.rightDerivedLowerStarUpperShriekAdjunctionOfIsProper A
    (CoordinateSectionNormalization.sectionMap T)).rightAdjointUniq
      (CoordinateSectionNormalization.closedAdjunction A T)

/-- Whisker the adjunction-preserving ordinary closed comparison by the actual
comparison functors. Source: finite-site transport sentence
(blueprint: def-pur-coordinate-section-tate-coordinates). -/
def closedComparison (A : Type (u + 1)) [CommRing A] [Finite A]
    (T : Scheme.{u}) :
    rightDerivedUpperShriek A (CoordinateSectionNormalization.sectionMap T) ≅
      CoordinateSectionNormalization.proClosed A T :=
  Functor.isoWhiskerLeft
    (comparisonLowerStar (ModuleCat.{u + 1} A) (AffineSpace PUnit.{u + 1} T)).rightDerivedFunctor
      (Functor.isoWhiskerRight (ordinaryClosedComparison A T) (comparison A T))

/-- Compare the rank-one ordinary twisted source with the actual next ordered
Tate target. Source: even-twist and finite-site transport sentences
(blueprint: def-pur-coordinate-section-tate-coordinates). -/
def supportedTargetComparison (P : PurityFiniteSetting.{u}) (n : ℕ) (B : Scheme.{u})
    (aB : B ⟶ Spec (.of P.field.k)) (r : ℕ) :
    (comparison (setting P n).Coefficient (iteratedAffineLine B (r + 1))).obj
      ((CoordinateLine.right (setting P n).Coefficient
        (P.coefficients.l ^ ((setting P n).level + 1)) (annihilates (setting P n))
        (iteratedAffineLine B r)).obj (input P n (iteratedAffineLine B r) r)) ≅
      target P n (iteratedAffineLine B (r + 1)) (r + 1) :=
  (comparison (setting P n).Coefficient (iteratedAffineLine B (r + 1))).mapIso
      (CoordinateLine.sourceCoordinates (setting P n) (iteratedAffineLine B r)
        (setting P n).level (annihilates (setting P n))
        (input P n (iteratedAffineLine B r) r)).symm ≪≫
    sourceComparison P.coefficients.l P.extension n (iteratedAffineLine B r)
      (setting P n).level (annihilates (setting P n))
      (target P n (iteratedAffineLine B r) r) (input P n (iteratedAffineLine B r) r)
      (tateComparison P n _ (towerBase aB r) r) ≪≫
    (eqToIso (lineSource_obj_eq (setting P n) (iteratedAffineLine B r)
      (target P n (iteratedAffineLine B r) r))).symm ≪≫
    (CoordinateTowerNormalization.stepSource P n B aB r).symm

/-- The actual target of the exceptional adjunct in ordinary normalization
coordinates. Source: finite-site transport sentence
(blueprint: def-pur-coordinate-section-tate-coordinates). -/
def orientationTargetComparison (P : PurityFiniteSetting.{u}) (n : ℕ) (B : Scheme.{u})
    (aB : B ⟶ Spec (.of P.field.k)) (r : ℕ) :
    (rightDerivedUpperShriek (setting P n).Coefficient (lastSection B r)).obj
      (target P n (iteratedAffineLine B (r + 1)) (r + 1)) ≅
    (CoordinateSectionNormalization.proClosed (setting P n).Coefficient
      (iteratedAffineLine B r)).obj
        ((comparison (setting P n).Coefficient (iteratedAffineLine B (r + 1))).obj
          ((CoordinateLine.right (setting P n).Coefficient
            (P.coefficients.l ^ ((setting P n).level + 1)) (annihilates (setting P n))
            (iteratedAffineLine B r)).obj (input P n (iteratedAffineLine B r) r))) :=
  (rightDerivedUpperShriek (setting P n).Coefficient (lastSection B r)).mapIso
      (supportedTargetComparison P n B aB r).symm ≪≫
    (closedComparison (setting P n).Coefficient (iteratedAffineLine B r)).app _

end AlgebraicGeometry.ProEtale.CoordinateSectionCoordinates
