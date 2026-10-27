/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q41
-/
module

public import Sheaf.Paper.AffineLinePurityComparison
public import Sheaf.AlgebraicGeometry.AffineTraceConstruction
public import Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Adjunction
public import Mathlib.CategoryTheory.Adjunction.Mates

public import Sheaf.Paper.PurityFiniteSetting
public import Sheaf.AlgebraicGeometry.EtaleFiniteTwistPullback
public import Mathlib.AlgebraicGeometry.AffineSpace
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import Mathlib.CategoryTheory.Adjunction.Basic
public import Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients
public import Sheaf.Paper.AffineLinePuritySource
public import Sheaf.Paper.AffineLinePurityCoordinateMaps
public import Sheaf.AlgebraicGeometry.FiniteCompactProjectionFormula
public import Sheaf.Paper.VectorIntegrationSiteComparison

/-! # Canonical coordinate-line adjunction maps

Source: main-20261015, sec-smooth-purity/sk-prop-an,
cor-pur-affine-space-zero-section-purity.proof.md, first two sentences and final paragraph
(blueprint: def-pur-coordinate-line-adjunction-maps).

The ordinary right-adjoint comparison is conjugation of the identity left functor.
The line coefficient is the canonical restriction of the shifted projective Tate line;
its normalized Tate pullback identifies it with L_X[2].
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CoordinateLine
open AffineLinePurity VectorIntegrationSite

variable (A : Type (u + 1)) [CommRing A] [Finite A] (N : ℕ) (hA : (N : A) = 0)
variable (T : Scheme.{u})

/-- The existing ordinary shifted Tate line restricted by the standard chart.
Source: source paragraph (blueprint: def-pur-coordinate-line-adjunction-maps). -/
abbrev line :=
  (Etale.ordinaryFinitePullback A (ProjectiveLine.affineChart T)).obj
    ((Etale.ordinaryFiniteLine A N hA (ProjectiveLine T))⟦(2 : ℤ)⟧)

/-- The source functor K ↦ p* K tensor L_X[2], in restricted-line coordinates.
Source: G_p display (blueprint: def-pur-coordinate-line-adjunction-maps). -/
@[irreducible]
def right : Etale.DerivedCategoryModule A T ⥤
    Etale.DerivedCategoryModule A (AffineSpace PUnit.{u + 1} T) :=
  Etale.ordinaryFiniteTwistedPullback A
  (AffineSpace PUnit.{u + 1} T ↘ T) (line A N hA T)

/-- Canonical tensor pullback followed by inverse-image composition, with no choice.
Source: proof Step 3 (blueprint: def-pur-coordinate-line-adjunction-maps). -/
@[irreducible]
def rightComparison : Etale.affineTraceLineRight A N hA T ≅ right A N hA T := by
  unfold right
  exact Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (Etale.ordinaryFinitePullback A (ProjectiveLine T ↘ T))
      (Etale.derivedTensorRightCompLeftDerivedUpperStarIso (ModuleCat.{u + 1} A)
        (ProjectiveLine.affineChart T)
        ((Etale.ordinaryFiniteLine A N hA (ProjectiveLine T))⟦(2 : ℤ)⟧)) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} A)
        (ProjectiveLine.affineChart T) (ProjectiveLine T ↘ T)
        (AffineSpace PUnit.{u + 1} T ↘ T) (ProjectiveLine.affineChart_over T).symm).symm
      (Etale.derivedTensorRight (ModuleCat.{u + 1} A) _ (line A N hA T))

/-- Literal tensor coordinates, cached before coefficient specialization.
Source: the G_p display (blueprint: def-pur-coordinate-line-adjunction-maps). -/
@[irreducible]
def rightCoordinates (K : Etale.DerivedCategoryModule A T) :
    ordinarySourceObject A (AffineSpace PUnit.{u + 1} T ↘ T) (line A N hA T) K ≅
      (right A N hA T).obj K := by
  unfold ordinarySourceObject right
  exact Iso.refl _

/-- Tensor a coefficient isomorphism in the generic cached source coordinates.
Source: exponent comparison of G_p (blueprint: def-pur-coordinate-line-adjunction-maps). -/
@[irreducible]
def tensorCoefficientIso
    (W W' : DerivedCategory
      (Sheaf (Scheme.ProEt.topology (AffineSpace PUnit.{u + 1} T)) (ModuleCat.{u + 1} A)))
    (e : W ≅ W')
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A))) :
    projectionSourceObject A (AffineSpace PUnit.{u + 1} T ↘ T) W K ≅
      projectionSourceObject A (AffineSpace PUnit.{u + 1} T ↘ T) W' K := by
  unfold projectionSourceObject
  exact ((derivedTensor (ModuleCat.{u + 1} A) (AffineSpace PUnit.{u + 1} T)).obj
    ((upperStar (ModuleCat.{u + 1} A) (AffineSpace PUnit.{u + 1} T ↘ T)).leftDerivedFunctor.obj
      K)).mapIso e

variable (hN : 0 < N) [IsNoetherian T] (hT : IsUnit (N : Γ(T, ⊤)))

/-- The actual composite open/projective adjunction, transported by the canonical
right comparison. Source: compose-adjunction paragraph
(blueprint: def-pur-coordinate-line-adjunction-maps). -/
@[irreducible]
def adjunction : Etale.affineTraceLineLeft A T ⊣ right A N hA T :=
  (Etale.affineTraceLineAdjunction A N hA
    (Etale.projectiveLineTraceTransport N hN A hA) T hT
    (Etale.projectiveLineTraceDatum N hN A hA T hT)).ofNatIsoRight
      (rightComparison A N hA T)

/-- Restrict t_q by Rq_* of the actual extension-by-zero counit.
Source: I_p display (blueprint: def-pur-coordinate-line-adjunction-maps). -/
@[irreducible]
def integration : (Etale.affineTraceLineLeft A T).obj (line A N hA T) ⟶
    Etale.ordinaryFiniteUnit A T :=
  (Etale.ordinaryFinitePushforward A (ProjectiveLine T ↘ T)).map
    ((Etale.affineTraceOpenAdjunction A T).counit.app
      ((Etale.ordinaryFiniteLine A N hA (ProjectiveLine T))⟦(2 : ℤ)⟧)) ≫
    Etale.projectiveLineTrace N hN A hA T hT

set_option allowUnsafeReducibility true in
attribute [local implicit_reducible] right

/-- The coefficient-first symmetry conjugate of the canonical compact-support PF.
Source: PF_p display and tensor conventions
(blueprint: def-pur-coordinate-line-adjunction-maps). -/
@[irreducible]
def projection (K : Etale.DerivedCategoryModule A T) :
    ((Etale.ordinaryFiniteTensor A T).obj K).obj
      ((Etale.affineTraceLineLeft A T).obj (line A N hA T)) ⟶
        (Etale.affineTraceLineLeft A T).obj ((right A N hA T).obj K) :=
  let j := ProjectiveLine.affineChart T
  let q := ProjectiveLine T ↘ T
  let J := Etale.affineTraceOpenLeft A T
  let Q := Etale.ordinaryFinitePushforward A q
  ((Etale.derivedTensorSymmetry (ModuleCat.{u + 1} A) T).hom.app K).app
      (Q.obj (J.obj (line A N hA T))) ≫
    ((Etale.rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} A) q).app
      (J.obj (line A N hA T))).app K ≫
    Q.map (((Etale.derivedOpenImmersionLowerShriekProjectionIso
      (ModuleCat.{u + 1} A) j).inv.app (line A N hA T)).app
        ((Etale.ordinaryFinitePullback A q).obj K)) ≫
    Q.map (J.map (((Etale.derivedTensor (ModuleCat.{u + 1} A)
      (AffineSpace PUnit.{u + 1} T)).obj (line A N hA T)).map
        ((Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} A) j q
          (AffineSpace PUnit.{u + 1} T ↘ T)
          (ProjectiveLine.affineChart_over T).symm).inv.app K))) ≫
    (Etale.affineTraceLineLeft A T).map
      (((Etale.derivedTensorSymmetry (ModuleCat.{u + 1} A)
        (AffineSpace PUnit.{u + 1} T)).hom.app (line A N hA T)).app
          ((Etale.ordinaryFinitePullback A (AffineSpace PUnit.{u + 1} T ↘ T)).obj K))

/-- Brown representability for the literal standard compactification.
Source: the ordinary exceptional adjoint paragraph
(blueprint: def-pur-coordinate-line-adjunction-maps). -/
instance leftAdjoint :
    (Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A)
      (affineTraceLineCompactification T)).IsLeftAdjoint :=
  Etale.isLeftAdjoint_rightDerivedLowerShriekOfCompactification A
    (affineTraceLineCompactification T)

/-- Use the existing Brown right adjoint to the literal standard compactification.
Source: ordinary exceptional-adjoint paragraph
(blueprint: def-pur-coordinate-line-adjunction-maps). -/
@[irreducible]
def exceptionalAdjunction : Etale.affineTraceLineLeft A T ⊣
    (Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A)
      (affineTraceLineCompactification T)).rightAdjoint :=
  Adjunction.ofIsLeftAdjoint
    (Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A)
      (affineTraceLineCompactification T))

/-- The adjunction-preserving natural isomorphism is conjugation of the identity
left functor, so its normalization is fixed. Source: comparison paragraph
(blueprint: def-pur-coordinate-line-adjunction-maps). -/
@[irreducible]
def comparison : right A N hA T ≅
    (Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A)
      (affineTraceLineCompactification T)).rightAdjoint :=
  conjugateIsoEquiv (adjunction A N hA T hN hT)
    (exceptionalAdjunction A T) (Iso.refl _)

/-- The ordinary normalization is expressed without an arbitrarily chosen inverse:
the witness has hom equal to the specified canonical projection map.
Source: displayed counit equation, proof Step 4
(blueprint: def-pur-coordinate-line-adjunction-maps). -/
def CounitNormalization (K : Etale.DerivedCategoryModule A T) : Prop :=
  ∃ pf : ((Etale.ordinaryFiniteTensor A T).obj K).obj
      ((Etale.affineTraceLineLeft A T).obj (line A N hA T)) ≅
        (Etale.affineTraceLineLeft A T).obj ((right A N hA T).obj K),
    pf.hom = projection A N hA T K ∧
    (adjunction A N hA T hN hT).counit.app K =
      pf.inv ≫ ((Etale.ordinaryFiniteTensor A T).obj K).map
        (integration A N hA T hN hT) ≫ (Etale.derivedTensorSingleUnitIso K).hom

/-- The actual ordinary counit formula and the adjunction-preserving transpose equations.
Source: counit and comparison displays (blueprint: def-pur-coordinate-line-adjunction-maps). -/
def NormalizedOrdinary : Prop :=
  (∀ (K : Etale.DerivedCategoryModule A T),
    Etale.DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} A) T K →
    CounitNormalization A N hA T hN hT K) ∧
  (∀ K : Etale.DerivedCategoryModule A T,
    (Etale.affineTraceLineLeft A T).map ((comparison A N hA T hN hT).hom.app K) ≫
      (exceptionalAdjunction A T).counit.app K =
        (adjunction A N hA T hN hT).counit.app K) ∧
  ∀ K : Etale.DerivedCategoryModule A T,
    (comparison A N hA T hN hT).hom.app K =
      (exceptionalAdjunction A T).homEquiv _ K ((adjunction A N hA T hN hT).counit.app K)

end AlgebraicGeometry.ProEtale.CoordinateLine

namespace AlgebraicGeometry.ProEtale.CoordinateLine
open AffineLinePurity VectorIntegrationSite

variable (P : WeilConjectures.PurityFiniteSetting.{u}) (T : Scheme.{u})
variable (r : ℕ) (hA : ((P.coefficients.l ^ (r + 1) : ℕ) : Ring P) = 0)

/-- Reassociation to the already specified ordinary source; no new Tate coefficient.
Source: canonical tensor coordinates, proof Steps 3 and 6
(blueprint: def-pur-coordinate-line-adjunction-maps). -/
@[irreducible]
def sourceCoordinates (Ke : Etale.DerivedCategoryModule (Ring P) T) :
    etaleSource P.coefficients.l P.extension (P.level - 1) T r hA Ke ≅
      (right (Ring P) (P.coefficients.l ^ (r + 1)) hA T).obj Ke := by
  exact eqToIso (etaleSource_eq P.coefficients.l P.extension (P.level - 1) T r hA Ke) ≪≫
    eqToIso (congrArg
      (fun W ↦ ordinarySourceObject (Ring P) (AffineSpace PUnit.{u + 1} T ↘ T) W Ke)
      (etaleCoefficient_eq P.coefficients.l P.extension (P.level - 1) T r hA)) ≪≫
    rightCoordinates (Ring P) (P.coefficients.l ^ (r + 1)) hA T Ke

/-- The compared conjugate, with exactly the source identification, comparison unit,
and representative map. This names the map in the node's site-comparison clause.
Source: proof Steps 5--6 (blueprint: def-pur-coordinate-line-adjunction-maps). -/
@[irreducible]
def comparedConjugate [IsNoetherian T]
    (hT : IsUnit ((P.coefficients.l ^ (r + 1) : ℕ) : Γ(T, ⊤)))
    (K : DerivedCategory.Plus (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} (Ring P))))
    (Ke : Etale.DerivedCategoryModule (Ring P) T)
    (eK : (VectorIntegrationSite.comparison (Ring P) T).obj Ke ≅ K.obj) :
    source P.coefficients.l P.extension (P.level - 1) T r hA K.obj ⟶
      (sfFiniteExceptionalAt (Ring P) (affineTraceLineCompactification T)).obj K.obj :=
  (sourceComparison P.coefficients.l P.extension (P.level - 1) T r hA K.obj Ke eK).inv ≫
    (VectorIntegrationSite.comparison (Ring P) (AffineSpace PUnit.{u + 1} T)).map
      ((sourceCoordinates P T r hA Ke).hom ≫
        (CoordinateLine.comparison (Ring P) (P.coefficients.l ^ (r + 1)) hA T
          (pow_pos (Fact.out : P.coefficients.l.Prime).pos _) hT).hom.app Ke) ≫
    boundedSiteRho (Ring P)
      (Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} (Ring P))
        (affineTraceLineCompactification T)).rightAdjoint Ke ≫
    (sfFiniteExceptionalAt (Ring P) (affineTraceLineCompactification T)).map eK.hom

end AlgebraicGeometry.ProEtale.CoordinateLine
