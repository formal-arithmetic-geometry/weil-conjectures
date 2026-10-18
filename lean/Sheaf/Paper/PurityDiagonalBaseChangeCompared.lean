/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q21
-/
module

public import Sheaf.Paper.PuritySectionInvariantCompared
public import WeilConjectures.Compactification.BaseChange
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarIdCoherence
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Sheaf.AlgebraicGeometry.ProEtaleConstantRingComposition
import Sheaf.AlgebraicGeometry.ProEtaleDerivedPullbackIdentity
import Sheaf.Paper.CohomologicalSmoothnessTheorem
import Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients
import Sheaf.Paper.DerivedPullbackTensorHom
import Sheaf.Paper.IntegralFinitePullbackComposition
import Sheaf.Paper.PurityFiniteSetting
import Sheaf.Paper.PuritySectionInvariantIntrinsic

/-!
# The specified diagonal base-change comparison in finite coordinates

Source: blueprint lem-pur-diagonal-base-change, all displayed comparisons
(blueprint: lem-pur-diagonal-base-change).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor

namespace WeilConjectures.PurityFiniteSetting

/-- The diagonal chain, in its canonical etale presentation. Its first arrow is the
pullback of the inverse of the specified base-change mate, not an arbitrary isomorphism.
Source: blueprint lem-pur-diagonal-base-change, final chain
(blueprint: lem-pur-diagonal-base-change). -/
def finiteDiagonalRestriction (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]
    (b : (Etale.upperStar (ModuleCat.{u + 1} Λ)
      (pullback.snd f f)).leftDerivedFunctor.obj
        (Etale.dualizingComplex (ModuleCat.{u + 1} Λ) f) ≅
      Etale.dualizingComplex (ModuleCat.{u + 1} Λ) (pullback.fst f f)) :
    Etale.sectionInvariant Λ (pullback.fst f f) (pullback.diagonal f) ≅
      Etale.dualizingComplex (ModuleCat.{u + 1} Λ) f :=
  (Etale.upperStar (ModuleCat.{u + 1} Λ)
      (pullback.diagonal f)).leftDerivedFunctor.mapIso b.symm ≪≫
    (Etale.leftDerivedUpperStarCompSectionIso (ModuleCat.{u + 1} Λ)
      (pullback.diagonal f) (pullback.snd f f) (pullback.diagonal_snd f)).app _

/-- The diagonal chain, in its canonical etale presentation. Its first arrow is the
pullback of the inverse of the specified base-change mate, not an arbitrary isomorphism.
Source: blueprint lem-pur-diagonal-base-change, final chain
(blueprint: lem-pur-diagonal-base-change). -/
def diagonalComparedRestriction (P : PurityFiniteSetting.{u})
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]
    (b : (Etale.upperStar (ModuleCat.{u + 1} P.Coefficient)
      (pullback.snd f f)).leftDerivedFunctor.obj
        (Etale.dualizingComplex (ModuleCat.{u + 1} P.Coefficient) f) ≅
      Etale.dualizingComplex (ModuleCat.{u + 1} P.Coefficient) (pullback.fst f f)) :
    Etale.sectionInvariant P.Coefficient (pullback.fst f f) (pullback.diagonal f) ≅
      Etale.dualizingComplex (ModuleCat.{u + 1} P.Coefficient) f :=
  (Etale.upperStar (ModuleCat.{u + 1} P.Coefficient)
      (pullback.diagonal f)).leftDerivedFunctor.mapIso b.symm ≪≫
    (Etale.leftDerivedUpperStarCompSectionIso (ModuleCat.{u + 1} P.Coefficient)
      (pullback.diagonal f) (pullback.snd f f) (pullback.diagonal_snd f)).app _

/-- The same specified comparison on the actual small pro-etale section invariant.
Source: blueprint lem-pur-diagonal-base-change, final chain
(blueprint: lem-pur-diagonal-base-change). -/
def diagonalComparedProEtale (P : PurityFiniteSetting.{u})
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]
    (b : (Etale.upperStar (ModuleCat.{u + 1} P.Coefficient)
      (pullback.snd f f)).leftDerivedFunctor.obj
        (Etale.dualizingComplex (ModuleCat.{u + 1} P.Coefficient) f) ≅
      Etale.dualizingComplex (ModuleCat.{u + 1} P.Coefficient) (pullback.fst f f)) :
    P.comparedSectionInvariant (pullback.fst f f) (pullback.diagonal f) ≅
      ProEtale.finiteComparedDualizing P f :=
  P.comparedSectionPresentation _ _ ≪≫
    (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) X).mapDerivedCategory.mapIso
      (P.diagonalComparedRestriction f b)

/-- Both self-product base-change mates are invertible; the displayed restriction
construction then supplies exactly the specified diagonal comparison.
Source: blueprint lem-pur-diagonal-base-change, all three chains
(blueprint: lem-pur-diagonal-base-change).
Proof: the fibre-product universal property gives the two Cartesian squares and the
section identities. Smooth base change of thm-pur-cohomological-smoothness clause 3
makes each specified counit mate invertible. The coefficient exponent is invertible
because the fixed coefficient prime differs from the characteristic. Pull the inverse
of the first mate along the diagonal, compose pullbacks, and use diagonal_snd and
identity pullback. These are precisely diagonalComparedRestriction and its explicit
comparison-site transport diagonalComparedProEtale. No orientation is involved. -/
theorem comparedDiagonalBaseChange (P : PurityFiniteSetting.{u}) {X Y : Scheme.{u}}
    (d : ℕ) (f : X ⟶ Y) [HasCompactification f] [QuasiCompact f]
    [IsSeparated f] [SmoothOfRelativeDimension d f]
    (aX : X ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aX] [QuasiCompact aX]
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    (hf : f ≫ aY = aX) :
    IsPullback (pullback.snd f f) (pullback.fst f f) f f ∧
    SmoothOfRelativeDimension d (pullback.fst f f) ∧
    SmoothOfRelativeDimension d (pullback.snd f f) ∧
    IsIso (Etale.dualizingComplexBaseChangeMap P.Coefficient
      (IsPullback.of_hasPullback f f).flip) ∧
    IsIso (Etale.dualizingComplexBaseChangeMap P.Coefficient
      (IsPullback.of_hasPullback f f)) := by
  sorry

end WeilConjectures.PurityFiniteSetting
