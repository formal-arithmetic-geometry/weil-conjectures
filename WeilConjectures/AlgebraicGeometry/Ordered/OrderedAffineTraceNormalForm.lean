/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Affine.Space.AffineSpaceTopTrace
import all WeilConjectures.AlgebraicGeometry.Affine.Trace.AffineTraceRightNormalForm

/-! # The specified ordered affine right normal form

Source: main-20261015 blueprint, proposition-purity-vector-bundles, Steps 5(b) and 6
(blueprint: def-sp-ordered-affine-right-normal-form).
This definition node owns the specified ordered normal form and its degree-zero
Tate product. It exposes the existing construction used in the trace proof;
the published trace theorem and its DAG record are unchanged.
-/

public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace AlgebraicGeometry.Etale

attribute [local irreducible] Functor.leftDerivedFunctor Functor.mapDerivedCategory
  derivedTensor upperStar lowerStar
set_option backward.isDefEq.respectTransparency true

/-- The direct pullback, ordered Tate power, and accumulated even shift.
Source: blueprint proposition-purity-vector-bundles, affine right normal form
(blueprint: def-sp-ordered-affine-right-normal-form). -/
@[expose]
def orderedAffineRight (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (S : Scheme.{u}) :
    (d : ℕ) → DerivedCategoryModule A S ⥤ DerivedCategoryModule A (affineTraceTower S d)
  | 0 => 𝟭 _
  | d + 1 => ordinaryFinitePullback A (affineTraceProjection S (d + 1)) ⋙
      derivedTensorRight (ModuleCat.{u + 1} A) (affineTraceTower S (d + 1))
        ((_root_.DerivedCategory.singleFunctor _ 0).obj
          (Scheme.finiteEtaleTateSheaf A N (affineTraceTower S (d + 1)) hA
            ((d + 1 : ℕ) : ℤ))) ⋙ shiftFunctor _ (2 * ((d + 1 : ℕ) : ℤ))

/-- The actual ordered normal form used to construct the affine-space trace.
It is the existing recursive construction, not a choice from Nonempty.
Source: blueprint proposition-purity-vector-bundles, Steps 5(b), 6; Charts of reduction-exceptional
(blueprint: def-sp-ordered-affine-right-normal-form). -/
@[irreducible]
def orderedAffineRightIso (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    (S : Scheme.{u}) (hS : IsUnit (N : Γ(S, ⊤))) :
    (d : ℕ) → affineTraceRight A N hA S d ≅ orderedAffineRight A N hA S d
  | 0 => Iso.refl _
  | d + 1 => AlgebraicGeometry.Etale.towerENormalForm (ModuleCat.{u + 1} A) N
      (fun X e ↦ Scheme.finiteEtaleTateSheaf A N X hA (e : ℤ))
      (fun f hY e ↦ (Scheme.finiteEtaleTwistPullbackData A N hN hA).c f hY
        (affineTracePullbackInvertible N f hY) e)
      (fun _ ↦ Iso.refl _) (fun X hX e ↦
        AlgebraicGeometry.Etale.twistFlat A N hN hA X hX e)
      (fun X hX e ↦ AlgebraicGeometry.Etale.twistSheafProduct A N hA
        (Scheme.finiteEtaleTwistPullbackData A N hN hA) X hX e) S hS (d + 1)

end AlgebraicGeometry.Etale
