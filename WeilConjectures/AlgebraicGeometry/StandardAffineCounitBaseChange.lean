/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CoordinateCounitArrows
import WeilConjectures.AlgebraicGeometry.StandardAffineCounitTowerBaseChange
import WeilConjectures.AlgebraicGeometry.StandardAffineCounitCoordinateTransport
import WeilConjectures.AlgebraicGeometry.StandardAffineCounitCoordinateSquare

/-! # Base change of the standard affine counit adjunct
Source: sk-thm-dnc, local construction, standard affine model.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Etale
open SectionComparisonArrows SectionLocalDualizingComparisons

/-- The standard affine counit adjunct commutes with arbitrary Noetherian base change.
Source: sk-thm-dnc, Local construction, standard affine model; ordered trace base change
(blueprint: lem-trf-standard-affine-counit-base-change).

Proof: transpose the ordered tower counit. Compact-support exchange and its unit
comparison transport the trace base-change equation to actual compact support;
the defining exceptional-mate counit equation identifies the two transposes, by
injectivity of the adjunction bijection.
Identify the tower coefficient through affineLinearCoefficientDescent and baseTateIso.
Induction on the ordered tensor length, using normalized root products, tensor
pullback and even-shift coherence, identifies its base-change map with towerTateIso
followed by canonical Tate pullback. The coordinate isomorphism from the ordered
tower to affine space is natural in the base: both maps have the same coordinate
functions. Paste its Cartesian squares with the tower square. Exceptional mate
pasting and inverse-image compositor naturality carry the tower equation to the
standard affine space equation below. At d=0 use the identity tower and unit
comparisons. All calculations hold for an empty base or the zero coefficient ring.
-/
theorem standardAffineCounit_baseChange (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA)
    (D : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (N : Γ(T, ⊤))),
      OrdinaryFiniteP1Datum A N hA t T hT)
    {S T : Scheme.{u}} [IsNoetherian S] [IsNoetherian T]
    (v : T ⟶ S) (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ) :
    (upperStar (ModuleCat.{u + 1} A) (AffineSpace.map (ULift.{u} (Fin d)) v)).leftDerivedFunctor.map
        (CoordinateCounitArrows.standardAdjoint N hN A hA t D S hS d) ≫
      dualizingComplexBaseChangeMap A (AffineSpace.isPullback_map v) =
    (tatePullback A N hN hA (AffineSpace.map (ULift.{u} (Fin d)) v)
      (invertibleOnSource N (AffineSpace (ULift.{u} (Fin d)) S ↘ S) hS)
      (invertibleOnSource N (AffineSpace (ULift.{u} (Fin d)) T ↘ T)
        (invertibleOnSource N v hS)) d).hom ≫
      CoordinateCounitArrows.standardAdjoint N hN A hA t D T
        (invertibleOnSource N v hS) d := by
  simp only [CoordinateCounitArrows.standardAdjoint]
  simpa only [Functor.map_comp, Category.assoc] using
    (standardAffineCounit_coordinateTransport N hN A hA t v hS d
      (CoordinateCounitArrows.towerAdjoint N hN A hA t D S hS d)
      (CoordinateCounitArrows.towerAdjoint N hN A hA t D T
        (invertibleOnSource N v hS) d)
      (standardAffineCounit_coordinateSquare v d)
      (standardAffineCounit_towerBaseChange N hN A hA t D v hS d))

end AlgebraicGeometry.Etale
