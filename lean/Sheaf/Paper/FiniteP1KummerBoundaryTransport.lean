/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.FiniteP1CoefficientAdjunctionCoordinates
public import Sheaf.Paper.TowerClassFinite
public import Sheaf.AlgebraicGeometry.GeoP1Cohomology

/-! # Transport of the finite Kummer boundary comparison

Source: blueprint latest, diagonal-tower trace proof (1), scalar Kummer
normalization in paragraph (1).
(blueprint: lem-sfb-finite-p1-kummer-boundary-transport).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.ProEtale.DiagonalTrace
open SpTowerClasses

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The finite boundary equality at the pulled-back hyperplane class. -/
def FiniteP1BoundaryData
    {X S : Scheme.{u}} [IsNoetherian X] [IsNoetherian S]
    (e : X ≅ ProjectiveLine S) (cX : Chern l E X) (n : ℕ)
    [Finite (SpTowerShriek.R l E n)] : Prop :=
  finiteBoundaryEquality
    ((DerivedCategory.singleFunctor (DiagonalAb X) 0).map
      (finiteQuotient l E X n))
    (((DerivedCategory.singleFunctor (DiagonalAb X) 0).map
      (finiteRootMap l E X n))⟦(2 : ℤ)⟧')
    (mapSingleArrow (finiteForget l E X n) (2 : ℤ)
      (evaluatedChern l E cX
        (Scheme.Pic.mapHom e.hom (hyperplanePic S)) n))
    (mapSingleArrow (abEvaluation X n) (2 : ℤ)
      (kummerComposite (C := Ab X)
        (ShortComplex.mk cX.kummer.inclusion cX.kummer.power cX.kummer.zero)
        cX.kummer.exact
        (lineBundleClass X (Scheme.Pic.mapHom e.hom (hyperplanePic S)))))

/--
A finite boundary equality transports through the normalized coefficient and
site comparisons to the displayed derived equality.  The statement isolates
the scalar Kummer step from construction of the line comparison isomorphism.
Source: diagonal-tower trace (1), scalar Kummer normalization in paragraph (1).
(blueprint: lem-sfb-finite-p1-kummer-boundary-transport).
-/
theorem finiteP1_kummer_chern_realization_of_boundary
    {X S : Scheme.{u}} [IsNoetherian X] [IsNoetherian S]
    (e : X ≅ ProjectiveLine S) (cX : Chern l E X)
    (hS : IsUnit (l : Γ(S, ⊤))) (n : ℕ)
    [Finite (SpTowerShriek.R l E n)]
    {hX : IsUnit ((l ^ (n + 1) : ℕ) : Γ(X, ⊤))}
    (c : SpTowerP1.CoefficientCoordinates l E n X hX)
    (t : (SpTowerShriek.Ev l E X n).obj ((line l E cX)⟦(2 : ℤ)⟧) ≅
      (finiteOverRealization l E n e).obj
        (geoP1Twist (FiniteRing l E n) (l ^ (n + 1))
          (ULift.ext _ _ (coefficient_annihilates l E n)) (ProjectiveLine S) 1 2))
    (hb : FiniteP1BoundaryData l E e cX n) :
    (SpTowerShriek.Ev l E X n).map
        (firstChern l E cX
          (Scheme.Pic.mapHom e.hom (hyperplanePic S))) ≫ t.hom =
      (finiteOverUnitCoordinate l E n e c).hom ≫
        (finiteOverRealization l E n e).map
          ((geoP1Comparison (FiniteRing l E n) (ProjectiveLine S)).map
            (geoP1EtaleChern (FiniteRing l E n) (l ^ (n + 1))
              (pow_pos (Fact.out : l.Prime).pos _)
              (ULift.ext _ _ (coefficient_annihilates l E n)) S
              (by simpa only [Nat.cast_pow] using hS.pow (n + 1)))) := by
  sorry

end AlgebraicGeometry.ProEtale.DiagonalTrace
