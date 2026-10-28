/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE
-/
module

public import Sheaf.Paper.DiagonalCoefficientFiniteRealization
public import Sheaf.Paper.DiagonalCoefficientUnitPush

/-! # Normalized finite coefficient-unit square

Source: diagonal tower coefficient changes (1), normalized finite push square.
(blueprint: lem-diagonal-finite-unit-push)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

attribute [local irreducible] Functor.mapDerivedCategory Functor.leftAdjoint
  Functor.rightAdjoint FiniteRealization.derivedUnit

/-- The normalized finite push square on the coefficient unit, before cancellation
of the finite realization unit isomorphism. This is the single-object instance of
`FinitePushSquare.derived.normalization`, combined with the ordinary unit
normalization and the canonical derived-unit equation. The ordinary square is
first evaluated on the regular module, then the single-complex comparisons are
cancelled; the result is the displayed equation. No line, trace, or positivity
hypothesis enters this coefficient-unit step.
(blueprint: lem-diagonal-finite-unit-push-square)

Proof: evaluate the supplied finite push-square normalization at the regular module,
use the ordinary unit normalization to identify the coefficient map, cancel the
single-complex comparison isomorphisms, and apply the canonical derived-unit
equation and the finite adjunction hom-equivalence. -/
theorem finite_unit_push_square
    {R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}} [MonObj R] [IsCommMonObj R]
    {A : Type (u + 1)} [CommRing A] (Y : Scheme.{u})
    (eY : FiniteRealization R A Y) (eP : FiniteRealization R A (ProjectiveLine Y))
    (D : DiagonalRightDerived (CondensedRing.lowerStar R (ProjectiveLine Y ↘ Y)))
    (D' : DiagonalRightDerived (lowerStar (ModuleCat.{u + 1} A) (ProjectiveLine Y ↘ Y)))
    (hc : D'.R = geoP1Pushforward A (ProjectiveLine Y ↘ Y))
    (hcanonical : IsCanonicalRightDerived
      (lowerStar (ModuleCat.{u + 1} A) (ProjectiveLine Y ↘ Y)) D' hc)
    (s : FinitePushSquare R A (ProjectiveLine Y ↘ Y) eP eY D D') :
    let t := s.derived.iso.hom ≫
      Functor.whiskerLeft eP.F.mapDerivedCategory (eqToIso hc).hom
    let i : eP.F.mapDerivedCategory.obj (unit R (ProjectiveLine Y)) ≅
        geoP1Unit A (ProjectiveLine Y) :=
      (eP.F.mapDerivedCategorySingleFunctor 0).app _ ≪≫
        (DerivedCategory.singleFunctor _ 0).mapIso eP.unitIso ≪≫
          (finiteUnitComparison A (ProjectiveLine Y)).symm
    eY.F.mapDerivedCategory.map (coefficientUnitPush R Y D) ≫
        t.app (unit R (ProjectiveLine Y)) ≫
        (geoP1Pushforward A (ProjectiveLine Y ↘ Y)).map eP.derivedUnit =
      eY.derivedUnit ≫ finiteUnitAdjunct A Y ≫
        (geoP1Pushforward A (ProjectiveLine Y ↘ Y)).map
          (i.inv ≫
            eP.F.mapDerivedCategory.map (𝟙 (unit R (ProjectiveLine Y))) ≫
              eP.derivedUnit) := by sorry

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
