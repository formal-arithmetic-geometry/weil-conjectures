/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ScalarSixTensorComparison
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Shift.Adjunction
import WeilConjectures.CategoryTheory.Right.RightExactTensorShiftCancellation
import all WeilConjectures.CategoryTheory.Derived.DerivedTensorRightExact

/-! Scalar tensor cancellation data for the native Hom shift calculation. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open scoped CategoryTheory.Obj CategoryTheory.Functor
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
attribute [local irreducible] Functor.leftDerivedFunctor Functor.leftDerivedFunctorCounit
namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- The canonical shift structure of derived scalar extension: the left-adjoint shift
structure of the derived extension/restriction adjunction, the one for which
`scalarSixHom_rows_exact` shows scalar extension is triangulated.
Source: blueprint det-prop-scalar-six-tensor-hom.proof.md, Reduction, shifts
(blueprint: lem-sfb-native-scalar-hom-tensor-cancellation). -/
@[instance_reducible]
def scalarSixChangeCommShift {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ') (X : Scheme.{u}) :
    (scalarSixChange a X).CommShift ℤ :=
  let adj : scalarSixChange a X ⊣ (Mod.comap
      (coefficientMap (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom X)).mapDerivedCategory :=
    Mod.derivedExtendMapDerivedCategoryAdjunction
      (coefficientMap (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom X)
  adj.leftAdjointCommShift ℤ

set_option maxHeartbeats 2000000 in
-- Concrete internal scalar tensor structures require large definitional conversions.
end AlgebraicGeometry.ProEtale.CondensedRing
