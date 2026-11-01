/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Reduction.ReductionExceptionalObjects
import all WeilConjectures.AlgebraicGeometry.Reduction.ReductionDirectImage
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.HomComparison
import WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek
import Mathlib.CategoryTheory.Adjunction.Restrict
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded

/-! # Realization of a finite-coefficient exceptional adjunction -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genCtorIdx false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace CategoryTheory

end CategoryTheory

namespace AlgebraicGeometry.ProEtale

@[irreducible] private def ordinaryAdjunction (A : Type u) [CommRing A] [Finite A]
    {X Z Y : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j] (p : Z ⟶ Y) [IsProper p]
    [HasCompactification (j ≫ p)] [QuasiCompact (j ≫ p)] :
    Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} (ULift.{u + 1} A))
      (⟨Z, p, j, rfl, inferInstance, inferInstance⟩ : Compactification (j ≫ p)) ⊣
        Etale.rightDerivedUpperShriek (ULift.{u + 1} A) (j ≫ p) :=
  (Etale.rightDerivedUpperShriekAdjunction (ULift.{u + 1} A) (j ≫ p)).ofNatIsoLeft
    (Etale.rightDerivedLowerShriekIso (ULift.{u + 1} A)
      (⟨Z, p, j, rfl, inferInstance, inferInstance⟩ : Compactification (j ≫ p))).symm

end AlgebraicGeometry.ProEtale
