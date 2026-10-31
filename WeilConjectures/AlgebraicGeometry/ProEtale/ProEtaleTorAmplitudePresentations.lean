/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Ringed.RingedProEtaleTorAmplitudeOfUniverses
public import WeilConjectures.CategoryTheory.DerivedCategory.TorAmplitude
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Tensor

/-! # Tor amplitude in ringed and fixed-coefficient presentations

Source: Stacks Project, Tags 06YY and 08FZ
(blueprint: def-weil-proetale-tor-amplitude).

The original interface is retained; its fixed-coefficient specialization uses the
existing module-sheaf localization, scalar adjunction and derived tensor.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme
/-- The existing universal degree-zero module test in fixed-coefficient coordinates.
Source: Stacks 08FZ (blueprint: def-weil-proetale-tor-amplitude). -/
abbrev HasFixedCoefficientProEtaleTorAmplitude (X : Scheme.{u})
    (A : Type (u + 1)) [CommRing A]
    (K : DerivedCategory (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} A))) (a b : ℤ) : Prop :=
  a ≤ b ∧ DerivedCategory.torAmplitudeIn
    (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} A)) a b K
end AlgebraicGeometry.Scheme
