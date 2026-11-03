/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleTorAmplitude
public import WeilConjectures.AlgebraicGeometry.ProEtale.Fixed.ProEtaleFixedModuleConstructible

/-! Intrinsic Dctf predicate used by the general-field compact-support scalar square.

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-smooth-purity/sec-sp-grp-ladic-summary/sec-change-of-finite-coefficients/
sk-lem-sp-reduction/sk-lem-sp-reduction-exceptional.md, the constructible finite-Tor
input (blueprint: def-pur-general-field-dctf).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.ProEtale

/-- Bounded constructibility and finite Tor amplitude on the ordinary intrinsic
pro-etale derived category.
(blueprint: def-pur-general-field-dctf) -/
def generalFieldDctf (T : Scheme.{u}) (A : Type u) [CommRing A] [Finite A]
    (M : proEtaleDerivedCategory T A) : Prop :=
  Set.Finite {i : ℤ | ¬ IsZero ((DerivedCategory.homologyFunctor
      (proEtaleRingModules T (proEtaleConstantRing T A)) i).obj M)} ∧
    (∀ i : ℤ, Scheme.IsConstructibleProEtaleModuleSheaf T A
      ((DerivedCategory.homologyFunctor
        (proEtaleRingModules T (proEtaleConstantRing T A)) i).obj M)) ∧
    HasFiniteProEtaleTorAmplitude T A M

end AlgebraicGeometry.ProEtale
