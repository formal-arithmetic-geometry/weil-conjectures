/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NI
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Sheaf.AlgebraicGeometry.SmoothBaseChangeCoefficients
public import Sheaf.AlgebraicGeometry.BoundedConstructibleComplexes
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Defs

/-!
# Constructibility under higher direct image

Source: blueprint `sec-smooth-purity/sk-prop-sf-cbc/def-finrepair-property-c.md`,
order 1592 (blueprint: def-finrepair-property-c).

The base `B` makes explicit the base relative to which the source's schemes are of finite
type. No field, separation or Noetherian hypothesis is imposed on this base.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.Etale

/-- The property `C(f)`: every nonnegative higher direct image of every constructible
etale sheaf of finite coefficient modules is constructible. The schemes are of finite
type over `B`; finite type means locally of finite type and quasi-compact, as in
`def-weil-pbc-scheme-conventions`. The coefficient convention is required on both schemes.
This condition contains no bound on the degrees and no vanishing assertion.
Source: blueprint `sec-smooth-purity/sk-prop-sf-cbc/def-finrepair-property-c.md`,
order 1592 (blueprint: def-finrepair-property-c). -/
def IsConstructibleHigherDirectImage (N : ℕ) (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    (B : Scheme.{u}) {X S : Scheme.{u}} [X.Over B] [S.Over B]
    [LocallyOfFiniteType (X ↘ B)] [QuasiCompact (X ↘ B)]
    [LocallyOfFiniteType (S ↘ B)] [QuasiCompact (S ↘ B)]
    (_hX : IsSmoothBaseChangeCoefficients N Λ X)
    (_hS : IsSmoothBaseChangeCoefficients N Λ S) (f : X ⟶ S) : Prop :=
  ∀ (q : ℕ) (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
    Scheme.IsConstructibleEtaleModuleSheaf F →
      Scheme.IsConstructibleEtaleModuleSheaf (higherDirectImage Λ f (q : ℤ) F)

end AlgebraicGeometry.Etale
