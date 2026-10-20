/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NG
-/
module

public import Sheaf.AlgebraicGeometry.SmoothBaseChangeCoefficients
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Defs

/-!
# Constructibility under higher direct image

Source: literature/blueprint/master/blueprint/sec-smooth-purity/sk-prop-sf-cbc/
`def-finrepair-property-c.md` (blueprint: def-finrepair-property-c).

The finite-type field context is the one used in the surrounding constructibility argument,
in particular `lem-finrepair-projective-from-line` and `thm-dg-finite-type-constructibility`.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Etale

/-- Property `C(f)`: every nonnegative higher direct image of every constructible
`Λ`-module sheaf is constructible. The schemes are of finite type over a field and satisfy
the coefficient convention for the same positive integer `N`. There is no uniform
vanishing condition. Higher direct image is the homology of the recorded derived direct
image applied to the sheaf in degree zero; constructibility uses the recorded finite
locally constant stratification predicate.
Source: blueprint `sec-smooth-purity/sk-prop-sf-cbc/def-finrepair-property-c.md`
(blueprint: def-finrepair-property-c). -/
def HasConstructibleHigherDirectImages (k : Type u) [Field k]
    (N : ℕ) (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X S : Scheme.{u}} [X.Over (Spec (.of k))] [S.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (S ↘ Spec (.of k))] [QuasiCompact (S ↘ Spec (.of k))]
    (_hX : IsSmoothBaseChangeCoefficients N Λ X)
    (_hS : IsSmoothBaseChangeCoefficients N Λ S) (f : X ⟶ S) : Prop :=
  ∀ (q : ℕ) (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
    Scheme.IsConstructibleEtaleModuleSheaf F →
      Scheme.IsConstructibleEtaleModuleSheaf (higherDirectImage Λ f (q : ℤ) F)

end AlgebraicGeometry.Etale
