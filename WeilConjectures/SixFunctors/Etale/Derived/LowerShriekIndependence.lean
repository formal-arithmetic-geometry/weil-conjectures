/-
Copyright (c) 2026 Weil conjectures project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weil conjectures project
-/
module

public import WeilConjectures.Compactification.CommonRefinement
public import WeilConjectures.Mathlib.CategoryTheory.Adjunction.FullyFaithful
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComparison
public import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriek
public import WeilConjectures.SixFunctors.OpenClosed.Derived

/-!

# Independence of the derived lower shriek of the compactification

Let `f : X ⟶ Y` be a quasi-compact morphism of schemes and let `c`, `d` be two
compactifications of `f`. This file constructs an isomorphism `Rf_!(c)[A]+ ≅ Rf_!(d)[A]+`
of the bounded below derived lower shrieks attached to `c` and `d`. It passes through the
common refinement `e = Compactification.inf c d`, the closure of the graph of `X` in
`c.Z ×_Y d.Z`:

`Rf_!(c)[A]+ ≅ Rf_!(e)[A]+ ≅ Rf_!(d)[A]+`,

where both isomorphisms are comparisons along a refinement with cartesian square over `X`
(`AlgebraicGeometry.Etale.rightDerivedLowerShriekOfCompactificationPlusComparison`). Such a
comparison is an isomorphism by proper base change. This is not proved yet and is stated
here as an instance.

## Main definitions

- `AlgebraicGeometry.Etale.rightDerivedLowerShriekOfCompactificationPlusIso`: the isomorphism
  `Rf_!(c)[A]+ ≅ Rf_!(d)[A]+`;
- `AlgebraicGeometry.Etale.rightDerivedLowerShriekOfCompactificationPlusιIso`: its
  unbounded counterpart on bounded below objects, an isomorphism
  `Plus.ι ⋙ Rf_!(c)[A] ≅ Plus.ι ⋙ Rf_!(d)[A]`.

## Main results

- `AlgebraicGeometry.Etale.isIso_rightDerivedLowerShriekOfCompactificationPlusComparison`:
  the comparison along a refinement with cartesian square over `X` is an isomorphism
  (blueprint: `BA43-RHO`). Not proved yet.

-/

@[expose] public section

universe u' u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [HasSmallSiteSheafify A]

namespace Etale

variable {X Y : Scheme.{u}} {f : X ⟶ Y}

section Torsion

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

end Torsion

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] [QuasiCompact f]

end Etale

end AlgebraicGeometry

