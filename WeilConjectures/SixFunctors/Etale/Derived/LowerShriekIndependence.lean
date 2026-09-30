/-
Copyright (c) 2026 Weil conjectures project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weil conjectures project
-/
module

public import WeilConjectures.Compactification.CommonRefinement
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComparison

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

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [HasSmallSiteSheafify A]

namespace Etale

variable {X Y : Scheme.{u}} {f : X ⟶ Y}

/-- **The comparison of derived lower shrieks along a refinement is an isomorphism**: for a
refinement `r : c.Refinement d` whose square over `X` is cartesian, the comparison
`Rf_!(d)[A]+ ⟶ Rf_!(c)[A]+` is an isomorphism. This is the isomorphism property of
`(BA43-RHO)` in the blueprint and rests on proper base change for `r.hom`, which is not yet
available. -/
instance isIso_rightDerivedLowerShriekOfCompactificationPlusComparison
    {c d : Compactification f} (r : c.Refinement d) (hcart : IsPullback c.i (𝟙 X) r.hom d.i) :
    IsIso (rightDerivedLowerShriekOfCompactificationPlusComparison A r hcart) :=
  sorry

variable [QuasiCompact f]

/-- **The bounded below derived lower shriek does not depend on the compactification**: for
two compactifications `c` and `d` of a quasi-compact morphism `f`, the isomorphism
`Rf_!(c)[A]+ ≅ Rf_!(d)[A]+` obtained by comparing both with the common refinement
`Compactification.inf c d`: the comparison along `Compactification.infFst c d` followed by
the inverse of the comparison along `Compactification.infSnd c d`. -/
noncomputable def rightDerivedLowerShriekOfCompactificationPlusIso
    (c d : Compactification f) : Rf_!(c)[A]+ ≅ Rf_!(d)[A]+ :=
  asIso (rightDerivedLowerShriekOfCompactificationPlusComparison A
      (Compactification.infFst c d) (Compactification.isPullback_infFst c d)) ≪≫
    (asIso (rightDerivedLowerShriekOfCompactificationPlusComparison A
      (Compactification.infSnd c d) (Compactification.isPullback_infSnd c d))).symm

/-- The unbounded derived lower shrieks attached to two compactifications `c` and `d` of a
quasi-compact morphism `f` agree on bounded below objects: the isomorphism
`Plus.ι ⋙ Rf_!(c)[A] ≅ Plus.ι ⋙ Rf_!(d)[A]` induced by
`rightDerivedLowerShriekOfCompactificationPlusIso` through the compatibilities
`rightDerivedLowerShriekOfCompactificationPlusCompatibility` of the bounded below and the
unbounded derived lower shrieks. -/
noncomputable def rightDerivedLowerShriekOfCompactificationPlusιIso
    (c d : Compactification f) :
    DerivedCategory.Plus.ι ⋙ Rf_!(c)[A] ≅ DerivedCategory.Plus.ι ⋙ Rf_!(d)[A] :=
  (rightDerivedLowerShriekOfCompactificationPlusCompatibility A c).symm ≪≫
    Functor.isoWhiskerRight (rightDerivedLowerShriekOfCompactificationPlusIso A c d)
      DerivedCategory.Plus.ι ≪≫
    rightDerivedLowerShriekOfCompactificationPlusCompatibility A d

end Etale

end AlgebraicGeometry

