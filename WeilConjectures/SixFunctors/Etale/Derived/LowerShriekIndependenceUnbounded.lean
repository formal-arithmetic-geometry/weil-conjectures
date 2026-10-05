/-
Copyright (c) 2026 Weil conjectures project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weil conjectures project
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
public import WeilConjectures.Compactification.CommonRefinement
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComparison
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar

/-!

# Independence of the unbounded derived lower shriek of the compactification

Let `f : X ⟶ Y` be a morphism of schemes. This file is the unbounded counterpart of
`WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComparison` and
`WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence`. For a refinement
`r : c.Refinement d` of compactifications of `f` whose square over `X` is cartesian, it
constructs the comparison

`Rf_!(d)[A] ⟶ Rf_!(c)[A]`

of the derived lower shrieks on the unbounded derived categories, from the coarser
compactification `d` to the finer one `c`, in the same way as its bounded below version
`AlgebraicGeometry.Etale.rightDerivedLowerShriekOfCompactificationPlusComparison`: the unit of
the derived adjunction `D(r.hom)^* ⊣ R(r.hom)_*`, the inverse of the base change isomorphism
`D(c.i)_! ≅ D(d.i)_! ⋙ D(r.hom)^*`, and the composition isomorphism
`R(r.hom)_* ⋙ R(d.g)_* ≅ R(c.g)_*`. Since `(r.hom)^*` is exact, the adjunction is
`AlgebraicGeometry.Etale.mapDerivedUpperStarLowerStarAdjunction`, and no monoidal structure
on the coefficient category `A` is needed.

When `f` is quasi-compact, passing through the common refinement `Compactification.inf c d`
gives an isomorphism `Rf_!(c)[A] ≅ Rf_!(d)[A]` for any two compactifications, and in
particular an isomorphism `Rf_!(c)[A] ≅ R(f)_![A]` with the derived lower shriek defined by
the chosen compactification.

On bounded below objects, whiskering `rightDerivedLowerShriekOfCompactificationIso c d` by
`DerivedCategory.Plus.ι` should give the isomorphism
`AlgebraicGeometry.Etale.rightDerivedLowerShriekOfCompactificationPlusιIso c d` built from the
bounded below comparisons. This is not proved yet: it needs the compatibility of the
unbounded derived unit, base change and composition isomorphisms with their bounded below
counterparts.

## Main definitions

- `AlgebraicGeometry.Etale.rightDerivedLowerShriekOfCompactificationComparison`: the
  comparison `Rf_!(d)[A] ⟶ Rf_!(c)[A]` along a refinement with cartesian square over `X`;
- `AlgebraicGeometry.Etale.rightDerivedLowerShriekOfCompactificationIso`: the isomorphism
  `Rf_!(c)[A] ≅ Rf_!(d)[A]`;
- `AlgebraicGeometry.Etale.rightDerivedLowerShriekIso`: the isomorphism
  `Rf_!(c)[A] ≅ R(f)_![A]`.

## Main results

- `AlgebraicGeometry.Etale.isIso_rightDerivedLowerShriekOfCompactificationComparison`: the
  comparison is an isomorphism. Not proved yet, see its docstring for the missing hypotheses.

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

variable {X Y : Scheme.{u}} {f : X ⟶ Y} {c d : Compactification f} (r : c.Refinement d)

/-- The base change isomorphism `D(c.i)_! ≅ D(d.i)_! ⋙ D(r.hom)^*` on unbounded derived
categories, induced by `Compactification.Refinement.openImmersionLowerShriekBaseChange` for a
refinement whose square over `X` is cartesian. This is the unbounded counterpart of
`refinementLowerShriekBaseChangeDerivedPlusIso`. -/
noncomputable def refinementLowerShriekBaseChangeDerivedIso
    (hcart : IsPullback c.i (𝟙 X) r.hom d.i) :
    D((c.i)_!open[A]) ≅ D((d.i)_!open[A]) ⋙ D((r.hom)^*[A]) :=
  haveI := r.isIso_openImmersionLowerShriekBaseChange A hcart
  Functor.mapDerivedCategoryNatIso (asIso (r.openImmersionLowerShriekBaseChange A)) ≪≫
    Functor.mapDerivedCategoryCompIso _ _

/-- The comparison `Rf_!(d)[A] ⟶ Rf_!(c)[A]` of the unbounded derived lower shrieks attached
to two compactifications `c`, `d` of `f : X ⟶ Y` linked by a refinement `r : c.Refinement d`
whose square over `X` is cartesian. With `q = r.hom`, it is the composite

```
D(d.i)_! ⋙ R(d.g)_* ──η──▶ D(d.i)_! ⋙ Dq^* ⋙ Rq_* ⋙ R(d.g)_*
   ──(bc)⁻¹──▶ D(c.i)_! ⋙ Rq_* ⋙ R(d.g)_* ──comp──▶ D(c.i)_! ⋙ R(c.g)_*
```

of the unit `η` of the derived adjunction `Dq^* ⊣ Rq_*`, the inverse of the base change
isomorphism `refinementLowerShriekBaseChangeDerivedIso`, and the composition isomorphism
`Rq_* ⋙ R(d.g)_* ≅ R(c.g)_*`. As in the bounded below case
(`rightDerivedLowerShriekOfCompactificationPlusComparison`), it goes from the coarser
compactification `d` to the finer one `c`. (blueprint: unbounded analogue of `BA43-RHO`) -/
noncomputable def rightDerivedLowerShriekOfCompactificationComparison
    (hcart : IsPullback c.i (𝟙 X) r.hom d.i) : Rf_!(d)[A] ⟶ Rf_!(c)[A] :=
  Functor.whiskerRight (Functor.whiskerLeft D((d.i)_!open[A])
      (Etale.mapDerivedUpperStarLowerStarAdjunction A r.hom).unit) R((d.g)_*[A]) ≫
    Functor.whiskerRight (refinementLowerShriekBaseChangeDerivedIso A r hcart).inv
      (R((r.hom)_*[A]) ⋙ R((d.g)_*[A])) ≫
    Functor.whiskerLeft D((c.i)_!open[A])
      (Functor.rightDerivedFunctorCompIso' (r.hom)_*[A] (d.g)_*[A]
        (refinementLowerStarComp A r)).hom

/-- **The comparison of unbounded derived lower shrieks along a refinement is an
isomorphism**: for a refinement `r : c.Refinement d` whose square over `X` is cartesian, the
comparison `Rf_!(d)[A] ⟶ Rf_!(c)[A]` is an isomorphism.

Not proved yet, and not expected to hold in this generality. The blueprint (`BA43-RHO`) only
states the bounded below version, with torsion coefficients: it rests on proper base change
for `r.hom`, which needs torsion coefficients. Passing from `D⁺` to the unbounded derived
category moreover needs `R(r.hom)_*` to have finite cohomological dimension, since étale
topoi are not left-complete in general.

TODO: add the corresponding hypotheses on `A` and on `f`. This is the single place where they
are missing: the formal consequences of `R(f)_!`, such as
`AlgebraicGeometry.Etale.nonempty_iso_rightDerivedLowerShriek_comp`,
`AlgebraicGeometry.Etale.nonempty_iso_rightDerivedLowerShriek_rightDerivedLowerStar` and the
theorems built on them, will inherit them from here. -/
instance isIso_rightDerivedLowerShriekOfCompactificationComparison
    (hcart : IsPullback c.i (𝟙 X) r.hom d.i) :
    IsIso (rightDerivedLowerShriekOfCompactificationComparison A r hcart) :=
  sorry

variable [QuasiCompact f]

/-- **The unbounded derived lower shriek does not depend on the compactification**: for two
compactifications `c` and `d` of a quasi-compact morphism `f`, the isomorphism
`Rf_!(c)[A] ≅ Rf_!(d)[A]` obtained by comparing both with the common refinement
`Compactification.inf c d`: the comparison along `Compactification.infFst c d` followed by the
inverse of the comparison along `Compactification.infSnd c d`.
(blueprint: unbounded analogue of `κ_{C,D}` in `BA43-RHO`) -/
noncomputable def rightDerivedLowerShriekOfCompactificationIso
    (c d : Compactification f) : Rf_!(c)[A] ≅ Rf_!(d)[A] :=
  asIso (rightDerivedLowerShriekOfCompactificationComparison A
      (Compactification.infFst c d) (Compactification.isPullback_infFst c d)) ≪≫
    (asIso (rightDerivedLowerShriekOfCompactificationComparison A
      (Compactification.infSnd c d) (Compactification.isPullback_infSnd c d))).symm

variable [HasCompactification f]

/-- The unbounded derived lower shriek attached to any compactification `c` of a
quasi-compact morphism `f` is isomorphic to `R(f)_![A]`, the one attached to the chosen
compactification `HasCompactification.compactification f`.
(blueprint: unbounded analogue of `κ_{C,D}` in `BA43-RHO`) -/
noncomputable def rightDerivedLowerShriekIso (c : Compactification f) :
    Rf_!(c)[A] ≅ R(f)_![A] :=
  rightDerivedLowerShriekOfCompactificationIso A c (HasCompactification.compactification f)

end Etale

end AlgebraicGeometry
