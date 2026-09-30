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
`WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence`. For a refinement
`r : c.Refinement d` of compactifications of `f` whose square over `X` is cartesian, it
constructs the comparison

`Rf_!(d)[A] ⟶ Rf_!(c)[A]`

of the derived lower shrieks on the unbounded derived categories, from the coarser
compactification `d` to the finer one `c`, in the same way as its bounded below version
`AlgebraicGeometry.Etale.rightDerivedLowerShriekOfCompactificationPlusComparison`: the unit of
the derived adjunction `L(r.hom)^* ⊣ R(r.hom)_*`, the inverse of the base change isomorphism
`D(c.i)_! ≅ D(d.i)_! ⋙ D(r.hom)^*`, and the composition isomorphism
`R(r.hom)_* ⋙ R(d.g)_* ≅ R(c.g)_*`.

When `f` is quasi-compact, passing through the common refinement `Compactification.inf c d`
gives an isomorphism `Rf_!(c)[A] ≅ Rf_!(d)[A]` for any two compactifications, and in
particular an isomorphism `Rf_!(c)[A] ≅ R(f)_![A]` with the derived lower shriek defined by
the chosen compactification.

## Main definitions

- `AlgebraicGeometry.Etale.rightDerivedLowerShriekOfCompactificationComparison`: the
  comparison `Rf_!(d)[A] ⟶ Rf_!(c)[A]` along a refinement with cartesian square over `X`;
- `AlgebraicGeometry.Etale.rightDerivedLowerShriekOfCompactificationIso`: the isomorphism
  `Rf_!(c)[A] ≅ Rf_!(d)[A]`;
- `AlgebraicGeometry.Etale.rightDerivedLowerShriekIso`: the isomorphism
  `Rf_!(c)[A] ≅ R(f)_![A]`.

## Main results

- `AlgebraicGeometry.Etale.rightDerivedLowerShriekOfCompactificationComparison_plus`: on bounded
  below objects, the comparison restricts to its bounded below version. Not proved yet.
- `AlgebraicGeometry.Etale.isIso_rightDerivedLowerShriekOfCompactificationComparison`: the
  comparison is an isomorphism (blueprint: `BA43-RHO`). Not proved yet; it rests on proper
  base change.

-/

@[expose] public section

universe u' u

open CategoryTheory Limits

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] [HasSmallSiteSheafify A]

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
whose square over `X` is cartesian.

It is the composite of the unit of the derived adjunction `L(r.hom)^* ⊣ R(r.hom)_*` (with
`L(r.hom)^*` identified with `D(r.hom)^*`, the pullback being exact), the inverse of the base
change isomorphism `D(c.i)_! ≅ D(d.i)_! ⋙ D(r.hom)^*`, and the composition isomorphism
`R(r.hom)_* ⋙ R(d.g)_* ≅ R(c.g)_*`. As in the bounded below case
(`rightDerivedLowerShriekOfCompactificationPlusComparison`), it goes from the coarser
compactification `d` to the finer one `c`. (blueprint: `BA43-RHO`) -/
noncomputable def rightDerivedLowerShriekOfCompactificationComparison
    (hcart : IsPullback c.i (𝟙 X) r.hom d.i) : Rf_!(d)[A] ⟶ Rf_!(c)[A] :=
  haveI : ((r.hom)_*[A]).PreservesKInjectiveComplexes :=
    (Etale.upperStarLowerStarAdjunction A r.hom).preservesKInjectiveComplexes
  Functor.whiskerRight (Functor.whiskerLeft D((d.i)_!open[A])
      ((Etale.derivedUpperStarLowerStarAdjunction A r.hom).unit ≫
        Functor.whiskerRight (Etale.leftDerivedUpperStarIsoMapDerivedCategory A r.hom).hom _))
      R((d.g)_*[A]) ≫
    Functor.whiskerRight (refinementLowerShriekBaseChangeDerivedIso A r hcart).inv
      (R((r.hom)_*[A]) ⋙ R((d.g)_*[A])) ≫
    Functor.whiskerLeft D((c.i)_!open[A])
      (Functor.rightDerivedFunctorCompIso' (r.hom)_*[A] (d.g)_*[A]
        (refinementLowerStarComp A r)).hom

/-- On bounded below objects, the unbounded comparison
`rightDerivedLowerShriekOfCompactificationComparison` restricts to the bounded below
comparison `rightDerivedLowerShriekOfCompactificationPlusComparison`, through the
compatibilities `rightDerivedLowerShriekOfCompactificationPlusCompatibility`.

Not proved yet: it requires comparing, factor by factor, the unbounded unit, base change
and composition isomorphisms with their bounded below counterparts. -/
theorem rightDerivedLowerShriekOfCompactificationComparison_plus
    (hcart : IsPullback c.i (𝟙 X) r.hom d.i) :
    Functor.whiskerLeft DerivedCategory.Plus.ι
        (rightDerivedLowerShriekOfCompactificationComparison A r hcart) =
      (rightDerivedLowerShriekOfCompactificationPlusCompatibility A d).inv ≫
        Functor.whiskerRight (rightDerivedLowerShriekOfCompactificationPlusComparison A r hcart)
          DerivedCategory.Plus.ι ≫
        (rightDerivedLowerShriekOfCompactificationPlusCompatibility A c).hom :=
  sorry

/-- **The comparison of unbounded derived lower shrieks along a refinement is an
isomorphism**: for a refinement `r : c.Refinement d` whose square over `X` is cartesian, the
comparison `Rf_!(d)[A] ⟶ Rf_!(c)[A]` is an isomorphism. This is the isomorphism property of
`(BA43-RHO)` in the blueprint and rests on proper base change for `r.hom`, which is not yet
available. -/
theorem isIso_rightDerivedLowerShriekOfCompactificationComparison
    (hcart : IsPullback c.i (𝟙 X) r.hom d.i) :
    IsIso (rightDerivedLowerShriekOfCompactificationComparison A r hcart) :=
  sorry

variable [QuasiCompact f]

/-- **The unbounded derived lower shrieks does not depend on the compactification**: for two
compactifications `c` and `d` of a quasi-compact morphism `f`, the isomorphism
`Rf_!(c)[A] ≅ Rf_!(d)[A]` obtained by comparing both with the common refinement
`Compactification.inf c d`: the comparison along `Compactification.infFst c d` followed by the
inverse of the comparison along `Compactification.infSnd c d`. -/
noncomputable def rightDerivedLowerShriekOfCompactificationIso
    (c d : Compactification f) : Rf_!(c)[A] ≅ Rf_!(d)[A] :=
  haveI := isIso_rightDerivedLowerShriekOfCompactificationComparison A
    (Compactification.infFst c d) (Compactification.isPullback_infFst c d)
  haveI := isIso_rightDerivedLowerShriekOfCompactificationComparison A
    (Compactification.infSnd c d) (Compactification.isPullback_infSnd c d)
  asIso (rightDerivedLowerShriekOfCompactificationComparison A
      (Compactification.infFst c d) (Compactification.isPullback_infFst c d)) ≪≫
    (asIso (rightDerivedLowerShriekOfCompactificationComparison A
      (Compactification.infSnd c d) (Compactification.isPullback_infSnd c d))).symm

/-- The unbounded derived lower shriek attached to any compactification `c` of a
quasi-compact morphism `f` is isomorphic to `R(f)_![A]`, the one attached to the chosen
compactification `HasCompactification.compactification f`. -/
noncomputable def rightDerivedLowerShriekIso (c : Compactification f) [HasCompactification f] :
    Rf_!(c)[A] ≅ R(f)_![A] :=
  rightDerivedLowerShriekOfCompactificationIso A c (HasCompactification.compactification f)

end Etale

end AlgebraicGeometry
