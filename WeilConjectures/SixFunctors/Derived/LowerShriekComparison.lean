/-
Copyright (c) 2026 Weil conjectures project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weil conjectures project
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusAdjunction
public import WeilConjectures.SixFunctors.Derived.LowerShriek
public import WeilConjectures.SixFunctors.LowerShriek.OpenImmersion.BaseChange

/-!

# Comparison of derived lower shrieks along a refinement of compactifications

Let `f : X ⟶ Y` be a morphism of schemes, let `c` and `d` be compactifications of `f` and let
`r : c.Refinement d` be a refinement, i.e. a morphism `q = r.hom : c.Z ⟶ d.Z` with
`c.i ≫ q = d.i` and `q ≫ d.g = c.g`. This file constructs the comparison

`Rf_!(d)[A]+ ⟶ Rf_!(c)[A]+`

of the bounded below derived lower shrieks attached to the two compactifications, under the
hypothesis that the square

```
X --c.i--> c.Z
|          |
𝟙          q
|          |
X --d.i--> d.Z
```

is cartesian, i.e. `q ⁻¹ (X) = X`.

Note the direction: the comparison goes from the *coarser* compactification `d` to the
*finer* one `c`. Neither direction is formal — the adjunctions produce a cospan of natural
transformations into `D(d.i)_! ⋙ Dq^* ⋙ Rq_* ⋙ R(d.g)_*`, and one of the two legs has to be
inverted to obtain an arrow. Inverting the leg coming from the base change comparison for
`j_!` is what the cartesian hypothesis buys, and it produces the direction above; inverting
the other leg is proper base change and produces the opposite direction.

The composite is, with `q = r.hom`:

```
D(d.i)_! ⋙ R(d.g)_*
  ⟶ D(d.i)_! ⋙ Dq^* ⋙ Rq_* ⋙ R(d.g)_*   (unit of `Dq^* ⊣ Rq_*`)
  ⟶ D(c.i)_! ⋙ Rq_* ⋙ R(d.g)_*          (inverse of base change for `j_!`)
  ⟶ D(c.i)_! ⋙ R(c.g)_*                 (composition of derived pushforwards)
```

## Main definitions

- `AlgebraicGeometry.Etale.refinementLowerStarComp`: the composition isomorphism
  `(r.hom)_* ⋙ (d.g)_* ≅ (c.g)_*` of pushforwards attached to a refinement.

- `AlgebraicGeometry.Etale.rightDerivedLowerShriekOfCompactificationPlusComparison`: the
  comparison `Rf_!(d)[A]+ ⟶ Rf_!(c)[A]+` above. (blueprint: `BA43-RHO`)

## Implementation notes

Only the bounded below variant is constructed. The unbounded variant would need both the
unbounded derived adjunction `Dq^* ⊣ Rq_*` and the unbounded composition isomorphism for
derived pushforwards, neither of which is available.

That the comparison is an isomorphism is proper base change and is not proved here, nor are
its compatibilities with `Compactification.Refinement.id` and
`Compactification.Refinement.comp`.

-/

@[expose] public section

universe u' u

open CategoryTheory Limits

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

namespace Etale

variable {X Y : Scheme.{u}} {f : X ⟶ Y} {c d : Compactification f} (r : c.Refinement d)

/-- The composition isomorphism `(r.hom)_* ⋙ (d.g)_* ≅ (c.g)_*` of pushforwards on étale
sheaves attached to a refinement `r : c.Refinement d`, coming from
`Etale.lowerStarComp` and the relation `r.hom ≫ d.g = c.g`. -/
noncomputable def refinementLowerStarComp : (r.hom)_*[A] ⋙ (d.g)_*[A] ≅ (c.g)_*[A] :=
  Etale.lowerStarComp A r.hom d.g ≪≫ eqToIso (by rw [r.hom_g])

/-- The base change isomorphism `D(c.i)_! ≅ D(d.i)_! ⋙ D(r.hom)^*` on bounded below derived
categories, induced by `Compactification.Refinement.openImmersionLowerShriekBaseChange` for
a refinement whose square over `X` is cartesian. -/
noncomputable def refinementLowerShriekBaseChangeDerivedPlusIso
    (hcart : IsPullback c.i (𝟙 X) r.hom d.i) :
    (c.i)_!open[A].mapDerivedCategoryPlus ≅
      (d.i)_!open[A].mapDerivedCategoryPlus ⋙ (r.hom)^*[A].mapDerivedCategoryPlus :=
  haveI := r.isIso_openImmersionLowerShriekBaseChange A hcart
  Functor.mapDerivedCategoryPlusNatIso (asIso (r.openImmersionLowerShriekBaseChange A)) ≪≫
    Functor.mapDerivedCategoryPlusCompIso _ _

/-- The comparison `Rf_!(d)[A]+ ⟶ Rf_!(c)[A]+` of the bounded below derived lower shrieks
attached to two compactifications `c`, `d` of `f : X ⟶ Y` linked by a refinement
`r : c.Refinement d` whose square over `X` is cartesian.

It is the composite of the unit of the derived adjunction
`D(r.hom)^* ⊣ R(r.hom)_*`, the inverse of the base change isomorphism
`D(c.i)_! ≅ D(d.i)_! ⋙ D(r.hom)^*`, and the composition isomorphism
`R(r.hom)_* ⋙ R(d.g)_* ≅ R(c.g)_*`. Note that it goes from the coarser compactification `d`
to the finer one `c`. (blueprint: `BA43-RHO`) -/
noncomputable def rightDerivedLowerShriekOfCompactificationPlusComparison
    (hcart : IsPullback c.i (𝟙 X) r.hom d.i) : Rf_!(d)[A]+ ⟶ Rf_!(c)[A]+ :=
  haveI : ((r.hom)_*[A]).PreservesInjectiveObjects :=
    Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
      (Etale.upperStarLowerStarAdjunction A r.hom)
  Functor.whiskerRight (Functor.whiskerLeft (d.i)_!open[A].mapDerivedCategoryPlus
      (Etale.upperStarLowerStarAdjunction A r.hom).derivedPlus.unit)
      (d.g)_*[A].rightDerivedFunctorPlus ≫
    Functor.whiskerRight (refinementLowerShriekBaseChangeDerivedPlusIso A r hcart).inv
      ((r.hom)_*[A].rightDerivedFunctorPlus ⋙ (d.g)_*[A].rightDerivedFunctorPlus) ≫
    Functor.whiskerLeft (c.i)_!open[A].mapDerivedCategoryPlus
      (Functor.rightDerivedFunctorPlusCompIso' (r.hom)_*[A] (d.g)_*[A]
        (refinementLowerStarComp A r)).hom

end Etale

end AlgebraicGeometry
