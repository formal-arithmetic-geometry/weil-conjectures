/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.FieldTheory.IsSepClosed
public import WeilConjectures.AlgebraicGeometry.InvertibleExponent
public import WeilConjectures.SixFunctors.ProEtale.Comparison
public import WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriek

/-!
# The admissibility datum for the ambient exceptional right adjoint

The existence of the ambient exceptional right adjoint `Rf^×` on the *unbounded* derived
category of the small pro-étale site is not a theorem of this development: it is an explicit
hypothesis, recorded here as `AlgebraicGeometry.ProEtale.AmbientExceptionalAdjointData`. Its
two ingredients are a uniform cohomological-dimension bound for the proper part `p` of a
compactification — which is what makes `Rp_*` preserve coproducts, hence Brown representability
applicable — and the requirement that the resulting right adjoint preserve the small
subcategories in which the purity statements live.

On the *étale-origin* class the bound is a theorem, with `c = 2 dim X̄`: it follows from the
finiteness of proper direct images in ordinary étale cohomology together with the pro-étale
comparison.

## Implementation notes

The datum is a `structure`, not a `class`: it is indexed by a family `P` of object properties
which instance resolution cannot solve for, so it is meant to be named and passed explicitly.

The blueprint's "compatibly with refinements" clause of `sk-def-sf-admissible` is not among
the fields: the repository has no refinement relation between compactifications to state it
against.

The purity chapter itself is stated on the small *étale* site, with
`AlgebraicGeometry.Etale.rightDerivedUpperShriek`, while the datum here is about the pro-étale
`Rf^!`. The bridge between the two is the comparison of
`WeilConjectures.SixFunctors.ProEtale.Comparison`; that `ν^*` intertwines the two exceptional
inverse images is not stated anywhere yet, and is a TODO of the block.

## Main definitions

- `AlgebraicGeometry.ProEtale.HasUniformCohomologicalDimensionLE`: the uniform
  cohomological-dimension bound, stable under base change along the pro-étale site.
- `AlgebraicGeometry.ProEtale.AmbientExceptionalAdjointData`: the admissibility datum.

## Main statements

- `AlgebraicGeometry.ProEtale.isZero_homology_rightDerivedLowerStar_comparisonUpperStar`
-/

@[expose] public section

universe u' u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

namespace ProEtale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  {X Y : Scheme.{u}}

/-- Blueprint `sk-def-sf-admissible`: Admissibility datum: an explicit hypothesis

`p : X ⟶ Y` *has uniform cohomological dimension at most `c` at `A`* if the higher direct
images of `p`, and of all its base changes along objects of `Y_proét`, vanish above `c` on
*every* pro-étale sheaf of `A`-modules:

```
  X' --g'--> X
  |          |          R^r p'_* F = 0 for r > c, all F on X'_proét
  p'         p
  |          |
  v          v
  V.left --V.hom--> Y        V an object of Y_proét
```

This is the uniform bound that makes `Rp_*` preserve coproducts on the unbounded derived
category. The base changes are taken along the pro-étale site of `Y`, as in the blueprint, and
not along arbitrary morphisms of schemes: the latter is a strictly stronger hypothesis than
`sk-prop-sf-fullcd-etale-origin` can deliver. -/
def HasUniformCohomologicalDimensionLE (p : X ⟶ Y) (c : ℕ) : Prop :=
  ∀ (V : Y.ProEt) ⦃X' : Scheme.{u}⦄ (g' : X' ⟶ X) (p' : X' ⟶ V.left),
    IsPullback g' p' p V.hom →
      ∀ (F : Sheaf (Scheme.ProEt.topology X') A) (r : ℤ), (c : ℤ) < r →
        IsZero ((_root_.DerivedCategory.homologyFunctor _ r).obj
          ((R((p')_*[A])).obj ((_root_.DerivedCategory.singleFunctor _ 0).obj F)))

/-- Blueprint `sk-def-sf-admissible`: Admissibility datum: an explicit hypothesis

The *ambient exceptional right adjoint datum* for a separated finite-type `f : X ⟶ Y` at `A`,
relative to a family `P` of object properties standing for the constructible intervals and the
finite-Tor subcategory: a uniform cohomological-dimension bound for the proper part of the
chosen compactification of `f`, together with the requirement that `Rf^!` preserve `P`.

This is an *assumption*, not a property proved here; the existence of the right adjoint itself
is the ambient instance
`AlgebraicGeometry.ProEtale.isLeftAdjoint_rightDerivedLowerShriek`, which is why it is not
repeated as a field. -/
structure AmbientExceptionalAdjointData (f : X ⟶ Y) [HasCompactification f]
    (P : ∀ Z : Scheme.{u},
      ObjectProperty (_root_.DerivedCategory (Sheaf (Scheme.ProEt.topology Z) A))) : Prop where
  /-- A uniform cohomological-dimension bound for the proper part of the compactification. -/
  exists_hasUniformCohomologicalDimensionLE :
    ∃ c : ℕ, HasUniformCohomologicalDimensionLE A (HasCompactification.compactification f).g c
  /-- The exceptional right adjoint preserves the small subcategories. -/
  rightDerivedUpperShriek_mem : ∀ K, P Y K → P X ((R(f)^![A]).obj K)

/-- Blueprint `sk-prop-sf-fullcd-etale-origin`: `FullCD` on the étale-origin class

**The cohomological-dimension bound on the étale-origin class.** Let `k` be separably closed,
let `p : X' ⟶ Y` be a proper morphism of finite-type `k`-schemes with `dim X' ≤ d`, and let
`Λ` be a finite coefficient ring whose exponent is invertible on `X'` — so that every sheaf of
`Λ`-modules is torsion, which is the first line of the blueprint proof. Then for every étale
sheaf `F` of `Λ`-modules on any base change `X''` of `X'`,

`H^r(Rp'_{proét,*} ν_{X''}^* F) = 0` for `r > 2d`.

Quantifying over the base changes is what turns the statement into the bound
`HasUniformCohomologicalDimensionLE` on the essential image of `ν^*`, which is the point of
the subsection; without it the theorem would not imply admissibility.

What remains open — and is why the ambient datum of `sk-def-sf-admissible` is an assumption —
is the vanishing for pro-étale module sheaves that are *not* of étale origin. -/
theorem isZero_homology_rightDerivedLowerStar_comparisonUpperStar (Λ : Type (u + 1))
    [CommRing Λ] [Finite Λ] {k : Type u} [Field k] [IsSepClosed k] {X' : Scheme.{u}}
    (p : X' ⟶ Y) [IsProper p] (aX' : X' ⟶ Spec (.of k)) (aY : Y ⟶ Spec (.of k))
    [LocallyOfFiniteType aX'] [LocallyOfFiniteType aY] (hp : p ≫ aY = aX')
    [HasInvertibleExponent Λ X'] (d : ℕ) (hd : topologicalKrullDim X' ≤ (d : WithBot ℕ∞))
    {X'' Y'' : Scheme.{u}} (g' : X'' ⟶ X') (p' : X'' ⟶ Y'') (g : Y'' ⟶ Y)
    (sq : IsPullback g' p' p g)
    (F : Sheaf X''.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (r : ℤ) (hr : (2 * d : ℤ) < r) :
    IsZero ((_root_.DerivedCategory.homologyFunctor _ r).obj
      ((R((p')_*[ModuleCat.{u + 1} Λ])).obj ((_root_.DerivedCategory.singleFunctor _ 0).obj
        ((comparisonUpperStar (ModuleCat.{u + 1} Λ) X'').obj F)))) :=
  sorry

end ProEtale

end AlgebraicGeometry
