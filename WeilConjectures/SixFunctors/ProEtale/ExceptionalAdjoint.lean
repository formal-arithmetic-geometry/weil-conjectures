/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Comparison
public import WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriek

/-!
# The admissibility datum for the ambient exceptional right adjoint

The existence of the ambient exceptional right adjoint `Rf^×` on the *unbounded* derived
category of the small pro-étale site is not a theorem of this development: it is an explicit
hypothesis, recorded here as `AlgebraicGeometry.ProEtale.HasAmbientExceptionalAdjoint`. Its
two ingredients are a uniform cohomological-dimension bound `FullCD(p, A; c)` for the proper
part `p` of a compactification — which is what makes `Rp_*` preserve coproducts, hence Brown
representability applicable — and the requirement that the resulting right adjoint preserve
the small subcategories in which the purity statements live.

On the *étale-origin* class the bound is a theorem, with `c = 2 dim X̄`: it follows from the
finiteness of proper direct images in ordinary étale cohomology together with the pro-étale
comparison.

## Main definitions

- `AlgebraicGeometry.ProEtale.FullCD`: the uniform cohomological-dimension bound.
- `AlgebraicGeometry.ProEtale.HasAmbientExceptionalAdjoint`: the admissibility datum.

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

`FullCD(p, A; c)`: the higher direct images of `p`, and of all its base changes, vanish above
`c` on *every* pro-étale sheaf of `A`-modules. This is the uniform cohomological-dimension
bound that makes `Rp_*` preserve coproducts on the unbounded derived category. -/
def FullCD (p : X ⟶ Y) (c : ℕ) : Prop :=
  ∀ ⦃X' Y' : Scheme.{u}⦄ (g' : X' ⟶ X) (p' : X' ⟶ Y') (g : Y' ⟶ Y), IsPullback g' p' p g →
    ∀ (F : Sheaf (Scheme.ProEt.topology X') A) (r : ℤ), (c : ℤ) < r →
      IsZero ((_root_.DerivedCategory.homologyFunctor _ r).obj
        ((R((p')_*[A])).obj ((_root_.DerivedCategory.singleFunctor _ 0).obj F)))

/-- Blueprint `sk-def-sf-admissible`: Admissibility datum: an explicit hypothesis

A separated finite-type `f : X ⟶ Y` *carries the ambient exceptional right adjoint datum at
`A`* — relative to a family `P` of object properties standing for the constructible intervals
and the finite-Tor subcategory — when `FullCD(p, A; c)` holds for some `c` and the proper part
`p` of the chosen compactification of `f`, when `Rf_!` has a right adjoint on the unbounded
derived categories of the small pro-étale sites, and when that right adjoint preserves `P`.

This is an *assumption*, not a definition of a property: which morphisms satisfy it is a
theorem, namely the existence statement of
`AlgebraicGeometry.ProEtale.isLeftAdjoint_rightDerivedLowerShriek` together with the
preservation clauses. -/
class HasAmbientExceptionalAdjoint (f : X ⟶ Y) [HasCompactification f]
    (P : ∀ Z : Scheme.{u},
      ObjectProperty (_root_.DerivedCategory (Sheaf (Scheme.ProEt.topology Z) A))) : Prop where
  /-- A uniform cohomological-dimension bound for the proper part of the compactification. -/
  exists_fullCD : ∃ c : ℕ, FullCD A (HasCompactification.compactification f).g c
  /-- `Rf_!` has a right adjoint on the unbounded derived categories. -/
  isLeftAdjoint_rightDerivedLowerShriek : (R(f)_![A]).IsLeftAdjoint
  /-- The right adjoint preserves the small subcategories. -/
  upperShriek_mem : ∀ K, P Y K → P X ((R(f)^![A]).obj K)

/-- Blueprint `sk-prop-sf-fullcd-etale-origin`: `FullCD` on the étale-origin class

**The cohomological-dimension bound on the étale-origin class.** Let `k` be separably closed,
let `p : X̄ ⟶ Y` be a proper morphism of finite-type `k`-schemes of dimension at most `d`, and
let `A` be a finite coefficient stage. Then for every étale sheaf `F` of `A`-modules on `X̄`,

`H^r(Rp_{proét,*} ν_{X̄}^* F) = 0` for `r > 2d`,

and the same bound holds for every base change of `p`. Equivalently,
`FullCD(p, A; 2 dim X̄)` holds on the essential image of `ν_{X̄}^*`, which contains every
bounded constructible pro-étale complex.

What remains open — and is why the ambient datum of `sk-def-sf-admissible` is an assumption —
is the vanishing for pro-étale module sheaves that are *not* of étale origin. -/
theorem isZero_homology_rightDerivedLowerStar_comparisonUpperStar {X' : Scheme.{u}}
    (p : X' ⟶ Y) [IsProper p] (d : ℕ) (_hd : topologicalKrullDim X' ≤ (d : WithBot ℕ∞))
    (F : Sheaf X'.smallEtaleTopology A) (r : ℤ) (_hr : (2 * d : ℤ) < r) :
    IsZero ((_root_.DerivedCategory.homologyFunctor _ r).obj
      ((R((p)_*[A])).obj ((_root_.DerivedCategory.singleFunctor _ 0).obj
        ((comparisonUpperStar A X').obj F)))) :=
  sorry

end ProEtale

end AlgebraicGeometry
