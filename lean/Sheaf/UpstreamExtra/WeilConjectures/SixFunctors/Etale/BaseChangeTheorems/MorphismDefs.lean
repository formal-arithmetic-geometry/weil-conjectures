module

public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.MorphismDefs
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MapDerivedCategory
public import WeilConjectures.Mathlib.CategoryTheory.Functor.SquareTransport

/-!
Declarations of ours that lived in the upstream file
`WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.MorphismDefs`
(moved out by the scheduled sync, tools/upstream_verbatim.py, 2026-10-20:
upstream files are verbatim in live).
-/

/-!

# The derived base-change morphism on bounded below derived categories

This file constructs the derived base-change morphism on the bounded below derived
categories (`DerivedCategory.Plus`). Fix a commutative square of schemes

```
X' --g'--> X
|          |
f'         f
v          v
Y' --g---> Y
```

recorded as `sq : CommSq g' f' f g`.
This file constructs the *derived base-change morphism*

`BC_sq : Rf_* ⋙ Lg^* ⟶ Lg'^* ⋙ Rf'_*` (in diagrammatic `⋙`-order)

on the bounded below derived categories, as the composite of three named
transformations: unit insertion, square transport along the pullback comparison
`θ_sq : Lf'^* ∘ Lg^* ≅ Lg'^* ∘ Lf^*`, and counit contraction.

The square transport is an instance of the purely categorical construction
`CategoryTheory.Functor.squareTransport`: a natural isomorphism `θ : G₁ ⋙ G₂ ≅ G₃ ⋙ G₄`
is transported under `R` on the left and `R'` on the right (with the reassociations) to
`(R ⋙ G₁) ⋙ (G₂ ⋙ R') ≅ (R ⋙ G₃) ⋙ (G₄ ⋙ R')`, whose component at `K` is
`R'.mapIso (θ.app (R.obj K))`.

## Main definitions

- `CategoryTheory.Functor.squareTransport` (in
  `WeilConjectures.Mathlib.CategoryTheory.Functor.SquareTransport`): transport of a natural
  isomorphism under an outer functor on each side, with its component lemmas.
- `AlgebraicGeometry.Etale.pullbackSquareComparison`: the pullback comparison `θ_sq`
  of a commutative square on the bounded below derived categories.
- `AlgebraicGeometry.Etale.baseChangeUnitStep`, `Etale.baseChangeSquareStep`,
  `Etale.baseChangeCounitStep`: the three steps of the construction.
- `AlgebraicGeometry.Etale.baseChange`: the derived base-change morphism `BC_sq`.

## Implementation notes (@Edison Xie)

The component lemmas of `Etale.baseChangeSquareStep` are obtained from the component lemmas
of `Functor.squareTransport`, which are stated for arbitrary functors. A direct `simp` proof
on the unfolded concrete transformation elaborates quickly but produces a proof term whose
kernel check does not terminate in practice, because the kernel normalises the composite
transformation through the concrete derived functors `rightDerivedFunctorPlus` and
`mapDerivedCategoryPlus` into the localised category.

The isomorphism-level lemma `Etale.baseChangeSquareStep_app` is proved by `simp`: its
left-hand side is headed by the ordinary definition `Iso.app`, for which the kernel compares
arguments first, so nothing is unfolded. The morphism-level lemmas
`Etale.baseChangeSquareStep_hom_app` and `Etale.baseChangeSquareStep_inv_app` are instead
derived from it by `congrArg`. Instantiating `Functor.squareTransport_hom_app` at the
concrete functors directly (by `simp`, `rw` or `exact`) produces a syntactically matching
equation, but its kernel check was observed not to terminate: its left-hand side is headed by
the projection functions `NatTrans.app` and `Iso.hom`, which the kernel reduces by fully
normalising the underlying structure `squareTransport …` rather than by comparing
arguments.

-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory MonoidalClosed Abelian

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme Etale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

section PullbackComposition

variable {X Y X' Y' : Scheme.{u}}
  {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}

/-- Equation for the pullback square behind its cached interface. -/
lemma Etale.pullbackSquareComparison_def (sq : CommSq g' f' f g) :
    Etale.pullbackSquareComparison A sq =
      (Etale.upperStarPlusComp A f' g).symm ≪≫
        eqToIso (by rw [← sq.w]) ≪≫ Etale.upperStarPlusComp A g' f := by
  unfold Etale.pullbackSquareComparison
  rfl

end PullbackComposition

end AlgebraicGeometry
