/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib
public import WeilConjectures.SixFunctors.ProperBaseChange.«BaseChangeMorphism'»
public import WeilConjectures.DerivedCategory.Constructible

/-!

# The proper base change theorem on bounded below derived categories

This file is the bounded below (`DerivedCategory.Plus`) counterpart of
`WeilConjectures.SixFunctors.ProperBaseChange.Proper`. Fix a finite commutative ring
`Λ` and a cartesian square of schemes

```
X' --g'--> X
|          |
f'         f
v          v
Y' --g---> Y
```

with `f` **proper**, recorded as `sq : IsPullback g' f' f g`. This file states the
proper base change theorem in étale cohomology on the bounded below derived categories:
the derived base-change morphism

`BC'_sq(K) : Lg^*(Rf_* K) ⟶ Rf'_*(Lg'^* K)`

of `WeilConjectures.SixFunctors.ProperBaseChange.BaseChangeMorphism'` is an isomorphism
for *every* bounded below `K`. No hypothesis is imposed on `g`, and no invertibility
hypothesis on the torsion order of `Λ` is required: the finiteness of `Λ` guarantees
that all étale sheaves of `Λ`-modules are torsion. This is Stacks Project,
Theorem 59.91.11, whose natural habitat is precisely the bounded below derived
category of torsion sheaves.

The cohomological consequences are recorded as well: for every `q`, the maps
`g^* H^q(Rf_* K) ⟶ H^q(Rf'_* Lg'^* K)` and, for a single sheaf `F`,
`g^* R^q f_* F ⟶ R^q f'_* g'^* F` are isomorphisms.

## Main statements

- `AlgebraicGeometry.Etale.properBaseChange'`: proper base change for an arbitrary
  object of the bounded below derived category (finite coefficients).
- `AlgebraicGeometry.Etale.properBaseChange'_constructible`: the specialization to
  bounded below objects whose image in the unbounded derived category is bounded
  constructible.
- `AlgebraicGeometry.Etale.isIso_baseChange'_of_isProper`: the base-change
  transformation is an isomorphism of functors.
- `AlgebraicGeometry.Etale.properBaseChange'_cohomological`: cohomological proper base
  change.
- `AlgebraicGeometry.Etale.properBaseChange'_sheaf`: classical proper base change
  `g^* R^q f_* F ≅ R^q f'_* g'^* F` for a single sheaf `F`.

## References

- Stacks Project, Section 59.91, *The proper base change theorem*,
  <https://stacks.math.columbia.edu/tag/095S>

-/

@[expose] public section

universe w u

open CategoryTheory Limits MonoidalCategory Abelian

namespace AlgebraicGeometry

open Scheme

variable (Λ : Type u) [CommRing Λ] [Finite Λ]

/- Sheafification (also on the localized sites, as needed for constructibility),
pointwise left Kan extensions and chosen localized derived categories for the small étale
sites of all schemes, with coefficients in the finite ring `Λ`. -/
variable [∀ (T : Scheme.{u}), HasWeakSheafify T.smallEtaleTopology (ModuleCat.{u} Λ)]
  [∀ (T : Scheme.{u}) (U : T.Etale),
    HasWeakSheafify (T.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
  [∀ (T S : Scheme.{u}) (φ : T ⟶ S) (F : S.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ),
    (MorphismProperty.Over.pullback @Etale ⊤ φ).op.HasLeftKanExtension F]
  [∀ (T : Scheme.{u}),
    HasDerivedCategory.{w} (Sheaf T.smallEtaleTopology (ModuleCat.{u} Λ))]

/- The K-flat resolution package on the coefficient category `ModuleCat Λ`, as in
`WeilConjectures.SixFunctors.ProperBaseChange.BaseChangeMorphism'`; the monoidal
structure, its preadditivity and the existence of colimits are provided by mathlib's
instances for `ModuleCat`. -/
variable [∀ (X : ModuleCat.{u} Λ), PreservesFilteredColimitsOfSize.{u, u} (tensorLeft X)]
  [∀ (X : ModuleCat.{u} Λ), PreservesFilteredColimitsOfSize.{u, u} (tensorRight X)]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ (ModuleCat.{u} Λ)),
    GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ (ModuleCat.{u} Λ)),
    GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ (ModuleCat.{u} Λ)),
    GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [HasExactColimitsOfShape ℤ (ModuleCat.{u} Λ)]
  [∀ (X : ModuleCat.{u} Λ),
    PreservesColimitsOfShape ℤ ((curriedTensor (ModuleCat.{u} Λ)).obj X)]
  [∀ (X : ModuleCat.{u} Λ),
    PreservesColimitsOfShape ℤ ((curriedTensor (ModuleCat.{u} Λ)).flip.obj X)]
  [Abelian.HasFunctorialFlatResolution (ModuleCat.{u} Λ)]

variable {X Y X' Y' : Scheme.{u}}
  {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}

/-- **Proper base change** on the bounded below derived categories: for a cartesian
square with `f` proper and coefficients in a finite commutative ring `Λ`, the derived
base-change morphism `Lg^*(Rf_* K) ⟶ Rf'_*(Lg'^* K)` is an isomorphism for *every*
object `K` of the bounded below derived category of étale sheaves of `Λ`-modules. For
`Λ = ℤ/nℤ` this is Stacks Project, Theorem 59.91.11 (every object of the bounded below
derived category is a bounded-below complex of torsion sheaves since `Λ` is finite);
the general finite case follows by restriction of scalars. No hypothesis on `g` and no
invertibility hypothesis on the torsion order are required. -/
theorem Etale.properBaseChange' [IsProper f] (sq : IsPullback g' f' f g)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ))) :
    IsIso ((Etale.baseChange' (ModuleCat.{u} Λ) sq.toCommSq).app K) :=
  sorry

/-- **Proper base change** for bounded constructible objects: the specialization of
`Etale.properBaseChange'` to a bounded below `K` whose image in the unbounded derived
category is bounded constructible, `ι K ∈ D^b_c(X_ét, Λ)`. -/
theorem Etale.properBaseChange'_constructible [IsProper f] (sq : IsPullback g' f' f g)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)))
    (_hK : Etale.DerivedCategory.boundedConstructible (ModuleCat.{u} Λ) X
      (DerivedCategory.Plus.ι.obj K)) :
    IsIso ((Etale.baseChange' (ModuleCat.{u} Λ) sq.toCommSq).app K) :=
  Etale.properBaseChange' Λ sq K

/-- The base-change transformation `Lg^* ∘ Rf_* ⟶ Rf'_* ∘ Lg'^*` of a cartesian square
with `f` proper is an isomorphism of functors on the bounded below derived categories
(finite coefficients). -/
theorem Etale.isIso_baseChange'_of_isProper [IsProper f] (sq : IsPullback g' f' f g) :
    IsIso (Etale.baseChange' (ModuleCat.{u} Λ) sq.toCommSq) :=
  haveI : ∀ K, IsIso ((Etale.baseChange' (ModuleCat.{u} Λ) sq.toCommSq).app K) :=
    fun K => Etale.properBaseChange' Λ sq K
  NatIso.isIso_of_isIso_app _

/-- **Cohomological proper base change** on the bounded below derived categories: for a
cartesian square with `f` proper and finite coefficients, the cohomological base-change
morphism `g^* H^n(Rf_* K) ⟶ H^n(Rf'_* Lg'^* K)` is an isomorphism for every `n` and
every bounded below `K`. -/
theorem Etale.properBaseChange'_cohomological [IsProper f] (sq : IsPullback g' f' f g)
    (n : ℤ) (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ))) :
    IsIso ((Etale.cohomologicalBaseChange' (ModuleCat.{u} Λ) sq.toCommSq n).app K) := by
  haveI := Etale.properBaseChange' Λ sq K
  simp only [Etale.cohomologicalBaseChange', NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app]
  infer_instance

/-- **Classical proper base change on sheaves**, computed on the bounded below derived
categories: for a cartesian square with `f` proper and finite coefficients, the
base-change morphism `g^* R^n f_* F ⟶ R^n f'_* g'^* F` is an isomorphism for every `n`
and every sheaf `F` of `Λ`-modules (all such sheaves are torsion since `Λ` is
finite). -/
theorem Etale.properBaseChange'_sheaf [IsProper f] (sq : IsPullback g' f' f g)
    (n : ℤ) (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) :
    IsIso ((Etale.sheafBaseChange' (ModuleCat.{u} Λ) sq.toCommSq n).app F) := by
  haveI := Etale.properBaseChange'_cohomological Λ sq n
    ((DerivedCategory.Plus.singleFunctor
      (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) 0).obj F)
  simp only [Etale.sheafBaseChange', NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app]
  infer_instance

end AlgebraicGeometry
