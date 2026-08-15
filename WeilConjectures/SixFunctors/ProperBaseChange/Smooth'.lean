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

# The smooth base change theorem on bounded below derived categories

This file is the bounded below (`DerivedCategory.Plus`) counterpart of
`WeilConjectures.SixFunctors.ProperBaseChange.Smooth`. Fix a finite commutative ring
`Λ` together with a positive integer `n` with `n Λ = 0`, and a cartesian square of
schemes

```
X' --g'--> X
|          |
f'         f
v          v
Y' --g---> Y
```

recorded as `sq : IsPullback g' f' f g`. Smooth base change places the geometric
hypotheses as follows: the *base-changing* morphism `g` is smooth, the morphism `f`
whose direct image is being derived is quasi-compact and quasi-separated, and the
torsion order `n` is invertible on the base `Y`. Under these hypotheses the derived
base-change morphism

`BC'_sq(K) : Lg^*(Rf_* K) ⟶ Rf'_*(Lg'^* K)`

of `WeilConjectures.SixFunctors.ProperBaseChange.BaseChangeMorphism'` is an isomorphism
for every bounded below `K`; this is Stacks Project, Theorem 59.89.2, whose natural
habitat is precisely the bounded below derived category: in contrast to proper base
change, no unbounded statement is available, since a general quasi-compact
quasi-separated morphism does not have finite cohomological dimension. On the bounded
below derived category no boundedness hypothesis on `K` remains: it is carried by the
category itself, in contrast to the hypothesis `DerivedCategory.TStructure.t.plus K` of
the unbounded formulation `Etale.smoothBaseChange_plus`.

## Main statements

- `AlgebraicGeometry.Etale.smoothBaseChange'`: smooth base change for an arbitrary
  object of the bounded below derived category.
- `AlgebraicGeometry.Etale.smoothBaseChange'_constructible`: the specialization to
  bounded below objects whose image in the unbounded derived category is bounded
  constructible.
- `AlgebraicGeometry.Etale.smoothBaseChange'_cohomological`: cohomological smooth base
  change.
- `AlgebraicGeometry.Etale.smoothBaseChange'_sheaf`: classical smooth base change
  `g^* R^m f_* F ≅ R^m f'_* g'^* F` for a single sheaf `F`.

## References

- Stacks Project, Theorem 59.89.2, *Smooth base change*,
  <https://stacks.math.columbia.edu/tag/0EYU>

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

/-- **Smooth base change** on the bounded below derived categories: for a cartesian
square with `g` smooth and `f` quasi-compact and quasi-separated, a finite commutative
ring `Λ` whose torsion order `n > 0` (i.e. `n Λ = 0`) is invertible on the base `Y`,
the derived base-change morphism `Lg^*(Rf_* K) ⟶ Rf'_*(Lg'^* K)` is an isomorphism for
*every* bounded below `K`. This is Stacks Project, Theorem 59.89.2: the cohomology
sheaves of `K` are torsion with orders dividing `n`, hence invertible on `Y`. -/
theorem Etale.smoothBaseChange' [Smooth g] [QuasiCompact f] [QuasiSeparated f]
    (sq : IsPullback g' f' f g) (n : ℕ) (hn : 0 < n) (hnΛ : (n : Λ) = 0)
    (hnY : IsUnit (n : Γ(Y, ⊤)))
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ))) :
    IsIso ((Etale.baseChange' (ModuleCat.{u} Λ) sq.toCommSq).app K) :=
  sorry

/-- **Smooth base change** for bounded constructible objects: the specialization of
`Etale.smoothBaseChange'` to a bounded below `K` whose image in the unbounded derived
category is bounded constructible, `ι K ∈ D^b_c(X_ét, Λ)`. -/
theorem Etale.smoothBaseChange'_constructible [Smooth g] [QuasiCompact f]
    [QuasiSeparated f] (sq : IsPullback g' f' f g) (n : ℕ) (hn : 0 < n)
    (hnΛ : (n : Λ) = 0) (hnY : IsUnit (n : Γ(Y, ⊤)))
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)))
    (_hK : Etale.DerivedCategory.boundedConstructible (ModuleCat.{u} Λ) X
      (DerivedCategory.Plus.ι.obj K)) :
    IsIso ((Etale.baseChange' (ModuleCat.{u} Λ) sq.toCommSq).app K) :=
  Etale.smoothBaseChange' Λ sq n hn hnΛ hnY K

/-- **Cohomological smooth base change** on the bounded below derived categories: under
the hypotheses of smooth base change, the cohomological base-change morphism
`g^* H^m(Rf_* K) ⟶ H^m(Rf'_* Lg'^* K)` is an isomorphism for every `m` and every
bounded below `K`. -/
theorem Etale.smoothBaseChange'_cohomological [Smooth g] [QuasiCompact f]
    [QuasiSeparated f] (sq : IsPullback g' f' f g) (n : ℕ) (hn : 0 < n)
    (hnΛ : (n : Λ) = 0) (hnY : IsUnit (n : Γ(Y, ⊤))) (m : ℤ)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ))) :
    IsIso ((Etale.cohomologicalBaseChange' (ModuleCat.{u} Λ) sq.toCommSq m).app K) := by
  haveI := Etale.smoothBaseChange' Λ sq n hn hnΛ hnY K
  simp only [Etale.cohomologicalBaseChange', NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app]
  infer_instance

/-- **Classical smooth base change on sheaves**, computed on the bounded below derived
categories: under the hypotheses of smooth base change, the base-change morphism
`g^* R^m f_* F ⟶ R^m f'_* g'^* F` is an isomorphism for every `m` and every sheaf `F`
of `Λ`-modules. -/
theorem Etale.smoothBaseChange'_sheaf [Smooth g] [QuasiCompact f] [QuasiSeparated f]
    (sq : IsPullback g' f' f g) (n : ℕ) (hn : 0 < n) (hnΛ : (n : Λ) = 0)
    (hnY : IsUnit (n : Γ(Y, ⊤))) (m : ℤ)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) :
    IsIso ((Etale.sheafBaseChange' (ModuleCat.{u} Λ) sq.toCommSq m).app F) := by
  haveI := Etale.smoothBaseChange'_cohomological Λ sq n hn hnΛ hnY m
    ((DerivedCategory.Plus.singleFunctor
      (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) 0).obj F)
  simp only [Etale.sheafBaseChange', NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app]
  infer_instance

end AlgebraicGeometry
