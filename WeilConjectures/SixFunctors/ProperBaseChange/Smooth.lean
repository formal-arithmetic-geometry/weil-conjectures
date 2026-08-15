/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib
public import WeilConjectures.SixFunctors.ProperBaseChange.BaseChangeMorphism
public import WeilConjectures.DerivedCategory.Constructible

/-!

# The smooth base change theorem

Fix a finite commutative ring `Λ` together with a positive integer `n` with `n Λ = 0`,
and a cartesian square of schemes

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

`BC_sq(K) : Lg^*(Rf_* K) ⟶ Rf'_*(Lg'^* K)`

of `WeilConjectures.SixFunctors.ProperBaseChange.BaseChangeMorphism` is an isomorphism
for every bounded-below `K`; this is Stacks Project, Theorem 59.89.2 (for
bounded-below complexes whose cohomology sheaves are torsion with orders invertible on
`Y` — automatic here since `n Λ = 0` and `n` is invertible on `Y`). The headline
statement `Etale.smoothBaseChange` is the specialization to the bounded constructible
category `D^b_c(X_ét, Λ)`.

In contrast to proper base change, the invertibility hypothesis is essential, and the
statement is limited to bounded-below complexes: no unbounded version is stated, since a
general quasi-compact quasi-separated morphism does not have finite cohomological
dimension.

## Main statements

- `AlgebraicGeometry.Etale.smoothBaseChange`: smooth base change on `D^b_c`.
- `AlgebraicGeometry.Etale.smoothBaseChange_plus`: smooth base change for bounded-below
  complexes.
- `AlgebraicGeometry.Etale.smoothBaseChange_cohomological`: cohomological smooth base
  change.
- `AlgebraicGeometry.Etale.smoothBaseChange_sheaf`: classical smooth base change
  `g^* R^q f_* F ≅ R^q f'_* g'^* F` for a single sheaf `F`.

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
`WeilConjectures.SixFunctors.ProperBaseChange.BaseChangeMorphism`; the monoidal
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

/-- **Smooth base change**, bounded-below version: for a cartesian square with `g`
smooth and `f` quasi-compact and quasi-separated, a finite commutative ring `Λ` whose
torsion order `n > 0` (i.e. `n Λ = 0`) is invertible on the base `Y`, the derived
base-change morphism `Lg^*(Rf_* K) ⟶ Rf'_*(Lg'^* K)` is an isomorphism for every
bounded-below `K`. This is Stacks Project, Theorem 59.89.2: the cohomology sheaves of
`K` are torsion with orders dividing `n`, hence invertible on `Y`. -/
theorem Etale.smoothBaseChange_plus [Smooth g] [QuasiCompact f] [QuasiSeparated f]
    (sq : IsPullback g' f' f g) (n : ℕ) (hn : 0 < n) (hnΛ : (n : Λ) = 0)
    (hnY : IsUnit (n : Γ(Y, ⊤)))
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)))
    (hK : DerivedCategory.TStructure.t.plus K) :
    IsIso ((Etale.baseChange (ModuleCat.{u} Λ) sq.toCommSq).app K) :=
  sorry

/-- **Smooth base change** on the bounded constructible category: for a cartesian square
with `g` smooth and `f` quasi-compact and quasi-separated, a finite commutative ring `Λ`
whose torsion order `n > 0` is invertible on the base `Y`, and `K ∈ D^b_c(X_ét, Λ)`, the
derived base-change morphism `Lg^*(Rf_* K) ⟶ Rf'_*(Lg'^* K)` is an isomorphism. -/
theorem Etale.smoothBaseChange [Smooth g] [QuasiCompact f] [QuasiSeparated f]
    (sq : IsPullback g' f' f g) (n : ℕ) (hn : 0 < n) (hnΛ : (n : Λ) = 0)
    (hnY : IsUnit (n : Γ(Y, ⊤)))
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)))
    (hK : Etale.DerivedCategory.boundedConstructible (ModuleCat.{u} Λ) X K) :
    IsIso ((Etale.baseChange (ModuleCat.{u} Λ) sq.toCommSq).app K) :=
  Etale.smoothBaseChange_plus Λ sq n hn hnΛ hnY K hK.1.1

/-- **Cohomological smooth base change**: under the hypotheses of smooth base change,
the cohomological base-change morphism `g^* H^m(Rf_* K) ⟶ H^m(Rf'_* Lg'^* K)` is an
isomorphism for every `m` and every bounded-below `K`. -/
theorem Etale.smoothBaseChange_cohomological [Smooth g] [QuasiCompact f]
    [QuasiSeparated f] (sq : IsPullback g' f' f g) (n : ℕ) (hn : 0 < n)
    (hnΛ : (n : Λ) = 0) (hnY : IsUnit (n : Γ(Y, ⊤))) (m : ℤ)
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)))
    (hK : DerivedCategory.TStructure.t.plus K) :
    IsIso ((Etale.cohomologicalBaseChange (ModuleCat.{u} Λ) sq.toCommSq m).app K) := by
  haveI := Etale.smoothBaseChange_plus Λ sq n hn hnΛ hnY K hK
  simp only [Etale.cohomologicalBaseChange, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app]
  infer_instance

/-- **Classical smooth base change on sheaves**: under the hypotheses of smooth base
change, the base-change morphism `g^* R^m f_* F ⟶ R^m f'_* g'^* F` is an isomorphism
for every `m` and every sheaf `F` of `Λ`-modules. -/
theorem Etale.smoothBaseChange_sheaf [Smooth g] [QuasiCompact f] [QuasiSeparated f]
    (sq : IsPullback g' f' f g) (n : ℕ) (hn : 0 < n) (hnΛ : (n : Λ) = 0)
    (hnY : IsUnit (n : Γ(Y, ⊤))) (m : ℤ)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) :
    IsIso ((Etale.sheafBaseChange (ModuleCat.{u} Λ) sq.toCommSq m).app F) := by
  haveI := Etale.smoothBaseChange_cohomological Λ sq n hn hnΛ hnY m
    ((DerivedCategory.singleFunctor (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) 0).obj F)
    ⟨0, inferInstance⟩
  simp only [Etale.sheafBaseChange, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app]
  infer_instance

end AlgebraicGeometry
