/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib
public import WeilConjectures.SixFunctors.ProperBaseChange.BaseChangeMorphism
public import WeilConjectures.SixFunctors.DerivedFunctors.CategoryConstruction

/-!

# The proper base change theorem

Fix a finite commutative ring `Λ` and a cartesian square of schemes

```
X' --g'--> X
|          |
f'         f
v          v
Y' --g---> Y
```

with `f` **proper**, recorded as `sq : IsPullback g' f' f g`. This file states the proper
base change theorem in étale cohomology: the derived base-change morphism

`BC_sq(K) : Lg^*(Rf_* K) ⟶ Rf'_*(Lg'^* K)`

of `WeilConjectures.SixFunctors.ProperBaseChange.BaseChangeMorphism` is an isomorphism.
No hypothesis is imposed on `g`, and no invertibility hypothesis on the torsion order of
`Λ` is required: the finiteness of `Λ` guarantees that all étale sheaves of `Λ`-modules
are torsion.

The headline statement `Etale.properBaseChange` is the theorem on the bounded
constructible category `D^b_c(X_ét, Λ)`, as in Stacks Project, Theorem 59.91.11 (the
theorem there applies to any bounded-below complex of torsion sheaves; every object of
`D^b_c` qualifies since `Λ` is finite). It is deduced from the unbounded finite-level
statement `Etale.properBaseChange_unbounded` (Stacks Project, Lemma 0F0C for
`Λ = ℤ/nℤ`; the case of a general finite ring `Λ` follows by restriction of scalars
along `ℤ/nℤ → Λ` for `n` the additive exponent of `Λ`, since restriction of scalars is
exact, conservative, and commutes with `g^*` and `Rf_*`).

The cohomological consequences are recorded as well: for every `q`, the maps
`g^* H^q(Rf_* K) ⟶ H^q(Rf'_* Lg'^* K)` and, for a single sheaf `F`,
`g^* R^q f_* F ⟶ R^q f'_* g'^* F` are isomorphisms.

## Main statements

- `AlgebraicGeometry.Etale.properBaseChange`: proper base change on `D^b_c`.
- `AlgebraicGeometry.Etale.properBaseChange_unbounded`: proper base change for an
  arbitrary object of the unbounded derived category (finite coefficients).
- `AlgebraicGeometry.Etale.isIso_baseChange_of_isProper`: the base-change transformation
  is an isomorphism of functors.
- `AlgebraicGeometry.Etale.properBaseChange_cohomological`: cohomological proper base
  change.
- `AlgebraicGeometry.Etale.properBaseChange_sheaf`: classical proper base change
  `g^* R^q f_* F ≅ R^q f'_* g'^* F` for a single sheaf `F`.

## References

- Stacks Project, Section 59.91, *The proper base change theorem*,
  <https://stacks.math.columbia.edu/tag/095S>
- Stacks Project, Lemma 59.92.3, unbounded proper base change,
  <https://stacks.math.columbia.edu/tag/0F0C>

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

/- The K-flat resolution package on the étale sheaf categories with `Λ`-module
coefficients, as in `WeilConjectures.SixFunctors.ProperBaseChange.BaseChangeMorphism`. -/
variable [∀ (T : Scheme.{u}), MonoidalCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u} Λ))]
  [∀ (T : Scheme.{u}), MonoidalPreadditive (Sheaf T.smallEtaleTopology (ModuleCat.{u} Λ))]
  [∀ (T : Scheme.{u}) (j : ℤ), HasColimitsOfShape
    (Discrete ((ComplexShape.up ℤ).π (ComplexShape.up ℤ) (ComplexShape.up ℤ) ⁻¹' {j}))
    (Sheaf T.smallEtaleTopology (ModuleCat.{u} Λ))]
  [∀ (T : Scheme.{u}) (X₁ X₂ X₃ X₄ :
      GradedObject ℤ (Sheaf T.smallEtaleTopology (ModuleCat.{u} Λ))),
    GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (T : Scheme.{u}) (X₁ X₂ X₃ :
      GradedObject ℤ (Sheaf T.smallEtaleTopology (ModuleCat.{u} Λ))),
    GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (T : Scheme.{u}) (X₁ X₂ X₃ :
      GradedObject ℤ (Sheaf T.smallEtaleTopology (ModuleCat.{u} Λ))),
    GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [∀ (T : Scheme.{u}), HasColimitsOfShape ℤ (Sheaf T.smallEtaleTopology (ModuleCat.{u} Λ))]
  [∀ (T : Scheme.{u}),
    HasExactColimitsOfShape ℤ (Sheaf T.smallEtaleTopology (ModuleCat.{u} Λ))]
  [∀ (T : Scheme.{u}) (F : Sheaf T.smallEtaleTopology (ModuleCat.{u} Λ)),
    PreservesColimitsOfShape ℤ
      ((curriedTensor (Sheaf T.smallEtaleTopology (ModuleCat.{u} Λ))).obj F)]
  [∀ (T : Scheme.{u}) (F : Sheaf T.smallEtaleTopology (ModuleCat.{u} Λ)),
    PreservesColimitsOfShape ℤ
      ((curriedTensor (Sheaf T.smallEtaleTopology (ModuleCat.{u} Λ))).flip.obj F)]
  [∀ (T : Scheme.{u}),
    Abelian.HasFunctorialFlatResolution (Sheaf T.smallEtaleTopology (ModuleCat.{u} Λ))]

variable {X Y X' Y' : Scheme.{u}}
  {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}

/-- **Proper base change**, unbounded finite-coefficient version: for a cartesian square
with `f` proper and coefficients in a finite commutative ring `Λ`, the derived
base-change morphism `Lg^*(Rf_* K) ⟶ Rf'_*(Lg'^* K)` is an isomorphism for *every*
object `K` of the unbounded derived category of étale sheaves of `Λ`-modules. For
`Λ = ℤ/nℤ` this is Stacks Project, Lemma 0F0C; the general finite case follows by
restriction of scalars. No hypothesis on `g` and no invertibility hypothesis on the
torsion order are required. -/
theorem Etale.properBaseChange_unbounded [IsProper f] (sq : IsPullback g' f' f g)
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ))) :
    IsIso ((Etale.baseChange (ModuleCat.{u} Λ) sq.toCommSq).app K) :=
  sorry

/-- **Proper base change** on the bounded constructible category: for a cartesian square
with `f` proper, a finite commutative ring `Λ`, and `K ∈ D^b_c(X_ét, Λ)`, the derived
base-change morphism `Lg^*(Rf_* K) ⟶ Rf'_*(Lg'^* K)` is an isomorphism. This is the
specialization of Stacks Project, Theorem 59.91.11 (proper base change for bounded-below
complexes of torsion sheaves): every object of `D^b_c` is bounded and all its cohomology
sheaves are torsion because `Λ` is finite. -/
theorem Etale.properBaseChange [IsProper f] (sq : IsPullback g' f' f g)
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)))
    (_hK : Etale.boundedConstructible (ModuleCat.{u} Λ) X K) :
    IsIso ((Etale.baseChange (ModuleCat.{u} Λ) sq.toCommSq).app K) :=
  Etale.properBaseChange_unbounded Λ sq K

/-- The base-change transformation `Lg^* ∘ Rf_* ⟶ Rf'_* ∘ Lg'^*` of a cartesian square
with `f` proper is an isomorphism of functors (finite coefficients). -/
theorem Etale.isIso_baseChange_of_isProper [IsProper f] (sq : IsPullback g' f' f g) :
    IsIso (Etale.baseChange (ModuleCat.{u} Λ) sq.toCommSq) :=
  haveI : ∀ K, IsIso ((Etale.baseChange (ModuleCat.{u} Λ) sq.toCommSq).app K) :=
    fun K => Etale.properBaseChange_unbounded Λ sq K
  NatIso.isIso_of_isIso_app _

/-- **Cohomological proper base change**: for a cartesian square with `f` proper and
finite coefficients, the cohomological base-change morphism
`g^* H^n(Rf_* K) ⟶ H^n(Rf'_* Lg'^* K)` is an isomorphism for every `n` and every `K`. -/
theorem Etale.properBaseChange_cohomological [IsProper f] (sq : IsPullback g' f' f g)
    (n : ℤ) (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ))) :
    IsIso ((Etale.cohomologicalBaseChange (ModuleCat.{u} Λ) sq.toCommSq n).app K) := by
  haveI := Etale.properBaseChange_unbounded Λ sq K
  simp only [Etale.cohomologicalBaseChange, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app]
  infer_instance

/-- **Classical proper base change on sheaves**: for a cartesian square with `f` proper
and finite coefficients, the base-change morphism `g^* R^n f_* F ⟶ R^n f'_* g'^* F` is
an isomorphism for every `n` and every sheaf `F` of `Λ`-modules (all such sheaves are
torsion since `Λ` is finite). -/
theorem Etale.properBaseChange_sheaf [IsProper f] (sq : IsPullback g' f' f g)
    (n : ℤ) (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) :
    IsIso ((Etale.sheafBaseChange (ModuleCat.{u} Λ) sq.toCommSq n).app F) := by
  haveI := Etale.properBaseChange_cohomological Λ sq n
    ((DerivedCategory.singleFunctor (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) 0).obj F)
  simp only [Etale.sheafBaseChange, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app]
  infer_instance

end AlgebraicGeometry
