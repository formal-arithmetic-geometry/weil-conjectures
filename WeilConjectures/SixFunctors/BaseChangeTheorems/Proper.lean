/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib
public import WeilConjectures.SixFunctors.BaseChangeTheorems.MorphismDefs
public import WeilConjectures.SixFunctors.BaseChangeTheorems.TorsionSheaf

/-!

# The proper base change theorem

Fix a commutative ring `Λ` and a cartesian square of schemes

```
X' --g'--> X
|          |
f'         f
v          v
Y' --g---> Y
```

with `f` **proper**, recorded as `sq : IsPullback g' f' f g`. This file states the
general proper base change theorem in étale cohomology: for every object `K` of the
bounded below derived category `D⁺(X_ét, Λ)` all of whose cohomology sheaves are torsion
(`AlgebraicGeometry.Etale.DerivedCategory.Plus.torsionHomology`), the derived
base-change morphism

`BC_sq(K) : Lg^*(Rf_* K) ⟶ Rf'_*(Lg'^* K)`

of `WeilConjectures.SixFunctors.BaseChangeTheorems.MorphismDefs` is an isomorphism. No
hypothesis is imposed on `g`.

Torsion refers to the underlying abelian groups, so the statement contains the two
classical forms of the theorem at once:

- for `Λ = ℤ` it is proper base change for bounded below complexes of abelian sheaves
  with torsion cohomology, as in [SGA 4, Exp. XII, Thm 5.1] and Stacks Project,
  Tag 0DDE;
- for `Λ` torsion as an additive group — in particular for the finite rings
  `Λ = ℤ/ℓⁿℤ` of the `ℓ`-adic formalism — every sheaf of `Λ`-modules is torsion, the
  hypothesis is vacuous, and the base-change transformation itself is an isomorphism of
  functors (`Etale.isIso_baseChange_of_isProper`). The passage between coefficient
  rings is by restriction of scalars, which is exact, conservative, and compatible with
  the base-change mates; see `reference.pdf` in this directory.

The sheaf-level special case `g^*(f_* F) ≅ Rf'_*(g'^* F)` for a single torsion sheaf
`F`, placed in degree `0`, is recorded as `Etale.properBaseChange_single`.

All statements are `Prop`-valued and their proofs are deferred (`sorry`); this file is
the statement layer of the theorem.

## Main statements

- `AlgebraicGeometry.Etale.properBaseChange`: the general proper base change theorem,
  for a bounded below complex with torsion cohomology.
- `AlgebraicGeometry.Etale.isIso_baseChange_of_isProper`: for a torsion coefficient
  ring, the base-change transformation of a proper cartesian square is an isomorphism
  of functors.
- `AlgebraicGeometry.Etale.properBaseChange_single`: proper base change for a single
  torsion sheaf placed in degree `0`.

## References

- Stacks Project, Section 59.91, *The proper base change theorem*,
  <https://stacks.math.columbia.edu/tag/095S>
- Stacks Project, Lemma 59.91.12, the derived statement,
  <https://stacks.math.columbia.edu/tag/0DDE>
- [SGA 4, Exp. XII, Théorème 5.1]

-/

@[expose] public section

universe w u

open CategoryTheory Limits MonoidalCategory Abelian

namespace AlgebraicGeometry

open Scheme

variable (Λ : Type u) [CommRing Λ]

/- Pointwise left Kan extensions and chosen localized derived categories for the small
étale sites of all schemes at once, with coefficients in the ring `Λ`, following the
convention of `WeilConjectures.SixFunctors.BaseChangeTheorems.MorphismDefs`;
sheafification for the small étale sites is provided by mathlib's `HasSheafify` instance
for the concrete category `ModuleCat Λ`. -/
variable [∀ (T S : Scheme.{u}) (φ : T ⟶ S) (F : S.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ),
    (MorphismProperty.Over.pullback @Etale ⊤ φ).op.HasLeftKanExtension F]
  [∀ (T : Scheme.{u}),
    HasDerivedCategory.{w} (Sheaf T.smallEtaleTopology (ModuleCat.{u} Λ))]

/- The K-flat resolution package on the coefficient category `ModuleCat Λ`, as in
`WeilConjectures.SixFunctors.BaseChangeTheorems.MorphismDefs`; the monoidal structure,
its preadditivity and the existence of colimits are provided by mathlib's instances for
`ModuleCat`. -/
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

/-- **The proper base change theorem** in étale cohomology: for a cartesian square of
schemes

```
X' --g'--> X
|          |
f'         f
v          v
Y' --g---> Y
```

with `f` proper and every bounded below complex `K ∈ D⁺(X_ét, Λ)` all of whose
cohomology sheaves are torsion, the derived base-change morphism

`BC_sq(K) : Lg^*(Rf_* K) ⟶ Rf'_*(Lg'^* K)`

is an isomorphism in `D⁺(Y'_ét, Λ)`. No hypothesis is imposed on `g`. For `Λ = ℤ` this
is [SGA 4, Exp. XII, Thm 5.1] and Stacks Project, Tag 0DDE; the case of a general
coefficient ring follows by restriction of scalars. -/
theorem Etale.properBaseChange [IsProper f] (sq : IsPullback g' f' f g)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)))
    (hK : Etale.DerivedCategory.Plus.torsionHomology Λ X K) :
    IsIso ((Etale.baseChange (ModuleCat.{u} Λ) sq.toCommSq).app K) :=
  sorry

/-- **Proper base change as an isomorphism of functors**: if the coefficient ring `Λ` is
torsion as an additive group — in particular if `Λ` is finite, e.g. `Λ = ℤ/ℓⁿℤ` — then
for a cartesian square with `f` proper the base-change transformation

`BC_sq : Rf_* ⋙ Lg^* ⟶ Lg'^* ⋙ Rf'_*`

on the bounded below derived categories is an isomorphism: every complex of sheaves of
`Λ`-modules automatically has torsion cohomology. -/
theorem Etale.isIso_baseChange_of_isProper (hΛ : AddMonoid.IsTorsion Λ) [IsProper f]
    (sq : IsPullback g' f' f g) :
    IsIso (Etale.baseChange (ModuleCat.{u} Λ) sq.toCommSq) :=
  have : ∀ K, IsIso ((Etale.baseChange (ModuleCat.{u} Λ) sq.toCommSq).app K) := fun K ↦
    Etale.properBaseChange Λ sq K
      (Etale.DerivedCategory.Plus.torsionHomology_of_isTorsion Λ X hΛ K)
  NatIso.isIso_of_isIso_app _

/-- **Proper base change for a single torsion sheaf**: for a cartesian square with `f`
proper and a torsion sheaf `F` of `Λ`-modules on `X_ét`, the base-change morphism
`Lg^*(Rf_* F) ⟶ Rf'_*(g'^* F)`, with `F` placed in degree `0`, is an isomorphism. This
is the classical form `g^* Rᵠf_* F ≅ Rᵠf'_* g'^* F` of the theorem [Stacks 095T], read
in the bounded below derived category. -/
theorem Etale.properBaseChange_single [IsProper f] (sq : IsPullback g' f' f g)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) [IsTorsionSheaf F] :
    IsIso ((Etale.baseChange (ModuleCat.{u} Λ) sq.toCommSq).app
      ((DerivedCategory.Plus.singleFunctor (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) 0).obj
        F)) :=
  Etale.properBaseChange Λ sq _ (by
    -- the cohomology of `F[0]` is `F` in degree `0` and zero otherwise, hence torsion
    sorry)

end AlgebraicGeometry
