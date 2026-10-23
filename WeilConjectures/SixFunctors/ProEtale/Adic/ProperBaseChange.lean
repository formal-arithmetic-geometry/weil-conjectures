/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.BaseChange
public import WeilConjectures.SixFunctors.ProEtale.Adic.Localization

/-!
# Proper base change for `ℓ`-adic sheaves

Let
```
X' --g'--> X
|          |
f'         f
v          v
Y' --g---> Y
```
be a commutative square of schemes. The *base change map* `D(g^*) ∘ Rf_* ⟶ Rf'_* ∘ D(g'^*)` on
the derived categories of sheaves of modules over the constant `ℓ`-adic sheaves
(`AlgebraicGeometry.ProEtale.adicDerivedBaseChangeMap`) is the mate, along the adjunctions
`D(g'^*) ⊣ Rg'_*` and `D(g^*) ⊣ Rg_*`, of the composition isomorphism
`Rf_* ∘ Rg'_* ≅ R(g' ≫ f)_* = R(f' ≫ g)_* ≅ Rg_* ∘ Rf'_*`.

The proper base change theorem (blueprint `thm-weil-pbc-qbar`) asserts that it is an isomorphism
on `Dᵇc(X, ℚ̄_ℓ)` when the square is cartesian and `f` is proper. As in
`WeilConjectures.SixFunctors.ProEtale.Adic.Localization`, the stage `Dᵇc(-, ℚ̄_ℓ)` is realised in
the Bhatt–Scholze model. The theorem belongs to the proper base change chapter
(`sec-proper-base-change`) and is stated here with `sorry`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.ProEtale

variable (l : ℕ) [Fact l.Prime]

variable {X X' Y Y' : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}

/-- The square isomorphism `Rg'_* ⋙ Rf_* ≅ Rf'_* ⋙ Rg_*` of derived pushforwards of `ℓ`-adic
sheaves attached to a commutative square `g' ≫ f = f' ≫ g`. -/
noncomputable def adicDerivedSquareLowerStarIso (sq : CommSq g' f' f g) :
    (g')_*ᵃ[l].rightDerivedFunctor ⋙ (f)_*ᵃ[l].rightDerivedFunctor ≅
      (f')_*ᵃ[l].rightDerivedFunctor ⋙ (g)_*ᵃ[l].rightDerivedFunctor :=
  have := (adicUpperStarLowerStarAdjunction l g').preservesKInjectiveComplexes
  have := (adicUpperStarLowerStarAdjunction l f').preservesKInjectiveComplexes
  Functor.rightDerivedFunctorCompIso' _ _ (adicLowerStarComp l g' f) ≪≫
    Functor.rightDerivedFunctorNatIso (adicLowerStarCongr l sq.w) ≪≫
    (Functor.rightDerivedFunctorCompIso' _ _ (adicLowerStarComp l f' g)).symm

/-- **The base change map** `D(g^*) ∘ Rf_* ⟶ Rf'_* ∘ D(g'^*)` of `ℓ`-adic sheaves for a
commutative square `g' ≫ f = f' ≫ g`: the mate of
`AlgebraicGeometry.ProEtale.adicDerivedSquareLowerStarIso` along `D(g'^*) ⊣ Rg'_*` and
`D(g^*) ⊣ Rg_*`. -/
noncomputable def adicDerivedBaseChangeMap (sq : CommSq g' f' f g) :
    (f)_*ᵃ[l].rightDerivedFunctor ⋙ (g)^*ᵃ[l].mapDerivedCategory ⟶
      (g')^*ᵃ[l].mapDerivedCategory ⋙ (f')_*ᵃ[l].rightDerivedFunctor :=
  ((mateEquiv (adicDerivedUpperStarLowerStarAdjunction l g')
    (adicDerivedUpperStarLowerStarAdjunction l g)).symm
    (TwoSquare.mk _ _ _ _ (adicDerivedSquareLowerStarIso l sq).hom)).natTrans

variable {l}

/-- Blueprint `thm-weil-pbc-qbar`: **proper base change on `Dᵇc(-, ℚ̄_ℓ)`**. For a cartesian
square
```
X' --g'--> X
|          |
f'         f
v          v
Y' --g---> Y
```
of schemes with `f` proper, `Y` quasi-compact and locally of finite type over a field `k` with
`ringChar k ≠ ℓ`, `Y'` locally of finite type over `k`, and `K ∈ Dᵇc(X, ℚ̄_ℓ)`, the base change
map `g^* Rf_* K ⟶ Rf'_* g'^* K` (`AlgebraicGeometry.ProEtale.adicDerivedBaseChangeMap`) is an
isomorphism. Here `Dᵇc(-, ℚ̄_ℓ)` is realised in the Bhatt–Scholze model (sheaves of modules over
the constant `ℓ`-adic sheaf) rather than as the `2`-colimit over finite extensions of `ℚ_ℓ`. -/
theorem isIso_adicDerivedBaseChangeMap_app_of_isProper {k : Type u} [Field k]
    (sY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType sY] [QuasiCompact sY]
    [LocallyOfFiniteType (g ≫ sY)] (hk : ringChar k ≠ l) (sq : IsPullback g' f' f g)
    [IsProper f] (K : DerivedCategory (AdicSheaf l X))
    (hK : DerivedCategory.boundedConstructibleAdic l X K) :
    IsIso ((adicDerivedBaseChangeMap l sq.toCommSq).app K) :=
  sorry

/-- **Proper base change, vanishing form.** In the situation of
`AlgebraicGeometry.ProEtale.isIso_adicDerivedBaseChangeMap_app_of_isProper`, if `g'^* K = 0`
then `g^* Rf_* K = 0`. -/
theorem isZero_adicUpperStar_rightDerivedLowerStar_of_isProper {k : Type u} [Field k]
    (sY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType sY] [QuasiCompact sY]
    [LocallyOfFiniteType (g ≫ sY)] (hk : ringChar k ≠ l) (sq : IsPullback g' f' f g)
    [IsProper f] (K : DerivedCategory (AdicSheaf l X))
    (hK : DerivedCategory.boundedConstructibleAdic l X K)
    (h : IsZero ((g')^*ᵃ[l].mapDerivedCategory.obj K)) :
    IsZero ((g)^*ᵃ[l].mapDerivedCategory.obj ((f)_*ᵃ[l].rightDerivedFunctor.obj K)) :=
  have := isIso_adicDerivedBaseChangeMap_app_of_isProper sY hk sq K hK
  ((f')_*ᵃ[l].rightDerivedFunctor.map_isZero h).of_iso
    (asIso ((adicDerivedBaseChangeMap l sq.toCommSq).app K))

end AlgebraicGeometry.ProEtale
