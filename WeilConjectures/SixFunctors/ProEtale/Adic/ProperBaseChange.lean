/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.BaseChangeMate
public import WeilConjectures.SixFunctors.ProEtale.Adic.ClosedSupport
public import WeilConjectures.SixFunctors.ProEtale.Adic.ExtensionByZero

/-!
# Proper base change for `ℓ`-adic sheaves

For a commutative square of schemes
```
X' --g'--> X
|          |
f'         f
v          v
Y' --g---> Y
```
the *derived base change morphism* `Rf_* ⋙ D(g^*) ⟶ D(g'^*) ⋙ Rf'_*` of sheaves of modules over the
constant `ℓ`-adic sheaves (`AlgebraicGeometry.ProEtale.adicDerivedBaseChange`) is the mate of the
isomorphism `D(g^*) ⋙ D(f'^*) ≅ D(f^*) ⋙ D(g'^*)` of pullbacks under the derived adjunctions
`D(f^*) ⊣ Rf_*` and `D(f'^*) ⊣ Rf'_*` (`CategoryTheory.Adjunction.derivedBaseChange`).

The proper base change theorem with `ℚ̄_ℓ`-coefficients (blueprint `thm-weil-pbc-qbar`) asserts
that it is an isomorphism on `Dᵇc(X, ℚ̄_ℓ)` for a cartesian square with `f` proper
(`AlgebraicGeometry.ProEtale.isIso_adicDerivedBaseChange_app_of_isProper`). Here `Dᵇc(-, ℚ̄_ℓ)` is
realised in the Bhatt–Scholze model (`ProEtale.DerivedCategory.boundedConstructibleAdic`), for
schemes of finite type over an algebraically closed field of characteristic different from `ℓ`.
The theorem belongs to the proper base change chapter, whose `ℓ`-adic part is not formalised:
it is recorded here without proof.

As a consequence, the direct image `Rb_*(l_! N)` of an extension by zero along a proper `b` vanishes
on every closed subscheme missing the image of `l`
(`AlgebraicGeometry.ProEtale.isZero_adicUpperStar_rightDerivedLowerStar_openImmersionLowerShriek`):
this is the input for the interchange of proper direct images and extensions by zero.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.ProEtale

variable (l : ℕ) [Fact l.Prime]

section BaseChange

variable {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}

/-- The derived base change morphism `Rf_* ⋙ D(g^*) ⟶ D(g'^*) ⋙ Rf'_*` of sheaves of modules over
the constant `ℓ`-adic sheaves attached to a commutative square `g' ≫ f = f' ≫ g`: the mate of the
isomorphism of pullbacks `D(g^*) ⋙ D(f'^*) ≅ D(f^*) ⋙ D(g'^*)` under `D(f^*) ⊣ Rf_*` and
`D(f'^*) ⊣ Rf'_*`. -/
noncomputable def adicDerivedBaseChange (sq : CommSq g' f' f g) :
    TwoSquare (adicLowerStar l f).rightDerivedFunctor (adicUpperStar l g').mapDerivedCategory
      (adicUpperStar l g).mapDerivedCategory (adicLowerStar l f').rightDerivedFunctor :=
  Adjunction.derivedBaseChange (adicUpperStarLowerStarAdjunction l f)
    (adicUpperStarLowerStarAdjunction l f') (adicUpperStarCompIso l sq.w.symm)

/-- Blueprint `thm-weil-pbc-qbar`: `ℚ̄_ℓ` proper base change.

Let `k` be an algebraically closed field with `ringChar k ≠ ℓ` and let
```
X' --g'--> X
|          |
f'         f
v          v
Y' --g---> Y
```
be a cartesian square of schemes quasi-compact and locally of finite type over `k`, with `f`
proper. For `K ∈ Dᵇc(X, ℚ̄_ℓ)` the base change morphism `g^* Rf_* K ⟶ Rf'_* g'^* K`
(`AlgebraicGeometry.ProEtale.adicDerivedBaseChange`) is an isomorphism. Here `Dᵇc(-, ℚ̄_ℓ)` is
realised by bounded complexes of sheaves of modules over the constant `ℓ`-adic sheaf with
constructible cohomology sheaves (Bhatt–Scholze), rather than as the common-stage category of the
finite coefficient fields `E ⊆ ℚ̄_ℓ` of the blueprint; the base change morphism is the mate of the
identification of pullbacks, which is the classical exchange morphism. The theorem belongs to the
proper base change chapter and is not formalised there yet. -/
theorem isIso_adicDerivedBaseChange_app_of_isProper {k : Type u} [Field k] [IsAlgClosed k]
    (hk : ringChar k ≠ l) (sY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType sY] [QuasiCompact sY]
    (sY' : Y' ⟶ Spec (.of k)) [LocallyOfFiniteType sY'] [QuasiCompact sY'] (hg : g ≫ sY = sY')
    (sq : IsPullback g' f' f g) [IsProper f] (K : DerivedCategory (AdicSheaf l X))
    (hK : DerivedCategory.boundedConstructibleAdic l X K) :
    IsIso ((adicDerivedBaseChange l sq.toCommSq).natTrans.app K) :=
  sorry

end BaseChange

section Vanishing

variable {U' Z' U Z C : Scheme.{u}} {t : U' ⟶ U} {l' : U' ⟶ Z'} {r : U ⟶ Z} {b : Z' ⟶ Z}

/-- **The direct image of an extension by zero vanishes away from the open.** Let
`t ≫ r = l' ≫ b` be a commutative square of schemes with `l'` a quasi-compact open immersion and
`b` proper, and let `i : C ⟶ Z` be a morphism whose image misses that of `r`, with `Z` and `C`
quasi-compact and locally of finite type over an algebraically closed field `k`,
`ringChar k ≠ ℓ`. Then `i^* Rb_* (l'_! N) = 0` for `N ∈ Dᵇc(U', ℚ̄_ℓ)`: by proper base change
(blueprint `thm-weil-pbc-qbar`) it is computed by the pullback of `l'_! N` to `Z' ×_Z C`, which
misses the image of `l'`. -/
lemma isZero_adicUpperStar_rightDerivedLowerStar_openImmersionLowerShriek
    [IsOpenImmersion l'] [QuasiCompact l'] [IsProper b] (w : t ≫ r = l' ≫ b) (i : C ⟶ Z)
    (hi : Disjoint (Set.range i.base) (Set.range r.base)) {k : Type u} [Field k] [IsAlgClosed k]
    (hk : ringChar k ≠ l) (sZ : Z ⟶ Spec (.of k)) [LocallyOfFiniteType sZ] [QuasiCompact sZ]
    (sC : C ⟶ Spec (.of k)) [LocallyOfFiniteType sC] [QuasiCompact sC] (hC : i ≫ sZ = sC)
    (N : DerivedCategory (AdicSheaf l U'))
    (hN : DerivedCategory.boundedConstructibleAdic l U' N) :
    IsZero ((adicUpperStar l i).mapDerivedCategory.obj ((adicLowerStar l b).rightDerivedFunctor.obj
      ((adicOpenImmersionLowerShriek l l').mapDerivedCategory.obj N))) := by
  sorry

end Vanishing

end AlgebraicGeometry.ProEtale
