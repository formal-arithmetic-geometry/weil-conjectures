/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.ProEtale.Comparison.Defs
public import WeilConjectures.SixFunctors.ProEtale.Derived.UpperLowerStar

/-!
# The comparison between the small étale and the small pro-étale site

Every étale morphism is weakly étale, so the small étale site of a scheme `X` sits inside its
small pro-étale site. The resulting morphism of sites `ν_X : X_proét ⟶ X_ét` has a pullback
`ν_X^*` on sheaves, and the comparison theorem says that at a finite coefficient ring `ν_X^*`
is exact and fully faithful with `id ≅ Rν_* ν^*`, that it identifies bounded constructible
étale complexes with bounded constructible pro-étale ones, and that it commutes with
quasi-compact quasi-separated direct images.

This is the bridge between the étale statements of the purity chapter and the pro-étale
categories in which the six operations of the framework are typed: the *étale-origin* objects
are exactly those in the essential image of `ν^*`.

## Implementation notes

The inclusion `AlgebraicGeometry.Scheme.toProEt` of small sites, the functors `ν^*` and `ν_*`,
the adjunction `ν^* ⊣ ν_*` and the exactness of `ν^*` are
`WeilConjectures.SixFunctors.ProEtale.Comparison.Defs`, sorry-free; this file states the
remaining clauses of `sk-prop-sf-comparison` on top of them.

The remaining clause of `sk-prop-sf-comparison` — that `ν_T^*` restricts to an equivalence of
`D^b_c(T_ét, Λ)` onto the constructible subcategory of `D^b_c(T_proét, Λ)` — is not stated:
the repository has no constructibility notion on the pro-étale site to be an equivalence onto.

## Main statements

- `AlgebraicGeometry.ProEtale.preservesFiniteColimits_comparisonUpperStar`: `ν^*` is right
  exact; left exactness is `AlgebraicGeometry.ProEtale.preservesFiniteLimits_comparisonUpperStar`.
- `AlgebraicGeometry.ProEtale.full_comparisonUpperStar`,
  `AlgebraicGeometry.ProEtale.faithful_comparisonUpperStar` and
  `AlgebraicGeometry.ProEtale.isIso_comparisonAdjunction_unit`: `ν^*` is fully faithful, with
  invertible unit.
- `AlgebraicGeometry.ProEtale.nonempty_iso_comparisonUpperStar_comp_rightDerivedLowerStar`
  (the comparison commutes with direct images) and
  `AlgebraicGeometry.ProEtale.comparisonUpperStarUnitIso` (`ν^*` preserves the monoidal unit).
-/

@[expose] public section

universe u' u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

namespace ProEtale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

/-- Blueprint `sk-prop-sf-comparison`: The pro-étale comparison

*Right exactness.* The comparison pullback preserves finite colimits — indeed all colimits,
being a left adjoint. Together with
`AlgebraicGeometry.ProEtale.preservesFiniteLimits_comparisonUpperStar` this is the exactness
of `ν^*`, which is what lets it be applied degreewise to complexes. -/
instance preservesFiniteColimits_comparisonUpperStar (X : Scheme.{u}) :
    PreservesFiniteColimits (comparisonUpperStar A X) :=
  inferInstance

/-- Blueprint `sk-prop-sf-comparison`: The pro-étale comparison

*Fullness.* The comparison pullback is full. -/
instance full_comparisonUpperStar (X : Scheme.{u}) : (comparisonUpperStar A X).Full :=
  sorry

/-- Blueprint `sk-prop-sf-comparison`: The pro-étale comparison

*Faithfulness.* The comparison pullback is faithful. -/
instance faithful_comparisonUpperStar (X : Scheme.{u}) : (comparisonUpperStar A X).Faithful :=
  sorry

/-- Blueprint `sk-prop-sf-comparison`: The pro-étale comparison

*Full faithfulness, in the form the chapter uses.* The unit `id ⟶ ν_* ν^*` of the comparison
adjunction is an isomorphism; this is the assertion `id ≅ Rν_{T*} ν_T^*` of the blueprint, and
it is strictly stronger than the existence of some isomorphism between the two functors.

Detection of isomorphisms is by covering families and on the affine ind-étale basis, not by
geometric points: geometric-point stalks are *not* conservative on all pro-étale sheaves, and
no argument of the purity chapter uses them off the étale-origin objects. -/
theorem isIso_comparisonAdjunction_unit (X : Scheme.{u}) :
    IsIso (comparisonAdjunction A X).unit :=
  sorry

/-- Blueprint `sk-prop-sf-comparison`: The pro-étale comparison

**The comparison direct image.** For `u : U ⟶ V` quasi-compact and quasi-separated the
comparison commutes with direct images:

```
  D⁺(U_ét) --R u_{ét,*}--> D⁺(V_ét)
      |                        |
   ν_U^*                    ν_V^*
      |                        |
      v                        v
  D⁺(U_proét) -R u_{proét,*}-> D⁺(V_proét)
```

commutes up to isomorphism, `ν_V^* ∘ R u_{ét,*} ≅ R u_{proét,*} ∘ ν_U^*`. Exactness of `ν^*`,
which is what allows it to be applied degreewise to complexes, is
`AlgebraicGeometry.ProEtale.preservesFiniteLimits_comparisonUpperStar`. -/
theorem nonempty_iso_comparisonUpperStar_comp_rightDerivedLowerStar {U V : Scheme.{u}}
    (u : U ⟶ V) [QuasiCompact u] [QuasiSeparated u] :
    Nonempty (R+(Etale.lowerStar A u) ⋙ D+(comparisonUpperStar A V) ≅
      D+(comparisonUpperStar A U) ⋙ R+(ProEtale.lowerStar A u)) :=
  sorry


section Unit

open MonoidalCategory Functor.OplaxMonoidal

variable (Λ : Type (u + 1)) [CommRing Λ] (X : Scheme.{u})

/-- The comparison pullback `ν^*` sends the constant sheaf `Λ_X`, the monoidal unit of étale
sheaves of `Λ`-modules, to the monoidal unit of pro-étale sheaves. This is the comparison map
`η` of the oplax monoidal pullback of sheaves along the inclusion of sites, which is invertible
since that inclusion is representably flat
(`CategoryTheory.Functor.sheafPullbackConstruction.isIso_η_sheafPullback`). -/
noncomputable def comparisonUpperStarUnitIso :
    ν^*(X)[ModuleCat.{u + 1} Λ].obj (𝟙_ _) ≅ 𝟙_ _ :=
  have (K : X.ProEtᵒᵖ) : IsConnected (CostructuredArrow (X.toProEt).op K) :=
    have : IsFiltered (CostructuredArrow (X.toProEt).op K) :=
      IsFiltered.of_equivalence (structuredArrowOpEquivalence _ (Opposite.unop K))
    IsFiltered.isConnected _
  have := Functor.sheafPullbackConstruction.isIso_η_sheafPullback (X.toProEt)
    (ModuleCat.{u + 1} Λ) X.smallEtaleTopology (Scheme.ProEt.topology X)
  asIso (η (Functor.sheafPullbackConstruction.sheafPullback (X.toProEt) (ModuleCat.{u + 1} Λ)
    X.smallEtaleTopology (Scheme.ProEt.topology X)))

end Unit
end ProEtale

end AlgebraicGeometry
