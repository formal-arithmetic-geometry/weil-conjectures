/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.ProEtale.Comparison.Defs
public import WeilConjectures.SixFunctors.ProEtale.Comparison.FullyFaithful
public import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStarAcyclic
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusBaseChange
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperLowerStar

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

## Implementation details

The inclusion `AlgebraicGeometry.toProEt` of small sites, the functors `ν^*` and `ν_*`,
the adjunction `ν^* ⊣ ν_*` and the exactness of `ν^*` are
defined in the `Comparison.Defs` file; this file states the remaining clauses of the comparison
theorem on top of them.

The remaining clause of the comparison theorem — that `ν_T^*` restricts to an
equivalence of `D^b_c(T_ét, Λ)` onto the constructible subcategory of `D^b_c(T_proét, Λ)` — is not
stated: the repository has no constructibility notion on the pro-étale site to be an equivalence
onto.

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

/-- The comparison pullback preserves finite colimits (indeed all colimits, being a left
adjoint). -/
instance preservesFiniteColimits_comparisonUpperStar (X : Scheme.{u}) :
    PreservesFiniteColimits (comparisonUpperStar A X) :=
  inferInstance

/-- **The comparison direct image.** For `u : U ⟶ V` quasi-compact and quasi-separated the
comparison commutes with direct images: `ν_V^* ∘ R u_{ét,*} ≅ R u_{proét,*} ∘ ν_U^*`. -/
theorem nonempty_iso_comparisonUpperStar_comp_rightDerivedLowerStar {U V : Scheme.{u}}
    (u : U ⟶ V) [QuasiCompact u] [QuasiSeparated u] :
    Nonempty (R+(Etale.lowerStar A u) ⋙ D+(comparisonUpperStar A V) ≅
      D+(comparisonUpperStar A U) ⋙ R+(ProEtale.lowerStar A u)) :=
  have := isIso_lowerStarComparisonUpperStarBaseChange u A
  have : IsIso (Functor.rightDerivedFunctorPlusBaseChange
      (lowerStarComparisonUpperStarBaseChange u A)) :=
    Functor.isIso_rightDerivedFunctorPlusBaseChange_of_rightAcyclic
      (asIso (lowerStarComparisonUpperStarBaseChange u A))
      (fun I _ ↦ rightAcyclic_lowerStar_comparisonUpperStar_obj_of_injective A u I)
  ⟨asIso (Functor.rightDerivedFunctorPlusBaseChange
    (lowerStarComparisonUpperStarBaseChange u A))⟩

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
