/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
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

The instances needed to build `ν^*` — that left Kan extensions along `ν_X^{op}` exist, and
that `ν_X` is continuous for the two topologies — are `sorry`, exactly as the corresponding
instances for base change in
`WeilConjectures.CategoryTheory.GrothendieckAbelian.HasLeftKanExtension` are.

## Main definitions

- `AlgebraicGeometry.Scheme.etaleToProEt`: the inclusion `X_ét ⥤ X_proét` of small sites.
- `AlgebraicGeometry.ProEtale.comparisonUpperStar`: `ν_X^*`.

## Main statements

- `AlgebraicGeometry.ProEtale.comparisonUpperStar_spec`
-/

@[expose] public section

universe u' u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

/-- The inclusion of the small étale site of `X` into its small pro-étale site: an étale
morphism is weakly étale, so an object of `X.Etale` is an object of `X.ProEt`, and the same on
morphisms. This is the underlying functor of the comparison morphism of sites
`ν_X : X_proét ⟶ X_ét`. -/
noncomputable def Scheme.etaleToProEt (X : Scheme.{u}) : X.Etale ⥤ X.ProEt :=
  MorphismProperty.Over.changeProp X (fun _ _ _ hf ↦ have := hf; inferInstance) le_rfl

/-- Left Kan extensions along the opposite of the comparison functor exist for `A`-valued
presheaves: both sites are essentially small and the Grothendieck abelian category `A` is
cocomplete. -/
instance ProEtale.hasLeftKanExtension_op_etaleToProEt (A : Type u') [Category.{u + 1} A]
    [Abelian A] [IsGrothendieckAbelian.{u + 1} A] (X : Scheme.{u}) (F : X.Etaleᵒᵖ ⥤ A) :
    (Scheme.etaleToProEt X).op.HasLeftKanExtension F :=
  sorry

/-- The comparison functor is continuous: an étale covering family of an étale `X`-scheme is a
pro-étale covering family of the same scheme viewed pro-étale. -/
instance ProEtale.isContinuous_etaleToProEt (X : Scheme.{u}) :
    (Scheme.etaleToProEt X).IsContinuous X.smallEtaleTopology (Scheme.ProEt.topology X) :=
  sorry

namespace ProEtale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

/-- The comparison pullback `ν_X^* : Sh(X_ét) ⥤ Sh(X_proét)`: left Kan extension along the
inclusion of small sites followed by pro-étale sheafification, left adjoint to the restriction
`ν_{X*}`. -/
noncomputable def comparisonUpperStar (X : Scheme.{u}) :
    Sheaf X.smallEtaleTopology A ⥤ Sheaf (Scheme.ProEt.topology X) A :=
  Functor.sheafPullbackConstruction.sheafPullback (Scheme.etaleToProEt X) A
    X.smallEtaleTopology (Scheme.ProEt.topology X)

/-- The restriction `ν_{X*} : Sh(X_proét) ⥤ Sh(X_ét)` along the inclusion of small sites. -/
noncomputable def comparisonLowerStar (X : Scheme.{u}) :
    Sheaf (Scheme.ProEt.topology X) A ⥤ Sheaf X.smallEtaleTopology A :=
  (Scheme.etaleToProEt X).sheafPushforwardContinuous A X.smallEtaleTopology
    (Scheme.ProEt.topology X)

/-- The comparison restriction is additive: it acts on morphisms by whiskering. -/
instance additive_comparisonLowerStar (X : Scheme.{u}) : (comparisonLowerStar A X).Additive where

/-- The comparison adjunction `ν^* ⊣ ν_*`. -/
noncomputable def comparisonAdjunction (X : Scheme.{u}) :
    comparisonUpperStar A X ⊣ comparisonLowerStar A X :=
  Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (Scheme.etaleToProEt X) A
    X.smallEtaleTopology (Scheme.ProEt.topology X)

/-- The comparison pullback is additive, being a left adjoint. -/
instance additive_comparisonUpperStar (X : Scheme.{u}) : (comparisonUpperStar A X).Additive :=
  (comparisonAdjunction A X).left_adjoint_additive

/-- The comparison pullback preserves homology as soon as it is left exact: it preserves all
colimits, being a left adjoint. -/
instance preservesHomology_comparisonUpperStar (X : Scheme.{u})
    [PreservesFiniteLimits (comparisonUpperStar A X)] :
    (comparisonUpperStar A X).PreservesHomology := by
  have : PreservesColimitsOfSize.{0, 0} (comparisonUpperStar A X) :=
    (comparisonAdjunction A X).leftAdjoint_preservesColimits
  exact {}

/-- Blueprint `sk-prop-sf-comparison`: The pro-étale comparison

**The comparison theorem.** For the comparison morphism `ν_T : T_proét ⟶ T_ét` and a finite
coefficient ring, the pullback `ν_T^*` is exact and fully faithful with `id ≅ Rν_{T*} ν_T^*`;
and the comparison direct image `ν_V^* R u_{ét,*} ≅ R u_{proét,*} ν_U^*` is an isomorphism of
functors on bounded below derived categories for `u : U ⟶ V` quasi-compact and
quasi-separated.

Detection of isomorphisms is by covering families and on the affine ind-étale basis, not by
geometric points: geometric-point stalks are *not* conservative on all pro-étale sheaves, and
no argument of the purity chapter uses them off the étale-origin objects.

The remaining clause of the blueprint statement — that `ν_T^*` restricts to an equivalence of
`D^b_c(T_ét, Λ)` onto the constructible subcategory of `D^b_c(T_proét, Λ)` — is not stated
here: the repository has no constructibility notion on the pro-étale site to be an equivalence
onto. -/
theorem full_and_faithful_comparisonUpperStar (X : Scheme.{u}) :
    PreservesFiniteLimits (comparisonUpperStar A X) ∧
      PreservesFiniteColimits (comparisonUpperStar A X) ∧
      (comparisonUpperStar A X).Full ∧ (comparisonUpperStar A X).Faithful ∧
      Nonempty (𝟭 (Sheaf X.smallEtaleTopology A) ≅
        comparisonUpperStar A X ⋙ comparisonLowerStar A X) :=
  sorry

/-- Blueprint `sk-prop-sf-comparison`: The pro-étale comparison

**The comparison direct image.** For `u : U ⟶ V` quasi-compact and quasi-separated the
comparison commutes with direct images:

`ν_V^* ∘ R u_{ét,*} ≅ R u_{proét,*} ∘ ν_U^*`

as functors `D⁺(U_ét, Λ) ⥤ D⁺(V_proét, Λ)`. Exactness of `ν^*`, which is what allows it to be
applied degreewise to complexes, is the first clause of
`AlgebraicGeometry.ProEtale.full_and_faithful_comparisonUpperStar` and is carried here as a
hypothesis. -/
theorem nonempty_iso_comparisonUpperStar_comp_rightDerivedLowerStar {U V : Scheme.{u}}
    (u : U ⟶ V) [QuasiCompact u] [QuasiSeparated u]
    [PreservesFiniteLimits (comparisonUpperStar A U)]
    [PreservesFiniteColimits (comparisonUpperStar A U)]
    [PreservesFiniteLimits (comparisonUpperStar A V)]
    [PreservesFiniteColimits (comparisonUpperStar A V)] :
    Nonempty (R+(Etale.lowerStar A u) ⋙ D+(comparisonUpperStar A V) ≅
      D+(comparisonUpperStar A U) ⋙ R+(ProEtale.lowerStar A u)) :=
  sorry

end ProEtale

end AlgebraicGeometry
