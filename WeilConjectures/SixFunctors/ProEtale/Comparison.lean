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

The two instances needed to *build* `ν^*` — that left Kan extensions along `ν_X^{op}` exist,
and that `ν_X` is continuous for the two topologies — are `sorry`, exactly as the
corresponding instances for base change in
`WeilConjectures.CategoryTheory.GrothendieckAbelian.HasLeftKanExtension` are. Both are Prop
valued, so no datum below carries `sorryAx`, but every statement about `ν^*` rests on them.
Both are infrastructure rather than blueprint content, and both should be provable outright:
essential smallness of the two sites together with cocompleteness of `A` gives the Kan
extension, and an étale covering family of an étale `X`-scheme is a pro-étale covering family
of the same scheme viewed pro-étale.

The remaining clause of `sk-prop-sf-comparison` — that `ν_T^*` restricts to an equivalence of
`D^b_c(T_ét, Λ)` onto the constructible subcategory of `D^b_c(T_proét, Λ)` — is not stated:
the repository has no constructibility notion on the pro-étale site to be an equivalence onto.

## Main definitions

- `AlgebraicGeometry.Scheme.etaleToProEt`: the inclusion `X_ét ⥤ X_proét` of small sites.
- `AlgebraicGeometry.ProEtale.comparisonUpperStar`: `ν_X^*`.
- `AlgebraicGeometry.ProEtale.comparisonLowerStar`: `ν_{X*}`.
- `AlgebraicGeometry.ProEtale.comparisonAdjunction`: `ν^* ⊣ ν_*`.

## Main statements

- `AlgebraicGeometry.ProEtale.preservesFiniteLimits_comparisonUpperStar` and
  `AlgebraicGeometry.ProEtale.preservesFiniteColimits_comparisonUpperStar`: `ν^*` is exact.
- `AlgebraicGeometry.ProEtale.full_comparisonUpperStar`,
  `AlgebraicGeometry.ProEtale.faithful_comparisonUpperStar` and
  `AlgebraicGeometry.ProEtale.isIso_comparisonAdjunction_unit`: `ν^*` is fully faithful, with
  invertible unit.
- `AlgebraicGeometry.ProEtale.nonempty_iso_comparisonUpperStar_comp_rightDerivedLowerStar`
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

namespace ProEtale

/-- Left Kan extensions along the opposite of the comparison functor exist for `A`-valued
presheaves: both sites are essentially small and the Grothendieck abelian category `A` is
cocomplete. -/
instance hasLeftKanExtension_op_etaleToProEt (A : Type u') [Category.{u + 1} A]
    [Abelian A] [IsGrothendieckAbelian.{u + 1} A] (X : Scheme.{u}) (F : X.Etaleᵒᵖ ⥤ A) :
    (Scheme.etaleToProEt X).op.HasLeftKanExtension F :=
  sorry

/-- The comparison functor is continuous: an étale covering family of an étale `X`-scheme is a
pro-étale covering family of the same scheme viewed pro-étale. -/
instance isContinuous_etaleToProEt (X : Scheme.{u}) :
    (Scheme.etaleToProEt X).IsContinuous X.smallEtaleTopology (Scheme.ProEt.topology X) :=
  sorry

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

/-- The comparison pullback `ν_X^* : Sh(X_ét) ⥤ Sh(X_proét)`: left Kan extension along the
inclusion of small sites followed by pro-étale sheafification, left adjoint to the restriction
`ν_{X*}`.

It is built from the two `sorry`ed instances above, so every statement about it is conditional
on them; see the implementation notes. -/
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

/-- Blueprint `sk-prop-sf-comparison`: The pro-étale comparison

*Left exactness.* The comparison pullback preserves finite limits; together with
`AlgebraicGeometry.ProEtale.preservesFiniteColimits_comparisonUpperStar` this is the exactness
of `ν^*`, which is what lets it be applied degreewise to complexes. -/
instance preservesFiniteLimits_comparisonUpperStar (X : Scheme.{u}) :
    PreservesFiniteLimits (comparisonUpperStar A X) :=
  sorry

/-- Blueprint `sk-prop-sf-comparison`: The pro-étale comparison

*Right exactness.* The comparison pullback preserves finite colimits — indeed all colimits,
being a left adjoint. -/
instance preservesFiniteColimits_comparisonUpperStar (X : Scheme.{u}) :
    PreservesFiniteColimits (comparisonUpperStar A X) :=
  sorry

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

/-- The comparison pullback preserves homology: it is exact and preserves all colimits, being
a left adjoint. -/
instance preservesHomology_comparisonUpperStar (X : Scheme.{u}) :
    (comparisonUpperStar A X).PreservesHomology := by
  have : PreservesColimitsOfSize.{0, 0} (comparisonUpperStar A X) :=
    (comparisonAdjunction A X).leftAdjoint_preservesColimits
  constructor <;> infer_instance

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

end ProEtale

end AlgebraicGeometry
