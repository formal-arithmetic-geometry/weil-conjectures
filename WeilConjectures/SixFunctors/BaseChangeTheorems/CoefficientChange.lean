/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib
public import WeilConjectures.DerivedCategory.RightDerivedFunctor.Exchange
public import WeilConjectures.SixFunctors.BaseChangeTheorems.MorphismDefs

/-!

# Compatibility of the base-change morphism with a change of coefficients

This file states, step by step, the compatibility of the derived base-change morphism
`Etale.baseChange` of `WeilConjectures.SixFunctors.BaseChangeTheorems.MorphismDefs`
with a change of the coefficient category, following the note *Restriction of Scalars
and Proper Base Change* (`reference.pdf` on the `base-change-reference` branch).

The change of coefficients is an exact functor `U : A ⥤ B` between two coefficient
categories, preserving all limits and filtered colimits (the model is restriction of
scalars along a ring homomorphism, which has adjoints on both sides — reference,
Lemma 2.1). Postcomposition with `U` induces the functor `Res = Etale.coefficientChange`
between the categories of étale sheaves; being exact, it derives levelwise to
`Etale.coefficientChangePlus` on the bounded below derived categories (reference,
Proposition 3.1) — no resolutions enter.

Fix a commutative square of schemes

```
X' --g'--> X
|          |
f'         f
v          v
Y' --g---> Y
```

recorded as `sq : CommSq g' f' f g`. The compatibility of the two base-change morphisms
`BC_sq^A = Etale.baseChange A sq` and `BC_sq^B = Etale.baseChange B sq` is the
*coefficient-change exchange rectangle* (reference, Proposition 9.1)

`χ_{f'} ∘ Res(BC_sq^A) = BC_sq^B(Res) ∘ χ_f`   (up to the pullback comparisons `λ`),

where the two canonical comparisons entering the rectangle are constructed here:

- `λ_g = Etale.upperStarCoefficientChange`: the comparison `Res ∘ g^* ⟵ g^* ∘ Res` of
  the underived pullbacks, defined as the mate of the pushforward comparison
  (reference, Lemma 4.1), with derived version `Etale.upperStarPlusCoefficientChangeIso`;
- `χ_g = Etale.lowerStarPlusCoefficientChange`: the comparison
  `Res ∘ Rg_* ⟶ Rg_* ∘ Res` of the derived pushforwards, defined by the composition
  theorem for right derived functors via
  `Functor.rightDerivedFunctorPlusExchange` (reference, Proposition 6.1).

The mate identities (reference, Propositions 7.1 and 7.2) relating `χ` to the units and
counits of the derived adjunctions `Lg^* ⊣ Rg_*`, and the compatibility of the pullback
square comparison `θ_sq = Etale.pullbackSquareComparison` with the coefficient change
(reference, Section 8), are stated as the intermediate steps from which the rectangle
follows; their proofs, as well as the acyclicity input making `χ` an isomorphism
(reference, Propositions 5.4 and 6.1), are deferred (`sorry`).

The payoff is the coefficient-forgetting transfer theorem (reference, Theorem 1.1),
`Etale.isIso_baseChange_app_of_coefficientChange`: if the coefficient change reflects
isomorphisms, then `BC_sq^A` is an isomorphism at `K` as soon as `BC_sq^B` is an
isomorphism at `Res K`. This is the statement through which a base-change theorem
proved for one coefficient category (say `B = Ab`) is transferred to another (say
`A = ModuleCat (ZMod (ℓ ^ n))`) without repeating the geometric argument.

## Main definitions

- `AlgebraicGeometry.Etale.coefficientChange` and
  `AlgebraicGeometry.Etale.coefficientChangePlus`: the coefficient change on étale
  sheaves and on the bounded below derived categories.
- `AlgebraicGeometry.Etale.lowerStarCoefficientChangeIso`: the pushforward compatibility
  `g_* ∘ Res ≅ Res ∘ g_*` (underived).
- `AlgebraicGeometry.Etale.upperStarCoefficientChange` and
  `AlgebraicGeometry.Etale.upperStarPlusCoefficientChangeIso`: the pullback comparison
  `λ_g` and its derived version.
- `AlgebraicGeometry.Etale.lowerStarPlusCoefficientChange`: the derived pushforward
  comparison `χ_g`.
- `AlgebraicGeometry.Etale.lowerStarPlusCoefficientChange_unit` and
  `AlgebraicGeometry.Etale.lowerStarPlusCoefficientChange_counit`: the mate identities.
- `AlgebraicGeometry.Etale.pullbackSquareComparison_coefficientChange`: compatibility of
  `θ_sq` with the coefficient change.
- `AlgebraicGeometry.Etale.baseChange_coefficientChange`: the exchange rectangle.
- `AlgebraicGeometry.Etale.isIso_baseChange_app_of_coefficientChange`: the
  coefficient-forgetting transfer theorem.

-/

@[expose] public section

universe w w' uA uB u

open CategoryTheory Limits MonoidalCategory Abelian

namespace AlgebraicGeometry

open Scheme

/- The two coefficient categories `A` and `B`, each a concrete Grothendieck abelian
category as in the convention of `WeilConjectures.ConstructibleSheaf.Defs`, carrying the
K-flat resolution package of `WeilConjectures.SixFunctors.Derived`, and each equipped
with sheafification, pointwise left Kan extensions and chosen localized derived
categories for the small étale sites of all schemes at once — the variable context of
`WeilConjectures.SixFunctors.BaseChangeTheorems.MorphismDefs`, taken twice. -/
variable {A : Type uA} [Category.{u} A] [Abelian A]
  {FA : A → A → Type*} {CA : A → Type u}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{u} A FA]
  [PreservesLimits (CategoryTheory.forget A)]
  [(CategoryTheory.forget A).ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{u, u} (CategoryTheory.forget A)]
  [IsGrothendieckAbelian.{u} A]
  [∀ (T : Scheme.{u}), HasWeakSheafify T.smallEtaleTopology A]
  [∀ (T S : Scheme.{u}) (φ : T ⟶ S) (F : S.Etaleᵒᵖ ⥤ A),
    (MorphismProperty.Over.pullback @Etale ⊤ φ).op.HasLeftKanExtension F]
  [∀ (T : Scheme.{u}), HasDerivedCategory.{w} (Sheaf T.smallEtaleTopology A)]
  [MonoidalCategory A] [MonoidalPreadditive A]
  [∀ (X : A), PreservesFilteredColimitsOfSize.{u, u} (tensorLeft X)]
  [∀ (X : A), PreservesFilteredColimitsOfSize.{u, u} (tensorRight X)]
  [HasColimitsOfShape (Discrete ℤ) A]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ A), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ A), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ A), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [HasColimitsOfShape ℤ A] [HasExactColimitsOfShape ℤ A]
  [∀ (X : A), PreservesColimitsOfShape ℤ ((curriedTensor A).obj X)]
  [∀ (X : A), PreservesColimitsOfShape ℤ ((curriedTensor A).flip.obj X)]
  [Abelian.HasFunctorialFlatResolution A]

variable {B : Type uB} [Category.{u} B] [Abelian B]
  {FB : B → B → Type*} {CB : B → Type u}
  [∀ X Y, FunLike (FB X Y) (CB X) (CB Y)] [ConcreteCategory.{u} B FB]
  [PreservesLimits (CategoryTheory.forget B)]
  [(CategoryTheory.forget B).ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{u, u} (CategoryTheory.forget B)]
  [IsGrothendieckAbelian.{u} B]
  [∀ (T : Scheme.{u}), HasWeakSheafify T.smallEtaleTopology B]
  [∀ (T S : Scheme.{u}) (φ : T ⟶ S) (F : S.Etaleᵒᵖ ⥤ B),
    (MorphismProperty.Over.pullback @Etale ⊤ φ).op.HasLeftKanExtension F]
  [∀ (T : Scheme.{u}), HasDerivedCategory.{w'} (Sheaf T.smallEtaleTopology B)]
  [MonoidalCategory B] [MonoidalPreadditive B]
  [∀ (X : B), PreservesFilteredColimitsOfSize.{u, u} (tensorLeft X)]
  [∀ (X : B), PreservesFilteredColimitsOfSize.{u, u} (tensorRight X)]
  [HasColimitsOfShape (Discrete ℤ) B]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ B), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ B), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ B), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [HasColimitsOfShape ℤ B] [HasExactColimitsOfShape ℤ B]
  [∀ (X : B), PreservesColimitsOfShape ℤ ((curriedTensor B).obj X)]
  [∀ (X : B), PreservesColimitsOfShape ℤ ((curriedTensor B).flip.obj X)]
  [Abelian.HasFunctorialFlatResolution B]

/- The coefficient change `U : A ⥤ B`: an exact functor preserving all limits (of the
universe of the base schemes) and filtered colimits. The model is restriction of
scalars along a ring homomorphism, which is simultaneously a left and a right adjoint
(reference, Lemma 2.1), so it satisfies all three preservation hypotheses. The
limit preservation gives that postcomposition with `U` preserves étale sheaves; the
filtered-colimit preservation makes postcomposition commute with sheafification via the
stalks at the geometric points of the small étale sites. -/
variable (U : A ⥤ B) [U.Additive] [PreservesLimitsOfSize.{u, u} U]
  [PreservesFiniteColimits U] [PreservesFilteredColimitsOfSize.{u, u} U]

section CoefficientChange

/-!
## The coefficient change on étale sheaves and its exactness

Reference: Sections 2 and 3. The functor `Res` is postcomposition with `U`; it
preserves sheaves since `U` preserves limits
(`Etale.hasSheafCompose_smallEtaleTopology`). Its exactness is inherited from the
exactness of `U` (for finite limits because limits of sheaves are computed objectwise,
for finite colimits through sheafification via the stalks), and it derives levelwise to
the bounded below derived categories.
-/

/-- The coefficient change `Res : Sh(T_ét, A) ⥤ Sh(T_ét, B)` on étale sheaves induced by
the functor `U : A ⥤ B` on the coefficient categories: postcomposition with `U`, which
preserves sheaves since `U` preserves limits. For `U` the restriction of scalars along
a ring homomorphism this is the restriction of scalars of étale sheaves (reference,
Section 2.1). -/
noncomputable def Etale.coefficientChange (T : Scheme.{u}) :
    Sheaf T.smallEtaleTopology A ⥤ Sheaf T.smallEtaleTopology B :=
  have := Etale.hasSheafCompose_smallEtaleTopology A T U
  sheafCompose T.smallEtaleTopology U

/-- The coefficient change on étale sheaves is additive: it acts on morphisms by
whiskering with the additive functor `U`. -/
instance Etale.coefficientChange_additive (T : Scheme.{u}) :
    (Etale.coefficientChange U T).Additive :=
  have := Etale.hasSheafCompose_smallEtaleTopology A T U
  have : (Etale.coefficientChange U T ⋙ sheafToPresheaf _ _).Additive :=
    Functor.additive_of_iso
      (F := sheafToPresheaf _ _ ⋙ (Functor.whiskeringRight _ _ _).obj U) (Iso.refl _)
  Functor.additive_of_comp_faithful _ (sheafToPresheaf _ _)

/-- The coefficient change on étale sheaves is left exact: finite limits of sheaves are
computed objectwise in the category of presheaves, and `U` preserves them. -/
instance Etale.preservesFiniteLimits_coefficientChange (T : Scheme.{u}) :
    PreservesFiniteLimits (Etale.coefficientChange U T) :=
  sorry

/-- The coefficient change on étale sheaves is right exact: finite colimits of sheaves
are the sheafifications of the objectwise finite colimits of presheaves, `U` preserves
the latter, and postcomposition with `U` commutes with sheafification since `U`
preserves the limits and filtered colimits computing the stalks at the geometric points
of the small étale site. For `U` the restriction of scalars, exactness is the
biadjunction argument of the reference, Lemma 2.1. -/
instance Etale.preservesFiniteColimits_coefficientChange (T : Scheme.{u}) :
    PreservesFiniteColimits (Etale.coefficientChange U T) :=
  sorry

/-- If the coefficient change `U` reflects isomorphisms, so does the induced functor on
étale sheaves: an isomorphism of sheaves is detected objectwise, and `U` detects
isomorphisms of the sections. Reference, Lemma 2.2. -/
instance Etale.reflectsIsomorphisms_coefficientChange [U.ReflectsIsomorphisms]
    (T : Scheme.{u}) :
    (Etale.coefficientChange U T).ReflectsIsomorphisms :=
  sorry

/-- The coefficient change on the bounded below derived categories of étale sheaves:
since `Res` is exact, it is derived levelwise by `Functor.mapDerivedCategoryPlus` — it
is its own left and right derived functor, and no resolutions are needed. Reference,
Proposition 3.1. -/
noncomputable def Etale.coefficientChangePlus (T : Scheme.{u}) :
    DerivedCategory.Plus (Sheaf T.smallEtaleTopology A) ⥤
      DerivedCategory.Plus (Sheaf T.smallEtaleTopology B) :=
  (Etale.coefficientChange U T).mapDerivedCategoryPlus

/-- If the coefficient change `U` reflects isomorphisms, the induced functor on the
bounded below derived categories is conservative: it is t-exact (being levelwise), so
it commutes with the homology sheaves, and a morphism of the derived category is an
isomorphism if and only if it is one on all homology sheaves, where
`Etale.reflectsIsomorphisms_coefficientChange` applies. Reference, Proposition 3.4. -/
instance Etale.reflectsIsomorphisms_coefficientChangePlus [U.ReflectsIsomorphisms]
    (T : Scheme.{u}) :
    (Etale.coefficientChangePlus U T).ReflectsIsomorphisms :=
  sorry

end CoefficientChange

section LowerStarCompatibility

/-!
## Compatibility with the pushforward and the pullback (underived)

Reference: Section 4. The pushforward `g_*` acts on sheaves by precomposition with the
base change functor of étale sites, while `Res` acts by postcomposition with `U`, so
the two literally commute (Lemma 4.2). The pullback comparison `λ_g` is *defined* as
the mate of this commutation under the two adjunctions `g^* ⊣ g_*` (Lemma 4.1); that
it is an isomorphism is a statement about stalks and is deferred.
-/

variable {Z Y : Scheme.{u}} (g : Z ⟶ Y)

/-- The compatibility `g_* ∘ Res ≅ Res ∘ g_*` of the pushforward along `g : Z ⟶ Y` with
the coefficient change on étale sheaves: the pushforward is precomposition with the
base change functor of the small étale sites and the coefficient change is
postcomposition with `U`, so the two composites are literally equal. Reference,
Lemma 4.2. -/
noncomputable def Etale.lowerStarCoefficientChangeIso :
    Etale.lowerStar A g ⋙ Etale.coefficientChange U Y ≅
      Etale.coefficientChange U Z ⋙ Etale.lowerStar B g :=
  NatIso.ofComponents (fun G ↦ Iso.refl _)

/-- The pullback comparison `λ_g : Res ∘ g^* ⟶ g^* ∘ Res` of the coefficient change
with the pullback along `g : Z ⟶ Y` on étale sheaves, defined as the mate of the
pushforward compatibility `Etale.lowerStarCoefficientChangeIso` under the adjunctions
`g^* ⊣ g_*` for the two coefficient categories. Reference, Lemma 4.1. -/
noncomputable def Etale.upperStarCoefficientChange :
    Etale.coefficientChange U Y ⋙ Etale.upperStar B g ⟶
      Etale.upperStar A g ⋙ Etale.coefficientChange U Z :=
  (mateEquiv (Etale.upperStarLowerStarAdjunction A g)
      (Etale.upperStarLowerStarAdjunction B g)).symm
    (Etale.lowerStarCoefficientChangeIso U g).hom

/-- The pullback comparison `λ_g` is an isomorphism: on the stalk at a geometric point
of `Z`, both composites compute the stalk of the original sheaf at the image point,
compatibly with `U`, and the small étale site has enough points. Reference,
Lemma 4.1. -/
instance Etale.isIso_upperStarCoefficientChange :
    IsIso (Etale.upperStarCoefficientChange U g) :=
  sorry

/-- The pullback comparison `λ_g : Res ∘ g^* ≅ g^* ∘ Res` as an isomorphism. -/
noncomputable def Etale.upperStarCoefficientChangeIso :
    Etale.coefficientChange U Y ⋙ Etale.upperStar B g ≅
      Etale.upperStar A g ⋙ Etale.coefficientChange U Z :=
  asIso (Etale.upperStarCoefficientChange U g)

end LowerStarCompatibility

section DerivedComparisons

/-!
## The derived comparisons `λ^D` and `χ`

Reference: Sections 5 and 6. On the bounded below derived categories, the pullback
comparison derives levelwise, since all functors involved are exact. The direct-image
comparison `χ_g : Res ∘ Rg_* ⟶ Rg_* ∘ Res` is produced by the composition theorem for
right derived functors (`Functor.rightDerivedFunctorPlusExchange`): since `Res` is
exact, `Rg_* ∘ Res` is an honest right derived functor of the composite `g_* ∘ Res`,
and the underived commutation `Res ∘ g_* = g_* ∘ Res` then yields the canonical
comparison to the candidate `Res ∘ Rg_*`. That `χ_g` is an isomorphism is exactly the
acyclicity input of the composition theorem (reference, Propositions 5.1 and 5.4) and
is deferred.
-/

variable {Z Y : Scheme.{u}} (g : Z ⟶ Y)

/-- The derived pullback comparison `λ^D_g : Res ∘ Lg^* ≅ Lg^* ∘ Res` on the bounded
below derived categories: the levelwise derivation of the underived comparison
`Etale.upperStarCoefficientChangeIso`, using that derived pullback and coefficient
change are both computed levelwise (`Functor.mapDerivedCategoryPlus`). -/
noncomputable def Etale.upperStarPlusCoefficientChangeIso :
    Etale.coefficientChangePlus U Y ⋙ (Etale.upperStar B g).mapDerivedCategoryPlus ≅
      (Etale.upperStar A g).mapDerivedCategoryPlus ⋙ Etale.coefficientChangePlus U Z :=
  (Functor.mapDerivedCategoryPlusCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryPlusNatIso (Etale.upperStarCoefficientChangeIso U g) ≪≫
    Functor.mapDerivedCategoryPlusCompIso _ _

/-- The derived direct-image comparison `χ_g : Res ∘ Rg_* ⟶ Rg_* ∘ Res` on the bounded
below derived categories, obtained from the composition theorem for right derived
functors applied to the underived commutation `Res ∘ g_* = g_* ∘ Res`
(`Etale.lowerStarCoefficientChangeIso`), via the exchange transformation
`Functor.rightDerivedFunctorPlusExchange`. Reference, Proposition 6.1; by the mate
identities below, this comparison coincides with the right mate of the pullback
comparison `λ_g`. -/
noncomputable def Etale.lowerStarPlusCoefficientChange :
    (Etale.lowerStar A g).rightDerivedFunctorPlus ⋙ Etale.coefficientChangePlus U Y ⟶
      Etale.coefficientChangePlus U Z ⋙ (Etale.lowerStar B g).rightDerivedFunctorPlus :=
  Functor.rightDerivedFunctorPlusExchange (Etale.lowerStar A g) (Etale.lowerStar B g)
    (Etale.coefficientChange U Z) (Etale.coefficientChange U Y)
    (Etale.lowerStarCoefficientChangeIso U g).hom

/-- The derived direct-image comparison `χ_g` is an isomorphism: by the composition
theorem for right derived functors it suffices that `Res` sends injective sheaves of
`A`-coefficients to `g_*`-acyclic sheaves of `B`-coefficients. This is the one
cohomological input of the coefficient-change package: the higher direct images are
computed on the étale slices, where restriction preserves injectivity, and étale
cohomology does not depend on the recorded coefficient category since `U` preserves
the products and filtered colimits computing it. Reference, Lemma 5.2, Lemma 5.3 and
Proposition 5.4. Note that `Res` need *not* send injectives to injectives (reference,
Warning 6.2); only the acyclicity is claimed. -/
instance Etale.isIso_lowerStarPlusCoefficientChange :
    IsIso (Etale.lowerStarPlusCoefficientChange U g) :=
  sorry

end DerivedComparisons

section MateIdentities

/-!
## The mate identities

Reference: Section 7. The comparison `χ_g` is compatible with the units and counits of
the derived adjunctions `Lg^* ⊣ Rg_*` for the two coefficient categories, through the
derived pullback comparison `λ^D_g`. These two identities say precisely that `χ_g` is
the right mate of `λ^D_g`; they are the only properties of `χ` used in the proof of
the exchange rectangle.
-/

variable {Z Y : Scheme.{u}} (g : Z ⟶ Y)

/-- The *unit identity* (reference, Proposition 7.1): inserting the unit of the derived
adjunction `Lg^* ⊣ Rg_*` with `B`-coefficients after the coefficient change agrees with
inserting the `A`-coefficient unit and then transporting along the comparisons `χ_g`
and `λ^D_g`. Both sides are natural transformations
`Res ⟶ Res ∘ Lg^* ∘ Rg_*` (in diagrammatic order). -/
theorem Etale.lowerStarPlusCoefficientChange_unit :
    (Functor.rightUnitor _).inv ≫
      Functor.whiskerLeft (Etale.coefficientChangePlus U Y)
        (Etale.derivedUpperStarLowerStarAdjunctionPlus B g).unit =
    (Functor.leftUnitor _).inv ≫
      Functor.whiskerRight (Etale.derivedUpperStarLowerStarAdjunctionPlus A g).unit
        (Etale.coefficientChangePlus U Y) ≫
      (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft (Etale.upperStar A g).mapDerivedCategoryPlus
        (Etale.lowerStarPlusCoefficientChange U g) ≫
      (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight (Etale.upperStarPlusCoefficientChangeIso U g).inv
        ((Etale.lowerStar B g).rightDerivedFunctorPlus) ≫
      (Functor.associator _ _ _).hom :=
  sorry

/-- The *counit identity* (reference, Proposition 7.2): the coefficient change of the
counit of the derived adjunction `Lg^* ⊣ Rg_*` with `A`-coefficients agrees with
transporting along the comparisons `λ^D_g` and `χ_g` and then contracting with the
`B`-coefficient counit. Both sides are natural transformations
`Rg_* ∘ Lg^* ∘ Res ⟶ Res` (in diagrammatic order). -/
theorem Etale.lowerStarPlusCoefficientChange_counit :
    Functor.whiskerRight (Etale.derivedUpperStarLowerStarAdjunctionPlus A g).counit
        (Etale.coefficientChangePlus U Z) ≫
      (Functor.leftUnitor _).hom =
    (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft ((Etale.lowerStar A g).rightDerivedFunctorPlus)
        (Etale.upperStarPlusCoefficientChangeIso U g).inv ≫
      (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight (Etale.lowerStarPlusCoefficientChange U g)
        ((Etale.upperStar B g).mapDerivedCategoryPlus) ≫
      (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft (Etale.coefficientChangePlus U Z)
        (Etale.derivedUpperStarLowerStarAdjunctionPlus B g).counit ≫
      (Functor.rightUnitor _).hom :=
  sorry

end MateIdentities

section PullbackComparisonCompatibility

/-!
## Compatibility of the pullback comparisons

Reference: Section 8 ("forgetting from `B` to `A` carries `θ_B` to `θ_A` literally").
In the formalization the two pullback square comparisons live over different coefficient
categories, so their agreement is expressed as a commuting square through the derived
pullback comparisons `λ^D`. It reduces to the corresponding compatibility of the
composition isomorphisms `Etale.upperStarPlusComp`, which is stated first.
-/

/-- Compatibility of the composition isomorphism
`L(h₁ ≫ h₂)^* ≅ Lh₂^* ∘ Lh₁^*` (`Etale.upperStarPlusComp`) with the coefficient
change, through the derived pullback comparisons `λ^D`: transporting the composite
pullback and then decomposing agrees with decomposing and transporting each factor. -/
theorem Etale.upperStarPlusComp_coefficientChange {T S R : Scheme.{u}}
    (h₁ : T ⟶ S) (h₂ : S ⟶ R) :
    (Etale.upperStarPlusCoefficientChangeIso U (h₁ ≫ h₂)).hom ≫
      Functor.whiskerRight (Etale.upperStarPlusComp A h₁ h₂).hom
        (Etale.coefficientChangePlus U T) ≫
      (Functor.associator _ _ _).hom =
    Functor.whiskerLeft (Etale.coefficientChangePlus U R)
        (Etale.upperStarPlusComp B h₁ h₂).hom ≫
      (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight (Etale.upperStarPlusCoefficientChangeIso U h₂).hom
        ((Etale.upperStar B h₁).mapDerivedCategoryPlus) ≫
      (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft ((Etale.upperStar A h₂).mapDerivedCategoryPlus)
        (Etale.upperStarPlusCoefficientChangeIso U h₁).hom :=
  sorry

variable {X Y X' Y' : Scheme.{u}}
  {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}

/-- Compatibility of the pullback square comparison
`θ_sq : Lf'^* ∘ Lg^* ≅ Lg'^* ∘ Lf^*` (`Etale.pullbackSquareComparison`) with the
coefficient change: transporting along the derived pullback comparisons `λ^D` of the
four sides carries the `B`-coefficient comparison to the `A`-coefficient one. This is
the formal consequence of `Etale.upperStarPlusComp_coefficientChange` for the two
composites `g' ≫ f = f' ≫ g`; it is the square-specific input of the exchange
rectangle. Reference, Section 8. -/
theorem Etale.pullbackSquareComparison_coefficientChange (sq : CommSq g' f' f g) :
    Functor.whiskerLeft (Etale.coefficientChangePlus U Y)
        (Etale.pullbackSquareComparison B sq).hom ≫
      (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight (Etale.upperStarPlusCoefficientChangeIso U f).hom
        ((Etale.upperStar B g').mapDerivedCategoryPlus) ≫
      (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft ((Etale.upperStar A f).mapDerivedCategoryPlus)
        (Etale.upperStarPlusCoefficientChangeIso U g').hom =
    (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight (Etale.upperStarPlusCoefficientChangeIso U g).hom
        ((Etale.upperStar B f').mapDerivedCategoryPlus) ≫
      (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft ((Etale.upperStar A g).mapDerivedCategoryPlus)
        (Etale.upperStarPlusCoefficientChangeIso U f').hom ≫
      (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight (Etale.pullbackSquareComparison A sq).hom
        (Etale.coefficientChangePlus U X') ≫
      (Functor.associator _ _ _).hom :=
  sorry

end PullbackComparisonCompatibility

section ExchangeRectangle

/-!
## The exchange rectangle and the transfer theorem

Reference: Sections 9 and 10. The base-change morphisms with `A`- and `B`-coefficients
are intertwined by the comparisons `χ` and `λ^D`; this is the central compatibility of
this file. Combined with the invertibility of `χ` and the conservativity of the derived
coefficient change, it transfers a base-change theorem between coefficient categories.
-/

variable {X Y X' Y' : Scheme.{u}}
  {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}

/-- The *coefficient-change exchange rectangle* (reference, Proposition 9.1): for a
commutative square `g' ≫ f = f' ≫ g` of schemes, the derived base-change morphisms
`BC_sq^A = Etale.baseChange A sq` and `BC_sq^B = Etale.baseChange B sq` of the two
coefficient categories are intertwined by the direct-image comparisons `χ_f`, `χ_{f'}`
and the pullback comparisons `λ^D_g`, `λ^D_{g'}`:

`λ_{g'} ∘ χ_{f'} ∘ Res(BC_sq^A) = Res(BC_sq^B) ∘ χ_f ∘ λ_g`

as natural transformations `Rf_*^A ∘ Lg^* ∘ Res ⟶ Res ∘ Lg'^* ∘ Rf'_*^B` (in
diagrammatic order). The proof follows the reference: expand `BC_sq^A` into its three
steps (`Etale.baseChangeUnitStep`, `Etale.baseChangeSquareStep`,
`Etale.baseChangeCounitStep`), move `χ_{f'}` through the unit insertion by the unit
identity `Etale.lowerStarPlusCoefficientChange_unit`, transport the square comparison
by `Etale.pullbackSquareComparison_coefficientChange`, and absorb the counit
contraction by the counit identity `Etale.lowerStarPlusCoefficientChange_counit`. -/
theorem Etale.baseChange_coefficientChange (sq : CommSq g' f' f g) :
    Functor.whiskerRight (Etale.baseChange A sq) (Etale.coefficientChangePlus U Y') ≫
      (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft (Etale.upperStar A g').mapDerivedCategoryPlus
        (Etale.lowerStarPlusCoefficientChange U f') ≫
      (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight (Etale.upperStarPlusCoefficientChangeIso U g').inv
        ((Etale.lowerStar B f').rightDerivedFunctorPlus) ≫
      (Functor.associator _ _ _).hom =
    (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft ((Etale.lowerStar A f).rightDerivedFunctorPlus)
        (Etale.upperStarPlusCoefficientChangeIso U g).inv ≫
      (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight (Etale.lowerStarPlusCoefficientChange U f)
        ((Etale.upperStar B g).mapDerivedCategoryPlus) ≫
      (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft (Etale.coefficientChangePlus U X) (Etale.baseChange B sq) :=
  sorry

/-- The *coefficient-forgetting transfer theorem* (reference, Theorem 1.1): if the
coefficient change `U : A ⥤ B` reflects isomorphisms, and the base-change morphism with
`B`-coefficients is an isomorphism at the coefficient change of `K`, then the
base-change morphism with `A`-coefficients is an isomorphism at `K`.

Following the compact template of the reference (Appendix B): by the exchange rectangle
`Etale.baseChange_coefficientChange`, the image of `(BC_sq^A).app K` under the derived
coefficient change is the composite of `(BC_sq^B).app (Res K)` with the comparison
isomorphisms `χ` and `λ^D`, hence an isomorphism, and the derived coefficient change is
conservative (`Etale.reflectsIsomorphisms_coefficientChangePlus`).

All geometric hypotheses (properness of `f`, torsion coefficients, …) enter only
through the hypothesis `hK`; the transfer itself is formal. It applies to the
*canonical* base-change morphism only: an arbitrary isomorphism between the same two
objects does not suffice (reference, Warning 12.1). -/
theorem Etale.isIso_baseChange_app_of_coefficientChange [U.ReflectsIsomorphisms]
    (sq : CommSq g' f' f g)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology A))
    (hK : IsIso ((Etale.baseChange B sq).app ((Etale.coefficientChangePlus U X).obj K))) :
    IsIso ((Etale.baseChange A sq).app K) :=
  sorry

end ExchangeRectangle

end AlgebraicGeometry
