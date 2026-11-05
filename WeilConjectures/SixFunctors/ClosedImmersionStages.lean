/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Complete.RationalCoefficient
public import WeilConjectures.CategoryTheory.DerivedCategory.RationalizationMap
public import WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect
public import WeilConjectures.Mathlib.CategoryTheory.Idempotents.FunctorExtension
public import WeilConjectures.SixFunctors.ProEtale.Adic.LowerStar
public import WeilConjectures.SixFunctors.ProEtale.Adic.ClosedImmersion
public import WeilConjectures.SixFunctors.Etale.Derived.DerivedComplete
public import WeilConjectures.SixFunctors.Etale.Derived.Triangulated
public import WeilConjectures.SixFunctors.ProEtale.Adic.ConstantSheaf
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ClosedUpperShriek

/-!
# The direct image along a closed immersion is fully faithful at every coefficient stage

Blueprint `prop-sf-closed-unit-all-stages`: for a closed immersion `i : Z ⟶ X`, the direct image
`i_* = Ri_* = Ri_!` is fully faithful on the categories `Dᵇc(-, Λ)` at each of the coefficient
stages `Λ = A_{E,n}, 𝒪_E, E, ℚ̄_ℓ`, and consequently, at every stage at which `i_*` has a right
adjoint `Ri^!` on these categories, the unit `Q ⟶ Ri^! i_* Q` is an isomorphism.

In this repository the stages are realised as follows.

* `A_{E,n}`: the bounded constructible objects `Dᵇc_proét(-, Λ)` of the derived category of
  pro-étale sheaves of `Λ`-modules, `Λ` finite
  (`AlgebraicGeometry.ProEtale.DerivedCategory.boundedConstructible`). Here `Ri_*` is fully
  faithful on the whole derived category
  (`AlgebraicGeometry.ProEtale.full_rightDerivedFunctor_lowerStar`), and the right adjoint
  exists on the ambient categories (`prop-sf-closed-immersion-unit`,
  `AlgebraicGeometry.ProEtale.isIso_derivedLowerStarClosedUpperShriekAdjunction_unit_app`).
* `𝒪_E`: the derived complete objects `D_comp(X_ét, 𝒪_E)` of the derived category of étale
  sheaves of `𝒪_E`-modules (`DerivedCategoryDerivedCompleteIntegral`), which `Rf_*` preserves
  (`AlgebraicGeometry.Etale.derivedCompleteIntegral_rightDerivedLowerStar`). As `Ri_*` is fully
  faithful on the whole étale derived category, it is so on `D_comp(-, 𝒪_E)`
  (`AlgebraicGeometry.Etale.full_rightDerivedLowerStarDerivedCompleteIntegral`).
* `E`: the rationalization `D_comp(X_ét, E)` of `D_comp(X_ét, 𝒪_E)`
  (`DerivedCategoryDerivedCompleteRational`), whose `Hom` groups are those of
  `D_comp(X_ét, 𝒪_E)` with the nonzero elements of `𝒪_E` inverted. The functor induced by an
  `𝒪_E`-linear fully faithful triangulated functor is fully faithful
  (`CategoryTheory.Rationalization.full_map`), which is the blueprint's argument that
  bijectivity persists after tensoring with `E`.
* `ℚ̄_ℓ`: the bounded constructible objects `Dᵇc(X, ℚ̄_ℓ)` of the derived category of `ℓ`-adic
  sheaves `AlgebraicGeometry.ProEtale.AdicSheaf l X`, i.e. pro-étale sheaves of modules over the
  constant `ℓ`-adic sheaf `ℚ̄_ℓ,X`
  (`AlgebraicGeometry.ProEtale.DerivedCategory.boundedConstructibleAdic`). The `ℓ`-adic `i_*` is
  fully faithful and preserves K-injective complexes, so `Ri_*` is fully faithful on the whole
  derived category
  (`AlgebraicGeometry.ProEtale.full_boundedConstructibleAdic_ι_comp_rightDerivedLowerStar`).

At each stage the full faithfulness is stated for the inclusion of the stage category followed by
`Ri_*`, which is full faithfulness of `i_* : Dᵇc(Z, Λ) ⥤ Dᵇc(X, Λ)` whatever the target
subcategory, and the unit statement for any right adjoint of the corestriction of `i_*` to a
full subcategory containing its image.

The blueprint's proof at the integral stage goes through the Roos triangles of the
`𝒪_E`-adic towers; in the derived-complete model used here this is unnecessary, since the
integral stage is a full subcategory of the derived category of `𝒪_E`-modules, on which `Ri_*`
is fully faithful outright.
-/

@[expose] public section

universe w u

open CategoryTheory Limits

namespace AlgebraicGeometry

open Scheme

variable {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]

section Finite

variable {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ]

/-- Blueprint `prop-sf-closed-unit-all-stages`, finite stage `A_{E,n}`: the direct image
`Ri_*` along a closed immersion is fully faithful on the bounded constructible pro-étale
complexes `Dᵇc_proét(Z, Λ)`, `Λ` finite. -/
instance ProEtale.full_boundedConstructible_ι_comp_rightDerivedLowerStar :
    ((ProEtale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) Z).ι ⋙
      (ProEtale.lowerStar (ModuleCat.{u + 1} Λ) i).rightDerivedFunctor).Full :=
  inferInstance

instance ProEtale.faithful_boundedConstructible_ι_comp_rightDerivedLowerStar :
    ((ProEtale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) Z).ι ⋙
      (ProEtale.lowerStar (ModuleCat.{u + 1} Λ) i).rightDerivedFunctor).Faithful :=
  inferInstance

end Finite

section Integral

/-- The small étale site of a scheme is essentially small. Instance search does not find this
in the presence of the imports of this file. -/
local instance (X : Scheme.{u}) : EssentiallySmall.{u + 1} X.Etale :=
  have : LocallySmall.{u + 1} X.Etale :=
    @locallySmall_of_univLE X.Etale _ (@univLE_of_max.{u, u + 1} UnivLE.self)
  essentiallySmall_of_small_of_locallySmall _

variable (l : ℕ) [Fact l.Prime] (E : Type w) [Field E] [Algebra E (PadicAlgCl l)]
  [Small.{u + 1} E] [Algebra ℚ_[l] E] [IsScalarTower ℚ_[l] E (PadicAlgCl l)]
  [FiniteDimensional ℚ_[l] E]

/-- The right derived direct image along a closed immersion is fully faithful on étale sheaves
with values in any Grothendieck abelian category: `i_*` is fully faithful
(`AlgebraicGeometry.Etale.full_lowerStar_of_isClosedImmersion`) and preserves K-injective
complexes as a right adjoint of the exact `i^*`. -/
instance Etale.full_rightDerivedFunctor_lowerStar_of_isClosedImmersion (A : Type*)
    [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A] [HasSmallSiteSheafify A] :
    (Etale.lowerStar A i).rightDerivedFunctor.Full :=
  have : (Etale.lowerStar A i).PreservesKInjectiveComplexes :=
    (Etale.upperStarLowerStarAdjunction A i).preservesKInjectiveComplexes
  inferInstance

instance Etale.faithful_rightDerivedFunctor_lowerStar_of_isClosedImmersion (A : Type*)
    [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A] [HasSmallSiteSheafify A] :
    (Etale.lowerStar A i).rightDerivedFunctor.Faithful :=
  have : (Etale.lowerStar A i).PreservesKInjectiveComplexes :=
    (Etale.upperStarLowerStarAdjunction A i).preservesKInjectiveComplexes
  inferInstance

end Integral

section BoundedConstructible

/-! ### The categories `Dᵇc(-, Λ)` at the integral, rational and `ℚ̄_ℓ` stages -/

variable (l : ℕ) [Fact l.Prime] (E : Type w) [Field E] [Algebra E (PadicAlgCl l)]
  [Small.{u + 1} E] [Algebra ℚ_[l] E] [IsScalarTower ℚ_[l] E (PadicAlgCl l)]
  [FiniteDimensional ℚ_[l] E]

/-- The small étale site of a scheme is essentially small. Instance search does not find this
in the presence of the imports of this file. -/
local instance (X : Scheme.{u}) : EssentiallySmall.{u + 1} X.Etale :=
  have : LocallySmall.{u + 1} X.Etale :=
    @locallySmall_of_univLE X.Etale _ (@univLE_of_max.{u, u + 1} UnivLE.self)
  essentiallySmall_of_small_of_locallySmall _

instance ProEtale.full_adicLowerStar : (ProEtale.adicLowerStar l i).Full :=
  (ProEtale.adicUpperStarLowerStarAdjunction l i).fullyFaithfulROfIsIsoCounit.full

instance ProEtale.faithful_adicLowerStar : (ProEtale.adicLowerStar l i).Faithful :=
  (ProEtale.adicUpperStarLowerStarAdjunction l i).fullyFaithfulROfIsIsoCounit.faithful

/-- Algebraically closed coefficient category.

The stage `ℚ̄_ℓ` of `Dᵇc(X, ℚ̄_ℓ)`: bounded complexes of sheaves of modules over the
constant `ℓ`-adic sheaf `ℚ̄_ℓ,X` with constructible cohomology sheaves
(`AlgebraicGeometry.ProEtale.adicConstructibleSheaf`), the `2`-colimit over finite `E ⊆ ℚ̄_ℓ`
realised in the Bhatt–Scholze model. -/
abbrev ProEtale.DerivedCategory.boundedConstructibleAdic (X : Scheme.{u}) :
    ObjectProperty (DerivedCategory (ProEtale.AdicSheaf l X)) :=
  DerivedCategory.TStructure.t.bounded ⊓
    DerivedCategory.homologyProperty (ProEtale.adicConstructibleSheaf l X)

/-- Blueprint `prop-sf-closed-unit-all-stages`, stage `ℚ̄_ℓ`: the direct image `Ri_*` along a
closed immersion is fully faithful on `Dᵇc(Z, ℚ̄_ℓ)`. The `ℓ`-adic `i_*` is fully faithful, its
counit being an isomorphism, and preserves K-injective complexes, so its right derived functor is
fully faithful. -/
instance ProEtale.full_boundedConstructibleAdic_ι_comp_rightDerivedLowerStar :
    ((ProEtale.DerivedCategory.boundedConstructibleAdic l Z).ι ⋙
      (ProEtale.adicLowerStar l i).rightDerivedFunctor).Full :=
  inferInstance

instance ProEtale.faithful_boundedConstructibleAdic_ι_comp_rightDerivedLowerStar :
    ((ProEtale.DerivedCategory.boundedConstructibleAdic l Z).ι ⋙
      (ProEtale.adicLowerStar l i).rightDerivedFunctor).Faithful :=
  inferInstance

end BoundedConstructible

end AlgebraicGeometry
