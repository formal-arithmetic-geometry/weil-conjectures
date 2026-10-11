/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Complete.RationalCoefficient
public import WeilConjectures.CategoryTheory.DerivedCategory.Complete.RationalizationMap
public import WeilConjectures.SixFunctors.Etale.Derived.DerivedComplete
public import WeilConjectures.SixFunctors.Etale.Derived.Triangulated
public import WeilConjectures.SixFunctors.ProEtale.Adic.ConstantSheaf
public import WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek

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
* `ℚ̄_ℓ`: pro-étale sheaves of `ℚ̄_ℓ`-modules (`AlgebraicGeometry.WeilCoefficients`), the
  coefficients of the Weil sheaves of `WeilConjectures.WeilSheaf.Category`. Again `Ri_*` is fully
  faithful on the whole derived category.

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

/-- For a full subcategory `P` of `C` and a functor `G : C ⥤ D` that is fully faithful on `P`,
the unit of any adjunction whose left adjoint is a corestriction of `P.ι ⋙ G` to a full
subcategory `P'` of `D` is an isomorphism. -/
lemma _root_.CategoryTheory.ObjectProperty.isIso_unit_app_of_lift {C D : Type*} [Category C]
    [Category D] {P : ObjectProperty C} {P' : ObjectProperty D} {G : C ⥤ D}
    [(P.ι ⋙ G).Full] [(P.ι ⋙ G).Faithful] (h : ∀ K, P' ((P.ι ⋙ G).obj K))
    {G' : P'.FullSubcategory ⥤ P.FullSubcategory} (adj : P'.lift (P.ι ⋙ G) h ⊣ G')
    (Q : P.FullSubcategory) : IsIso (adj.unit.app Q) :=
  inferInstance

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

omit [Finite Λ] in
/-- Blueprint `prop-sf-closed-unit-all-stages`, the unit at the finite stage: for any right
adjoint `Ri^!` of the corestriction of `Ri_* : Dᵇc_proét(Z, Λ) ⥤ D(X_proét, Λ)` to a full
subcategory `P` (for instance `Dᵇc_proét(X, Λ)`), the unit `Q ⟶ Ri^! Ri_* Q` is an isomorphism.
On the ambient categories the right adjoint exists, and this is
`AlgebraicGeometry.ProEtale.isIso_derivedLowerStarClosedUpperShriekAdjunction_unit_app`. -/
theorem ProEtale.isIso_unit_app_boundedConstructible
    {P : ObjectProperty (DerivedCategory (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} Λ)))}
    (h : ∀ K, P (((ProEtale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) Z).ι ⋙
      (ProEtale.lowerStar (ModuleCat.{u + 1} Λ) i).rightDerivedFunctor).obj K))
    {G : P.FullSubcategory ⥤
      (ProEtale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) Z).FullSubcategory}
    (adj : P.lift _ h ⊣ G)
    (Q : (ProEtale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) Z).FullSubcategory) :
    IsIso (adj.unit.app Q) :=
  ObjectProperty.isIso_unit_app_of_lift h adj Q

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

/-- `Rf_*` on derived complete objects, as a functor between the full subcategories of
`AlgebraicGeometry.DerivedCategory.derivedCompleteIntegral`. -/
noncomputable abbrev Etale.rightDerivedLowerStarDerivedCompleteIntegralAux {Y X : Scheme.{u}}
    (f : Y ⟶ X) :
    (DerivedCategory.derivedCompleteIntegral Y.smallEtaleTopology l E).FullSubcategory ⥤
      (DerivedCategory.derivedCompleteIntegral X.smallEtaleTopology l E).FullSubcategory :=
  (DerivedCategory.derivedCompleteIntegral X.smallEtaleTopology l E).lift
    ((DerivedCategory.derivedCompleteIntegral Y.smallEtaleTopology l E).ι ⋙
      (Etale.lowerStar (ModuleCat.{u + 1} (Shrink.{u + 1} (PadicAlgCl.integers l E)))
        f).rightDerivedFunctor)
    (fun K ↦ Etale.derivedCompleteIntegral_rightDerivedLowerStar l E f _ K.property)

/-- The direct image `Rf_* : D_comp(Y_ét, 𝒪_E) ⥤ D_comp(X_ét, 𝒪_E)` on derived complete
objects, the restriction of `Rf_*`
(`AlgebraicGeometry.Etale.derivedCompleteIntegral_rightDerivedLowerStar`). -/
noncomputable def Etale.rightDerivedLowerStarDerivedCompleteIntegral {Y X : Scheme.{u}}
    (f : Y ⟶ X) :
    DerivedCategoryDerivedCompleteIntegral Y.smallEtaleTopology l E ⥤
      DerivedCategoryDerivedCompleteIntegral X.smallEtaleTopology l E :=
  Etale.rightDerivedLowerStarDerivedCompleteIntegralAux l E f

noncomputable instance {Y X : Scheme.{u}} (f : Y ⟶ X) :
    (Etale.rightDerivedLowerStarDerivedCompleteIntegral l E f).CommShift ℤ :=
  inferInstanceAs ((Etale.rightDerivedLowerStarDerivedCompleteIntegralAux l E f).CommShift ℤ)

instance {Y X : Scheme.{u}} (f : Y ⟶ X) :
    (Etale.rightDerivedLowerStarDerivedCompleteIntegral l E f).IsTriangulated :=
  inferInstanceAs
    (Etale.rightDerivedLowerStarDerivedCompleteIntegralAux l E f).IsTriangulated

instance {Y X : Scheme.{u}} (f : Y ⟶ X) :
    (Etale.rightDerivedLowerStarDerivedCompleteIntegral l E f).Linear
      (Shrink.{u + 1} (PadicAlgCl.integers l E)) where
  map_smul _ _ :=
    (DerivedCategory.derivedCompleteIntegral X.smallEtaleTopology l E).ι.map_injective <|
      (Etale.lowerStar (ModuleCat.{u + 1} (Shrink.{u + 1} (PadicAlgCl.integers l E)))
        f).rightDerivedFunctor.map_smul _ _

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

/-- Blueprint `prop-sf-closed-unit-all-stages`, integral stage `𝒪_E`: the direct image `Ri_*`
along a closed immersion is fully faithful on the derived complete objects
`D_comp(Z_ét, 𝒪_E)`. -/
instance Etale.full_rightDerivedLowerStarDerivedCompleteIntegral :
    (Etale.rightDerivedLowerStarDerivedCompleteIntegral l E i).Full :=
  inferInstanceAs (Etale.rightDerivedLowerStarDerivedCompleteIntegralAux l E i).Full

instance Etale.faithful_rightDerivedLowerStarDerivedCompleteIntegral :
    (Etale.rightDerivedLowerStarDerivedCompleteIntegral l E i).Faithful :=
  inferInstanceAs (Etale.rightDerivedLowerStarDerivedCompleteIntegralAux l E i).Faithful

/-- The direct image `Rf_* : D_comp(Y_ét, E) ⥤ D_comp(X_ét, E)` at the rational stage, induced
on the rationalizations by `AlgebraicGeometry.Etale.rightDerivedLowerStarDerivedCompleteIntegral`.
-/
noncomputable def Etale.rightDerivedLowerStarDerivedCompleteRational {Y X : Scheme.{u}}
    (f : Y ⟶ X) :
    DerivedCategoryDerivedCompleteRational Y.smallEtaleTopology l E ⥤
      DerivedCategoryDerivedCompleteRational X.smallEtaleTopology l E :=
  Rationalization.map _ (Etale.rightDerivedLowerStarDerivedCompleteIntegral l E f)

/-- Blueprint `prop-sf-closed-unit-all-stages`, rational stage `E`: the direct image `Ri_*`
along a closed immersion is fully faithful on `D_comp(Z_ét, E)`. -/
instance Etale.full_rightDerivedLowerStarDerivedCompleteRational :
    (Etale.rightDerivedLowerStarDerivedCompleteRational l E i).Full :=
  Rationalization.full_map _

instance Etale.faithful_rightDerivedLowerStarDerivedCompleteRational :
    (Etale.rightDerivedLowerStarDerivedCompleteRational l E i).Faithful :=
  Rationalization.faithful_map _

/-- Blueprint `prop-sf-closed-unit-all-stages`, the unit at the integral stage: for any right
adjoint `Ri^!` of `Ri_* : D_comp(Z_ét, 𝒪_E) ⥤ D_comp(X_ét, 𝒪_E)`, the unit `Q ⟶ Ri^! Ri_* Q` is an
isomorphism. -/
theorem Etale.isIso_unit_app_rightDerivedLowerStarDerivedCompleteIntegral
    {G : DerivedCategoryDerivedCompleteIntegral X.smallEtaleTopology l E ⥤
      DerivedCategoryDerivedCompleteIntegral Z.smallEtaleTopology l E}
    (adj : Etale.rightDerivedLowerStarDerivedCompleteIntegral l E i ⊣ G)
    (Q : DerivedCategoryDerivedCompleteIntegral Z.smallEtaleTopology l E) :
    IsIso (adj.unit.app Q) :=
  inferInstance

/-- Blueprint `prop-sf-closed-unit-all-stages`, the unit at the rational stage: for any right
adjoint `Ri^!` of `Ri_* : D_comp(Z_ét, E) ⥤ D_comp(X_ét, E)`, the unit `Q ⟶ Ri^! Ri_* Q` is an
isomorphism. -/
theorem Etale.isIso_unit_app_rightDerivedLowerStarDerivedCompleteRational
    {G : DerivedCategoryDerivedCompleteRational X.smallEtaleTopology l E ⥤
      DerivedCategoryDerivedCompleteRational Z.smallEtaleTopology l E}
    (adj : Etale.rightDerivedLowerStarDerivedCompleteRational l E i ⊣ G)
    (Q : DerivedCategoryDerivedCompleteRational Z.smallEtaleTopology l E) :
    IsIso (adj.unit.app Q) :=
  inferInstance

end Integral

section AlgebraicClosure

variable (l : ℕ) [Fact l.Prime]

/-- Blueprint `prop-sf-closed-unit-all-stages`, stage `ℚ̄_ℓ`: the direct image `Ri_*` along a
closed immersion is fully faithful on the derived category of pro-étale sheaves of
`ℚ̄_ℓ`-modules, hence on any full subcategory of constructible objects. -/
instance ProEtale.full_rightDerivedFunctor_lowerStar_weilCoefficients :
    (ProEtale.lowerStar (WeilCoefficients.{u} l) i).rightDerivedFunctor.Full :=
  inferInstance

instance ProEtale.faithful_rightDerivedFunctor_lowerStar_weilCoefficients :
    (ProEtale.lowerStar (WeilCoefficients.{u} l) i).rightDerivedFunctor.Faithful :=
  inferInstance

/-- Blueprint `prop-sf-closed-unit-all-stages`, the unit at the stage `ℚ̄_ℓ`: for any right adjoint
`Ri^!` of `Ri_*` on pro-étale sheaves of `ℚ̄_ℓ`-modules, the unit `Q ⟶ Ri^! Ri_* Q` is an
isomorphism. -/
theorem ProEtale.isIso_unit_app_weilCoefficients
    {G : DerivedCategory (Sheaf (ProEt.topology X) (WeilCoefficients.{u} l)) ⥤
      DerivedCategory (Sheaf (ProEt.topology Z) (WeilCoefficients.{u} l))}
    (adj : (ProEtale.lowerStar (WeilCoefficients.{u} l) i).rightDerivedFunctor ⊣ G)
    (Q : DerivedCategory (Sheaf (ProEt.topology Z) (WeilCoefficients.{u} l))) :
    IsIso (adj.unit.app Q) :=
  inferInstance

end AlgebraicClosure

end AlgebraicGeometry
