/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.AlgebraicGeometry.BaseChangeDimension
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
public import WeilConjectures.SixFunctors.Etale.Derived.DirectImageVanishingTorsion
public import WeilConjectures.SixFunctors.Etale.Derived.GlobalSections
public import WeilConjectures.SixFunctors.Etale.Derived.SepClosedCohomology

/-!
# Cohomological dimension of étale sheaves of `Λ`-modules

The (torsion étale) cohomological dimension of a scheme and of a morphism, for sheaves of
`Λ`-modules (blueprint `def-kun-cd`), and its finiteness for schemes and morphisms of finite type
over a field (blueprint `lem-kun-0f10`, Stacks 0F10).

## Main definitions and statements

- `AlgebraicGeometry.Etale.HasFiniteCohomologicalDimension`,
  `AlgebraicGeometry.Etale.HasFiniteCohomologicalDimensionMorphism` (`def-kun-cd`).
- `AlgebraicGeometry.Etale.hasFiniteCohomologicalDimensionMorphism` and
  `AlgebraicGeometry.Etale.hasFiniteCohomologicalDimension_of_isSepClosed` (`lem-kun-0f10`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ]

section Defs

variable (X : Scheme.{u})

/-- Blueprint `def-kun-cd` (for sheaves of `Λ`-modules): the scheme `X` has *finite
cohomological dimension* for sheaves of `Λ`-modules if there is a `d` with `H^q(X, F) = 0` for
every étale sheaf `F` of `Λ`-modules and every `q > d`. For a torsion ring `Λ` every such sheaf
is a torsion abelian sheaf, so this follows from finiteness of the torsion étale cohomological
dimension `cd(X)` of the blueprint. -/
def HasFiniteCohomologicalDimension : Prop :=
  ∃ d : ℤ, ∀ (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℤ), d < q →
    IsZero ((cohomology (ModuleCat.{u + 1} Λ) X q).obj
      ((DerivedCategory.singleFunctor _ 0).obj F))

variable {X} in
/-- Blueprint `def-kun-cd` (for morphisms, and sheaves of `Λ`-modules): the morphism `f` has
*finite cohomological dimension* for sheaves of `Λ`-modules if there is a `d` with
`R^q f_* F = 0` for every étale sheaf `F` of `Λ`-modules and every `q > d`. -/
def HasFiniteCohomologicalDimensionMorphism {Y : Scheme.{u}} (f : X ⟶ Y) : Prop :=
  ∃ d : ℤ, ∀ (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℤ), d < q →
    IsZero ((DerivedCategory.homologyFunctor _ q).obj
      ((R((f)_*[ModuleCat.{u + 1} Λ])).obj ((DerivedCategory.singleFunctor _ 0).obj F)))

end Defs

/-- A quasi-compact scheme locally of finite type over a field has finite dimension. -/
lemma exists_topologicalKrullDim_le_of_locallyOfFiniteType {K : Type u} [Field K]
    {X : Scheme.{u}} (aX : X ⟶ Spec (.of K)) [LocallyOfFiniteType aX] [QuasiCompact aX] :
    ∃ d : ℕ, topologicalKrullDim X ≤ (d : WithBot ℕ∞) := by
  obtain ⟨d, hd⟩ := exists_topologicalKrullDim_le_of_isPullback aX
  exact ⟨d, hd K (𝟙 _) (𝟙 X) aX (IsPullback.id_horiz aX)⟩

/-- The `q`-th homology of `Rf_*` of a sheaf placed in degree `0` is the higher direct image
`R^q f_*`, computed on the bounded below derived category. -/
noncomputable def homologyRightDerivedLowerStarSingleIsoHigherDirectImage {X Y : Scheme.{u}}
    (f : X ⟶ Y) (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℕ) :
    (DerivedCategory.homologyFunctor _ q).obj
        ((R((f)_*[ModuleCat.{u + 1} Λ])).obj ((DerivedCategory.singleFunctor _ 0).obj F)) ≅
      Etale.higherDirectImage Λ f q F :=
  ((f)_*[ModuleCat.{u + 1} Λ]).homologyRightDerivedFunctorObjSingleFunctorIso F q ≪≫
    (((f)_*[ModuleCat.{u + 1} Λ]).homologyRightDerivedFunctorPlusObjSingleFunctorIso F q).symm

/-- Blueprint `lem-kun-0f10`, part (1), over a separably closed field: a morphism between
`K`-schemes of finite type has finite cohomological dimension, with bound `2 dim X`. This is
`AlgebraicGeometry.Etale.isZero_higherDirectImage_of_two_mul_lt`. -/
theorem hasFiniteCohomologicalDimensionMorphism_of_isSepClosed_of_locallyOfFiniteType
    (hΛ : IsAddTorsion Λ) {K : Type u} [Field K] [IsSepClosed K]
    {X Y : Scheme.{u}} (aX : X ⟶ Spec (.of K)) (aY : Y ⟶ Spec (.of K))
    [LocallyOfFiniteType aX] [QuasiCompact aX] [LocallyOfFiniteType aY] [QuasiCompact aY]
    (f : X ⟶ Y) (hf : f ≫ aY = aX) :
    HasFiniteCohomologicalDimensionMorphism Λ f := by
  obtain ⟨d, hd⟩ := exists_topologicalKrullDim_le_of_locallyOfFiniteType aX
  have : LocallyOfFiniteType f := by
    subst hf
    exact locallyOfFiniteType_of_comp f aY
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian aY
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace aX
  have : QuasiCompact f := inferInstance
  refine ⟨2 * d, fun F q hq ↦ ?_⟩
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, q = n := ⟨q.toNat, by omega⟩
  exact (Etale.isZero_higherDirectImage_of_two_mul_lt hΛ f aX aY hf d hd F n hq).of_iso
    (homologyRightDerivedLowerStarSingleIsoHigherDirectImage Λ f F n)

/-- Blueprint `lem-kun-0f10`: finite cohomological dimension of finite-type morphisms, part (1).

Let `K` be a field and `f : X ⟶ Y` a morphism between `K`-schemes of finite type. For a torsion
coefficient ring `Λ`, the higher direct images `R^q f_*` of étale sheaves of `Λ`-modules vanish
in all large degrees `q`. -/
theorem hasFiniteCohomologicalDimensionMorphism (hΛ : IsAddTorsion Λ) {K : Type u} [Field K]
    {X Y : Scheme.{u}} (aX : X ⟶ Spec (.of K)) (aY : Y ⟶ Spec (.of K))
    [LocallyOfFiniteType aX] [QuasiCompact aX] [LocallyOfFiniteType aY] [QuasiCompact aY]
    (f : X ⟶ Y) (_hf : f ≫ aY = aX) :
    HasFiniteCohomologicalDimensionMorphism Λ f :=
  sorry

/-- Blueprint `lem-kun-0f10`: finite cohomological dimension of finite-type morphisms, part (2).

Over a separably closed field `K`, a `K`-scheme `X` of finite type has finite étale
cohomological dimension: for a torsion coefficient ring `Λ`, `H^q(X, F) = 0` for every étale
sheaf `F` of `Λ`-modules and all large `q`. -/
theorem hasFiniteCohomologicalDimension_of_isSepClosed (hΛ : IsAddTorsion Λ) {K : Type u}
    [Field K] [IsSepClosed K] {X : Scheme.{u}} (aX : X ⟶ Spec (.of K))
    [LocallyOfFiniteType aX] [QuasiCompact aX] :
    HasFiniteCohomologicalDimension Λ X := by
  obtain ⟨d, hd⟩ := hasFiniteCohomologicalDimensionMorphism_of_isSepClosed_of_locallyOfFiniteType
    Λ hΛ aX (𝟙 _) aX (Category.comp_id _)
  refine ⟨d, fun F q hq ↦ ?_⟩
  -- `H^q(X, F) = H^q(Spec K, Ra_* F) = Γ(Spec K, R^q a_* F)`, `Γ` being exact on `Spec K`
  exact ((Sheaf.Γ _ _).map_isZero (hd F q hq)).of_iso
    ((DerivedCategory.homologyFunctor _ q).mapIso
      ((rightDerivedLowerStarCompRightDerivedGlobalSectionsIso _ aX).app _).symm ≪≫
      ((Sheaf.Γ (Spec (.of K)).smallEtaleTopology
        (ModuleCat.{u + 1} Λ)).rightDerivedFunctorHomologyFunctorIso q).symm.app _)

end Etale

end AlgebraicGeometry
