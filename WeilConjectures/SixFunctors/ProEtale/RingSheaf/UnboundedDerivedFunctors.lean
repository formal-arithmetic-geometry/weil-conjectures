/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Products
public import WeilConjectures.SixFunctors.ProEtale.RingSheaf.DerivedLimits

/-!
# Unbounded derived sections and direct images of module sheaves

Let `ℛ` be a sheaf of `R`-algebras on `X_proét` (a monoid object in pro-étale sheaves of
`R`-modules), `U` an object of `X_proét` and `f : X ⟶ Y` a morphism of schemes. The category of
`ℛ`-module sheaves is Grothendieck abelian (`CategoryTheory.Mod.isGrothendieckAbelian`), so it
has K-injective resolutions, and the total right derived functors on the *unbounded* derived
categories exist:

* `ProEtale.RingSheaf.rightDerivedSections ℛ U : D(X_proét, ℛ) ⥤ D(R)`, the derived sections
  `RΓ(U, -)`;
* `ProEtale.RingSheaf.rightDerivedLowerStarMod ℛ f : D(X_proét, ℛ) ⥤ D(Y_proét, f_* ℛ)`, the
  derived direct image `Rf_*` to `f_* ℛ`-module sheaves.

Both preserve products (`ProEtale.RingSheaf.preservesLimitsOfShape_discrete_rightDerivedSections`,
`ProEtale.RingSheaf.preservesLimitsOfShape_discrete_rightDerivedLowerStarMod`) and derived
inverse limits of towers (`ProEtale.RingSheaf.isHomotopyLimit_rightDerivedSections_mapCone`,
`ProEtale.RingSheaf.isHomotopyLimit_rightDerivedLowerStarMod_mapCone`): the underived functors
preserve products and products of `R`-modules and of `f_* ℛ`-module sheaves are exact
(blueprint `proposition-unbounded-functors-products`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite Pretriangulated

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.RingSheaf

open Scheme

attribute [local instance high] Mod.instHasLimitsOfShape_weilConjectures

variable {R : Type (u + 1)} [CommRing R] {X Y : Scheme.{u}}
  (ℛ : Sheaf (ProEt.topology X) (ModuleCat.{u + 1} R)) [MonObj ℛ]

/-- The sections `Γ(U, -)` over an object `U` of `X_proét` of `ℛ`-module sheaves, as
`R`-modules. -/
noncomputable def sections (U : X.ProEt) :
    Mod (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} R)) ℛ ⥤ ModuleCat.{u + 1} R :=
  Mod.forget ℛ ⋙ sheafToPresheaf (ProEt.topology X) (ModuleCat.{u + 1} R) ⋙
    (CategoryTheory.evaluation _ _).obj (op U)

/-- The direct image `f_*` from `ℛ`-module sheaves on `X_proét` to `f_* ℛ`-module sheaves on
`Y_proét`: the transport of module objects along the lax monoidal pushforward. -/
noncomputable abbrev lowerStarMod (f : X ⟶ Y) :
    Mod (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} R)) ℛ ⥤
      Mod (Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} R)) ((f)_*[ModuleCat.{u + 1} R].obj ℛ) :=
  (f)_*[ModuleCat.{u + 1} R].mapMod ℛ

/-- The sections functor is additive. -/
instance additive_sections (U : X.ProEt) : (sections ℛ U).Additive := by
  dsimp only [sections]
  infer_instance

/-- The direct image of module sheaves is additive, since it is so on underlying sheaves. -/
instance additive_lowerStarMod (f : X ⟶ Y) : (lowerStarMod ℛ f).Additive where
  map_add {_ _ a b} := (Mod.forget _).map_injective <| by
    rw [(Mod.forget _).map_add]
    exact (Mod.forget ℛ ⋙ (f)_*[ModuleCat.{u + 1} R]).map_add

/-- The sections functor preserves products. -/
instance preservesLimitsOfShape_sections (U : X.ProEt) (J : Type (u + 1)) :
    PreservesLimitsOfShape (Discrete J) (sections ℛ U) := by
  dsimp only [sections]
  infer_instance

/-- The direct image of module sheaves preserves products, since the forgetful functor creates
limits and `f_*` preserves them on underlying sheaves. -/
instance preservesLimitsOfShape_lowerStarMod (f : X ⟶ Y) (J : Type (u + 1)) :
    PreservesLimitsOfShape (Discrete J) (lowerStarMod ℛ f) := by
  have : PreservesLimitsOfShape (Discrete J) (lowerStarMod ℛ f ⋙ Mod.forget _) :=
    inferInstanceAs (PreservesLimitsOfShape (Discrete J)
      (Mod.forget ℛ ⋙ (f)_*[ModuleCat.{u + 1} R]))
  exact preservesLimitsOfShape_of_reflects_of_preserves _ (Mod.forget _)

/-- Module sheaves over `ℛ` form a Grothendieck abelian category. -/
instance isGrothendieckAbelian_mod :
    IsGrothendieckAbelian.{u + 1} (Mod (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} R)) ℛ) :=
  Mod.isGrothendieckAbelian.{u + 1} ℛ

variable [HasDerivedCategory (Mod (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} R)) ℛ)]

/-- Blueprint `proposition-unbounded-functors-products--1`: the derived sections
`RΓ(U, -) : D(X_proét, ℛ) ⥤ D(R)` on the unbounded derived category of `ℛ`-module sheaves, the
total right derived functor of `Γ(U, -)`, computed on K-injective resolutions (which exist since
`ℛ`-module sheaves form a Grothendieck abelian category). -/
noncomputable abbrev rightDerivedSections [HasDerivedCategory (ModuleCat.{u + 1} R)]
    (U : X.ProEt) :
    DerivedCategory (Mod (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} R)) ℛ) ⥤
      DerivedCategory (ModuleCat.{u + 1} R) :=
  (sections ℛ U).rightDerivedFunctor

/-- Blueprint `proposition-unbounded-functors-products--1`: the derived direct image
`Rf_* : D(X_proét, ℛ) ⥤ D(Y_proét, f_* ℛ)` on the unbounded derived categories, the total right
derived functor of `f_*` from `ℛ`-module sheaves to `f_* ℛ`-module sheaves, computed on
K-injective resolutions (which exist since `ℛ`-module sheaves form a Grothendieck abelian
category). -/
noncomputable abbrev rightDerivedLowerStarMod (f : X ⟶ Y)
    [HasDerivedCategory (Mod (Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} R))
      ((f)_*[ModuleCat.{u + 1} R].obj ℛ))] :
    DerivedCategory (Mod (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} R)) ℛ) ⥤
      DerivedCategory (Mod (Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} R))
        ((f)_*[ModuleCat.{u + 1} R].obj ℛ)) :=
  (lowerStarMod ℛ f).rightDerivedFunctor

/-- Blueprint `proposition-unbounded-functors-products--2`, products for `RΓ(U, -)`: the derived
sections on the unbounded derived category of `ℛ`-module sheaves preserve products, since
`Γ(U, -)` preserves products and products of `R`-modules are exact. -/
instance preservesLimitsOfShape_discrete_rightDerivedSections
    [HasDerivedCategory (ModuleCat.{u + 1} R)] (U : X.ProEt) (J : Type (u + 1)) :
    PreservesLimitsOfShape (Discrete J) (rightDerivedSections ℛ U) :=
  (sections ℛ U).preservesLimitsOfShape_discrete_rightDerivedFunctor

/-- Blueprint `proposition-unbounded-functors-products--2`, products for `Rf_*`: the derived
direct image from `ℛ`-module sheaves to `f_* ℛ`-module sheaves preserves products, since `f_*`
preserves products and products of `f_* ℛ`-module sheaves are exact. -/
instance preservesLimitsOfShape_discrete_rightDerivedLowerStarMod (f : X ⟶ Y)
    [HasDerivedCategory (Mod (Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} R))
      ((f)_*[ModuleCat.{u + 1} R].obj ℛ))] (J : Type (u + 1)) :
    PreservesLimitsOfShape (Discrete J) (rightDerivedLowerStarMod ℛ f) :=
  (lowerStarMod ℛ f).preservesLimitsOfShape_discrete_rightDerivedFunctor

/-- Blueprint `proposition-unbounded-functors-products--2`, derived limits for `RΓ(U, -)`: the
derived sections send a homotopy limit cone of a tower (whose point is the derived limit
`R lim Kₙ`, defined by the Milnor triangle) to a homotopy limit cone, being triangulated and
preserving countable products. -/
theorem isHomotopyLimit_rightDerivedSections_mapCone [HasDerivedCategory (ModuleCat.{u + 1} R)]
    (U : X.ProEt)
    {K : ℕᵒᵖ ⥤ DerivedCategory (Mod (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} R)) ℛ)}
    {c : Cone K} (hc : IsHomotopyLimit c) :
    IsHomotopyLimit ((rightDerivedSections ℛ U).mapCone c) :=
  have := preservesLimitsOfShape_discrete_rightDerivedSections ℛ U (ULift.{u + 1} ℕ)
  have : PreservesLimitsOfShape (Discrete ℕ) (rightDerivedSections ℛ U) :=
    preservesLimitsOfShape_of_equiv (Discrete.equivalence Equiv.ulift) _
  hc.map (rightDerivedSections ℛ U)

/-- Blueprint `proposition-unbounded-functors-products--2`, derived limits for `Rf_*`: the
derived direct image sends a homotopy limit cone of a tower (whose point is the derived limit
`R lim Kₙ`, defined by the Milnor triangle) to a homotopy limit cone, being triangulated and
preserving countable products. -/
theorem isHomotopyLimit_rightDerivedLowerStarMod_mapCone (f : X ⟶ Y)
    [HasDerivedCategory (Mod (Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} R))
      ((f)_*[ModuleCat.{u + 1} R].obj ℛ))]
    {K : ℕᵒᵖ ⥤ DerivedCategory (Mod (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} R)) ℛ)}
    {c : Cone K} (hc : IsHomotopyLimit c) :
    IsHomotopyLimit ((rightDerivedLowerStarMod ℛ f).mapCone c) :=
  have := preservesLimitsOfShape_discrete_rightDerivedLowerStarMod ℛ f (ULift.{u + 1} ℕ)
  have : PreservesLimitsOfShape (Discrete ℕ) (rightDerivedLowerStarMod ℛ f) :=
    preservesLimitsOfShape_of_equiv (Discrete.equivalence Equiv.ulift) _
  hc.map (rightDerivedLowerStarMod ℛ f)

/-- Blueprint `proposition-unbounded-functors-products--2`: the unbounded derived functors
`RΓ(U, -) : D(X_proét, ℛ) ⥤ D(R)` and `Rf_* : D(X_proét, ℛ) ⥤ D(Y_proét, f_* ℛ)` preserve
products (of any family indexed by a type in the universe of the site) and derived inverse
limits of towers (homotopy limit cones). -/
theorem rightDerivedSections_rightDerivedLowerStarMod_preserve_products_and_derivedLimits
    [HasDerivedCategory (ModuleCat.{u + 1} R)] (U : X.ProEt) (f : X ⟶ Y)
    [HasDerivedCategory (Mod (Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} R))
      ((f)_*[ModuleCat.{u + 1} R].obj ℛ))] :
    (∀ J : Type (u + 1), PreservesLimitsOfShape (Discrete J) (rightDerivedSections ℛ U)) ∧
      (∀ J : Type (u + 1),
        PreservesLimitsOfShape (Discrete J) (rightDerivedLowerStarMod ℛ f)) ∧
      (∀ {K : ℕᵒᵖ ⥤ DerivedCategory (Mod (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} R)) ℛ)}
        {c : Cone K}, IsHomotopyLimit c →
          IsHomotopyLimit ((rightDerivedSections ℛ U).mapCone c)) ∧
      (∀ {K : ℕᵒᵖ ⥤ DerivedCategory (Mod (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} R)) ℛ)}
        {c : Cone K}, IsHomotopyLimit c →
          IsHomotopyLimit ((rightDerivedLowerStarMod ℛ f).mapCone c)) :=
  ⟨fun J ↦ preservesLimitsOfShape_discrete_rightDerivedSections ℛ U J,
    fun J ↦ preservesLimitsOfShape_discrete_rightDerivedLowerStarMod ℛ f J,
    fun hc ↦ isHomotopyLimit_rightDerivedSections_mapCone ℛ U hc,
    fun hc ↦ isHomotopyLimit_rightDerivedLowerStarMod_mapCone ℛ f hc⟩

end AlgebraicGeometry.ProEtale.RingSheaf
