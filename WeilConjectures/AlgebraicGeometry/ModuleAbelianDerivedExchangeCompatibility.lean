/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ModuleAbelianDerivedDirectImageComparison
import WeilConjectures.AlgebraicGeometry.ModuleAbelianUnderivedExchange
import WeilConjectures.CategoryTheory.RightDerivedPlusCube

/-! # Compatibility of canonical coefficient comparisons with derived exchange

## References

* Stacks Project, Tags 0736, 07A7 and 03FD.
-/

@[expose] public section

universe u

open CategoryTheory Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

private theorem derivedBaseChange_module_eq
    (Λ : Type (u + 1)) [CommRing Λ] {X X' Y Y' : Scheme.{u}}
    {f : X ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X} {g : Y' ⟶ Y}
    (sq : CommSq g' f' f g) :
    derivedBaseChangeMapPlus (ModuleCat.{u + 1} Λ) sq =
      Functor.rightDerivedFunctorPlusBaseChange (baseChangeMap (ModuleCat.{u + 1} Λ) sq) := by
  rfl

private theorem derivedBaseChange_abelian_eq
    {X X' Y Y' : Scheme.{u}}
    {f : X ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X} {g : Y' ⟶ Y}
    (sq : CommSq g' f' f g) :
    derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq =
      Functor.rightDerivedFunctorPlusBaseChange (baseChangeMap AddCommGrpCat.{u + 1} sq) := by
  rfl

/-- Forgetting the source of derived exchange, using the canonical edge comparisons. -/
noncomputable def moduleAbelianDerivedExchangeSourceIso
    (Λ : Type (u + 1)) [CommRing Λ] {X Y Y' : Scheme.{u}}
    (f : X ⟶ Y) (g : Y' ⟶ Y)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    D+(moduleAbelianForget Λ Y').obj
        ((R+((f)_*[ModuleCat.{u + 1} Λ]) ⋙ D+((g)^*[ModuleCat.{u + 1} Λ])).obj K) ≅
      (R+((f)_*[AddCommGrpCat.{u + 1}]) ⋙ D+((g)^*[AddCommGrpCat.{u + 1}])).obj
        (D+(moduleAbelianForget Λ X).obj K) :=
  (moduleAbelianDerivedUpperStarIso Λ g).symm.app
      (R+((f)_*[ModuleCat.{u + 1} Λ]).obj K) ≪≫
    D+((g)^*[AddCommGrpCat.{u + 1}]).mapIso
      ((moduleAbelianDerivedLowerStarIso Λ f).app K)

/-- Forgetting the target of derived exchange, using the canonical edge comparisons. -/
noncomputable def moduleAbelianDerivedExchangeTargetIso
    (Λ : Type (u + 1)) [CommRing Λ] {X X' Y' : Scheme.{u}}
    (g' : X' ⟶ X) (f' : X' ⟶ Y')
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    D+(moduleAbelianForget Λ Y').obj
        ((D+((g')^*[ModuleCat.{u + 1} Λ]) ⋙ R+((f')_*[ModuleCat.{u + 1} Λ])).obj K) ≅
      (D+((g')^*[AddCommGrpCat.{u + 1}]) ⋙ R+((f')_*[AddCommGrpCat.{u + 1}])).obj
        (D+(moduleAbelianForget Λ X).obj K) :=
  (moduleAbelianDerivedLowerStarIso Λ f').app (D+((g')^*[ModuleCat.{u + 1} Λ]).obj K) ≪≫
    R+((f')_*[AddCommGrpCat.{u + 1}]).mapIso
      ((moduleAbelianDerivedUpperStarIso Λ g').symm.app K)

/-- Canonical coefficient comparisons intertwine the derived exchange transformations.
The maps in this equation are fixed by their units; no isomorphisms are chosen here
(Stacks, Tags 0736, 07A7 and 03FD). -/
theorem moduleAbelianDerivedExchange_compatibility
    (Λ : Type (u + 1)) [CommRing Λ]
    {X X' Y Y' : Scheme.{u}}
    {f : X ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X} {g : Y' ⟶ Y}
    (sq : CommSq g' f' f g)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    D+(moduleAbelianForget Λ Y').map
        ((derivedBaseChangeMapPlus (ModuleCat.{u + 1} Λ) sq).app K) ≫
        (moduleAbelianDerivedExchangeTargetIso Λ g' f' K).hom =
      (moduleAbelianDerivedExchangeSourceIso Λ f g K).hom ≫
        (derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq).app
          (D+(moduleAbelianForget Λ X).obj K) := by
  have h := Functor.rightDerivedFunctorPlusBaseChange_cube
    ((f)_*[ModuleCat.{u + 1} Λ]) ((f')_*[ModuleCat.{u + 1} Λ])
    ((f)_*[AddCommGrpCat.{u + 1}]) ((f')_*[AddCommGrpCat.{u + 1}])
    ((g')^*[ModuleCat.{u + 1} Λ]) ((g)^*[ModuleCat.{u + 1} Λ])
    ((g')^*[AddCommGrpCat.{u + 1}]) ((g)^*[AddCommGrpCat.{u + 1}])
    (moduleAbelianForget Λ X) (moduleAbelianForget Λ Y)
    (moduleAbelianForget Λ X') (moduleAbelianForget Λ Y')
    (baseChangeMap (ModuleCat.{u + 1} Λ) sq) (baseChangeMap AddCommGrpCat.{u + 1} sq)
    (moduleAbelianLowerStarIso Λ f).hom (moduleAbelianLowerStarIso Λ f').hom
    (moduleAbelianUpperStarIso Λ g) (moduleAbelianUpperStarIso Λ g')
    (moduleAbelianUnderivedExchange_compatibility Λ sq) K
  simpa only [moduleAbelianDerivedExchangeSourceIso, moduleAbelianDerivedExchangeTargetIso,
    moduleAbelianDerivedLowerStarIso, moduleAbelianDerivedLowerStarComparison,
    moduleAbelianDerivedUpperStarIso, Iso.symm_hom, Iso.trans_hom, Iso.app_hom, asIso_hom,
    derivedBaseChange_module_eq, derivedBaseChange_abelian_eq,
    Functor.mapIso_hom, Category.assoc] using h

end AlgebraicGeometry.Etale
