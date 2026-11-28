/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCompIsoExchangeCompatible
import all WeilConjectures.AlgebraicGeometry.UnboundedEtaleCompactSupportComparisons

/-!
# Associativity of the composition isomorphism of the lower shriek

For composable `f`, `g`, `h`, the two isomorphisms `R(f ≫ g ≫ h)_! ≅ Rf_! ⋙ Rg_! ⋙ Rh_!` built
from the composition isomorphisms `AlgebraicGeometry.Etale.rightDerivedLowerShriekCompIso` agree
(`AlgebraicGeometry.Etale.rightDerivedLowerShriekCompIso_assoc_app`). No finiteness assumption on
the schemes is needed. The same holds up to the congruence isomorphisms
(`AlgebraicGeometry.Etale.rightDerivedLowerShriekCompIso_congr_assoc_app`).
-/

@[expose] public section

universe u

open CategoryTheory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

attribute [local irreducible] DerivedCategory instCategoryDerivedCategory
  HasDerivedCategory.ofIsGrothendieckAbelian HasDerivedCategory.ofHasKInjectiveResolutions
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor Functor.mapDerivedCategory

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

/-- **Associativity of the composition isomorphism of the lower shriek**: for composable
`f`, `g`, `h`, the two isomorphisms `R(f ≫ g ≫ h)_! ≅ Rh_!(Rg_!(Rf_! -))` built from
`AlgebraicGeometry.Etale.rightDerivedLowerShriekCompIso` agree. -/
theorem rightDerivedLowerShriekCompIso_assoc_app {X Y Z T : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (h : Z ⟶ T) [HasCompactification f] [HasCompactification g] [HasCompactification h]
    [HasCompactification (f ≫ g)] [HasCompactification (g ≫ h)]
    [HasCompactification ((f ≫ g) ≫ h)] [HasCompactification (f ≫ g ≫ h)] [QuasiCompact f]
    [QuasiCompact g] [QuasiCompact h]
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (rightDerivedLowerShriekCongrIso Λ (Category.assoc f g h)).inv.app K ≫
        (rightDerivedLowerShriekCompIso Λ (f ≫ g) h).hom.app K ≫
          (R(h)_![ModuleCat.{u + 1} Λ]).map ((rightDerivedLowerShriekCompIso Λ f g).hom.app K) =
      (rightDerivedLowerShriekCompIso Λ f (g ≫ h)).hom.app K ≫
        (rightDerivedLowerShriekCompIso Λ g h).hom.app ((R(f)_![ModuleCat.{u + 1} Λ]).obj K) := by
  let := unbounded_has_base_change Λ
  let := unbounded_has_proper_exchange Λ
  have q := (unboundedFormalism Λ).lowerShriekCompIso_assoc f g h
  simp only [unbounded_chosen_comp] at q
  have hc : (unboundedFormalism Λ).lowerShriekCongr (Category.assoc f g h) =
      rightDerivedLowerShriekCongrIso Λ (Category.assoc f g h) := by
    generalize Category.assoc f g h = w
    cases w
    rfl
  rw [hc] at q
  have e := NatTrans.congr_app q K
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Category.id_comp] at e
  simp only [rightDerivedLowerShriekCompIso_eq_symm, Iso.symm_hom]
  rw [← cancel_mono ((unboundedEtaleLowerShriekCompIso Λ g h).hom.app
    ((R(f)_![ModuleCat.{u + 1} Λ]).obj K) ≫
      (unboundedEtaleLowerShriekCompIso Λ f (g ≫ h)).hom.app K)]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc, Iso.inv_hom_id_app]
  erw [← e, ← Functor.map_comp_assoc, Iso.inv_hom_id_app]
  rw [CategoryTheory.Functor.map_id, Category.id_comp,
    Iso.inv_hom_id_app_assoc, Iso.inv_hom_id_app]

omit [Finite Λ] in
/-- The congruence isomorphism of the lower shriek along `rfl` is the identity. -/
@[simp]
lemma rightDerivedLowerShriekCongrIso_refl {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasCompactification f] :
    rightDerivedLowerShriekCongrIso Λ (rfl : f = f) = Iso.refl _ :=
  rfl

/-- **Associativity of the composition isomorphism of the lower shriek, up to congruence**: for
`u₁ : X ⟶ Y`, `u₂ : Y ⟶ Z`, `a'' : Z ⟶ T` and `a' = u₂ ≫ a''`, `a = u₁ ≫ a'`, the two
isomorphisms `Ra_! ≅ Ra''_!(Ru₂_!(Ru₁_! -))` built from
`AlgebraicGeometry.Etale.rightDerivedLowerShriekCompIso` and
`AlgebraicGeometry.Etale.rightDerivedLowerShriekCongrIso` agree. -/
theorem rightDerivedLowerShriekCompIso_congr_assoc_app {X Y Z T : Scheme.{u}} (u₁ : X ⟶ Y)
    (u₂ : Y ⟶ Z) {a'' : Z ⟶ T} {a' : Y ⟶ T} {a : X ⟶ T} (h₁ : u₁ ≫ a' = a)
    (h₂ : u₂ ≫ a'' = a') (h₁₂ : (u₁ ≫ u₂) ≫ a'' = a) [HasCompactification u₁]
    [HasCompactification u₂] [HasCompactification a''] [HasCompactification a']
    [HasCompactification a] [HasCompactification (u₁ ≫ u₂)] [HasCompactification (u₁ ≫ a')]
    [HasCompactification (u₂ ≫ a'')] [HasCompactification ((u₁ ≫ u₂) ≫ a'')] [QuasiCompact u₁]
    [QuasiCompact u₂] [QuasiCompact a''] [QuasiCompact (u₁ ≫ u₂)] [QuasiCompact (u₁ ≫ a')]
    [QuasiCompact (u₂ ≫ a'')] [QuasiCompact ((u₁ ≫ u₂) ≫ a'')]
    (P : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (rightDerivedLowerShriekCongrIso Λ h₁₂).inv.app P ≫
        (rightDerivedLowerShriekCompIso Λ (u₁ ≫ u₂) a'').hom.app P ≫
          (R(a'')_![ModuleCat.{u + 1} Λ]).map ((rightDerivedLowerShriekCompIso Λ u₁ u₂).hom.app P) =
      (rightDerivedLowerShriekCongrIso Λ h₁).inv.app P ≫
        (rightDerivedLowerShriekCompIso Λ u₁ a').hom.app P ≫
          (rightDerivedLowerShriekCongrIso Λ h₂).inv.app ((R(u₁)_![ModuleCat.{u + 1} Λ]).obj P) ≫
            (rightDerivedLowerShriekCompIso Λ u₂ a'').hom.app
              ((R(u₁)_![ModuleCat.{u + 1} Λ]).obj P) := by
  subst h₁ h₂
  have h := rightDerivedLowerShriekCompIso_assoc_app Λ u₁ u₂ a'' P
  simp only [rightDerivedLowerShriekCongrIso_refl Λ (u₁ ≫ u₂ ≫ a''),
    rightDerivedLowerShriekCongrIso_refl Λ (u₂ ≫ a''), Iso.refl_inv, NatTrans.id_app,
    Category.id_comp] at h ⊢
  refine h.trans ?_
  erw [Category.id_comp]

end AlgebraicGeometry.Etale
