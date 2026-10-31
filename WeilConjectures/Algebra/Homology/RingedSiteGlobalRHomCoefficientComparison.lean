/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.RingedSiteGlobalRHomModel
public import WeilConjectures.Algebra.Homology.DerivedInternalHomSectionsModel
import WeilConjectures.Algebra.Homology.RingedSiteGlobalRHomSectionUnit


/-! Coefficient-preserving comparisons between representatives and global derived Hom. -/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe c v r a w z

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.RingedSiteGlobalRHom

variable {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{max c v r})
  [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  [HasDerivedCategory.{w} (Modules.{c, v, max c v r} R)]
  (A : Type a) [CommRing A] (φ : A →+* Scalars.{c, v, max c v r} R)
  [HasDerivedCategory.{z} (ModuleCat.{max c v r} A)]

attribute [local irreducible] homComplexFunctor derivedInternalHomOfUniverses
  Functor.rightDerivedFunctor Functor.rightDerivedFunctorUnit

private def coefficientComparison
    (L : CochainComplex (Modules.{c, v, max c v r} R) ℤ) :
    letI : IsGrothendieckAbelian.{max c v r} (Modules.{c, v, max c v r} R) :=
      (SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{c, v, r}
        J R).1
    (DerivedInternalHomSectionsModel.injectiveProperty.{c, v, r} R).ι ⋙
        representative.{c, v, r, a} R A φ L ⋙ DerivedCategory.Q ≅
      (DerivedInternalHomSectionsModel.injectiveProperty.{c, v, r} R).ι ⋙ DerivedCategory.Q.{w} ⋙
        globalHom.{c, v, r, a, w, z} R A φ (DerivedCategory.Q.{w}.obj L) := by
  let : IsGrothendieckAbelian.{max c v r} (Modules.{c, v, max c v r} R) :=
    (SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{c, v, r}
      J R).1
  let a := Classical.choice
    (DerivedInternalHomSectionsModel.derived_internalHom_sections_model.{c, v, r, w,
      max c v r} (R := R)).1
  let F := (sections.{c, v, max c v r} R A φ).rightDerivedFunctor
  refine NatIso.ofComponents (fun I ↦ ?_) ?_
  · have : I.obj.IsKInjective := I.property
    have := sections_unit_hom_isIso.{c, v, r, a, w, z} R A φ L I.obj
    exact asIso ((sections.{c, v, max c v r} R A φ).rightDerivedFunctorUnitQ
      (homComplex (R := R) L I.obj)) ≪≫ F.mapIso (a.app (op L, I)).symm
  · intro I I' f
    have hn := a.inv.naturality (X := (op L, I)) (Y := (op L, I')) (𝟙 _, f)
    dsimp only [DerivedInternalHomSectionsModel.representativeHom,
      DerivedInternalHomSectionsModel.representedInternalHom, Functor.comp_map,
      Functor.prod_map, Functor.prod_obj, Functor.uncurry_obj_map, Functor.id_map,
      Functor.id_obj, op_id,
      Functor.op_map, ObjectProperty.ι_map, Functor.map_id, unop_id,
      NatTrans.id_app, Category.id_comp] at hn
    simp only [Functor.map_id, NatTrans.id_app, Category.id_comp] at hn
    have hu := (sections.{c, v, max c v r} R A φ).rightDerivedFunctorUnitQ_naturality
      (((homComplexFunctor (R := R)).obj (op L)).map f.hom)
    dsimp only [Iso.trans_hom, asIso_hom, Functor.mapIso_hom, Iso.symm_hom,
      Functor.comp_map, ObjectProperty.ι_map, representative, homComplex,
      globalHom]
    change DerivedCategory.Q.map _ ≫ (_ ≫ F.map _) = (_ ≫ F.map _) ≫ F.map _
    rw [← Category.assoc, hu, Category.assoc, ← F.map_comp]
    change _ ≫ F.map (DerivedCategory.Q.map _ ≫ (a.app (op L, I')).inv) = _
    have hh := congrArg F.map hn
    change F.map (DerivedCategory.Q.map _ ≫ (a.app (op L, I')).inv) = _ at hh
    rw [hh, F.map_comp]
    exact (Category.assoc _ _ _).symm

/-- The section complex computes global RHom on K-injective targets, naturally.

Source: Stacks Project, Tags 0B6E, 08JA and 0A96.
(blueprint: lem-sfb-global-rhom-coefficient-comparison).

Proof: replace the source by a K-flat resolution. Its sheaf Hom into a K-injective
complex is K-injective, so the derived-section unit is invertible. Precomposition
with the resolution is a quasi-isomorphism on sheaf Hom and on global Hom.
Naturality of the derived unit transports invertibility to the original source.
Compose this unit with the existing internal-Hom representative comparison;
naturality of both factors gives the asserted natural isomorphism. -/
theorem representative_comparison
    (L : CochainComplex (Modules.{c, v, max c v r} R) ℤ) :
    letI : IsGrothendieckAbelian.{max c v r} (Modules.{c, v, max c v r} R) :=
      (SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{c, v, r}
        J R).1
    Nonempty ((DerivedInternalHomSectionsModel.injectiveProperty.{c, v, r} R).ι ⋙
        representative.{c, v, r, a} R A φ L ⋙ DerivedCategory.Q ≅
      (DerivedInternalHomSectionsModel.injectiveProperty.{c, v, r} R).ι ⋙ DerivedCategory.Q.{w} ⋙
        globalHom.{c, v, r, a, w, z} R A φ (DerivedCategory.Q.{w}.obj L)) :=
  ⟨coefficientComparison.{c, v, r, a, w, z} R A φ L⟩

end CategoryTheory.RingedSiteGlobalRHom
