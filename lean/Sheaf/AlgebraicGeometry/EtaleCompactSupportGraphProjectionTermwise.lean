/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A2
-/
module

public import Sheaf.AlgebraicGeometry.EtaleCompactSupportGraphProjection
public import Sheaf.CategoryTheory.ExactDerivedNaturalTransformation

/-!
# The sheaf projection and its exact derived image

Source: SGA 4 XVII 6.2.11; Stacks Project Tags 0F4L and 04VG.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

attribute [local irreducible] upperStar lowerStar etaleLowerShriek openImmersionLowerShriek

/-- The sheaf projection adjoint to a compactification comparison.
Source: SGA 4 XVII 6.2.11; Stacks Project Tag 0F4L.
(blueprint: lem-a2-compact-support-termwise-projection). -/
noncomputable def compactSupportGraphSheafProjection
    (A : Type (u + 1)) [CommRing A] {U X : Scheme.{u}} (f : U ⟶ X) [Etale f]
    (c : Compactification f)
    (a : etaleLowerShriek (ModuleCat.{u + 1} A) f inferInstance ⟶
      openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i ⋙
        lowerStar (ModuleCat.{u + 1} A) c.g) :
    etaleLowerShriek (ModuleCat.{u + 1} A) f inferInstance ⋙
        upperStar (ModuleCat.{u + 1} A) c.g ⟶
      openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i :=
  Functor.whiskerRight a (upperStar (ModuleCat.{u + 1} A) c.g) ≫
    Functor.whiskerLeft (openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i)
      (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) c.g).counit

private theorem transpose_on_homotopy
    {B C D : Type*} [Category B] [Category C] [Category D]
    [Abelian B] [Abelian C] [Abelian D]
    (E : B ⥤ C) (J : B ⥤ D) (P : C ⥤ D) (R : D ⥤ C)
    [E.Additive] [J.Additive] [P.Additive] [R.Additive] (adj : P ⊣ R)
    (a : E ⟶ J ⋙ R) (δ : E ⋙ P ⟶ J)
    (hδ : ∀ M, P.map (a.app M) ≫ adj.counit.app (J.obj M) = δ.app M)
    (K : HomotopyCategory B (.up ℤ)) :
    (P.mapHomotopyCategory (.up ℤ)).map
        ((a.mapHomotopyCategory (.up ℤ)).app K ≫
          (Functor.mapHomotopyCategoryCompIso (Iso.refl (J ⋙ R)) (.up ℤ)).inv.app K) ≫
        (adj.mapHomotopyCategory (.up ℤ)).counit.app
          ((J.mapHomotopyCategory (.up ℤ)).obj K) =
      (Functor.mapHomotopyCategoryCompIso (Iso.refl (E ⋙ P)) (.up ℤ)).hom.app K ≫
        (δ.mapHomotopyCategory (.up ℤ)).app K := by
  obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
  change _ ≫ (adj.mapHomotopyCategory (.up ℤ)).counit.app
    ((HomotopyCategory.quotient D (.up ℤ)).obj
      ((J.mapHomologicalComplex (.up ℤ)).obj K)) = _
  rw [Adjunction.mapHomotopyCategory_counit_app_quotient]
  change (HomotopyCategory.quotient D (.up ℤ)).map _ ≫
      (HomotopyCategory.quotient D (.up ℤ)).map _ =
    (HomotopyCategory.quotient D (.up ℤ)).map _ ≫
      (HomotopyCategory.quotient D (.up ℤ)).map _
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 1
  ext n
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
    NatTrans.mapHomologicalComplex_app_f, Functor.mapHomologicalComplexCompIso_hom_app_f,
    Functor.mapHomologicalComplexCompIso_inv_app_f,
    Adjunction.mapHomologicalComplex_counit_app_f, Iso.refl_hom, Iso.refl_inv,
    NatTrans.id_app, Functor.map_comp]
  change (P.map (a.app (K.X n)) ≫ P.map (𝟙 (R.obj (J.obj (K.X n))))) ≫
    adj.counit.app (J.obj (K.X n)) = 𝟙 (P.obj (E.obj (K.X n))) ≫ δ.app (K.X n)
  erw [P.map_id, Category.comp_id, Category.id_comp]
  exact hδ (K.X n)

/-- The homotopy projection is the termwise image of the sheaf projection.
Source: Stacks Project, Tag 0F4L.
(blueprint: lem-a2-compact-support-termwise-projection).

Proof: represent the homotopy object by a complex. The induced adjunction counit and
all composition comparisons are degreewise the sheaf counit and identity comparisons.
Each component is therefore the defining sheaf transpose. -/
theorem compactSupportGraphProjectionOnHomotopy_termwise
    (A : Type (u + 1)) [CommRing A] {U X : Scheme.{u}} (f : U ⟶ X) [Etale f]
    (c : Compactification f)
    (a : etaleLowerShriek (ModuleCat.{u + 1} A) f inferInstance ⟶
      openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i ⋙
        lowerStar (ModuleCat.{u + 1} A) c.g)
    (K : HomotopyCategory (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)) (.up ℤ)) :
    (compactSupportGraphProjectionOnHomotopy A f c a).app K =
      (Functor.mapHomotopyCategoryCompIso
        (Iso.refl (etaleLowerShriek (ModuleCat.{u + 1} A) f inferInstance ⋙
          upperStar (ModuleCat.{u + 1} A) c.g)) (.up ℤ)).hom.app K ≫
        ((compactSupportGraphSheafProjection A f c a).mapHomotopyCategory (.up ℤ)).app K := by
  have h := transpose_on_homotopy
    (etaleLowerShriek (ModuleCat.{u + 1} A) f inferInstance)
    (openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i)
    (upperStar (ModuleCat.{u + 1} A) c.g) (lowerStar (ModuleCat.{u + 1} A) c.g)
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) c.g)
    a (compactSupportGraphSheafProjection A f c a) (fun M ↦ by
      simp only [compactSupportGraphSheafProjection, NatTrans.comp_app,
        Functor.whiskerRight_app, Functor.whiskerLeft_app,
        Functor.comp_obj, Functor.id_obj]) K
  simpa only [compactSupportGraphProjectionOnHomotopy, graphProjectionTranspose_app,
    NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.associator_hom_app,
    Functor.rightUnitor_hom_app, Functor.comp_obj, Functor.id_obj,
    Category.id_comp, Category.comp_id] using h

/-- The descended graph projection is the image of its sheaf projection.
Source: Stacks Project, Tags 04VG and 0F4L.
(blueprint: lem-a2-compact-support-termwise-projection).

Proof: precompose with the homotopy localization and use the defining factorization
of each exact derived functor. The composition comparison cancels the two source
factorizations, and the preceding termwise transpose identity identifies the remaining
map. Localization full faithfulness gives the result. -/
theorem compactSupportGraphDerivedProjection_termwise
    (A : Type (u + 1)) [CommRing A] {U X : Scheme.{u}} (f : U ⟶ X) [Etale f]
    (c : Compactification f)
    (a : etaleLowerShriek (ModuleCat.{u + 1} A) f inferInstance ⟶
      openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i ⋙
        lowerStar (ModuleCat.{u + 1} A) c.g) :
    compactSupportGraphDerivedProjection A f c a =
      (Functor.mapDerivedCategoryCompIso
        (etaleLowerShriek (ModuleCat.{u + 1} A) f inferInstance)
        (upperStar (ModuleCat.{u + 1} A) c.g)).inv ≫
      Functor.mapDerivedCategoryNatTrans (compactSupportGraphSheafProjection A f c a) := by
  let E := etaleLowerShriek (ModuleCat.{u + 1} A) f inferInstance
  let P := upperStar (ModuleCat.{u + 1} A) c.g
  let J := openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i
  apply Localization.natTrans_ext DerivedCategory.Qh
    (HomotopyCategory.quasiIso (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)) (.up ℤ))
  intro K
  rw [← cancel_epi ((Functor.mapDerivedCategoryCompIso E P).hom.app
    (DerivedCategory.Qh.obj K)), ← cancel_mono (J.mapDerivedCategoryFactorsh.hom.app K)]
  dsimp only [E, P, J]
  rw [compactSupportGraphDerivedProjection, graphProjectionLocalizationDesc_app]
  simp only [NatTrans.comp_app, Functor.comp_obj, Category.assoc]
  rw [Iso.hom_inv_id_app_assoc, Functor.mapDerivedCategoryNatTrans_fac,
    Iso.inv_hom_id_app]
  simp only [Functor.comp_obj, Category.comp_id]
  rw [compactSupportGraphProjectionOnHomotopy_termwise,
    Functor.mapDerivedCategoryCompIso_hom_app_factorsh_assoc]
  rw [Functor.mapHomotopyCategoryCompIso_refl_hom_app]
  simp only [Category.id_comp]

end AlgebraicGeometry.Etale
