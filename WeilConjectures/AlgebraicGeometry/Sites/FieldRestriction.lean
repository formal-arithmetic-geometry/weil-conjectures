/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.FieldFiltration

/-!
# Restricting étale sheaves to a finite separable extension

Let `L/K` be a finite separable field extension and `M` an étale sheaf on `Spec K`. The
restriction `M|_L` of `M` along the étale morphism `Spec L ⟶ Spec K` has sections
`M|_L(Spec E) = M(Spec E)` over every étale `L`-algebra `E`, viewed as étale `K`-algebra
(`AlgebraicGeometry.Scheme.etaleSpecMapObjIso`). In particular a sheaf split by an extension
`N` of `L` stays split by `N` after restriction to `L`
(`AlgebraicGeometry.Scheme.IsSplitBy.localizationRestriction`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme

variable {K L : Type u} [Field K] [Field L] [Algebra K L] [Algebra.Etale K L]

/-- The étale `L`-scheme `Spec E`, viewed as an étale `K`-scheme, is the étale `K`-scheme
`Spec E`. -/
noncomputable def etaleSpecMapObjIso (E : Type u) [CommRing E] [Algebra L E] [Algebra K E]
    [IsScalarTower K L E] [Algebra.Etale L E] [Algebra.Etale K E] :
    (MorphismProperty.Over.map ⊤ (etaleSpec K L).prop).obj (etaleSpec L E) ≅ etaleSpec K E :=
  MorphismProperty.Over.isoMk (Iso.refl _) (by
    change 𝟙 _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [Category.id_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      ← IsScalarTower.algebraMap_eq])

/-- Viewing a morphism of étale `L`-schemes `Spec B ⟶ Spec A` as a morphism of étale
`K`-schemes. -/
lemma map_etaleSpecMap {A B : Type u} [CommRing A] [CommRing B] [Algebra L A] [Algebra L B]
    [Algebra K A] [Algebra K B] [IsScalarTower K L A] [IsScalarTower K L B] [Algebra.Etale L A]
    [Algebra.Etale L B] [Algebra.Etale K A] [Algebra.Etale K B] (β : A →ₐ[L] B) :
    (MorphismProperty.Over.map ⊤ (etaleSpec K L).prop).map (etaleSpecMap β) =
      (etaleSpecMapObjIso B).hom ≫ etaleSpecMap (β.restrictScalars K) ≫
        (etaleSpecMapObjIso A).inv := by
  apply MorphismProperty.Over.Hom.ext
  change Spec.map _ = 𝟙 _ ≫ Spec.map _ ≫ 𝟙 _
  rw [Category.id_comp, Category.comp_id]
  rfl

variable (M : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u + 1})

/-- The sections of the restriction `M|_L` over an étale `L`-algebra `E` are the sections of `M`
over `E`. -/
noncomputable def localizationRestrictionSectionsIso (E : Type u) [CommRing E] [Algebra L E]
    [Algebra K E] [IsScalarTower K L E] [Algebra.Etale L E] [Algebra.Etale K E] :
    ((Etale.localizationRestriction AddCommGrpCat.{u + 1} (etaleSpec K L).hom
      (etaleSpec K L).prop).obj M).obj.obj (op (etaleSpec L E)) ≅
        M.obj.obj (op (etaleSpec K E)) :=
  (M.obj.mapIso (etaleSpecMapObjIso E).op).symm

/-- **Split sheaves stay split after restriction.** If `M` is split by an extension `N` of `L`,
so is its restriction to `L`. -/
theorem IsSplitBy.localizationRestriction (N : Type u) [Field N] [Algebra L N] [Algebra K N]
    [IsScalarTower K L N] [Algebra.Etale L N] [Algebra.Etale K N] (hM : IsSplitBy N M) :
    IsSplitBy N ((Etale.localizationRestriction AddCommGrpCat.{u + 1} (etaleSpec K L).hom
      (etaleSpec K L).prop).obj M) := by
  intro E _ _ _ β
  let : Algebra K E := ((algebraMap L E).comp (algebraMap K L)).toAlgebra
  have : IsScalarTower K L E := .of_algebraMap_eq fun _ ↦ rfl
  have : Algebra.Etale K E := Algebra.Etale.comp K L E
  have hb := hM E (β.restrictScalars K)
  change Function.Bijective (M.obj.map ((MorphismProperty.Over.map ⊤
    (etaleSpec K L).prop).map (etaleSpecMap β)).op)
  rw [map_etaleSpecMap, op_comp, op_comp, Functor.map_comp, Functor.map_comp]
  simp only [AddCommGrpCat.hom_comp, AddMonoidHom.coe_comp]
  refine (ConcreteCategory.bijective_of_isIso _).comp
    (hb.comp (ConcreteCategory.bijective_of_isIso _))

end AlgebraicGeometry.Scheme
