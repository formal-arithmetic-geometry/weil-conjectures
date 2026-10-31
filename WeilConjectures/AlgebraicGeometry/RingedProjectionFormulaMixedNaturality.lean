/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectionFormulaArrows
import WeilConjectures.AlgebraicGeometry.RingedProjectionFormulaResolutionNaturality
import WeilConjectures.Algebra.Homology.KFlatResolutionGeneral

/-! Naturality of the mixed tensor representative. -/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace SheafOfModules
set_option backward.isDefEq.respectTransparency true
set_option synthInstance.maxSize 4096
attribute [local instance 2000] Limits.instHasColimitOfHasColimitsOfShape
  Limits.instHasLimitOfHasLimitsOfShape

/-- The mixed tensor representative is natural in its unrestricted first input.
Source: Stacks 07A4 and the common-resolution characterization of
`mixedTensorRepresentative` in ProjectionFormulaArrows.
(blueprint: new-lem-weil-pbc-mixed-tensor-representative-naturality).
Proof: regard the two sides as functors on complexes with the coefficient F fixed.
The restricted comparison is the inverse of rR, whose naturality is the naturality
of a natural isomorphism. Every complex has an epimorphic flat-term K-flat resolution,
and the first functor inverts quasi-isomorphisms. The defining characterization of
mixedTensorRepresentative supplies its square at every such resolution. Apply the
common-resolution naturality theorem. -/
theorem mixedTensorRepresentative_naturality
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{u}) [HasDerivedCategory.{w} (SheafOfModules.{u} ((sheafCompose J
      (forget₂ CommRingCat.{u} RingCat.{u})).obj R))]
  (PR : ObjectProperty (CochainComplex (SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u}
      RingCat.{u})).obj R)) ℤ))
  (hPR : ∀ P, PR P ↔ P.IsAcyclicTensorKFlat ∧ ∀ n : ℤ, (P.X n).IsFlat)
  (TR : DerivedCategory (SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u}
      RingCat.{u})).obj R)) × DerivedCategory (SheafOfModules.{u} ((sheafCompose J (forget₂
      CommRingCat.{u} RingCat.{u})).obj R)) ⥤ DerivedCategory (SheafOfModules.{u} ((sheafCompose J
      (forget₂ CommRingCat.{u} RingCat.{u})).obj R)))
  (rR : (PR.ι.prod PR.ι) ⋙ Functor.uncurry.obj
    ((@curriedTensor (SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj
      R)) _ (monoidalCategory R)).map₂HomologicalComplex
      (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)) ⋙ DerivedCategory.Q ≅
        ((PR.ι ⋙ DerivedCategory.Q).prod (PR.ι ⋙ DerivedCategory.Q)) ⋙ TR)
    {A B : CochainComplex (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ}
    (p : A ⟶ B)
    (F : CochainComplex (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ) (hf : PR F) :
    TR.map (Prod.mkHom (DerivedCategory.Q.map p) (𝟙 (DerivedCategory.Q.obj F))) ≫
        (mixedTensorRepresentative R PR hPR TR rR B F hf).hom =
      (mixedTensorRepresentative R PR hPR TR rR A F hf).hom ≫
        DerivedCategory.Q.map (HomologicalComplex.mapBifunctorMap p (𝟙 F)
          (@curriedTensor (SheafOfModules.{u}
            ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) _
              (monoidalCategory R)) (.up ℤ)) := by
  let M := SheafOfModules.{u}
    ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)
  let : MonoidalCategory M := monoidalCategory R
  let : MonoidalPreadditive M := ringedTensorPreadditive R
  let G : CochainComplex M ℤ ⥤ DerivedCategory M :=
    { obj := fun X ↦ TR.obj (DerivedCategory.Q.obj X, DerivedCategory.Q.obj F)
      map := fun q ↦ TR.map (Prod.mkHom (DerivedCategory.Q.map q) (𝟙 _))
      map_id := fun X ↦ by simp
      map_comp := fun f g ↦ by simp [← Functor.map_comp] }
  let : ∀ (K K' : CochainComplex M ℤ),
      HomologicalComplex.HasMapBifunctor K K' (curriedTensor M) (.up ℤ) :=
    fun K K' ↦ inferInstance
  let T : CochainComplex M ℤ ⥤ DerivedCategory M :=
    ((curriedTensor M).map₂CochainComplex.flip.obj F) ⋙ DerivedCategory.Q
  let b : PR.ι ⋙ G ⟶ PR.ι ⋙ T :=
    { app := fun X ↦ rR.inv.app (X, ⟨F, hf⟩)
      naturality := by
        intro X Y f
        have hn := rR.inv.naturality (Prod.mkHom f (𝟙 (⟨F, hf⟩ : PR.FullSubcategory)))
        simpa only [G, T, Functor.comp_map, Functor.prod_map, Functor.prod_obj,
          ObjectProperty.ι_obj, ObjectProperty.ι_map, Functor.uncurry_obj_map,
          ObjectProperty.FullSubcategory.id_hom, CategoryTheory.Functor.map_id,
          Category.comp_id, Functor.flip_obj_map, Iso.symm_hom, Iso.app_inv] using hn }
  have hres (K : CochainComplex M ℤ) :
      ∃ (P : CochainComplex M ℤ) (_hp : PR P) (q : P ⟶ K), QuasiIso q ∧ Epi q := by
    obtain ⟨P, q, hk, ht, hq, he⟩ := CochainComplex.exists_isKFlatResolutionGeneral K
    exact ⟨P, (hPR P).2 ⟨hk, ht⟩, q, hq, HomologicalComplex.epi_of_epi_f q he⟩
  have hG {X Y : CochainComplex M ℤ} (q : X ⟶ Y) (hq : QuasiIso q) :
      IsIso (G.map q) := by
    have : IsIso (DerivedCategory.Q.{w}.map q) :=
      (DerivedCategory.isIso_Q_map_iff_quasiIso M q).2 hq
    change IsIso (TR.map (Prod.mkHom (DerivedCategory.Q.map q) (𝟙 _)))
    have : IsIso (Prod.mkHom (DerivedCategory.Q.map q) (𝟙 (DerivedCategory.Q.obj F))) :=
      (isIso_prod_iff _ _).2 ⟨by assumption, by infer_instance⟩
    infer_instance
  exact resolutionComparison_naturality PR G T b hres hG
    (fun X ↦ (mixedTensorRepresentative R PR hPR TR rR X F hf).hom)
    (fun K P hp q hq ↦ Classical.choose_spec
      (mixedTensorRepresentative_existsUnique R PR hPR TR rR K F hf).exists P hp q hq) p

end SheafOfModules
