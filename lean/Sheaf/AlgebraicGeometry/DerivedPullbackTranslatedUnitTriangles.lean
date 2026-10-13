/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J3
-/
module

public import Sheaf.AlgebraicGeometry.DerivedPullback
public import Sheaf.AlgebraicGeometry.SchemeCanonicalShiftUnitIso
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.Functor
public import Mathlib.CategoryTheory.Triangulated.Functor
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Noetherian
import Sheaf.AlgebraicGeometry.DerivedPullbackTranslatedUnitKFlatCones
import Sheaf.AlgebraicGeometry.KFlatLocalizedConePresentation

/-! # Distinguished triangles for the translated-unit comparison

Source: Stacks Project, Tag 06YJ, mapping-cone exactness; translated-unit
comparison in lem-sc-derived-pullback-tensor-unit-shift.
(blueprint: lem-sc-derived-pullback-translated-unit-triangles).
-/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated MonoidalCategory
namespace AlgebraicGeometry

private noncomputable def translatedUnitIso {Z Y : Scheme.{u}} (f : Z ⟶ Y)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [Functor.Monoidal (derivedPullback f)]
    (e : (derivedPullback f).obj ((𝟙_ (schemeDerivedCategory Y))⟦(1 : ℤ)⟧) ≅
      (𝟙_ (schemeDerivedCategory Z))⟦(1 : ℤ)⟧)
    (K : schemeDerivedCategory Y) :
    (derivedPullback f).obj (K⟦(1 : ℤ)⟧) ≅ ((derivedPullback f).obj K)⟦(1 : ℤ)⟧ :=
  (derivedPullback f).mapIso (schemeCanonicalShiftUnitIso Y K).symm ≪≫
    asIso (Functor.OplaxMonoidal.δ (derivedPullback f)
      ((𝟙_ (schemeDerivedCategory Y))⟦(1 : ℤ)⟧) K) ≪≫
    tensorIso e (Iso.refl _) ≪≫ schemeCanonicalShiftUnitIso Z ((derivedPullback f).obj K)

private theorem unit_shift_naturality (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    {K N : schemeDerivedCategory X} (b : K ⟶ N) :
    (schemeCanonicalShiftUnitIso X K).hom ≫ b⟦(1 : ℤ)⟧' =
      ((𝟙_ (schemeDerivedCategory X))⟦(1 : ℤ)⟧) ◁ b ≫
        (schemeCanonicalShiftUnitIso X N).hom := by
  let := schemeCanonicalTensorShift X
  let : ∀ M : schemeDerivedCategory X, (tensorRight M).CommShift ℤ :=
    fun M ↦ Functor.CommShift₂.commShiftFlipObj (h := .int) M
  have : NatTrans.CommShift ((curriedTensor (schemeDerivedCategory X)).flip.map b) ℤ :=
    Functor.CommShift₂.commShift_flip_map (h := .int) b
  dsimp [schemeCanonicalShiftUnitIso]
  simp only [Category.assoc]
  rw [← Functor.map_comp, ← leftUnitor_naturality, Functor.map_comp]
  simpa only [Category.assoc, tensorRight, Functor.flip, curriedTensor] using
    congrArg (fun g ↦ g ≫ (shiftFunctor (schemeDerivedCategory X) (1 : ℤ)).map (λ_ N).hom)
      (NatTrans.shift_app_comm ((curriedTensor (schemeDerivedCategory X)).flip.map b)
        (1 : ℤ) (𝟙_ (schemeDerivedCategory X)))

private theorem unit_shift_inv_naturality (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    {K N : schemeDerivedCategory X} (b : K ⟶ N) :
    b⟦(1 : ℤ)⟧' ≫ (schemeCanonicalShiftUnitIso X N).inv =
      (schemeCanonicalShiftUnitIso X K).inv ≫
        ((𝟙_ (schemeDerivedCategory X))⟦(1 : ℤ)⟧) ◁ b := by
  apply (cancel_epi (schemeCanonicalShiftUnitIso X K).hom).1
  rw [← Category.assoc, unit_shift_naturality]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id, Iso.hom_inv_id_assoc]

private theorem tensor_unit_shift_naturality {Z Y : Scheme.{u}} (f : Z ⟶ Y)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [Functor.Monoidal (derivedPullback f)]
    (e : (derivedPullback f).obj ((𝟙_ (schemeDerivedCategory Y))⟦(1 : ℤ)⟧) ≅
      (𝟙_ (schemeDerivedCategory Z))⟦(1 : ℤ)⟧)
    {K N : schemeDerivedCategory Y} (b : K ⟶ N) :
    (derivedPullback f).map (b⟦(1 : ℤ)⟧') ≫
        (translatedUnitIso f e N).hom =
      (translatedUnitIso f e K).hom ≫
        ((derivedPullback f).map b)⟦(1 : ℤ)⟧' := by
  dsimp only [translatedUnitIso, Iso.trans_hom, Functor.mapIso_hom,
    Iso.symm_hom, asIso_hom]
  simp only [tensorIso, Iso.refl_hom, tensorHom_def, whiskerLeft_id,
    Category.comp_id, Category.assoc]
  rw [← (derivedPullback f).map_comp_assoc, unit_shift_inv_naturality,
    Functor.map_comp_assoc, ← Functor.OplaxMonoidal.δ_natural_right_assoc]
  rw [whisker_exchange_assoc, ← unit_shift_naturality]


/-- The translated-unit comparison can be normalized to preserve distinguished
localized homotopy triangles at degree one. No coherent integer-shift structure
or assertion about all derived triangles is assumed here.

Source: Stacks Project, Tag 06YJ; the mapping-cone part of the translated-unit
argument of lem-sc-derived-pullback-tensor-unit-shift.
(blueprint: lem-sc-derived-pullback-translated-unit-triangles).

Proof. Choose the shifted-unit comparison supplied by the K-flat cone
calculation. The canonical tensor-shift naturality and the left-unitor equation
give naturality of the source and target rewrites. Tensorator naturality and
whisker exchange then give naturality of their displayed composite. Present the
localized homotopy triangle as the localized cone of a map between K-flat
complexes, using localization right fractions and K-flat resolutions. Apply the
cone calculation to that map. Map the three components of the presentation
isomorphism by pullback. Its first two squares follow by functoriality. Its third
square follows by the naturality just proved, followed by the image of the
original connecting-map square. These components therefore give an isomorphism
of the displayed pullback triangles. Transport the distinguished cone image
along it. No integer-shift extension or assertion of exactness for an arbitrary
shift structure is used. -/
theorem exists_derivedPullback_translatedUnit_triangles
    {Z Y : Scheme.{u}} [IsNoetherian Z] [IsNoetherian Y] (f : Z ⟶ Y) [IsProper f]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [Functor.Monoidal (derivedPullback f)] :
    ∃ e : (derivedPullback f).obj ((𝟙_ (schemeDerivedCategory Y))⟦(1 : ℤ)⟧) ≅
        (𝟙_ (schemeDerivedCategory Z))⟦(1 : ℤ)⟧,
      ∀ T₀ : Triangle
          (HomotopyCategory (SheafOfModules.{u} (moduleRings Y.toRingedSpace))
            (ComplexShape.up ℤ)),
        T₀ ∈ distTriang (HomotopyCategory
          (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (ComplexShape.up ℤ)) →
        let Qh : HomotopyCategory
            (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (ComplexShape.up ℤ) ⥤
            schemeDerivedCategory Y := DerivedCategory.Qh
        let T := Qh.mapTriangle.obj T₀
        Triangle.mk ((derivedPullback f).map T.mor₁) ((derivedPullback f).map T.mor₂)
          ((derivedPullback f).map T.mor₃ ≫
            ((derivedPullback f).mapIso (schemeCanonicalShiftUnitIso Y T.obj₁).symm ≪≫
              asIso (Functor.OplaxMonoidal.δ (derivedPullback f)
                ((𝟙_ (schemeDerivedCategory Y))⟦(1 : ℤ)⟧) T.obj₁) ≪≫
              tensorIso e (Iso.refl _) ≪≫
              schemeCanonicalShiftUnitIso Z ((derivedPullback f).obj T.obj₁)).hom) ∈
          distTriang (schemeDerivedCategory Z) := by
  obtain ⟨e, he⟩ := exists_derivedPullback_translatedUnit_kFlat_cones f
  refine ⟨e, ?_⟩
  intro T₀ hT₀
  let Qh : HomotopyCategory
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (ComplexShape.up ℤ) ⥤
      schemeDerivedCategory Y := DerivedCategory.Qh
  obtain ⟨P, Q, p, hP, hQ, ⟨i⟩⟩ := exists_kFlat_localized_cone_presentation Y T₀ hT₀
  let F := derivedPullback f
  let image (T : Triangle (schemeDerivedCategory Y)) : Triangle (schemeDerivedCategory Z) :=
    Triangle.mk (F.map T.mor₁) (F.map T.mor₂)
      (F.map T.mor₃ ≫ (translatedUnitIso f e T.obj₁).hom)
  have hcone : image (Qh.mapTriangle.obj (CochainComplex.mappingCone.triangleh p)) ∈
      distTriang (schemeDerivedCategory Z) := he P Q p hP hQ
  change image (Qh.mapTriangle.obj T₀) ∈ distTriang (schemeDerivedCategory Z)
  apply CategoryTheory.Pretriangulated.isomorphic_distinguished _ hcone _
  refine Triangle.isoMk _ _ (F.mapIso (Triangle.π₁.mapIso i))
    (F.mapIso (Triangle.π₂.mapIso i)) (F.mapIso (Triangle.π₃.mapIso i)) ?_ ?_ ?_
  · change F.map _ ≫ F.map i.hom.hom₂ = F.map i.hom.hom₁ ≫ F.map _
    simpa only [← F.map_comp] using congrArg F.map i.hom.comm₁
  · change F.map _ ≫ F.map i.hom.hom₃ = F.map i.hom.hom₂ ≫ F.map _
    simpa only [← F.map_comp] using congrArg F.map i.hom.comm₂
  · change (F.map _ ≫ (translatedUnitIso f e _).hom) ≫
        (F.map i.hom.hom₁)⟦(1 : ℤ)⟧' =
      F.map i.hom.hom₃ ≫ F.map _ ≫ (translatedUnitIso f e _).hom
    rw [Category.assoc, ← tensor_unit_shift_naturality f e i.hom.hom₁]
    simpa only [Functor.map_comp, Category.assoc] using
      congrArg (fun b ↦ F.map b ≫ (translatedUnitIso f e
        (Qh.mapTriangle.obj (CochainComplex.mappingCone.triangleh p)).obj₁).hom)
        i.hom.comm₃

end AlgebraicGeometry
