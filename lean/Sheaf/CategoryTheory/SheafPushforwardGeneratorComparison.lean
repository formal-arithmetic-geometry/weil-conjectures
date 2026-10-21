/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q46
-/
module

public import Mathlib.CategoryTheory.Monoidal.Functor
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Sheaf.CategoryTheory.BraidedSheafTensorGenerators
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Functor

/-!
# The transported sheaf restriction maps on sheafification generators

Source: blueprint `sec-proetale-coefficients`,
`sk-def-sfb-module-pushforward-pullback/lem-sfb-pushforward-comp-monoidal.proof.md`,
second sentence (blueprint: lem-sfb-sheaf-pushforward-generator-comparison).

The restriction only assumes preservation of sheaves with the given coefficients.
Its lax structure is constructed using adjunction mates and counit transport.
-/

@[expose] public section

set_option autoImplicit false

universe w uA

open CategoryTheory CategoryTheory.MonoidalCategory

namespace CategoryTheory.Sheaf

variable {C D : Type w} [Category.{w} C] [Category.{w} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  {A : Type uA} [Category.{w} A] [Abelian A] [IsGrothendieckAbelian.{w} A]
  [MonoidalCategory A] [MonoidalClosed A] [BraidedCategory A]
  [HasWeakSheafify J A] [HasWeakSheafify K A]

/-- The actual tensor sheafification unit, transported along the prescribed object
identity. Source: blueprint pushforward-composition proof, second sentence
(blueprint: lem-sfb-sheaf-pushforward-generator-comparison). -/
noncomputable def BraidedTensorGenerators.tensorGenerator
    (T : BraidedTensorGenerators J A) (F G : Sheaf J A) :
    F.obj ⊗ G.obj ⟶ (T.monoidal.tensorObj F G).obj :=
  toSheafify J (F.obj ⊗ G.obj) ≫
    (eqToHom (T.tensorObj_eq F G).symm).hom

/-- The actual unit sheafification unit, transported along the prescribed object
identity. Source: blueprint pushforward-composition proof, second sentence
(blueprint: lem-sfb-sheaf-pushforward-generator-comparison). -/
noncomputable def BraidedTensorGenerators.unitGenerator
    (T : BraidedTensorGenerators J A) :
    𝟙_ (Cᵒᵖ ⥤ A) ⟶ T.monoidal.tensorUnit.obj :=
  toSheafify J (𝟙_ (Cᵒᵖ ⥤ A)) ≫ (eqToHom T.tensorUnit_eq.symm).hom

/-- Restriction on the full subcategory of sheaves when precomposition preserves
these sheaves. Source: blueprint pushforward-composition proof, second sentence
(blueprint: lem-sfb-sheaf-pushforward-generator-comparison). -/
def generatorRestriction (E : C ⥤ D)
    (hE : ∀ F : Sheaf K A, Presheaf.IsSheaf J (E.op ⋙ F.obj)) :
    Sheaf K A ⥤ Sheaf J A :=
  ObjectProperty.lift _
    (sheafToPresheaf K A ⋙ (Functor.whiskeringLeft _ _ A).obj E.op) hE

/-- The composite inclusion, restriction and sheafification is identified with
restriction by the sheafification counit. Source: blueprint pushforward-composition
proof, second sentence (blueprint: lem-sfb-sheaf-pushforward-generator-comparison). -/
noncomputable def generatorRestrictionCounitIso (E : C ⥤ D)
    (hE : ∀ F : Sheaf K A, Presheaf.IsSheaf J (E.op ⋙ F.obj)) :
    sheafToPresheaf K A ⋙ (Functor.whiskeringLeft _ _ A).obj E.op ⋙
      presheafToSheaf J A ≅ generatorRestriction E hE :=
  Functor.isoWhiskerLeft (generatorRestriction E hE)
      (asIso (sheafificationAdjunction J A).counit) ≪≫
    (generatorRestriction E hE).rightUnitor

/-- The specified lax structure: inclusion has the adjunction-mate structure,
restriction the pointwise strong structure, and sheafification its prescribed
strong structure; transport their composite along the counit isomorphism.
Source: blueprint pushforward-composition proof, second sentence
(blueprint: lem-sfb-sheaf-pushforward-generator-comparison). -/
@[instance_reducible]
noncomputable def generatorRestrictionLaxMonoidal
    (TC : BraidedTensorGenerators J A) (TD : BraidedTensorGenerators K A)
    (E : C ⥤ D) (hE : ∀ F : Sheaf K A, Presheaf.IsSheaf J (E.op ⋙ F.obj)) :
    @Functor.LaxMonoidal (Sheaf K A) _ TD.monoidal (Sheaf J A) _ TC.monoidal
      (generatorRestriction E hE) := by
  letI := TC.monoidal
  letI := TD.monoidal
  letI := TC.sheafification.toMonoidal
  letI := TD.sheafification.toMonoidal
  letI := (sheafificationAdjunction K A).rightAdjointLaxMonoidal
  exact Functor.LaxMonoidal.transport (generatorRestrictionCounitIso E hE)

/-- Tensor comparison of the specified counit-transported lax restriction.
Source: blueprint pushforward-composition proof, second sentence
(blueprint: lem-sfb-sheaf-pushforward-generator-comparison). -/
noncomputable def generatorRestrictionTensorComparison
    (TC : BraidedTensorGenerators J A) (TD : BraidedTensorGenerators K A)
    (E : C ⥤ D) (hE : ∀ F : Sheaf K A, Presheaf.IsSheaf J (E.op ⋙ F.obj))
    (F G : Sheaf K A) :
    TC.monoidal.tensorObj ((generatorRestriction E hE).obj F)
      ((generatorRestriction E hE).obj G) ⟶
        (generatorRestriction E hE).obj (TD.monoidal.tensorObj F G) :=
  @Functor.LaxMonoidal.μ (Sheaf K A) _ TD.monoidal (Sheaf J A) _ TC.monoidal
    (generatorRestriction E hE) (generatorRestrictionLaxMonoidal TC TD E hE) F G

/-- Unit comparison of the specified counit-transported lax restriction.
Source: blueprint pushforward-composition proof, second sentence
(blueprint: lem-sfb-sheaf-pushforward-generator-comparison). -/
noncomputable def generatorRestrictionUnitComparison
    (TC : BraidedTensorGenerators J A) (TD : BraidedTensorGenerators K A)
    (E : C ⥤ D) (hE : ∀ F : Sheaf K A, Presheaf.IsSheaf J (E.op ⋙ F.obj)) :
    TC.monoidal.tensorUnit ⟶ (generatorRestriction E hE).obj TD.monoidal.tensorUnit :=
  @Functor.LaxMonoidal.ε (Sheaf K A) _ TD.monoidal (Sheaf J A) _ TC.monoidal
    (generatorRestriction E hE) (generatorRestrictionLaxMonoidal TC TD E hE)

private theorem hom_of_heq {B : Type*} [Category B] {X X' Y Y' : B}
    (eX : X = X') (eY : Y = Y') (f : X ⟶ Y) (g : X' ⟶ Y') (h : HEq f g) :
    f = eqToHom eX ≫ g ≫ eqToHom eY.symm := by
  cases eX
  cases eY
  simpa using eq_of_heq h

private theorem tensorHom_prescribed (T : BraidedTensorGenerators J A)
    {F F' G G' : Sheaf J A} (f : F ⟶ F') (g : G ⟶ G') :
    let := T.monoidal
    f ⊗ₘ g = eqToHom (T.tensorObj_eq F G) ≫
      (presheafToSheaf J A).map (f.hom ⊗ₘ g.hom) ≫
        eqToHom (T.tensorObj_eq F' G').symm := by
  exact hom_of_heq (T.tensorObj_eq F G) (T.tensorObj_eq F' G') _ _
    (T.tensorHom_heq f g)

private theorem cotensorator_prescribed (T : BraidedTensorGenerators J A)
    (P Q : Cᵒᵖ ⥤ A) :
    let := T.monoidal
    let := T.sheafification.toMonoidal
    Functor.OplaxMonoidal.δ (presheafToSheaf J A) P Q =
      (presheafToSheaf J A).map (toSheafify J P ⊗ₘ toSheafify J Q) ≫
        eqToHom (T.tensorObj_eq _ _).symm := by
  simpa using hom_of_heq rfl (T.tensorObj_eq _ _) _ _ (T.cotensorator_heq P Q)

private theorem inclusion_tensor (T : BraidedTensorGenerators J A) (F G : Sheaf J A) :
    let := T.monoidal
    let := T.sheafification.toMonoidal
    let := (sheafificationAdjunction J A).rightAdjointLaxMonoidal
    Functor.LaxMonoidal.μ (sheafToPresheaf J A) F G = T.tensorGenerator F G := by
  let := T.monoidal
  let := T.sheafification.toMonoidal
  let := (sheafificationAdjunction J A).rightAdjointLaxMonoidal
  change Functor.LaxMonoidal.μ (sheafToPresheaf J A) F G = _
  rw [Adjunction.rightAdjointLaxMonoidal_μ, cotensorator_prescribed,
    tensorHom_prescribed]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  rw [← Functor.map_comp_assoc, tensorHom_comp_tensorHom]
  have h (H : Sheaf J A) :
      toSheafify J H.obj ≫ ((sheafificationAdjunction J A).counit.app H).hom =
        𝟙 H.obj := (sheafificationAdjunction J A).right_triangle_components H
  erw [h F, h G, id_tensorHom_id, Functor.map_id, Category.id_comp]
  rfl

private theorem inclusion_unit (T : BraidedTensorGenerators J A) :
    let := T.monoidal
    let := T.sheafification.toMonoidal
    let := (sheafificationAdjunction J A).rightAdjointLaxMonoidal
    Functor.LaxMonoidal.ε (sheafToPresheaf J A) = T.unitGenerator := by
  let := T.monoidal
  let := T.sheafification.toMonoidal
  let := (sheafificationAdjunction J A).rightAdjointLaxMonoidal
  have he : Functor.LaxMonoidal.ε (presheafToSheaf J A) =
      eqToHom T.tensorUnit_eq := by
    simpa using hom_of_heq T.tensorUnit_eq rfl _ _ T.unitComparison_heq
  have hi : Functor.OplaxMonoidal.η (presheafToSheaf J A) =
      eqToHom T.tensorUnit_eq.symm := by
    apply (cancel_epi (Functor.LaxMonoidal.ε (presheafToSheaf J A))).1
    rw [Functor.Monoidal.ε_η, he]
    simp
  change Functor.LaxMonoidal.ε (sheafToPresheaf J A) = _
  rw [Adjunction.rightAdjointLaxMonoidal_ε, hi]
  rfl

private theorem inverse_counits_tensor (T : BraidedTensorGenerators J A)
    (F G : Sheaf J A) :
    letI := T.monoidal
    letI := T.sheafification.toMonoidal
    (inv ((sheafificationAdjunction J A).counit.app F) ⊗ₘ
        inv ((sheafificationAdjunction J A).counit.app G)) ≫
      Functor.LaxMonoidal.μ (presheafToSheaf J A) F.obj G.obj =
        eqToHom (T.tensorObj_eq F G) := by
  let := T.monoidal
  let := T.sheafification.toMonoidal
  rw [tensorHom_prescribed]
  have hi (H : Sheaf J A) :
      (inv ((sheafificationAdjunction J A).counit.app H)).hom =
        toSheafify J H.obj := by
    change (sheafToPresheaf J A).map (inv _) = _
    rw [Functor.map_inv]
    exact (sheafificationAdjunction J A).inv_counit_map
  rw [hi F, hi G, Category.assoc, Category.assoc,
    ← reassoc_of% (cotensorator_prescribed T F.obj G.obj),
    Functor.Monoidal.δ_μ]
  simp

private theorem restriction_tensor_extension
    (TC : BraidedTensorGenerators J A) (TD : BraidedTensorGenerators K A)
    (E : C ⥤ D) (hE : ∀ F : Sheaf K A, Presheaf.IsSheaf J (E.op ⋙ F.obj))
    (F G : Sheaf K A) :
    generatorRestrictionTensorComparison TC TD E hE F G =
      eqToHom (TC.tensorObj_eq _ _) ≫
        (presheafToSheaf J A).map (Functor.whiskerLeft E.op (TD.tensorGenerator F G)) ≫
          (sheafificationAdjunction J A).counit.app
            ((generatorRestriction E hE).obj (TD.monoidal.tensorObj F G)) := by
  let := TC.monoidal
  let := TD.monoidal
  let := TC.sheafification.toMonoidal
  let := TD.sheafification.toMonoidal
  let := (sheafificationAdjunction K A).rightAdjointLaxMonoidal
  change (Functor.LaxMonoidal.transport (generatorRestrictionCounitIso E hE)).μ F G = _
  rw [Functor.LaxMonoidal.transport_μ]
  simp only [Functor.LaxMonoidal.comp_μ, inclusion_tensor]
  dsimp [generatorRestrictionCounitIso]
  have hr : Functor.LaxMonoidal.μ ((Functor.whiskeringLeft _ _ A).obj E.op)
      F.obj G.obj = 𝟙 _ := rfl
  rw [hr]
  erw [Functor.map_id]
  simp only [Category.id_comp, Category.comp_id, NatIso.isIso_inv_app, Category.assoc]
  erw [reassoc_of% (inverse_counits_tensor TC
    ((generatorRestriction E hE).obj F) ((generatorRestriction E hE).obj G))]

private theorem restriction_unit_extension
    (TC : BraidedTensorGenerators J A) (TD : BraidedTensorGenerators K A)
    (E : C ⥤ D) (hE : ∀ F : Sheaf K A, Presheaf.IsSheaf J (E.op ⋙ F.obj)) :
    generatorRestrictionUnitComparison TC TD E hE =
      eqToHom TC.tensorUnit_eq ≫
        (presheafToSheaf J A).map (Functor.whiskerLeft E.op TD.unitGenerator) ≫
          (sheafificationAdjunction J A).counit.app
            ((generatorRestriction E hE).obj TD.monoidal.tensorUnit) := by
  let := TC.monoidal
  let := TD.monoidal
  let := TC.sheafification.toMonoidal
  let := TD.sheafification.toMonoidal
  let := (sheafificationAdjunction K A).rightAdjointLaxMonoidal
  change (Functor.LaxMonoidal.transport (generatorRestrictionCounitIso E hE)).ε = _
  rw [Functor.LaxMonoidal.transport_ε]
  simp only [Functor.LaxMonoidal.comp_ε, inclusion_unit]
  dsimp [generatorRestrictionCounitIso]
  have hr : Functor.LaxMonoidal.ε ((Functor.whiskeringLeft _ _ A).obj E.op) =
      𝟙 _ := rfl
  have hc : Functor.LaxMonoidal.ε (presheafToSheaf J A) =
      eqToHom TC.tensorUnit_eq := by
    simpa using hom_of_heq TC.tensorUnit_eq rfl _ _ TC.unitComparison_heq
  rw [hr, hc]
  erw [Functor.map_id]
  simp

omit [Abelian A] [IsGrothendieckAbelian.{w} A] [MonoidalCategory A]
  [MonoidalClosed A] [BraidedCategory A] in
private theorem extension_generator {P : Cᵒᵖ ⥤ A} {H : Sheaf J A}
    (v : P ⟶ H.obj) :
    (sheafificationAdjunction J A).homEquiv P H
      ((presheafToSheaf J A).map v ≫ (sheafificationAdjunction J A).counit.app H) =
        v := (sheafificationAdjunction J A).homEquiv P H |>.apply_symm_apply v

/-- The transported tensor and unit comparisons extend the restricted actual
sheafification generators, uniquely. Source: blueprint pushforward-composition
proof, second sentence (blueprint: lem-sfb-sheaf-pushforward-generator-comparison).

Proof. 1. Expand the adjunction-mate tensor of inclusion as the adjoint of the
inverse sheafification tensorator followed by the tensor of counits. The generator
package identifies that inverse tensorator with sheafification of the tensor of
units; the triangle identities reduce the mate to the actual tensor generator.
The unit mate similarly equals the unit generator (`lem-sfb-monoidal-adjunction-mates`,
`lem-sfb-braided-sheaf-tensor-generators`, `def-weil-pbc-sheafification`).
2. Expand composite lax comparisons and counit transport. The inverse counits
on the inputs become the adjunction units under inclusion. Their tensor cancels
the strong sheafification tensorator, leaving the extension `ε_H a(v)`
(in right-to-left notation), where `v` is the restricted tensor generator.
The unit comparison gives the same extension formula for the unit generator.
3. Naturality of the sheafification unit and the triangle identity say that this
extension precomposed with the actual unit is `v`, giving both displayed equations.
4. Apply the two generator Hom bijections on the source site to get uniqueness
of both extensions. All equalities are in presheaf Hom sets; evaluation is never
asserted to preserve sheaf tensor products. -/
theorem generatorRestriction_comparison
    (TC : BraidedTensorGenerators J A) (TD : BraidedTensorGenerators K A)
    (E : C ⥤ D) (hE : ∀ F : Sheaf K A, Presheaf.IsSheaf J (E.op ⋙ F.obj)) :
    (∀ F G : Sheaf K A,
      TC.tensorGenerator ((generatorRestriction E hE).obj F)
          ((generatorRestriction E hE).obj G) ≫
        (generatorRestrictionTensorComparison TC TD E hE F G).hom =
          Functor.whiskerLeft E.op (TD.tensorGenerator F G) ∧
      ∀ h : TC.monoidal.tensorObj ((generatorRestriction E hE).obj F)
          ((generatorRestriction E hE).obj G) ⟶
            (generatorRestriction E hE).obj (TD.monoidal.tensorObj F G),
        TC.tensorGenerator ((generatorRestriction E hE).obj F)
            ((generatorRestriction E hE).obj G) ≫ h.hom =
          Functor.whiskerLeft E.op (TD.tensorGenerator F G) →
        h = generatorRestrictionTensorComparison TC TD E hE F G) ∧
    (TC.unitGenerator ≫ (generatorRestrictionUnitComparison TC TD E hE).hom =
        Functor.whiskerLeft E.op TD.unitGenerator ∧
      ∀ h : TC.monoidal.tensorUnit ⟶
          (generatorRestriction E hE).obj TD.monoidal.tensorUnit,
        TC.unitGenerator ≫ h.hom = Functor.whiskerLeft E.op TD.unitGenerator →
          h = generatorRestrictionUnitComparison TC TD E hE) := by
  have ht (F G : Sheaf K A) :
      TC.tensorGenerator ((generatorRestriction E hE).obj F)
          ((generatorRestriction E hE).obj G) ≫
        (generatorRestrictionTensorComparison TC TD E hE F G).hom =
          Functor.whiskerLeft E.op (TD.tensorGenerator F G) := by
    have h : (sheafificationAdjunction J A).homEquiv _ _
        (eqToHom (TC.tensorObj_eq _ _).symm ≫
          generatorRestrictionTensorComparison TC TD E hE F G) =
            Functor.whiskerLeft E.op (TD.tensorGenerator F G) := by
      rw [restriction_tensor_extension]
      simp only [← Category.assoc, eqToHom_trans, eqToHom_refl, Category.id_comp]
      exact extension_generator _
    rw [Adjunction.homEquiv_unit] at h
    change toSheafify J _ ≫ (eqToHom (TC.tensorObj_eq _ _).symm ≫
      generatorRestrictionTensorComparison TC TD E hE F G).hom = _ at h
    simpa only [BraidedTensorGenerators.tensorGenerator,
      ObjectProperty.FullSubcategory.comp_hom, Category.assoc] using h
  have hu : TC.unitGenerator ≫ (generatorRestrictionUnitComparison TC TD E hE).hom =
      Functor.whiskerLeft E.op TD.unitGenerator := by
    have h : (sheafificationAdjunction J A).homEquiv _ _
        (eqToHom TC.tensorUnit_eq.symm ≫
          generatorRestrictionUnitComparison TC TD E hE) =
            Functor.whiskerLeft E.op TD.unitGenerator := by
      rw [restriction_unit_extension]
      simp only [← Category.assoc, eqToHom_trans, eqToHom_refl, Category.id_comp]
      exact extension_generator _
    rw [Adjunction.homEquiv_unit] at h
    change toSheafify J _ ≫ (eqToHom TC.tensorUnit_eq.symm ≫
      generatorRestrictionUnitComparison TC TD E hE).hom = _ at h
    simpa only [BraidedTensorGenerators.unitGenerator,
      ObjectProperty.FullSubcategory.comp_hom, Category.assoc] using h
  refine ⟨fun F G ↦ ⟨ht F G, ?_⟩, hu, ?_⟩
  · intro h hh
    apply (cancel_epi (eqToHom (TC.tensorObj_eq _ _).symm)).1
    apply TC.tensorHom_ext ((generatorRestriction E hE).obj F)
      ((generatorRestriction E hE).obj G) _
    simpa only [BraidedTensorGenerators.tensorGenerator,
      ObjectProperty.FullSubcategory.comp_hom, Category.assoc] using hh.trans (ht F G).symm
  · intro h hh
    apply (cancel_epi (eqToHom TC.tensorUnit_eq.symm)).1
    apply TC.unitHom_ext
    simpa only [BraidedTensorGenerators.unitGenerator,
      ObjectProperty.FullSubcategory.comp_hom, Category.assoc] using hh.trans hu.symm

end CategoryTheory.Sheaf
