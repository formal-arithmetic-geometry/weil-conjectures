/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S9
-/
module

public import Sheaf.CategoryTheory.DerivedCategory.PerfectScalarTensorCoherence
public import Mathlib.CategoryTheory.Monoidal.Subcategory

/-! # The normalized monoidal scalar functor on perfect objects

Source: the balanced scalar coherence construction, Stacks 06Y6 and 0GWN
(blueprint: lem-sf-perfect-scalar-monoidal-functor).
-/

@[expose] public noncomputable section

set_option autoImplicit false

set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.unusedSimpArgs false

universe u c h
open CategoryTheory CategoryTheory.MonoidalCategory
namespace DerivedCategory.PerfectScalar

/-- The named scalar data satisfies all its recorded coherence equations. -/
theorem coherenceData_normalized : coherenceData.{u, u}.Normalized := by
  unfold coherenceData
  exact perfect_scalar_tensor_coherence_data.exists.choose_spec

/-- Perfectness as an existing object property. -/
abbrev perfectProperty (R : CommRingCat.{u}) : ObjectProperty (D.{u, u} R) :=
  IsPerfectRingComplex

/-- Closure of the perfect subcategory uses the recorded scalar coherence data. -/
instance perfectProperty_monoidal (R : CommRingCat.{u}) : (perfectProperty R).IsMonoidal where
  prop_unit := coherenceData.{u, u}.unitPerfect R
  prop_tensor P Q hP hQ := coherenceData.{u, u}.tensorPerfect R P Q hP hQ

/-- Restrict the actual scalar functor to the full perfect source subcategory. -/
def perfectFunctor {R S : CommRingCat.{u}} (f : R ⟶ S) :
    (perfectProperty R).FullSubcategory ⥤ D.{u, u} S :=
  (perfectProperty R).ι ⋙ B f

/-- The full perfect subcategory has the underlying associator.
Source: full monoidal subcategories (blueprint: lem-sf-perfect-scalar-monoidal-functor). -/
theorem perfect_associator_hom (R : CommRingCat.{u})
    (P Q Z : (perfectProperty R).FullSubcategory) :
    ((α_ P Q Z).hom).hom = (α_ P.obj Q.obj Z.obj).hom := by
  rfl

/-- The full perfect subcategory has the underlying left unitor.
Source: full monoidal subcategories (blueprint: lem-sf-perfect-scalar-monoidal-functor). -/
theorem perfect_leftUnitor_inv (R : CommRingCat.{u})
    (P : (perfectProperty R).FullSubcategory) :
    ((λ_ P).inv).hom = (λ_ P.obj).inv := by
  rfl

/-- Lift a specified perfect-valued functor without changing its morphisms. -/
def perfectLift {J : Type*} [Category J] {R : CommRingCat.{u}}
    (F : J ⥤ D.{u, u} R) (hF : ∀ X, IsPerfectRingComplex (F.obj X)) :
    J ⥤ (perfectProperty R).FullSubcategory :=
  ObjectProperty.lift _ F hF

/-- A strong monoidal comparison lifts to the full perfect subcategory. -/
def perfectLiftCore {J : Type*} [Category J] [MonoidalCategory J]
    {R : CommRingCat.{u}} (F : J ⥤ D.{u, u} R)
    (hF : ∀ X, IsPerfectRingComplex (F.obj X)) (cF : F.CoreMonoidal) :
    (perfectLift F hF).CoreMonoidal where
  εIso := ObjectProperty.isoMk _ cF.εIso
  μIso X Y := ObjectProperty.isoMk _ (cF.μIso X Y)
  μIso_hom_natural_left f X := by
    apply ObjectProperty.hom_ext
    exact cF.μIso_hom_natural_left f X
  μIso_hom_natural_right X f := by
    apply ObjectProperty.hom_ext
    exact cF.μIso_hom_natural_right X f
  associativity X Y Z := by
    apply ObjectProperty.hom_ext
    convert cF.associativity X Y Z using 1 <;> rfl
  left_unitality X := by
    apply ObjectProperty.hom_ext
    convert cF.left_unitality X using 1 <;> rfl
  right_unitality X := by
    apply ObjectProperty.hom_ext
    convert cF.right_unitality X using 1 <;> rfl

/-- The canonical balanced tensor and unit maps form an oplax monoidal functor. -/
@[instance_reducible] def perfectFunctorOplax {R S : CommRingCat.{u}} (f : R ⟶ S) :
    (perfectFunctor f).OplaxMonoidal where
  η := (coherenceData.{u, u}.unit f).hom
  δ P Q := (coherenceData.{u, u}.tensor f P.obj Q.obj P.property Q.property).hom
  δ_natural_left := by
    intro P Q a Z
    have hn := coherenceData_normalized.{u}.1 f P.obj Z.obj Q.obj Z.obj
      P.property Z.property Q.property Z.property a.hom (𝟙 Z.obj)
    change _ ≫ (B.{u, u} f).map a.hom ▷ (B.{u, u} f).obj Z.obj =
      (B.{u, u} f).map (a.hom ▷ Z.obj) ≫ _
    rw [(B.{u, u} f).map_id, tensorHom_id, tensorHom_id] at hn
    exact hn.symm
  δ_natural_right := by
    intro P Q Z a
    have hn := coherenceData_normalized.{u}.1 f Z.obj P.obj Z.obj Q.obj
      Z.property P.property Z.property Q.property (𝟙 Z.obj) a.hom
    change _ ≫ (B.{u, u} f).obj Z.obj ◁ (B.{u, u} f).map a.hom =
      (B.{u, u} f).map (Z.obj ◁ a.hom) ≫ _
    rw [(B.{u, u} f).map_id, id_tensorHom, id_tensorHom] at hn
    exact hn.symm
  oplax_associativity P Q Z := by
    have hn := coherenceData_normalized.{u}.2.2.2.2.2.2.2.1 f P.obj Q.obj Z.obj
      P.property Q.property Z.property
    dsimp only [perfectFunctor, Functor.comp_obj, Functor.comp_map,
      ObjectProperty.ι_obj, ObjectProperty.ι_map]
    erw [perfect_associator_hom]
    convert hn using 1 <;> rfl
  oplax_left_unitality P := by
    dsimp only [perfectFunctor, Functor.comp_obj, Functor.comp_map,
      ObjectProperty.ι_obj, ObjectProperty.ι_map]
    rw [perfect_leftUnitor_inv]
    have hu := coherenceData_normalized.{u}.2.2.2.2.2.2.2.2.2.1 f P.obj P.property
    have hunit : (𝟙_ (perfectProperty R).FullSubcategory).obj = 𝟙_ (D.{u, u} R) := rfl
    try simp_rw [hunit]
    apply (cancel_mono (λ_ ((B.{u, u} f).obj P.obj)).hom).1
    simp only [Category.assoc, Iso.inv_hom_id]
    have hu' := congrArg (fun t ↦ (B.{u, u} f).map (λ_ P.obj).inv ≫ t) hu
    simp only [← Functor.map_comp, Iso.inv_hom_id, Functor.map_id] at hu'
    convert hu'.symm using 1 <;> first | rfl | exact ((B f).map_id _).symm
  oplax_right_unitality P := by
    dsimp only [perfectFunctor, Functor.comp_obj, Functor.comp_map,
      ObjectProperty.ι_obj, ObjectProperty.ι_map]
    have hu := coherenceData_normalized.{u}.2.2.2.2.2.2.2.2.2.2.1 f P.obj P.property
    have he : ((ρ_ P).inv).hom = (ρ_ P.obj).inv := rfl
    rw [he]
    have hunit : (𝟙_ (perfectProperty R).FullSubcategory).obj = 𝟙_ (D.{u, u} R) := rfl
    try simp_rw [hunit]
    apply (cancel_mono (ρ_ ((B.{u, u} f).obj P.obj)).hom).1
    simp only [Category.assoc, Iso.inv_hom_id]
    have hu' := congrArg (fun t ↦ (B.{u, u} f).map (ρ_ P.obj).inv ≫ t) hu
    simp only [← Functor.map_comp, Iso.inv_hom_id, Functor.map_id] at hu'
    convert hu'.symm using 1 <;> first | rfl | exact ((B f).map_id _).symm

attribute [local instance] perfectFunctorOplax

/-- Invertibility of the balanced maps yields the canonical strong tensor structure. -/
def perfectFunctorCore {R S : CommRingCat.{u}} (f : R ⟶ S) :
    (perfectFunctor f).CoreMonoidal := by
  have : IsIso (Functor.OplaxMonoidal.η (perfectFunctor f)) := by
    change IsIso (coherenceData.{u, u}.unit f).hom
    infer_instance
  have : ∀ P Q, IsIso (Functor.OplaxMonoidal.δ (perfectFunctor f) P Q) :=
    fun P Q ↦ by
      change IsIso (coherenceData.{u, u}.tensor f P.obj Q.obj P.property Q.property).hom
      infer_instance
  exact Functor.CoreMonoidal.ofOplaxMonoidal (perfectFunctor f)


/-- Compose a perfect-valued tensor comparison with scalar extension once, retaining
its named core so consumers do not reconstruct the monoidal typeclass dictionaries.
Source: balanced scalar composition (blueprint: lem-sf-perfect-scalar-monoidal-functor). -/
@[irreducible] def perfectCompositeCore {J : Type c} [Category.{h} J] [MonoidalCategory J]
    {R S : CommRingCat.{u}} (F : J ⥤ D.{u, u} R)
    (hF : ∀ X, IsPerfectRingComplex (F.obj X)) (cF : F.CoreMonoidal) (f : R ⟶ S) :
    (F ⋙ B f).CoreMonoidal := by
  letI := (perfectLiftCore F hF cF).toMonoidal
  letI := (perfectFunctorCore f).toMonoidal
  exact Functor.CoreMonoidal.ofOplaxMonoidal (perfectLift F hF ⋙ perfectFunctor f)

end DerivedCategory.PerfectScalar
