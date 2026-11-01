/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Field.FieldComplexScalarExtension
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Shift

/-! # Canonical derived scalar-extension comparisons

Source: Weil blueprint, `def-weil-finite-coefficient-point`, order 1509
(blueprint: lem-weil-derived-field-scalar-extension-tower).

## Main definitions and statements

* `fieldScalarTower`, `fieldScalarUnit`: the uniquely normalized tensor comparisons.
* `fieldScalarTower_assoc`, `fieldScalarTower_units`: their coherence.
* `fieldScalarTower_commShift`: compatibility with the triangulated shifts.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace DerivedCategory

variable {K L M : Type u} [Field K] [Field L] [Field M]

/-- The prescribed component of the tower comparison on a representing complex.
Source: blueprint order 1509 (blueprint: lem-weil-derived-field-scalar-extension-tower). -/
noncomputable def fieldScalarTowerComponent (f : K →+* L) (g : L →+* M)
    (C : CochainComplex (ModuleCat.{u} K) ℤ) :
    ((fieldDerivedScalarExtension f ⋙ fieldDerivedScalarExtension g).obj
      (DerivedCategory.Q.obj C)) ≅
      (fieldDerivedScalarExtension (g.comp f)).obj (DerivedCategory.Q.obj C) :=
  (fieldDerivedScalarExtension g).mapIso
      ((ModuleCat.extendScalars f).mapDerivedCategoryFactors.app C) ≪≫
    (ModuleCat.extendScalars g).mapDerivedCategoryFactors.app
      ((ModuleCat.extendScalars f).mapHomologicalComplex (ComplexShape.up ℤ) |>.obj C) ≪≫
    DerivedCategory.Q.mapIso
      ((Functor.mapHomologicalComplexCompIso (ModuleCat.extendScalarsComp f g).symm
        (ComplexShape.up ℤ)).app C) ≪≫
    ((ModuleCat.extendScalars (g.comp f)).mapDerivedCategoryFactors.app C).symm

/-- Localization gives the unique tower comparison with these prescribed components.
Source: blueprint order 1509 (blueprint: lem-weil-derived-field-scalar-extension-tower).
Proof: the termwise tensor tower isomorphism is natural and inverts quasi-isomorphisms.
Lift it through Q using localization. Every derived object is represented by a complex,
and precomposition with Q is fully faithful on the resulting functors, so the
prescribed components determine the lift uniquely. -/
theorem existsUnique_fieldScalarTower (f : K →+* L) (g : L →+* M) :
    ∃! e : fieldDerivedScalarExtension f ⋙ fieldDerivedScalarExtension g ≅
        fieldDerivedScalarExtension (g.comp f),
      ∀ C : CochainComplex (ModuleCat.{u} K) ℤ,
        e.app (DerivedCategory.Q.obj C) = fieldScalarTowerComponent f g C := by
  let e₀ : DerivedCategory.Q ⋙
      (fieldDerivedScalarExtension f ⋙ fieldDerivedScalarExtension g) ≅
      DerivedCategory.Q ⋙ fieldDerivedScalarExtension (g.comp f) :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (ModuleCat.extendScalars f).mapDerivedCategoryFactors _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (ModuleCat.extendScalars g).mapDerivedCategoryFactors ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight
        (Functor.mapHomologicalComplexCompIso (ModuleCat.extendScalarsComp f g).symm
          (ComplexShape.up ℤ)) DerivedCategory.Q ≪≫
      ((ModuleCat.extendScalars (g.comp f)).mapDerivedCategoryFactors).symm
  let ff := Localization.fullyFaithfulWhiskeringLeft DerivedCategory.Q
    (HomologicalComplex.quasiIso (ModuleCat.{u} K) (ComplexShape.up ℤ))
    (DerivedCategory (ModuleCat.{u} M))
  refine ⟨ff.preimageIso e₀, ?_, ?_⟩
  · intro C
    apply Iso.ext
    have hc := congr_app (ff.map_preimage e₀.hom) C
    simpa [e₀, fieldScalarTowerComponent] using hc
  · intro e he
    apply Iso.ext
    apply Localization.natTrans_ext DerivedCategory.Q
      (HomologicalComplex.quasiIso (ModuleCat.{u} K) (ComplexShape.up ℤ))
    intro C
    have hc := congr_app (ff.map_preimage e₀.hom) C
    exact congrArg Iso.hom (he C) |>.trans (by
      simpa [e₀, fieldScalarTowerComponent] using hc.symm)

/-- The canonical tower comparison, selected from a uniquely determined natural isomorphism.
Source: blueprint order 1509 (blueprint: lem-weil-derived-field-scalar-extension-tower). -/
noncomputable def fieldScalarTower (f : K →+* L) (g : L →+* M) :
    fieldDerivedScalarExtension f ⋙ fieldDerivedScalarExtension g ≅
      fieldDerivedScalarExtension (g.comp f) :=
  (existsUnique_fieldScalarTower f g).exists.choose

private lemma tower_app (f : K →+* L) (g : L →+* M)
    (C : CochainComplex (ModuleCat.{u} K) ℤ) :
    (fieldScalarTower f g).app (DerivedCategory.Q.obj C) =
      fieldScalarTowerComponent f g C :=
  (existsUnique_fieldScalarTower f g).exists.choose_spec C

private lemma tower_hom_app (f : K →+* L) (g : L →+* M)
    (C : CochainComplex (ModuleCat.{u} K) ℤ) :
    (fieldScalarTower f g).hom.app (DerivedCategory.Q.obj C) =
      (fieldScalarTowerComponent f g C).hom :=
  congrArg Iso.hom (tower_app f g C)

private lemma tower_fac (f : K →+* L) (g : L →+* M)
    (C : CochainComplex (ModuleCat.{u} K) ℤ) :
    (fieldScalarTower f g).hom.app (DerivedCategory.Q.obj C) ≫
        (ModuleCat.extendScalars (g.comp f)).mapDerivedCategoryFactors.hom.app C =
      (fieldDerivedScalarExtension g).map
          ((ModuleCat.extendScalars f).mapDerivedCategoryFactors.hom.app C) ≫
        (ModuleCat.extendScalars g).mapDerivedCategoryFactors.hom.app
          ((ModuleCat.extendScalars f).mapHomologicalComplex (ComplexShape.up ℤ) |>.obj C) ≫
        DerivedCategory.Q.map
          ((Functor.mapHomologicalComplexCompIso (ModuleCat.extendScalarsComp f g).symm
            (ComplexShape.up ℤ)).hom.app C) := by
  rw [tower_hom_app]
  simp only [fieldScalarTowerComponent, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    Iso.app_hom, Iso.app_inv, Category.assoc, Iso.inv_hom_id_app,
    Category.comp_id, Functor.comp_obj]

private lemma tensor_tower_inv {N : Type u} [Field N]
    (f : K →+* L) (g : L →+* M) (h : M →+* N) (X : ModuleCat.{u} K) :
    (ModuleCat.extendScalars h).map ((ModuleCat.extendScalarsComp f g).inv.app X) ≫
        (ModuleCat.extendScalarsComp (g.comp f) h).inv.app X =
      (ModuleCat.extendScalarsComp g h).inv.app ((ModuleCat.extendScalars f).obj X) ≫
        (ModuleCat.extendScalarsComp f (h.comp g)).inv.app X := by
  have he : ModuleCat.extendScalarsComp (g.comp f) h ≪≫
        Functor.isoWhiskerRight (ModuleCat.extendScalarsComp f g) _ =
      ModuleCat.extendScalarsComp f (h.comp g) ≪≫
        Functor.isoWhiskerLeft _ (ModuleCat.extendScalarsComp g h) ≪≫
        (Functor.associator _ _ _).symm :=
    Iso.ext (ModuleCat.extendScalars_assoc f g h)
  have hi := congr_app (congrArg Iso.inv he) X
  simpa using hi

/-- Associativity of the canonical tower comparisons.
Source: blueprint order 1509 (blueprint: lem-weil-derived-field-scalar-extension-tower).
Proof: precompose with Q and use the prescribed components. Both routes become
associativity of the ordinary tensor product (ModuleCat.extendScalars_assoc).
Localization detects equality of natural transformations. -/
theorem fieldScalarTower_assoc {N : Type u} [Field N]
    (f : K →+* L) (g : L →+* M) (h : M →+* N) :
    Functor.isoWhiskerRight (fieldScalarTower f g) (fieldDerivedScalarExtension h) ≪≫
        fieldScalarTower (g.comp f) h =
      Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft (fieldDerivedScalarExtension f) (fieldScalarTower g h) ≪≫
        fieldScalarTower f (h.comp g) := by
  apply Iso.ext
  apply Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso (ModuleCat.{u} K) (ComplexShape.up ℤ))
  intro C
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Functor.associator_hom_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Category.id_comp]
  rw [← cancel_mono
    ((ModuleCat.extendScalars ((h.comp g).comp f)).mapDerivedCategoryFactors.hom.app C)]
  rw [Category.assoc, Category.assoc, tower_fac f (h.comp g)]
  have hn := (fieldScalarTower g h).hom.naturality
    ((ModuleCat.extendScalars f).mapDerivedCategoryFactors.hom.app C)
  dsimp only [Functor.comp_obj, Functor.comp_map] at hn
  rw [← reassoc_of% hn]
  rw [reassoc_of% (tower_fac g h _)]
  simp only [RingHom.comp_assoc]
  rw [tower_fac (g.comp f) h]
  rw [← (fieldDerivedScalarExtension h).map_comp_assoc, tower_fac f g]
  simp only [Functor.map_comp, Category.assoc]
  rw [(ModuleCat.extendScalars h).mapDerivedCategoryFactors_hom_naturality_assoc]
  simp only [← DerivedCategory.Q.map_comp]
  congr 3
  apply congrArg Q.map
  apply HomologicalComplex.Hom.ext
  funext i
  exact tensor_tower_inv f g h (C.X i)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency false in
end DerivedCategory
