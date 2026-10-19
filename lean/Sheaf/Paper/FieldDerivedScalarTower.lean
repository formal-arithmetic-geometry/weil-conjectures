/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N7
-/
module

public import Sheaf.Paper.FieldComplexScalarExtension
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

/-- The prescribed component of the unit comparison on a representing complex.
Source: blueprint order 1509 (blueprint: lem-weil-derived-field-scalar-extension-tower). -/
noncomputable def fieldScalarUnitComponent (K : Type u) [Field K]
    (C : CochainComplex (ModuleCat.{u} K) ℤ) :
    (fieldDerivedScalarExtension (RingHom.id K)).obj (DerivedCategory.Q.obj C) ≅
      DerivedCategory.Q.obj C :=
  (ModuleCat.extendScalars (RingHom.id K)).mapDerivedCategoryFactors.app C ≪≫
    DerivedCategory.Q.mapIso
      ((NatIso.mapHomologicalComplex (ModuleCat.extendScalarsId K) (ComplexShape.up ℤ) ≪≫
        Functor.mapHomologicalComplexIdIso (ModuleCat.{u} K) (ComplexShape.up ℤ)).app C)

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

/-- Localization gives the unique unit comparison with the termwise normalization.
Source: blueprint order 1509 (blueprint: lem-weil-derived-field-scalar-extension-tower).
Proof: lift the termwise tensor unit through Q. The localization's uniqueness and
essential surjectivity give uniqueness of the normalized natural isomorphism. -/
theorem existsUnique_fieldScalarUnit (K : Type u) [Field K] :
    ∃! e : fieldDerivedScalarExtension (RingHom.id K) ≅ 𝟭 (DerivedCategory (ModuleCat.{u} K)),
      ∀ C : CochainComplex (ModuleCat.{u} K) ℤ,
        e.app (DerivedCategory.Q.obj C) = fieldScalarUnitComponent K C := by
  let e₀ : DerivedCategory.Q ⋙ fieldDerivedScalarExtension (RingHom.id K) ≅
      DerivedCategory.Q ⋙ 𝟭 (DerivedCategory (ModuleCat.{u} K)) :=
    (ModuleCat.extendScalars (RingHom.id K)).mapDerivedCategoryFactors ≪≫
      Functor.isoWhiskerRight
        (NatIso.mapHomologicalComplex (ModuleCat.extendScalarsId K) (ComplexShape.up ℤ) ≪≫
          Functor.mapHomologicalComplexIdIso (ModuleCat.{u} K) (ComplexShape.up ℤ))
        DerivedCategory.Q ≪≫
      (Functor.rightUnitor DerivedCategory.Q).symm
  let ff := Localization.fullyFaithfulWhiskeringLeft DerivedCategory.Q
    (HomologicalComplex.quasiIso (ModuleCat.{u} K) (ComplexShape.up ℤ))
    (DerivedCategory (ModuleCat.{u} K))
  refine ⟨ff.preimageIso e₀, ?_, ?_⟩
  · intro C
    apply Iso.ext
    have hc := congr_app (ff.map_preimage e₀.hom) C
    simpa [e₀, fieldScalarUnitComponent] using hc
  · intro e he
    apply Iso.ext
    apply Localization.natTrans_ext DerivedCategory.Q
      (HomologicalComplex.quasiIso (ModuleCat.{u} K) (ComplexShape.up ℤ))
    intro C
    have hc := congr_app (ff.map_preimage e₀.hom) C
    exact congrArg Iso.hom (he C) |>.trans (by
      simpa [e₀, fieldScalarUnitComponent] using hc.symm)

/-- The canonical tower comparison, selected from a uniquely determined natural isomorphism.
Source: blueprint order 1509 (blueprint: lem-weil-derived-field-scalar-extension-tower). -/
noncomputable def fieldScalarTower (f : K →+* L) (g : L →+* M) :
    fieldDerivedScalarExtension f ⋙ fieldDerivedScalarExtension g ≅
      fieldDerivedScalarExtension (g.comp f) :=
  (existsUnique_fieldScalarTower f g).exists.choose

/-- The canonical unit comparison, selected with its termwise normalization.
Source: blueprint order 1509 (blueprint: lem-weil-derived-field-scalar-extension-tower). -/
noncomputable def fieldScalarUnit (K : Type u) [Field K] :
    fieldDerivedScalarExtension (RingHom.id K) ≅ 𝟭 (DerivedCategory (ModuleCat.{u} K)) :=
  (existsUnique_fieldScalarUnit K).exists.choose

private lemma tower_app (f : K →+* L) (g : L →+* M)
    (C : CochainComplex (ModuleCat.{u} K) ℤ) :
    (fieldScalarTower f g).app (DerivedCategory.Q.obj C) =
      fieldScalarTowerComponent f g C :=
  (existsUnique_fieldScalarTower f g).exists.choose_spec C

private lemma unit_app (C : CochainComplex (ModuleCat.{u} K) ℤ) :
    (fieldScalarUnit K).app (DerivedCategory.Q.obj C) = fieldScalarUnitComponent K C :=
  (existsUnique_fieldScalarUnit K).exists.choose_spec C

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

set_option backward.isDefEq.respectTransparency false in
private lemma tensor_right_unit (f : K →+* L) (X : ModuleCat.{u} K) :
    (ModuleCat.extendScalarsComp f (RingHom.id L)).inv.app X =
      (ModuleCat.extendScalarsId L).hom.app ((ModuleCat.extendScalars f).obj X) := by
  apply (cancel_epi ((ModuleCat.extendScalarsComp f (RingHom.id L)).hom.app X)).1
  have he := congr_app (ModuleCat.extendScalars_comp_id f) X
  dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.rightUnitor_hom_app,
    NatTrans.id_app] at he
  erw [Category.comp_id] at he
  simpa only [Category.comp_id, Iso.hom_inv_id_app] using he.symm

set_option backward.isDefEq.respectTransparency false in
private lemma tensor_left_unit (f : K →+* L) (X : ModuleCat.{u} K) :
    (ModuleCat.extendScalarsComp (RingHom.id K) f).inv.app X =
      (ModuleCat.extendScalars f).map ((ModuleCat.extendScalarsId K).hom.app X) := by
  apply (cancel_epi ((ModuleCat.extendScalarsComp (RingHom.id K) f).hom.app X)).1
  have he := congr_app (ModuleCat.extendScalars_id_comp f) X
  dsimp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.leftUnitor_hom_app,
    NatTrans.id_app] at he
  erw [Category.comp_id] at he
  simpa only [Category.comp_id, Iso.hom_inv_id_app] using he.symm

set_option backward.isDefEq.respectTransparency false in
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
/-- Unit coherence of the normalized tower comparisons.
Source: blueprint order 1509 (blueprint: lem-weil-derived-field-scalar-extension-tower).
Proof: on representing complexes both equations are the ordinary tensor unit
identities; localization detects equality. -/
theorem fieldScalarTower_units (f : K →+* L) :
    fieldScalarTower f (RingHom.id L) =
        Functor.isoWhiskerLeft _ (fieldScalarUnit L) ≪≫ Functor.rightUnitor _ ∧
      fieldScalarTower (RingHom.id K) f =
        Functor.isoWhiskerRight (fieldScalarUnit K) _ ≪≫ Functor.leftUnitor _ := by
  constructor
  · apply Iso.ext
    apply Localization.natTrans_ext DerivedCategory.Q
      (HomologicalComplex.quasiIso (ModuleCat.{u} K) (ComplexShape.up ℤ))
    intro C
    simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
      Functor.whiskerLeft_app, Functor.rightUnitor_hom_app]
    rw [← cancel_mono ((ModuleCat.extendScalars f).mapDerivedCategoryFactors.hom.app C)]
    have ht := tower_fac f (RingHom.id L) C
    erw [ht]
    simp only [Category.assoc]
    erw [Category.id_comp]
    have hn := (fieldScalarUnit L).hom.naturality
      ((ModuleCat.extendScalars f).mapDerivedCategoryFactors.hom.app C)
    dsimp only [Functor.id_map] at hn
    erw [← hn]
    erw [show (fieldScalarUnit L).hom.app
        (Q.obj (((ModuleCat.extendScalars f).mapHomologicalComplex (.up ℤ)).obj C)) =
        (fieldScalarUnitComponent L
          (((ModuleCat.extendScalars f).mapHomologicalComplex (.up ℤ)).obj C)).hom from
      congrArg Iso.hom (unit_app _)]
    simp only [fieldScalarUnitComponent, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom]
    congr 2
    apply congrArg Q.map
    apply HomologicalComplex.Hom.ext
    funext i
    erw [Category.comp_id]
    exact tensor_right_unit f (C.X i)
  · apply Iso.ext
    apply Localization.natTrans_ext DerivedCategory.Q
      (HomologicalComplex.quasiIso (ModuleCat.{u} K) (ComplexShape.up ℤ))
    intro C
    simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
      Functor.whiskerRight_app, Functor.leftUnitor_hom_app]
    rw [← cancel_mono ((ModuleCat.extendScalars f).mapDerivedCategoryFactors.hom.app C)]
    have ht := tower_fac (RingHom.id K) f C
    erw [ht]
    simp only [Category.assoc]
    erw [Category.id_comp]
    erw [show (fieldScalarUnit K).hom.app (Q.obj C) =
        (fieldScalarUnitComponent K C).hom from congrArg Iso.hom (unit_app C)]
    simp only [fieldScalarUnitComponent, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom,
      Functor.map_comp, Category.assoc]
    erw [(ModuleCat.extendScalars f).mapDerivedCategoryFactors_hom_naturality]
    congr 2
    apply congrArg Q.map
    apply HomologicalComplex.Hom.ext
    funext i
    change (ModuleCat.extendScalarsComp (RingHom.id K) f).inv.app (C.X i) =
      (ModuleCat.extendScalars f).map
        ((ModuleCat.extendScalarsId K).hom.app (C.X i) ≫ 𝟙 (C.X i))
    erw [Category.comp_id]
    exact tensor_left_unit f (C.X i)

/-- The normalized unit and tower comparisons commute with the exact-functor shifts.
Source: blueprint order 1509 (blueprint: lem-weil-derived-field-scalar-extension-tower).
Proof: on Q C these are maps of the termwise tensor/shift comparisons; those
commute with shifts degree by degree, including the differential signs.
Localization detects equality, giving the stated shift compatibilities. -/
theorem fieldScalarTower_commShift (f : K →+* L) (g : L →+* M) :
    NatTrans.CommShift (fieldScalarTower f g).hom ℤ ∧
      NatTrans.CommShift (fieldScalarUnit K).hom ℤ := by
  constructor
  · let e₀ : DerivedCategory.Q ⋙
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
    have he : Functor.whiskerLeft DerivedCategory.Q (fieldScalarTower f g).hom =
        e₀.hom := by
      ext C
      simpa [e₀, fieldScalarTowerComponent] using tower_hom_app f g C
    have : NatTrans.CommShift
        (Functor.whiskerLeft DerivedCategory.Q (fieldScalarTower f g).hom) ℤ := by
      rw [he]
      dsimp only [e₀, Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerLeft_hom,
        Functor.isoWhiskerRight_hom]
      infer_instance
    exact NatTrans.CommShift.of_whiskerLeft _ DerivedCategory.Q
      (fun X ↦ ⟨_, (DerivedCategory.Q.objObjPreimageIso X).inv, inferInstance⟩)
  · have hid : NatTrans.CommShift
        (Functor.mapHomologicalComplexIdIso (ModuleCat.{u} K) (.up ℤ)).hom ℤ := by
      constructor
      intro n
      ext C i
      dsimp
      simp
    have hnat : NatTrans.CommShift
        (NatIso.mapHomologicalComplex (ModuleCat.extendScalarsId K) (.up ℤ)).hom ℤ :=
      inferInstanceAs (NatTrans.CommShift
        (NatTrans.mapHomologicalComplex (ModuleCat.extendScalarsId K).hom (.up ℤ)) ℤ)
    let e₀ : DerivedCategory.Q ⋙ fieldDerivedScalarExtension (RingHom.id K) ≅
        DerivedCategory.Q ⋙ 𝟭 (DerivedCategory (ModuleCat.{u} K)) :=
      (ModuleCat.extendScalars (RingHom.id K)).mapDerivedCategoryFactors ≪≫
        Functor.isoWhiskerRight
          (NatIso.mapHomologicalComplex (ModuleCat.extendScalarsId K) (ComplexShape.up ℤ) ≪≫
            Functor.mapHomologicalComplexIdIso (ModuleCat.{u} K) (ComplexShape.up ℤ))
          DerivedCategory.Q ≪≫
        Functor.leftUnitor DerivedCategory.Q ≪≫
        (Functor.rightUnitor DerivedCategory.Q).symm
    have he : Functor.whiskerLeft DerivedCategory.Q (fieldScalarUnit K).hom =
        e₀.hom := by
      ext C
      simpa [e₀, fieldScalarUnitComponent] using congrArg Iso.hom (unit_app C)
    have : NatTrans.CommShift
        (Functor.whiskerLeft DerivedCategory.Q (fieldScalarUnit K).hom) ℤ := by
      rw [he]
      dsimp only [e₀, Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerLeft_hom,
        Functor.isoWhiskerRight_hom]
      infer_instance
    exact NatTrans.CommShift.of_whiskerLeft _ DerivedCategory.Q
      (fun X ↦ ⟨_, (DerivedCategory.Q.objObjPreimageIso X).inv, inferInstance⟩)

end DerivedCategory

