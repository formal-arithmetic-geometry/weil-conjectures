/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Field.FieldDerivedScalarTower
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Mathlib.RingTheory.TensorProduct.Finite

/-! # Cohomology and exact scalar extension

Source: Stacks Project, Algebra, Tag 00H9; Homology, Tags 010N and 010V
(blueprint: lem-weil-cohomology-commutes-scalar-extension).

## Main definitions and statements

* `fieldComplexHomologyIso`: the canonical exact scalar/cohomology comparison on complexes.
* `fieldDerivedHomologyIso`: its uniquely normalized localization lift.
* `fieldDerivedHomologyIso_tower`: compatibility with tensor towers.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace DerivedCategory

variable {K L : Type u} [Field K] [Field L]

/-- The canonical map on cohomology of complexes, in the direction from the tensored
complex to the tensor of its cohomology. Its inverse sends a tensor of a cycle class
to the class of that tensor. It is already an isomorphism by exactness.
Source: Stacks Tags 00H9, 010N, 010V
(blueprint: lem-weil-cohomology-commutes-scalar-extension). -/
noncomputable def fieldComplexHomologyIso (f : K →+* L) (i : ℤ) :
    (ModuleCat.extendScalars f).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        HomologicalComplex.homologyFunctor (ModuleCat.{u} L) (ComplexShape.up ℤ) i ≅
      HomologicalComplex.homologyFunctor (ModuleCat.{u} K) (ComplexShape.up ℤ) i ⋙
        ModuleCat.extendScalars f :=
  Functor.isoWhiskerLeft (HomologicalComplex.shortComplexFunctor _ _ i)
    (ShortComplex.homologyFunctorIso (ModuleCat.extendScalars f))

/-- The prescribed component of the derived cohomology comparison.
Source: Stacks Tags 00H9, 010N, 010V
(blueprint: lem-weil-cohomology-commutes-scalar-extension). -/
noncomputable def fieldDerivedHomologyComponent (f : K →+* L) (i : ℤ)
    (C : CochainComplex (ModuleCat.{u} K) ℤ) :
    (homologyFunctor (ModuleCat.{u} L) i).obj
        ((fieldDerivedScalarExtension f).obj (DerivedCategory.Q.obj C)) ≅
      (ModuleCat.extendScalars f).obj
        ((homologyFunctor (ModuleCat.{u} K) i).obj (DerivedCategory.Q.obj C)) :=
  (homologyFunctor (ModuleCat.{u} L) i).mapIso
      ((ModuleCat.extendScalars f).mapDerivedCategoryFactors.app C) ≪≫
    (homologyFunctorFactors (ModuleCat.{u} L) i).app _ ≪≫
    (fieldComplexHomologyIso f i).app C ≪≫
    (ModuleCat.extendScalars f).mapIso
      ((homologyFunctorFactors (ModuleCat.{u} K) i).app C).symm

/-- The natural cohomology comparison descends uniquely through localization.
Source: Stacks Tags 00H9, 010N, 010V
(blueprint: lem-weil-cohomology-commutes-scalar-extension).
Proof: the complex-level comparison is natural by the kernel/image universal
properties and is unchanged by quasi-isomorphisms. Descend it along Q. Its values
on Q C are prescribed and Q is essentially surjective, so this lift is unique. -/
theorem existsUnique_fieldDerivedHomologyIso (f : K →+* L) (i : ℤ) :
    ∃! e : fieldDerivedScalarExtension f ⋙ homologyFunctor (ModuleCat.{u} L) i ≅
        homologyFunctor (ModuleCat.{u} K) i ⋙ ModuleCat.extendScalars f,
      ∀ C : CochainComplex (ModuleCat.{u} K) ℤ,
        e.app (DerivedCategory.Q.obj C) = fieldDerivedHomologyComponent f i C := by
  let e₀ : DerivedCategory.Q ⋙
      (fieldDerivedScalarExtension f ⋙ homologyFunctor (ModuleCat.{u} L) i) ≅
      DerivedCategory.Q ⋙
        (homologyFunctor (ModuleCat.{u} K) i ⋙ ModuleCat.extendScalars f) :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (ModuleCat.extendScalars f).mapDerivedCategoryFactors _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (homologyFunctorFactors (ModuleCat.{u} L) i) ≪≫
      fieldComplexHomologyIso f i ≪≫
      Functor.isoWhiskerRight (homologyFunctorFactors (ModuleCat.{u} K) i).symm _ ≪≫
      Functor.associator _ _ _
  let h := Localization.fullyFaithfulWhiskeringLeft
    (DerivedCategory.Q (C := ModuleCat.{u} K))
    (HomologicalComplex.quasiIso (ModuleCat.{u} K) (ComplexShape.up ℤ)) (ModuleCat.{u} L)
  refine ⟨h.preimageIso e₀, ?_, ?_⟩
  · intro C
    apply Iso.ext
    exact congr_app (h.map_preimage e₀.hom) C
  · intro e he
    apply Iso.ext
    apply Localization.natTrans_ext DerivedCategory.Q
      (HomologicalComplex.quasiIso (ModuleCat.{u} K) (ComplexShape.up ℤ))
    intro C
    exact congrArg Iso.hom (he C) |>.trans (congr_app (h.map_preimage e₀.hom) C).symm

/-- The canonical derived cohomology comparison, uniquely normalized on complexes.
Source: Stacks Tags 00H9, 010N, 010V
(blueprint: lem-weil-cohomology-commutes-scalar-extension). -/
noncomputable def fieldDerivedHomologyIso (f : K →+* L) (i : ℤ) :
    fieldDerivedScalarExtension f ⋙ homologyFunctor (ModuleCat.{u} L) i ≅
      homologyFunctor (ModuleCat.{u} K) i ⋙ ModuleCat.extendScalars f :=
  (existsUnique_fieldDerivedHomologyIso f i).exists.choose

private theorem fieldDerivedHomologyIso_app_Q (f : K →+* L) (i : ℤ)
    (C : CochainComplex (ModuleCat.{u} K) ℤ) :
    (fieldDerivedHomologyIso f i).app (DerivedCategory.Q.obj C) =
      fieldDerivedHomologyComponent f i C :=
  (existsUnique_fieldDerivedHomologyIso f i).exists.choose_spec C

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem fieldShortHomologyIso_comp {M : Type u} [Field M]
    (f : K →+* L) (g : L →+* M) (S : ShortComplex (ModuleCat.{u} K)) :
    S.mapHomologyIso (ModuleCat.extendScalars f ⋙ ModuleCat.extendScalars g) =
      (S.map (ModuleCat.extendScalars f)).mapHomologyIso (ModuleCat.extendScalars g) ≪≫
        (ModuleCat.extendScalars g).mapIso (S.mapHomologyIso (ModuleCat.extendScalars f)) := by
  rw [ShortComplex.LeftHomologyData.mapHomologyIso_eq
    (S.homologyData.left.map (ModuleCat.extendScalars f)) (ModuleCat.extendScalars g)]
  apply Iso.ext
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Category.assoc]
  simp only [ShortComplex.mapHomologyIso]
  simp only [ShortComplex.LeftHomologyData.map_H, Functor.comp_obj]
  rw [← Functor.map_comp, Iso.inv_hom_id, CategoryTheory.Functor.map_id, Category.comp_id]
  apply (cancel_epi (S.map
    (ModuleCat.extendScalars f ⋙ ModuleCat.extendScalars g)).homologyπ).mp
  simp only [ShortComplex.LeftHomologyData.homologyπ_comp_homologyIso_hom,
    ShortComplex.LeftHomologyData.map_π, Functor.comp_map]
  congr 1
  apply (cancel_mono ((ModuleCat.extendScalars g).map
    ((ModuleCat.extendScalars f).map S.homologyData.left.i))).mp
  simpa only [ShortComplex.LeftHomologyData.map_i, Functor.comp_map] using
    (S.homologyData.left.map
      (ModuleCat.extendScalars f ⋙ ModuleCat.extendScalars g)).cyclesIso_hom_comp_i.trans
      (((S.homologyData.left.map (ModuleCat.extendScalars f)).map
        (ModuleCat.extendScalars g)).cyclesIso_hom_comp_i).symm

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem fieldComplexHomologyIso_tower {M : Type u} [Field M]
    (f : K →+* L) (g : L →+* M) (i : ℤ)
    (C : CochainComplex (ModuleCat.{u} K) ℤ) :
    (HomologicalComplex.homologyFunctor (ModuleCat.{u} M) (ComplexShape.up ℤ) i).mapIso
        ((Functor.mapHomologicalComplexCompIso (ModuleCat.extendScalarsComp f g).symm
          (ComplexShape.up ℤ)).app C) ≪≫ (fieldComplexHomologyIso (g.comp f) i).app C =
      (fieldComplexHomologyIso g i).app
          (((ModuleCat.extendScalars f).mapHomologicalComplex (ComplexShape.up ℤ)).obj C) ≪≫
        (ModuleCat.extendScalars g).mapIso ((fieldComplexHomologyIso f i).app C) ≪≫
        ((ModuleCat.extendScalarsComp f g).app (C.homology i)).symm := by
  apply Iso.ext
  change ShortComplex.homologyMap
      ((C.sc i).mapNatTrans (ModuleCat.extendScalarsComp f g).inv) ≫
        ((C.sc i).mapHomologyIso (ModuleCat.extendScalars (g.comp f))).hom =
    (((C.sc i).map (ModuleCat.extendScalars f)).mapHomologyIso
      (ModuleCat.extendScalars g)).hom ≫
        (ModuleCat.extendScalars g).map
          (((C.sc i).mapHomologyIso (ModuleCat.extendScalars f)).hom) ≫
        (ModuleCat.extendScalarsComp f g).inv.app (C.homology i)
  rw [ShortComplex.homologyMap_mapNatTrans]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [fieldShortHomologyIso_comp]
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Tensor/cohomology comparison is compatible with the scalar tower comparison.
Source: Stacks Tags 00H9, 010N, 010V
(blueprint: lem-weil-cohomology-commutes-scalar-extension).
Proof: on complexes the two routes send a tensor of a cycle class to the same
class, using tensor associativity. The kernel/image universal properties give
this equality, and uniqueness of localization extends it to derived objects. -/
theorem fieldDerivedHomologyIso_tower {M : Type u} [Field M]
    (f : K →+* L) (g : L →+* M) (i : ℤ)
    (C : DerivedCategory (ModuleCat.{u} K)) :
    (homologyFunctor (ModuleCat.{u} M) i).mapIso ((fieldScalarTower f g).app C) ≪≫
        (fieldDerivedHomologyIso (g.comp f) i).app C =
      (fieldDerivedHomologyIso g i).app ((fieldDerivedScalarExtension f).obj C) ≪≫
        (ModuleCat.extendScalars g).mapIso ((fieldDerivedHomologyIso f i).app C) ≪≫
        ((ModuleCat.extendScalarsComp f g).app
          ((homologyFunctor (ModuleCat.{u} K) i).obj C)).symm := by
  let e₁ := Functor.isoWhiskerRight (fieldScalarTower f g)
      (homologyFunctor (ModuleCat.{u} M) i) ≪≫ fieldDerivedHomologyIso (g.comp f) i
  let e₂ := Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (fieldDerivedScalarExtension f) (fieldDerivedHomologyIso g i) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (fieldDerivedHomologyIso f i) (ModuleCat.extendScalars g) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (homologyFunctor (ModuleCat.{u} K) i)
      (ModuleCat.extendScalarsComp f g).symm
  have he : e₁ = e₂ := by
    apply Iso.ext
    apply Localization.natTrans_ext DerivedCategory.Q
      (HomologicalComplex.quasiIso (ModuleCat.{u} K) (ComplexShape.up ℤ))
    intro A
    dsimp only [e₁, e₂, Iso.trans_hom, NatTrans.comp_app,
      Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
      Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
      Functor.associator_hom_app, Functor.associator_inv_app, Iso.symm_hom]
    simp only [Category.id_comp]
    have ht := (existsUnique_fieldScalarTower f g).exists.choose_spec A
    change (fieldScalarTower f g).app (DerivedCategory.Q.obj A) = _ at ht
    rw [show (fieldScalarTower f g).hom.app (DerivedCategory.Q.obj A) =
        (fieldScalarTowerComponent f g A).hom from congrArg Iso.hom ht]
    have hn := (NatTrans.naturality_2 (fieldDerivedHomologyIso g i).hom
      ((ModuleCat.extendScalars f).mapDerivedCategoryFactors.app A)).symm
    dsimp only [Functor.comp_obj] at hn
    rw [hn]
    rw [show (fieldDerivedHomologyIso (g.comp f) i).hom.app (DerivedCategory.Q.obj A) =
        (fieldDerivedHomologyComponent (g.comp f) i A).hom from
          congrArg Iso.hom (fieldDerivedHomologyIso_app_Q (g.comp f) i A)]
    rw [show (fieldDerivedHomologyIso f i).hom.app (DerivedCategory.Q.obj A) =
        (fieldDerivedHomologyComponent f i A).hom from
          congrArg Iso.hom (fieldDerivedHomologyIso_app_Q f i A)]
    rw [show (fieldDerivedHomologyIso g i).hom.app
        (DerivedCategory.Q.obj
          (((ModuleCat.extendScalars f).mapHomologicalComplex (ComplexShape.up ℤ)).obj A)) =
        (fieldDerivedHomologyComponent g i _).hom from
          congrArg Iso.hom (fieldDerivedHomologyIso_app_Q g i _)]
    simp only [fieldScalarTowerComponent, fieldDerivedHomologyComponent,
      Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom,
      Functor.comp_map, Functor.map_comp, Category.assoc]
    simp only [← Functor.map_comp_assoc, Iso.inv_hom_id,
      CategoryTheory.Functor.map_id, Category.id_comp]
    simp only [Iso.inv_hom_id_assoc, Functor.map_comp, Category.assoc]
    dsimp only [Iso.app_hom, Iso.app_inv]
    rw [homologyFunctorFactors_hom_naturality_assoc]
    have hc := congrArg Iso.hom (fieldComplexHomologyIso_tower f g i A)
    dsimp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom,
      Iso.app_hom, Iso.app_inv, HomologicalComplex.homologyFunctor_map] at hc
    rw [reassoc_of% hc]
    rw [← (ModuleCat.extendScalarsComp f g).inv.naturality]
    rfl
  exact congrArg (fun e ↦ e.app C) he

/-- Scalar extension preserves finite-dimensional cohomology and quasi-isomorphisms.
Source: Stacks Tags 00H9, 010N, 010V
(blueprint: lem-weil-cohomology-commutes-scalar-extension).
Proof: use the canonical homology comparison. Finite dimensionality survives tensor
extension. A quasi-isomorphism is an isomorphism on every cohomology module; tensor
extension preserves those isomorphisms, and naturality gives the same property for
the map between the scalar-extended complexes. -/
theorem fieldComplexScalarExtension_properties (f : K →+* L) :
    (∀ C : CochainComplex (ModuleCat.{u} K) ℤ,
      (∀ i : ℤ, FiniteDimensional K (C.homology i)) → ∀ i : ℤ,
        FiniteDimensional L
          (((ModuleCat.extendScalars f).mapHomologicalComplex (ComplexShape.up ℤ)).obj C
            |>.homology i)) ∧
    (∀ (C D : CochainComplex (ModuleCat.{u} K) ℤ) (g : C ⟶ D),
      QuasiIso g →
        QuasiIso
          (((ModuleCat.extendScalars f).mapHomologicalComplex (ComplexShape.up ℤ)).map g)) := by
  constructor
  · intro C hC i
    let := f.toAlgebra
    have := hC i
    have hfinite : FiniteDimensional L ((ModuleCat.extendScalars f).obj (C.homology i)) := by
      change FiniteDimensional L (TensorProduct K L (C.homology i))
      infer_instance
    let e := ((fieldComplexHomologyIso f i).app C).toLinearEquiv
    exact @Module.Finite.equiv _ _ _ _ _ _ _ _ hfinite e.symm
  · intro C D g hg
    have := hg
    infer_instance

end DerivedCategory
