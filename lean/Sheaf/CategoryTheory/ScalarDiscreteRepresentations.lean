/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q3
-/
module

public import Sheaf.CategoryTheory.ScalarObjects
public import WeilConjectures.RepresentationTheory.DiscreteContinuousRep
public import Mathlib.Algebra.Category.Grp.ZModuleEquivalence

/-! # Scalar objects in discrete representations

Source: Stacks Project, Tag 04JQ, scalar enhancement.
(blueprint: lem-exc-scalar-discrete-representations)
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe r g w
open CategoryTheory

namespace CategoryTheory.ScalarObject

variable (R : Type r) [Ring R] (G : Type g) [Group G]
  [TopologicalSpace G] [IsTopologicalGroup G]

omit [TopologicalSpace G] [IsTopologicalGroup G] in
/-- Integer representation morphisms are determined by their values.
Source: Stacks Project, Tag 04JQ.
(blueprint: lem-exc-scalar-discrete-representations) -/
theorem integerHom_ext {M N : Rep.{w} ℤ G} {f g : M ⟶ N}
    (h : ∀ x, f.hom x = g.hom x) : f = g := by
  let : Module ℤ M.V := M.hV2
  let : Module ℤ N.V := N.hV2
  apply Rep.hom_ext
  apply @Representation.IntertwiningMap.ext
  apply @LinearMap.ext
  intro x
  exact h x

/-- Scalar restriction on discrete representations. -/
def discreteRepToScalar : Rep.DiscreteContinuousRep.{r, g, w} R G ⥤
    ScalarObject R (Rep.DiscreteContinuousRep.{0, g, w} ℤ G) where
  obj M :=
    { X := ⟨Rep.of
        { toFun := fun g ↦ (M.obj.ρ g).toAddMonoidHom.toIntLinearMap
          map_one' := by apply @LinearMap.ext; intro x; exact LinearMap.congr_fun M.obj.ρ.map_one x
          map_mul' g h := by
            apply @LinearMap.ext
            intro x
            exact LinearMap.congr_fun (M.obj.ρ.map_mul g h) x },
        M.property⟩
      ρ :=
        { toFun := fun a ↦ ObjectProperty.homMk (Rep.ofHom
            ⟨(show AddMonoid.End M.obj.V from
                { toFun := fun x ↦ a • x
                  map_zero' := smul_zero a
                  map_add' := smul_add a }).toIntLinearMap,
              fun g ↦ by
                apply @LinearMap.ext
                intro x
                exact ((M.obj.ρ g).map_smul a x).symm⟩)
          map_one' := by
            apply ObjectProperty.hom_ext
            apply Rep.hom_ext
            apply @Representation.IntertwiningMap.ext
            apply @LinearMap.ext
            intro x
            exact one_smul R x
          map_mul' a b := by
            apply ObjectProperty.hom_ext
            apply Rep.hom_ext
            apply @Representation.IntertwiningMap.ext
            apply @LinearMap.ext
            intro x
            exact mul_smul a b x
          map_zero' := by
            apply ObjectProperty.hom_ext
            apply Rep.hom_ext
            apply @Representation.IntertwiningMap.ext
            apply @LinearMap.ext
            intro x
            exact zero_smul R x
          map_add' a b := by
            apply ObjectProperty.hom_ext
            apply Rep.hom_ext
            apply @Representation.IntertwiningMap.ext
            apply @LinearMap.ext
            intro x
            exact add_smul a b x } }
  map f :=
    { hom := ObjectProperty.homMk (Rep.ofHom
        ⟨f.hom.hom.toAddMonoidHom.toIntLinearMap,
          fun g ↦ by
            apply @LinearMap.ext
            intro x
            exact LinearMap.congr_fun (f.hom.hom.isIntertwining' g) x⟩)
      comm := fun a ↦ by
        apply ObjectProperty.hom_ext
        apply integerHom_ext G
        intro x
        exact f.hom.hom.map_smul a x }
  map_id M := by
    apply hom_ext
    apply ObjectProperty.hom_ext
    apply Rep.hom_ext
    apply @Representation.IntertwiningMap.ext
    apply @LinearMap.ext
    intro x
    rfl
  map_comp f g := rfl

/-- Construct a module representation by interpreting the given scalar operations. -/
def scalarToDiscreteRep :
    ScalarObject R (Rep.DiscreteContinuousRep.{0, g, w} ℤ G) ⥤
      Rep.DiscreteContinuousRep.{r, g, w} R G where
  obj M := by
    letI : Module ℤ M.X.obj.V := M.X.obj.hV2
    let B : AddCommGrpCat := AddCommGrpCat.of M.X.obj.V
    let φ : R →+* End B :=
      { toFun := fun a ↦ AddCommGrpCat.ofHom (M.ρ a).hom.hom.toAddMonoidHom
        map_one' := by
          apply AddCommGrpCat.hom_ext
          apply AddMonoidHom.ext
          intro x
          exact congrArg (fun f ↦ f.hom.hom x) M.ρ.map_one
        map_mul' a b := by
          apply AddCommGrpCat.hom_ext
          apply AddMonoidHom.ext
          intro x
          exact congrArg (fun f ↦ f.hom.hom x) (M.ρ.map_mul a b)
        map_zero' := by
          apply AddCommGrpCat.hom_ext
          apply AddMonoidHom.ext
          intro x
          exact congrArg (fun f ↦ f.hom.hom x) M.ρ.map_zero
        map_add' a b := by
          apply AddCommGrpCat.hom_ext
          apply AddMonoidHom.ext
          intro x
          exact congrArg (fun f ↦ f.hom.hom x) (M.ρ.map_add a b) }
    let N := ModuleCat.mkOfSMul φ
    let ρ : Representation R G N :=
      { toFun := fun g ↦
          { toFun := M.X.obj.ρ g
            map_add' := map_add _
            map_smul' := fun a x ↦
              (LinearMap.congr_fun ((M.ρ a).hom.hom.isIntertwining' g) x).symm }
        map_one' := by apply @LinearMap.ext; intro x; exact LinearMap.congr_fun M.X.obj.ρ.map_one x
        map_mul' g h := by
          apply @LinearMap.ext
          intro x
          exact LinearMap.congr_fun (M.X.obj.ρ.map_mul g h) x }
    exact ⟨Rep.of ρ, M.X.property⟩
  map {M N} f := by
    letI : Module ℤ M.X.obj.V := M.X.obj.hV2
    letI : Module ℤ N.X.obj.V := N.X.obj.hV2
    exact ObjectProperty.homMk (Rep.ofHom
    ⟨{ toFun := f.hom.hom.hom
       map_add' := map_add _
       map_smul' := fun a x ↦ congrArg (fun t ↦ t.hom.hom x) (f.comm a) },
      fun g ↦ by
        apply @LinearMap.ext
        intro x
        exact LinearMap.congr_fun (f.hom.hom.hom.isIntertwining' g) x⟩)
  map_id M := by
    apply ObjectProperty.hom_ext
    apply Rep.hom_ext
    apply @Representation.IntertwiningMap.ext
    apply @LinearMap.ext
    intro x
    rfl
  map_comp f g := by
    apply ObjectProperty.hom_ext
    apply Rep.hom_ext
    apply @Representation.IntertwiningMap.ext
    apply @LinearMap.ext
    intro x
    rfl

/-- An equivariant additive map is integer-linear for the given integer module structures.
Source: Stacks Project, Tag 04JQ.
(blueprint: lem-exc-scalar-discrete-representations) -/
def integerRepHom (M N : Rep.{w} ℤ G) (f : M.V →+ N.V)
    (hf : ∀ g x, f (M.ρ g x) = N.ρ g (f x)) : M ⟶ N := by
  letI : Module ℤ M.V := M.hV2
  letI : Module ℤ N.V := N.hV2
  exact Rep.ofHom ⟨
    { toFun := f
      map_add' := f.map_add
      map_smul' := fun n x ↦ by
        convert! f.map_zsmul n x <;> ext <;> apply int_smul_eq_zsmul },
    fun g ↦ by apply @LinearMap.ext; intro x; exact hf g x⟩

/-- Scalar operations in integer representations are precisely module representations.
The identity maps of the carriers are the unit and counit. The scalar compatibility
condition is linearity, and the original open stabilizers are unchanged.
Source: Stacks Project, Tag 04JQ.
(blueprint: lem-exc-scalar-discrete-representations) -/
noncomputable def discreteRepEquivalence :
    Rep.DiscreteContinuousRep.{r, g, w} R G ≌
      ScalarObject R (Rep.DiscreteContinuousRep.{0, g, w} ℤ G) where
  functor := discreteRepToScalar R G
  inverse := scalarToDiscreteRep R G
  unitIso := NatIso.ofComponents (fun M ↦ ObjectProperty.isoMk _
    { hom := Rep.ofHom ⟨
        { toFun := id
          map_add' := fun _ _ ↦ rfl
          map_smul' := fun _ _ ↦ rfl }, fun _ ↦ rfl⟩
      inv := Rep.ofHom ⟨
        { toFun := id
          map_add' := fun _ _ ↦ rfl
          map_smul' := fun _ _ ↦ rfl }, fun _ ↦ rfl⟩
      hom_inv_id := by
        apply Rep.hom_ext
        apply @Representation.IntertwiningMap.ext
        apply @LinearMap.ext
        intro x
        rfl
      inv_hom_id := by
        apply Rep.hom_ext
        apply @Representation.IntertwiningMap.ext
        apply @LinearMap.ext
        intro x
        rfl }) (by
      intros
      apply ObjectProperty.hom_ext
      apply Rep.hom_ext
      apply @Representation.IntertwiningMap.ext
      apply @LinearMap.ext
      intro x
      rfl)
  counitIso := NatIso.ofComponents (fun M ↦
    { hom := ⟨ObjectProperty.homMk (integerRepHom G _ _
        (AddMonoidHom.id _) (fun _ _ ↦ rfl)), fun _ ↦ by
          apply ObjectProperty.hom_ext
          apply integerHom_ext G
          intro x
          rfl⟩
      inv := ⟨ObjectProperty.homMk (integerRepHom G _ _
        (AddMonoidHom.id _) (fun _ _ ↦ rfl)), fun _ ↦ by
          apply ObjectProperty.hom_ext
          apply integerHom_ext G
          intro x
          rfl⟩
      hom_inv_id := hom_ext (by
        apply ObjectProperty.hom_ext
        apply integerHom_ext G
        intro x
        rfl)
      inv_hom_id := hom_ext (by
        apply ObjectProperty.hom_ext
        apply integerHom_ext G
        intro x
        rfl) }) (by
      intros
      apply hom_ext
      apply ObjectProperty.hom_ext
      apply integerHom_ext G
      intro x
      rfl)
  functor_unitIso_comp M := hom_ext (by
        apply ObjectProperty.hom_ext
        apply integerHom_ext G
        intro x
        rfl)

end CategoryTheory.ScalarObject
