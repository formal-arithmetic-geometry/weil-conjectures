/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H1
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Sheaf.Topology.InverseImageModule
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProduct

/-!
# Pullback of scheme modules by the tensor formula

Source: Stacks Project, Tags 0095, 0096, 0097; blueprint module base change in
`sec-abelian-varieties/sk-def-av-jacobian/def-pc-base-change.md`
(blueprint: def-pc-module-pullback).
-/

@[expose] public section

universe w

open CategoryTheory TopologicalSpace Opposite

namespace AlgebraicGeometry.Scheme.Modules

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {X Y Z : Scheme.{w}} (g : X ⟶ Y)

/-- The ring map `g⁻¹ O_Y → O_X` adjoint to the structure-sheaf map of `g`.
Source: Stacks, Tag 0095 (blueprint: def-pc-module-pullback). -/
def tensorPullbackRingMap : TopCat.Sheaf.inverseImageRing g.base Y.sheaf ⟶ X.sheaf :=
  (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (Opens.map g.base) CommRingCat.{w} _ _).homEquiv Y.sheaf X.sheaf |>.symm ⟨g.c⟩

/-- `O_X ⊗_{g⁻¹ O_Y} g⁻¹ M`: change of rings on the explicit abelian inverse image.
The section tensor has `O_X` as its first factor and is then sheafified.
Source: Stacks, Tag 0095 (blueprint: def-pc-module-pullback). -/
def tensorPullbackObj (M : Y.Modules) : X.Modules :=
  SheafOfModules.changeOfRings.{w, w, w} (tensorPullbackRingMap g)
    (TopCat.Sheaf.inverseImageModule g.base Y.sheaf M)

/-- The sectionwise map of tensor presheaves is natural.
Source: Stacks, Tag 0095 (blueprint: def-pc-module-pullback).
Proof: inverse image of `a` is linear and commutes with restriction (008X).
The map `id ⊗ g⁻¹a` therefore commutes with restrictions on pure tensors;
pure tensors generate each section tensor, giving the asserted naturality. -/
theorem tensorPullbackPresheafMap_naturality {M N : Y.Modules} (a : M ⟶ N)
    {U V : (Opens X)ᵒᵖ} (i : U ⟶ V) :
    (SheafOfModules.changeOfRingsPresheaf.{w, w, w} (tensorPullbackRingMap g)
      (TopCat.Sheaf.inverseImageModule g.base Y.sheaf M)).map i ≫
      (ModuleCat.restrictScalars (X.ringCatSheaf.obj.map i).hom).map
        ((ModuleCat.extendScalars ((tensorPullbackRingMap g).hom.app V).hom).map
          ((TopCat.Sheaf.inverseImageModuleMap g.base Y.sheaf M a).val.app V)) =
    ((ModuleCat.extendScalars ((tensorPullbackRingMap g).hom.app U).hom).map
      ((TopCat.Sheaf.inverseImageModuleMap g.base Y.sheaf M a).val.app U)) ≫
      (SheafOfModules.changeOfRingsPresheaf.{w, w, w} (tensorPullbackRingMap g)
        (TopCat.Sheaf.inverseImageModule g.base Y.sheaf N)).map i := by
  exact SheafOfModules.changeOfRingsHom_naturality (tensorPullbackRingMap g)
    (TopCat.Sheaf.inverseImageModule g.base Y.sheaf M)
    (TopCat.Sheaf.inverseImageModuleMap g.base Y.sheaf M a) i

/-- The tensor formula on morphisms, followed by module sheafification.
Source: Stacks, Tag 0095 (blueprint: def-pc-module-pullback). -/
def tensorPullbackMap {M N : Y.Modules} (a : M ⟶ N) :
    tensorPullbackObj g M ⟶ tensorPullbackObj g N :=
  (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
    { app := fun U ↦
        (ModuleCat.extendScalars ((tensorPullbackRingMap g).hom.app U).hom).map
          ((TopCat.Sheaf.inverseImageModuleMap g.base Y.sheaf M a).val.app U)
      naturality := tensorPullbackPresheafMap_naturality g a }

/-- Tensor pullback preserves identities. Source: Stacks, Tag 0095
(blueprint: def-pc-module-pullback).
Proof: the abelian inverse-image functor preserves identities; its module map is the
same map with linearity supplied. Extension of scalars and sheafification preserve identities. -/
theorem tensorPullbackMap_id (M : Y.Modules) :
    tensorPullbackMap g (𝟙 M) = 𝟙 (tensorPullbackObj g M) := by
  let p :
      SheafOfModules.changeOfRingsPresheaf.{w, w, w} (tensorPullbackRingMap g)
        (TopCat.Sheaf.inverseImageModule g.base Y.sheaf M) ⟶
      SheafOfModules.changeOfRingsPresheaf.{w, w, w} (tensorPullbackRingMap g)
        (TopCat.Sheaf.inverseImageModule g.base Y.sheaf M) :=
    { app := fun U ↦
        (ModuleCat.extendScalars ((tensorPullbackRingMap g).hom.app U).hom).map
          ((TopCat.Sheaf.inverseImageModuleMap g.base Y.sheaf M (𝟙 M)).val.app U)
      naturality := tensorPullbackPresheafMap_naturality g (𝟙 M) }
  have hp : p = 𝟙 _ := by
    apply PresheafOfModules.hom_ext
    intro U
    have hi :
        (TopCat.Sheaf.inverseImageModuleMap g.base Y.sheaf M (𝟙 M)).val.app U =
          𝟙 _ := by
      ext m
      simp [TopCat.Sheaf.inverseImageModuleMap, PresheafOfModules.homMk]
      rfl
    change (ModuleCat.extendScalars _).map _ = 𝟙 _
    rw [hi, CategoryTheory.Functor.map_id]
  change (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map p = _
  rw [hp, CategoryTheory.Functor.map_id]
  rfl

/-- Tensor pullback preserves composition. Source: Stacks, Tag 0095
(blueprint: def-pc-module-pullback).
Proof: the abelian inverse-image functor preserves composition; its module map is the
same map with linearity supplied. Extension of scalars and sheafification preserve composition. -/
theorem tensorPullbackMap_comp {M N P : Y.Modules} (a : M ⟶ N) (b : N ⟶ P) :
    tensorPullbackMap g (a ≫ b) = tensorPullbackMap g a ≫ tensorPullbackMap g b := by
  unfold tensorPullbackMap
  rw [← CategoryTheory.Functor.map_comp]
  congr 1
  apply PresheafOfModules.hom_ext
  intro U
  have hi :
      (TopCat.Sheaf.inverseImageModuleMap g.base Y.sheaf M (a ≫ b)).val.app U =
        (TopCat.Sheaf.inverseImageModuleMap g.base Y.sheaf M a).val.app U ≫
          (TopCat.Sheaf.inverseImageModuleMap g.base Y.sheaf N b).val.app U := by
    ext m
    simp [TopCat.Sheaf.inverseImageModuleMap, PresheafOfModules.homMk]
    rfl
  change (ModuleCat.extendScalars _).map _ =
    (ModuleCat.extendScalars _).map _ ≫ (ModuleCat.extendScalars _).map _
  rw [hi, CategoryTheory.Functor.map_comp]

/-- Pullback of modules along a scheme morphism, defined by the tensor formula.
Source: Stacks, Tag 0095 (blueprint: def-pc-module-pullback). -/
def tensorPullback : Y.Modules ⥤ X.Modules where
  obj := tensorPullbackObj g
  map := tensorPullbackMap g
  map_id := tensorPullbackMap_id g
  map_comp := tensorPullbackMap_comp g

/-- The tensor formula is left adjoint to the sectionwise module pushforward.
Source: Stacks, Tag 0096 (blueprint: def-pc-module-pullback).
Proof: apply the tensor/restriction adjunction to the change of rings, then the
inverse-image/direct-image module adjunction (008Y). The resulting bijection is natural
and its right-hand module action is restriction along `g.c`, hence the recorded pushforward.
These are the first two steps of this node, using lem-pc-module-pullback-adjunction. -/
theorem nonempty_tensorPullbackAdjunction : Nonempty (tensorPullback g ⊣ pushforward g) := by
  sorry

/-- Identity pullback is naturally isomorphic to the identity functor.
Source: Stacks, Tags 0095 and 0097 (blueprint: def-pc-module-pullback).
Proof: by the preceding adjunction and the identity pushforward isomorphism,
the tensor pullback of the identity and the identity functor are left adjoints of the
same functor. Uniqueness of left adjoints gives the isomorphism; this is the identity
case of step three, lem-pc-module-pullback-identity-composition. -/
theorem nonempty_tensorPullbackId (T : Scheme.{w}) :
    Nonempty (tensorPullback (𝟙 T) ≅ 𝟭 T.Modules) := by
  exact ⟨Adjunction.leftAdjointIdIso
    (Classical.choice (nonempty_tensorPullbackAdjunction (𝟙 T))) (pushforwardId T)⟩

/-- Composite pullback is naturally isomorphic to successive pullback.
Source: Stacks, Tag 0097 (blueprint: def-pc-module-pullback).
Proof: combine the two tensor-pullback adjunctions. Sectionwise pushforward composition
identifies their right adjoint with pushforward along `g ≫ h`. Uniqueness of left adjoints
gives this isomorphism; this is step three, lem-pc-module-pullback-identity-composition. -/
theorem nonempty_tensorPullbackComp (h : Y ⟶ Z) :
    Nonempty (tensorPullback (g ≫ h) ≅ tensorPullback h ⋙ tensorPullback g) := by
  exact ⟨(Adjunction.leftAdjointCompIso
    (Classical.choice (nonempty_tensorPullbackAdjunction h))
    (Classical.choice (nonempty_tensorPullbackAdjunction g))
    (Classical.choice (nonempty_tensorPullbackAdjunction (g ≫ h)))
    (pushforwardComp g h)).symm⟩

end
end AlgebraicGeometry.Scheme.Modules
