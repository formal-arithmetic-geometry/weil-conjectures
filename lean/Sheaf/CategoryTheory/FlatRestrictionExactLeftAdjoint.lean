/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J1
-/
module

public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits

/-! # Exact left adjoints to flat coefficient restriction

Source: Stacks Project, Modules on Sites, Tag 03CZ; Definition 03ER(3).
(blueprint: lem-weil-pbc-flat-restriction-exact-left-adjoint).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace SheafOfModules

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped ChangeOfRings

private noncomputable abbrev rb
    {C : Type u} [SmallCategory C] {K : GrothendieckTopology C}
    (R : Sheaf K CommRingCat.{u}) :=
  (sheafCompose K (forget₂ CommRingCat RingCat)).obj R

section Construction

variable {C : Type u} [SmallCategory C] {K : GrothendieckTopology C}
  {R S : Sheaf K CommRingCat.{u}} (a : R ⟶ S)

private noncomputable def extPre : SheafOfModules.{u} (rb R) ⥤
    PresheafOfModules.{u} (rb S).obj where
  obj M := changeOfRingsPresheaf.{u, u, u} a M
  map f :=
    { app U := (ModuleCat.extendScalars (a.hom.app U).hom).map (f.val.app U)
      naturality := changeOfRingsHom_naturality.{u, u, u} a _ f }
  map_id M := by
    apply PresheafOfModules.hom_ext
    intro U
    exact (ModuleCat.extendScalars (a.hom.app U).hom).map_id _
  map_comp f g := by
    apply PresheafOfModules.hom_ext
    intro U
    exact (ModuleCat.extendScalars (a.hom.app U).hom).map_comp _ _

private noncomputable def extFun :
    SheafOfModules.{u} (rb R) ⥤ SheafOfModules.{u} (rb S) :=
  extPre a ⋙ PresheafOfModules.sheafification (𝟙 (rb S).obj)

private noncomputable def preToRestrict
    (M : SheafOfModules.{u} (rb R)) (N : SheafOfModules.{u} (rb S))
    (f : changeOfRingsPresheaf.{u, u, u} a M ⟶
      (PresheafOfModules.restrictScalars (𝟙 (rb S).obj)).obj N.val) :
    M ⟶ (restrictScalars ((sheafCompose K (forget₂ CommRingCat RingCat)).map a)).obj N where
  val :=
    { app U := ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.toRestrictScalars
        (a.hom.app U).hom (f.app U)
      naturality := by
        intro U V i
        ext m
        change f.app V ((1 : S.obj.obj V) ⊗ₜ[R.obj.obj V,
          (a.hom.app V).hom] M.val.map i m) =
          N.val.map i (f.app U ((1 : S.obj.obj U) ⊗ₜ[R.obj.obj U,
            (a.hom.app U).hom] m))
        erw [← PresheafOfModules.naturality_apply f i]
        change _ = f.app V (changeOfRingsMap.{u, u, u} a M i _)
        rw [show ∀ s m, changeOfRingsMap.{u, u, u} a M i
          (s ⊗ₜ[R.obj.obj U, (a.hom.app U).hom] m) =
          S.obj.map i s ⊗ₜ[R.obj.obj V, (a.hom.app V).hom] M.val.map i m from
          Classical.choose_spec (exists_changeOfRingsMap.{u, u, u} a M i)]
        simp }

private noncomputable def preFromRestrict
    (M : SheafOfModules.{u} (rb R)) (N : SheafOfModules.{u} (rb S))
    (g : M ⟶ (restrictScalars
      ((sheafCompose K (forget₂ CommRingCat RingCat)).map a)).obj N) :
    changeOfRingsPresheaf.{u, u, u} a M ⟶
      (PresheafOfModules.restrictScalars (𝟙 (rb S).obj)).obj N.val where
  app U := ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars
    (a.hom.app U).hom (g.val.app U)
  naturality := by
    intro U V i
    apply ModuleCat.ExtendScalars.hom_ext
    intro m
    change ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars
      (a.hom.app V).hom (g.val.app V) (changeOfRingsMap.{u, u, u} a M i _) =
      N.val.map i (ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars
        (a.hom.app U).hom (g.val.app U) _)
    rw [show ∀ s m, changeOfRingsMap.{u, u, u} a M i
          (s ⊗ₜ[R.obj.obj U, (a.hom.app U).hom] m) =
          S.obj.map i s ⊗ₜ[R.obj.obj V, (a.hom.app V).hom] M.val.map i m from
          Classical.choose_spec (exists_changeOfRingsMap.{u, u, u} a M i)]
    simp only [map_one]
    let : Module (R.obj.obj V) (S.obj.obj V) :=
      Module.compHom (S.obj.obj V) (a.hom.app V).hom
    let : Module (R.obj.obj V) (N.val.obj V) :=
      Module.compHom (N.val.obj V) (a.hom.app V).hom
    let : Module (R.obj.obj U) (S.obj.obj U) :=
      Module.compHom (S.obj.obj U) (a.hom.app U).hom
    let : Module (R.obj.obj U) (N.val.obj U) :=
      Module.compHom (N.val.obj U) (a.hom.app U).hom
    erw [ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars_hom_apply
      («R» := R.obj.obj V) («S» := S.obj.obj V), TensorProduct.lift.tmul,
      ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars_hom_apply
      («R» := R.obj.obj U) («S» := S.obj.obj U), TensorProduct.lift.tmul]
    change (1 : S.obj.obj V) • (show N.val.obj V from g.val.app V (M.val.map i m)) =
      N.val.map i ((1 : S.obj.obj U) • (show N.val.obj U from g.val.app U m))
    simp only [one_smul]
    exact PresheafOfModules.naturality_apply g.val i m

private noncomputable def preHomEquiv
    (M : SheafOfModules.{u} (rb R)) (N : SheafOfModules.{u} (rb S)) :
    (changeOfRingsPresheaf.{u, u, u} a M ⟶
      (PresheafOfModules.restrictScalars (𝟙 (rb S).obj)).obj N.val) ≃
    (M ⟶ (restrictScalars ((sheafCompose K (forget₂ CommRingCat RingCat)).map a)).obj N) where
  toFun := preToRestrict a M N
  invFun := preFromRestrict a M N
  left_inv f := by
    apply PresheafOfModules.hom_ext
    intro U
    exact (ModuleCat.ExtendRestrictScalarsAdj.homEquiv (a.hom.app U).hom).left_inv _
  right_inv g := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    exact (ModuleCat.ExtendRestrictScalarsAdj.homEquiv (a.hom.app U).hom).right_inv _

private noncomputable def extHomEquiv
    (M : SheafOfModules.{u} (rb R)) (N : SheafOfModules.{u} (rb S)) :
    ((extFun a).obj M ⟶ N) ≃
      (M ⟶ (restrictScalars ((sheafCompose K (forget₂ CommRingCat RingCat)).map a)).obj N) :=
  (PresheafOfModules.sheafificationHomEquiv (𝟙 (rb S).obj)).trans (preHomEquiv a M N)

private theorem extHom_left
    (M M' : SheafOfModules.{u} (rb R)) (N : SheafOfModules.{u} (rb S))
    (f : M ⟶ M') (g : (extFun a).obj M' ⟶ N) :
    extHomEquiv a M N ((extFun a).map f ≫ g) = f ≫ extHomEquiv a M' N g := by
  change preHomEquiv a M N
    (((PresheafOfModules.sheafificationAdjunction (𝟙 (rb S).obj)).homEquiv _ _)
      ((PresheafOfModules.sheafification (𝟙 (rb S).obj)).map ((extPre a).map f) ≫ g)) = _
  erw [Adjunction.homEquiv_naturality_left]
  ext U m
  rfl

private theorem extHom_right
    (M : SheafOfModules.{u} (rb R)) (N N' : SheafOfModules.{u} (rb S))
    (f : (extFun a).obj M ⟶ N) (g : N ⟶ N') :
    extHomEquiv a M N' (f ≫ g) = extHomEquiv a M N f ≫
      (restrictScalars ((sheafCompose K (forget₂ CommRingCat RingCat)).map a)).map g := by
  change preHomEquiv a M N'
    (((PresheafOfModules.sheafificationAdjunction (𝟙 (rb S).obj)).homEquiv _ _)
      (f ≫ g)) = _
  rw [Adjunction.homEquiv_naturality_right]
  ext U m
  rfl

private noncomputable def extAdj : extFun a ⊣ restrictScalars
    ((sheafCompose K (forget₂ CommRingCat RingCat)).map a) :=
  Adjunction.mkOfHomEquiv
    { homEquiv := extHomEquiv a
      homEquiv_naturality_left_symm := by
        intro M M' N f g
        apply (extHomEquiv a M N).injective
        rw [Equiv.apply_symm_apply, extHom_left, Equiv.apply_symm_apply]
      homEquiv_naturality_right := extHom_right a _ _ _ }

private noncomputable abbrev scalarUnit : SheafOfModules.{u} (rb R) :=
  (restrictScalars ((sheafCompose K (forget₂ CommRingCat RingCat)).map a)).obj (unit (rb S))

private noncomputable def rawTensorIso (M : SheafOfModules.{u} (rb R)) :
    (changeOfRingsPresheaf.{u, u, u} a M).presheaf ≅
      (siteTensorPresheaf M.val (scalarUnit a).val).presheaf :=
  NatIso.ofComponents (fun U ↦ by
    letI : Module (R.obj.obj U) (S.obj.obj U) :=
      Module.compHom (S.obj.obj U) (a.hom.app U).hom
    exact (TensorProduct.comm (R.obj.obj U) (S.obj.obj U)
      (M.val.obj U)).toAddEquiv.toAddCommGrpIso) (by
    intro U V i
    apply AddCommGrpCat.hom_ext
    ext z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add z w hz hw => simp only [map_add, hz, hw]
    | tmul s m =>
      symm
      let : Module (R.obj.obj V) (S.obj.obj V) :=
        Module.compHom (S.obj.obj V) (a.hom.app V).hom
      change M.val.map i m ⊗ₜ[R.obj.obj V] S.obj.map i s =
        (TensorProduct.comm (R.obj.obj V) (S.obj.obj V) (M.val.obj V))
          (changeOfRingsMap.{u, u, u} a M i
            (s ⊗ₜ[R.obj.obj U, (a.hom.app U).hom] m))
      rw [show changeOfRingsMap.{u, u, u} a M i
          (s ⊗ₜ[R.obj.obj U, (a.hom.app U).hom] m) =
          S.obj.map i s ⊗ₜ[R.obj.obj V, (a.hom.app V).hom] M.val.map i m from
          Classical.choose_spec (exists_changeOfRingsMap.{u, u, u} a M i) s m]
      rfl)

private noncomputable def rawTensorNatIso :
    extPre a ⋙ PresheafOfModules.toPresheaf (rb S).obj ≅
      forget (rb R) ⋙ siteTensorRight (scalarUnit a).val ⋙
        PresheafOfModules.toPresheaf (rb R).obj :=
  NatIso.ofComponents (rawTensorIso a) (by
    intro M N f
    ext U z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add z w hz hw => simp only [map_add, hz, hw]
    | tmul s m => rfl)

private noncomputable def tensorNatIso :
    extFun a ⋙ toSheaf (rb S) ≅
      siteSheafTensorRight.{u, u, u, u} (scalarUnit.{u} a) ⋙ toSheaf (rb R) :=
  Functor.isoWhiskerRight (rawTensorNatIso a) (presheafToSheaf K AddCommGrpCat.{u})

end Construction

/-- Flat scalar restriction has an additive left adjoint preserving finite limits.
Source: Stacks Project, Tag 03CZ, lemma-adjointness-tensor-restrict; Tag 03ER(3).
(blueprint: lem-weil-pbc-flat-restriction-exact-left-adjoint).

Proof: Form the presheaf whose sections are S(U) tensor over R(U) M(U), with the
S(U)-action on the first factor. The tensor universal property defines restriction
maps and functoriality. Sheafify it as an S-module. Maps from this sheaf to N are,
by sheafification and the tensor universal properties, exactly R-linear maps from
M to the restriction of N; the inverse formulas are evaluation on 1 tensor m and
s tensor m mapped to s times f(m). These commute with site restrictions and are
natural in M and N, giving the adjunction. This functor is additive by the same
formulas. After restriction, tensor symmetry identifies it naturally with
siteSheafTensorRight of the restricted unit S: both are sheafifications of the
same balanced tensor presheaf. Restriction preserves and reflects exactness,
since kernels and sheafified cokernels have the same underlying abelian sheaves.
The flatness hypothesis therefore implies preservation of finite limits by the
S-module valued left adjoint. Its finite-colimit preservation follows from the
adjunction. The proof also applies to zero rings and to the empty site. -/
theorem flatRestriction_exact_leftAdjoint
    {C : Type u} [SmallCategory C] {K : GrothendieckTopology C}
    {R S : Sheaf K CommRingCat.{u}} (a : R ⟶ S)
    (hflat : IsFlatOnSite.{u, u, u, u}
      ((restrictScalars.{u} ((sheafCompose K (forget₂ CommRingCat RingCat)).map a)).obj
        (unit.{u} ((sheafCompose K (forget₂ CommRingCat RingCat)).obj S)))) :
    ∃ E : SheafOfModules.{u} ((sheafCompose K (forget₂ CommRingCat RingCat)).obj R) ⥤
        SheafOfModules.{u} ((sheafCompose K (forget₂ CommRingCat RingCat)).obj S),
      E.Additive ∧ PreservesFiniteLimits E ∧
        Nonempty (E ⊣ restrictScalars.{u}
          ((sheafCompose K (forget₂ CommRingCat RingCat)).map a)) := by
  have ht : PreservesFiniteLimits (siteSheafTensorRight.{u, u, u, u} (scalarUnit.{u} a)) := hflat.1
  have := ht
  have : PreservesFiniteLimits (toSheaf.{u} (rb R)) := inferInstance
  have : PreservesFiniteLimits
      (siteSheafTensorRight.{u, u, u, u} (scalarUnit.{u} a) ⋙ toSheaf.{u} (rb R)) :=
    comp_preservesFiniteLimits _ _
  have : PreservesFiniteLimits (extFun a ⋙ toSheaf (rb S)) :=
    preservesFiniteLimits_of_natIso (tensorNatIso a).symm
  have he : PreservesFiniteLimits (extFun a) :=
    preservesFiniteLimits_of_reflects_of_preserves (extFun a) (toSheaf (rb S))
  have := he
  refine ⟨extFun a, ?_, he, ⟨extAdj a⟩⟩
  have : (extFun a).IsLeftAdjoint := (extAdj a).isLeftAdjoint
  have : (extFun a).PreservesZeroMorphisms := by infer_instance
  exact Functor.additive_of_preserves_binary_products _

end SheafOfModules
