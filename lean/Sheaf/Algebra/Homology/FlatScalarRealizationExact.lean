/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F6
-/
module

public import Sheaf.Algebra.Homology.FlatScalarRealization
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.CategoryTheory.Sites.Limits
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification

/-! # Exactness of flat scalar realization -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct ChangeOfRings

namespace SheafOfModules
variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  {A : Type (max u v)} [CommRing A] {R : Sheaf J CommRingCat.{max u v}}
  [HasSheafify J AddCommGrpCat.{max u v}]
  (α : realizationRing J A ⟶ R)

private abbrev baseRing :=
  (sheafCompose J (forget₂ CommRingCat RingCat)).obj (realizationRing J A)

private abbrev targetRing := (sheafCompose J (forget₂ CommRingCat RingCat)).obj R

private def scalarPre : realizationModules J A ⥤
    PresheafOfModules.{max u v} (targetRing (J := J) (R := R)).obj where
  obj M := changeOfRingsPresheafOfUniverses.{v, u, max u v, max u v} α M
  map f :=
    { app U := (ModuleCat.extendScalars (α.hom.app U).hom).map (f.val.app U)
      naturality := changeOfRingsHom_naturalityOfUniverses α _ f }
  map_id M := by
    apply PresheafOfModules.hom_ext
    intro U
    exact (ModuleCat.extendScalars (α.hom.app U).hom).map_id _
  map_comp f g := by
    apply PresheafOfModules.hom_ext
    intro U
    exact (ModuleCat.extendScalars (α.hom.app U).hom).map_comp _ _

private abbrev scalarUnit : realizationModules J A :=
  (restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map α)).obj
    (unit (targetRing (J := J) (R := R)))

private def scalarRawIso (M : realizationModules J A) :
    (changeOfRingsPresheafOfUniverses.{v, u, max u v, max u v} α M).presheaf ≅
      (siteTensorPresheaf M.val (scalarUnit J α).val).presheaf :=
  NatIso.ofComponents (fun U ↦ by
    let : Module ((realizationRing J A).obj.obj U) (R.obj.obj U) :=
      Module.compHom (R.obj.obj U) (α.hom.app U).hom
    exact (TensorProduct.comm ((realizationRing J A).obj.obj U) (R.obj.obj U)
      (M.val.obj U)).toAddEquiv.toAddCommGrpIso) (by
    intro U V i
    apply AddCommGrpCat.hom_ext
    ext z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add z w hz hw => simp only [map_add, hz, hw]
    | tmul s m =>
      symm
      let : Module ((realizationRing J A).obj.obj V) (R.obj.obj V) :=
        Module.compHom (R.obj.obj V) (α.hom.app V).hom
      change M.val.map i m ⊗ₜ[(realizationRing J A).obj.obj V] R.obj.map i s =
        (TensorProduct.comm ((realizationRing J A).obj.obj V) (R.obj.obj V)
          (M.val.obj V)) (changeOfRingsMapOfUniverses α M i
            (s ⊗ₜ[(realizationRing J A).obj.obj U, (α.hom.app U).hom] m))
      rw [show changeOfRingsMapOfUniverses.{v, u, max u v, max u v} α M i
          (s ⊗ₜ[(realizationRing J A).obj.obj U, (α.hom.app U).hom] m) =
          R.obj.map i s ⊗ₜ[(realizationRing J A).obj.obj V, (α.hom.app V).hom]
            M.val.map i m from
          changeOfRingsMap_tmulOfUniverses.{v, u, max u v, max u v} α M i s m]
      rfl)

private def scalarRawNatIso :
    scalarPre J α ⋙ PresheafOfModules.toPresheaf (targetRing (J := J) (R := R)).obj ≅
      forget (baseRing J (A := A)) ⋙ siteTensorRight (scalarUnit J α).val ⋙
        PresheafOfModules.toPresheaf (baseRing J (A := A)).obj :=
  NatIso.ofComponents (scalarRawIso J α) (by
    intro M N f
    ext U z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add z w hz hw => simp only [map_add, hz, hw]
    | tmul s m => rfl)

private def scalarUnderlyingIso :
    flatScalarExtension J α ⋙ toSheaf (targetRing (J := J) (R := R)) ≅
      siteSheafTensorRight.{v, u, max u v, max u v} (A := realizationRing J A)
        (scalarUnit J α) ⋙ toSheaf (baseRing J (A := A)) :=
  Functor.isoWhiskerRight (scalarRawNatIso J α)
    (presheafToSheaf J AddCommGrpCat.{max u v})

/-- Flatness of the target algebra makes the canonical scalar realization exact.
Source: Stacks Project, Modules on Sites, Tags 093J and 03ER(3)
(blueprint: lem-sfb-flat-scalar-realization-exact).
Proof: after forgetting to abelian sheaves, scalar extension is naturally tensor
with the restricted target ring. The comparison is the sheafification of tensor
symmetry on sections. Flatness makes that tensor functor exact. Forgetting the
target action reflects finite limits and finite colimits, hence extension is exact.
Compose with exact constant module realization. The zero ring and empty site obey
the same tensor-symmetry identity. -/
theorem flatScalarRealization_exact
    (hflat : IsFlatOnSite (J := J) (R := realizationRing J A)
      ((restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map α)).obj
        (unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)))) :
    PreservesFiniteLimits (flatScalarRealization J α) ∧
      PreservesFiniteColimits (flatScalarRealization J α) := by
  have : PreservesFiniteLimits
      (siteSheafTensorRight.{v, u, max u v, max u v} (A := realizationRing J A)
        (scalarUnit J α)) := hflat.1
  have : PreservesFiniteColimits
      (siteSheafTensorRight.{v, u, max u v, max u v} (A := realizationRing J A)
        (scalarUnit J α)) := hflat.2
  have : PreservesFiniteLimits
      (siteSheafTensorRight.{v, u, max u v, max u v} (A := realizationRing J A)
        (scalarUnit J α) ⋙ toSheaf (baseRing J (A := A))) :=
    comp_preservesFiniteLimits _ _
  have : PreservesFiniteColimits
      (siteSheafTensorRight.{v, u, max u v, max u v} (A := realizationRing J A)
        (scalarUnit J α) ⋙ toSheaf (baseRing J (A := A))) :=
    comp_preservesFiniteColimits _ _
  have : PreservesFiniteLimits
      (flatScalarExtension J α ⋙ toSheaf (targetRing (J := J) (R := R))) :=
    preservesFiniteLimits_of_natIso (scalarUnderlyingIso J α).symm
  have : PreservesFiniteColimits
      (flatScalarExtension J α ⋙ toSheaf (targetRing (J := J) (R := R))) :=
    preservesFiniteColimits_of_natIso (scalarUnderlyingIso J α).symm
  have : PreservesFiniteLimits (flatScalarExtension J α) :=
    preservesFiniteLimits_of_reflects_of_preserves _ (toSheaf (targetRing (J := J) (R := R)))
  have : ReflectsFiniteColimits (toSheaf (targetRing (J := J) (R := R))) :=
    by infer_instance
  have : PreservesFiniteColimits (flatScalarExtension J α) :=
    preservesFiniteColimits_of_reflects_of_preserves _ (toSheaf (targetRing (J := J) (R := R)))
  exact ⟨comp_preservesFiniteLimits _ _, comp_preservesFiniteColimits _ _⟩

end SheafOfModules
