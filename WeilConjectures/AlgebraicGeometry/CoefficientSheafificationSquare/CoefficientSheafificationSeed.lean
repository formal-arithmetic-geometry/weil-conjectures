/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification

/-! # Extending the scalar-restricted module-sheafification unit

The construction and its forgetful identity are proved directly from the
module-sheafification adjunction.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genCtorIdx false
set_option Elab.async false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.CoefficientSheafificationSquare
section
variable {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    {R S : Type (u + 1)} [CommRing R] [CommRing S] (r : R →+* S)
    {T U : Sheaf J RingCat.{u + 1}} (a : T ⟶ U)
    (α : (Functor.const Cᵒᵖ).obj (RingCat.of R) ⟶ T.obj)
    (β : (Functor.const Cᵒᵖ).obj (RingCat.of S) ⟶ U.obj)
    [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α]
    [Presheaf.IsLocallyInjective J β] [Presheaf.IsLocallySurjective J β]
    [HasWeakSheafify J AddCommGrpCat.{u + 1}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
    (ha : (Functor.const Cᵒᵖ).map (RingCat.ofHom r) ≫ β = α ≫ a.hom)

include ha in
@[irreducible] def rawSeed
    (P : PresheafOfModules.{u + 1} ((Functor.const Cᵒᵖ).obj (RingCat.of S))) :
    (rawRestriction r).obj P ⟶
      (PresheafOfModules.restrictScalars α).obj
        ((SheafOfModules.restrictScalars a).obj
          ((PresheafOfModules.sheafification β).obj P)).val := by
  let η := (PresheafOfModules.sheafificationAdjunction β).unit.app P
  refine { app := fun V ↦ ?_, naturality := ?_ }
  · rename_i V
    refine ModuleCat.ofHom
      (X := ((rawRestriction r).obj P).obj V)
      (Y := ((PresheafOfModules.restrictScalars α).obj
        ((SheafOfModules.restrictScalars a).obj
          ((PresheafOfModules.sheafification β).obj P)).val).obj V)
      { toFun := fun x ↦ η.app V x
        map_add' := map_add _
        map_smul' := ?_ }
    intro s x
    have ht := congrArg (fun t ↦ t.app V s) ha
    change β.app V (r s) = a.hom.app V (α.app V s) at ht
    have he := (η.app V).hom.map_smul (r s) (show P.obj V from x)
    change η.app V (r s • (show P.obj V from x)) =
      (β.app V (r s)) •
        (show ((PresheafOfModules.sheafification β).obj P).val.obj V from η.app V x) at he
    rw [ht] at he
    exact he
  · intro V W f
    ext x
    exact PresheafOfModules.naturality_apply η f x

@[irreducible] def rawMap
    (P : PresheafOfModules.{u + 1} ((Functor.const Cᵒᵖ).obj (RingCat.of S))) :
    (PresheafOfModules.sheafification α).obj ((rawRestriction r).obj P) ⟶
      (SheafOfModules.restrictScalars a).obj
        ((PresheafOfModules.sheafification β).obj P) :=
  (PresheafOfModules.sheafificationHomEquiv α).symm (rawSeed J r a α β ha P)

end
end AlgebraicGeometry.Scheme.CoefficientSheafificationSquare
