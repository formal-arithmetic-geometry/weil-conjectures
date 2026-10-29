/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import WeilConjectures.AlgebraicGeometry.CondensedConstantConstructibility
public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteSchemeRing
public import WeilConjectures.CategoryTheory.InternalAbelianSheafModuleEquivalence
import WeilConjectures.AlgebraicGeometry.ConstantInternalModuleSheafEquivalence
import all WeilConjectures.AlgebraicGeometry.InternalModuleAbEquivalence

/-! # Specified finite coefficient realization and generator predicates

Source: blueprint finite comparison, coefficient paragraph
(auxiliary; not a blueprint node).

The constructions are kept separately so their coefficient-presentation lemmas can be
used by the localizing proof without a cyclic import.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
open CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj TensorProduct ZeroObject
namespace AlgebraicGeometry.ProEtale

/-- View fixed-scalar module presheaves as internal modules before sheafification.
Source: blueprint finite comparison, coefficient identification in proof step 1
(auxiliary; not a blueprint node). -/
def finiteComparisonPresheaf (X : Scheme.{u}) (B : Type) [CommRing B] :
    (X.ProEtᵒᵖ ⥤ ModuleCat.{u + 1} (ULift.{u + 1} B)) ⥤
      Mod (X.ProEtᵒᵖ ⥤ Ab.{u + 1})
        ((Functor.const X.ProEtᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} B))) where
  obj F := by
    let act :
        (Functor.const X.ProEtᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} B)) ⊗
            (F ⋙ forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} B)) Ab.{u + 1}) ⟶
          (F ⋙ forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} B)) Ab.{u + 1}) :=
      { app U := InternalAbelianSheafModule.ordinaryAction
          (S := ULift.{u + 1} B) (N := F.obj U)
        naturality U V f := by
          apply AddCommGrpCat.hom_ext_toIntLinearMap
          apply TensorProduct.ext'
          intro r m
          exact ((F.map f).hom.map_smul r m).symm }
    letI : ModObj
        ((Functor.const X.ProEtᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} B)))
        (F ⋙ forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} B)) Ab.{u + 1}) :=
      ModObj.mk' _ act (by
        apply NatTrans.ext
        funext U
        apply AddCommGrpCat.hom_ext_toIntLinearMap
        apply TensorProduct.ext'
        intro z m
        exact Int.cast_smul_eq_zsmul (M := F.obj U) (ULift.{u + 1} B) z.down m) (by
        apply NatTrans.ext
        funext U
        apply AddCommGrpCat.hom_ext_toIntLinearMap
        apply TensorProduct.ext_threefold
        intro r s m
        exact mul_smul (α := ULift.{u + 1} B) (β := F.obj U) r s m)
    exact ⟨F ⋙ forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} B)) Ab.{u + 1}⟩
  map f := Mod.homMk (Functor.whiskerRight f (forget₂ _ Ab.{u + 1})) (by
    apply NatTrans.ext
    funext U
    apply AddCommGrpCat.hom_ext_toIntLinearMap
    apply TensorProduct.ext'
    intro r m
    exact (f.app U).hom.map_smul r m)
  map_id F := by apply Mod.hom_ext; rfl
  map_comp f g := by apply Mod.hom_ext; rfl

/-- Sheafify the ordinary fixed-scalar action as an internal constant-ring action.
Source: blueprint finite comparison, proof step 1
(auxiliary; not a blueprint node). -/
def finiteComparisonConstantRealization (X : Scheme.{u}) (B : Type) [CommRing B] :
    Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1} B)) ⥤
      Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (Sheaf.sheafifyRingPresheaf.{u + 1, u, u + 1} (Scheme.ProEt.topology X)
          ((Functor.const X.ProEtᵒᵖ).obj (RingCat.of (ULift.{u + 1} B)))) :=
  sheafToPresheaf _ _ ⋙ finiteComparisonPresheaf X B ⋙
    (presheafToSheaf (Scheme.ProEt.topology X) Ab.{u + 1}).mapMod _

private noncomputable def finiteComparisonPresheafEncodingIso
    (X : Scheme.{u}) (B : Type) [CommRing B] :
    finiteComparisonPresheaf X B ⋙
        ConstantInternalModuleSheafEncoding.modulePresheafEncoding
          (C := X.ProEt) (ULift.{u + 1} B) (internalToModule (ULift.{u + 1} B)) ≅
      𝟭 (X.ProEtᵒᵖ ⥤ ModuleCat.{u + 1} (ULift.{u + 1} B)) := by
  refine NatIso.ofComponents (fun F ↦ NatIso.ofComponents (fun U ↦ ?_) ?_) ?_
  · exact ModuleCat.isoMk (Iso.refl _) (fun r ↦ by ext m; rfl)
  · intro U V f
    ext m
    rfl
  · intro F G f
    ext U m
    rfl

variable (B : Type) [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
  [DiscreteTopology B] [Finite B]

/-- Transport the sheafified scalar action along the specified coefficient ring isomorphism.
The isomorphism is exactly the pullback of the finite-discrete point identification.
Source: blueprint finite comparison, proof step 1
(auxiliary; not a blueprint node). -/
def finiteComparisonRealization (X : Scheme.{u})
    (eR : Sheaf.sheafifyRingPresheaf.{u + 1, u, u + 1} (coherentTopology Profinite.{u})
      ((Functor.const Profinite.{u}ᵒᵖ).obj (RingCat.of (ULift.{u + 1} B))) ≅
        Profinite.continuousMapRingObj.{u} B) [IsMonHom eR.hom] :
    Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1} B)) ⥤
      Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj (Profinite.continuousMapRingObj.{u} B) X) :=
  finiteComparisonConstantRealization X B ⋙
    Mod.comap (finiteDiscreteSchemeRingIso B X eR).inv

variable (eR : Sheaf.sheafifyRingPresheaf.{u + 1, u, u + 1} (coherentTopology Profinite.{u})
  ((Functor.const Profinite.{u}ᵒᵖ).obj (RingCat.of (ULift.{u + 1} B))) ≅
    Profinite.continuousMapRingObj.{u} B) [IsMonHom eR.hom]

end AlgebraicGeometry.ProEtale
