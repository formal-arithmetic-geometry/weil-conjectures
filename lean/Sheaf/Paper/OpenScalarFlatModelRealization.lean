/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F9
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleConstantExact
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Sheaf.AlgebraicGeometry.ProEtaleFiniteModules
public import WeilConjectures.SixFunctors.ProEtale.Comparison.Flat
import Sheaf.CategoryTheory.ConstantScalarRestrictionTensor
import all Sheaf.AlgebraicGeometry.ProEtaleConstantExact

/-! # Flatness of finite constant-coefficient realization

Source: Stacks Project, Tags 03CY and 03DA.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory
namespace AlgebraicGeometry.ProEtale.OpenScalarFlatModel

/-- The recorded pro-etale coefficient realization, restricted along its canonical
commutative constant-ring comparison. The finite ring has its discrete topology.
Source: Stacks 00YV, 03CY and 03ER
(blueprint: lem-sp-open-scalar-site-coherence). -/
private abbrev proRealization (A : Type (u + 1)) [CommRing A] [Finite A] (X : Scheme.{u}) :=
  letI : TopologicalSpace A := ⊥
  letI : DiscreteTopology A := ⟨rfl⟩
  finiteCoefficientRealization X A ⋙
    SheafOfModules.restrictScalars (finiteCoefficientCommRingComparison A X)

private def realizationRestrictionUnit
    (T : Scheme.{u}) (A : Type (u + 1)) [CommRing A] [Finite A]
    (M : Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A)) :
    M ⟶ (ConstantScalarRestriction.restriction (Scheme.ProEt.topology T) A).obj
      ((proRealization A T).obj M) := by
  letI : TopologicalSpace A := ⊥
  letI : DiscreteTopology A := ⟨rfl⟩
  let P := (finiteCoefficientModulePresheaf T.ProEt A).obj M.obj
  let η := (PresheafOfModules.sheafificationAdjunction.{u + 1}
    (finiteCoefficientScalarMap T A)).unit.app P
  have hc : toSheafify (Scheme.ProEt.topology T)
      ((Functor.const T.ProEtᵒᵖ).obj (RingCat.of A)) ≫
      ((constantCommuteCompose (Scheme.ProEt.topology T)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).inv.app
        (CommRingCat.of A)).hom ≫ (finiteCoefficientCommRingComparison A T).hom =
      finiteCoefficientScalarMap T A := by
    rw [← finiteTensorComparisonUnit A T]
    rw [← finiteTensorForgetUnit A T]
    have hi := congrArg (fun f ↦ f.hom) (Iso.hom_inv_id_app
      (constantCommuteCompose (Scheme.ProEt.topology T)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})) (CommRingCat.of A))
    change _ ≫ (((constantCommuteCompose (Scheme.ProEt.topology T)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).hom.app (CommRingCat.of A)).hom ≫
      ((constantCommuteCompose (Scheme.ProEt.topology T)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).inv.app (CommRingCat.of A)).hom) ≫ _ = _
    change _ ≫ _ = _ at hi
    erw [hi]
    erw [Category.id_comp]
  refine ⟨{ app := ?_, naturality := ?_ }⟩
  · intro W
    let N := (ConstantScalarRestriction.restriction (Scheme.ProEt.topology T) A).obj
      ((proRealization A T).obj M)
    letI : Module A (N.obj.obj W) := (N.obj.obj W).isModule
    change M.obj.obj W ⟶ N.obj.obj W
    refine ConcreteCategory.ofHom (C := ModuleCat A)
      (X := M.obj.obj W) (Y := N.obj.obj W)
      { toFun := η.app W
        map_add' := (η.app W).hom.map_add
        map_smul' := ?_ }
    intro a m
    let S := (PresheafOfModules.sheafification.{u + 1}
      (finiteCoefficientScalarMap T A)).obj P
    let : Module ((finiteCoefficientRingSheaf T A).obj.obj W) (S.val.obj W) :=
      (S.val.obj W).isModule
    have h := (η.app W).hom.map_smul a m
    change η.app W (a • m) =
      @SMul.smul ((finiteCoefficientRingSheaf T A).obj.obj W) (S.val.obj W) _
        ((finiteCoefficientScalarMap T A).app W a) (η.app W m) at h
    change η.app W (a • m) =
      @SMul.smul ((finiteCoefficientRingSheaf T A).obj.obj W) (S.val.obj W) _
        ((finiteCoefficientCommRingComparison A T).hom.app W
        (((constantCommuteCompose (Scheme.ProEt.topology T)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).inv.app
          (CommRingCat.of A)).hom.app W
            ((toSheafify (Scheme.ProEt.topology T)
              ((Functor.const T.ProEtᵒᵖ).obj (RingCat.of A))).app W a))) (η.app W m)
    rw [h]
    congr 1
    exact (ConcreteCategory.congr_hom (congr_app hc W) a).symm
  · intro W V f
    ext m
    exact ConcreteCategory.congr_hom (η.naturality f) m

private theorem realizationRestrictionUnit_isIso
    (T : Scheme.{u}) (A : Type (u + 1)) [CommRing A] [Finite A]
    (M : Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A)) :
    IsIso (realizationRestrictionUnit T A M) := by
  rw [← isIso_iff_of_reflects_iso _
    (sheafCompose (Scheme.ProEt.topology T)
      (forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1}))]
  rw [← isIso_iff_of_reflects_iso _ (sheafToPresheaf _ _)]
  change IsIso (toSheafify (Scheme.ProEt.topology T)
    (M.obj ⋙ forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1}))
  exact isIso_toSheafify (Scheme.ProEt.topology T)
    ((sheafCompose (Scheme.ProEt.topology T)
      (forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1})).obj M).property

/-- The canonical finite-coefficient realization preserves flat module sheaves.
Source: Stacks Project, Tags 03CY and 03DA
(blueprint: lem-sp-finite-coefficient-realization-flat).

Proof: the sheafification unit of the associated module sheaf is linear over
constant scalars, since the constant-ring comparison preserves those constants.
Its underlying additive map is the sheafification unit of an additive sheaf,
so it is invertible. Restricting the realized object to constant scalars therefore
recovers the original flat sheaf. The constant-scalar restriction equivalence
preserves and reflects flatness. This applies also to the empty site and zero ring. -/
theorem finiteCoefficientRealization_flat
    (T : Scheme.{u}) (A : Type (u + 1)) [CommRing A] [Finite A]
    (M : Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A))
    (hM : ObjectProperty.flat M) :
    letI : TopologicalSpace A := ⊥
    letI : DiscreteTopology A := ⟨rfl⟩
    SheafOfModules.IsFlatOnSite (J := Scheme.ProEt.topology T)
      (R := finiteCoefficientCommRing A T)
      ((finiteCoefficientRealization T A ⋙
        SheafOfModules.restrictScalars (finiteCoefficientCommRingComparison A T)).obj M) := by
  let : TopologicalSpace A := ⊥
  let : DiscreteTopology A := ⟨rfl⟩
  apply (ConstantScalarRestriction.flat_iff (Scheme.ProEt.topology T) A _).mpr
  have := realizationRestrictionUnit_isIso T A M
  exact (ObjectProperty.prop_of_iso ObjectProperty.flat
    (asIso (realizationRestrictionUnit T A M)) hM).2


end AlgebraicGeometry.ProEtale.OpenScalarFlatModel
