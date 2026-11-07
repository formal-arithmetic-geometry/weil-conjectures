/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.QuotientSectionTensor.QuotientSectionTensorData
import WeilConjectures.CategoryTheory.SixFunctors.InternalSectionScalarAdjunctionSupplement
import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsUnit

/-! Invertibility of the normalized sectionwise scalar map. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj ChangeOfRings

namespace AlgebraicGeometry.ProEtale.QuotientSectionTensor

open QuotientChange IntegralQuotient ModuleRingedComparison

variable {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
  (a : Λ ⟶ Λ') [IsMonHom a]

-- Full faithfulness compares the underlying section maps with their internal preimages.
private theorem extension_section_hom_ext (T : Scheme.{u}) (M : Modules Λ T)
    (N : ModuleRingedComparison.modules Λ' T)
    (f g : (equivalence Λ' T).functor.obj ((extension a T).obj M) ⟶ N)
    (h : ∀ (W : T.ProEtᵒᵖ) (m : M.X.obj.obj W),
      f.val.app W (((Mod.extendUnit (coefficientMap a T) M).hom.hom.app W) m) =
        g.val.app W (((Mod.extendUnit (coefficientMap a T) M).hom.hom.app W) m)) :
    f = g := by
  let F := (equivalence Λ' T).functor
  let e := (equivalence Λ' T).counitIso.app N
  let f' := F.preimage (f ≫ e.inv)
  let g' := F.preimage (g ≫ e.inv)
  have hp : f' = g' := by
    apply Mod.extendScalarsObj_hom_ext'
    ext W m
    have hf : F.map f' = f ≫ e.inv := F.map_preimage _
    have hg : F.map g' = g ≫ e.inv := F.map_preimage _
    have hh := congrArg (fun x ↦ e.inv.val.app W x) (h W m)
    change (f ≫ e.inv).val.app W
      (((Mod.extendUnit (coefficientMap a T) M).hom.hom.app W) m) =
        (g ≫ e.inv).val.app W
          (((Mod.extendUnit (coefficientMap a T) M).hom.hom.app W) m) at hh
    rw [← hf, ← hg] at hh
    exact hh
  apply (cancel_mono e.inv).mp
  rw [← F.map_preimage (f ≫ e.inv), ← F.map_preimage (g ≫ e.inv)]
  exact congrArg F.map hp

private theorem section_pair_unit (T : Scheme.{u})
    [HasDerivedCategory.{u + 2} (ModuleRingedComparison.modules Λ T)]
    [HasDerivedCategory.{u + 2} (ModuleRingedComparison.modules Λ' T)]
    (s : SheafOfModules.ScalarDerivedPair.{u + 1, u, u + 1, u + 2}
      (sectionQuotient a T))
    (N : ModuleRingedComparison.modules Λ T) (W : T.ProEtᵒᵖ) (m : N.val.obj W) :
    (eqToHom (s.extension_obj N)).val.app W
        ((s.ordinaryAdjunction.unit.app N).val.app W m) =
      (toSheafify (Scheme.ProEt.topology T)
        (SheafOfModules.changeOfRingsPresheaf (sectionQuotient a T) N).presheaf).app W
          ((1 : (ring Λ' T).obj.obj W)
            ⊗ₜ[(ring Λ T).obj.obj W,((sectionQuotient a T).hom.app W).hom] m) := by
  simpa only [ModuleCat.extendRestrictScalarsAdj_unit_app_apply] using s.ordinaryUnit N W m

set_option maxHeartbeats 800000 in
-- The unit square compares the ordinary components of two scalar adjunctions.
private theorem canonical_section_extension (T : Scheme.{u}) (M : Modules Λ T) :
    ∃ c : (equivalence Λ' T).functor.obj ((extension a T).obj M) ⟶
        (SheafOfModules.changeOfRings.{u, u + 1, u + 1}
          (J := Scheme.ProEt.topology T) (R₁ := ring Λ T) (R₂ := ring Λ' T)
          (sectionQuotient a T)
          ((equivalence Λ T).functor.obj M) : ModuleRingedComparison.modules Λ' T),
      IsIso c ∧ ∀ (W : T.ProEtᵒᵖ) (m : M.X.obj.obj W),
        c.val.app W
            (((Mod.extendUnit (coefficientMap a T) M).hom.hom.app W) m) =
          (toSheafify (Scheme.ProEt.topology T)
            (SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1}
              (sectionQuotient a T)
              ((equivalence Λ T).functor.obj M)).presheaf).app W
                ((1 : (ring Λ' T).obj.obj W)
                  ⊗ₜ[(ring Λ T).obj.obj W,((sectionQuotient a T).hom.app W).hom] m) := by
  let := HasDerivedCategory.standard (Modules Λ T)
  let := HasDerivedCategory.standard (Modules Λ' T)
  let := HasDerivedCategory.standard (ModuleRingedComparison.modules Λ T)
  let := HasDerivedCategory.standard (ModuleRingedComparison.modules Λ' T)
  obtain ⟨s, restriction, hrestriction, comparison, _, htranspose, _⟩ :=
    InternalAbelianSheafModule.internal_section_scalar_adjunction
      (Scheme.ProEt.topology T) (coefficientMap a T)
  let c := comparison.app M ≪≫
    eqToIso (s.extension_obj ((equivalence Λ T).functor.obj M))
  refine ⟨c.hom, inferInstance, ?_⟩
  intro W m
  have ht := htranspose M ((extension a T).obj M) (𝟙 _)
  rw [Adjunction.homEquiv_id, CategoryTheory.Functor.map_id] at ht
  erw [Category.comp_id, Adjunction.homEquiv_unit] at ht
  have hu := congrArg (fun f ↦ f ≫
    (SheafOfModules.scalarRestriction.{u + 1, u, u + 1}
      (InternalAbelianSheafModule.sectionScalarMap.{u + 1, u + 1, u}
        (Scheme.ProEt.topology T) (coefficientMap a T))).map
          (comparison.hom.app M)) ht
  simp only [Category.assoc, ← CategoryTheory.Functor.map_comp, Iso.inv_hom_id_app] at hu
  have hv := congrArg (fun f ↦ f.val.app W m) hu
  change (comparison.hom.app M).val.app W
    ((restriction.hom.app ((extension a T).obj M)).val.app W
      (((Mod.extendRestrictAdjunction (coefficientMap a T)).unit.app M).hom.hom.app W m)) =
    (s.ordinaryAdjunction.unit.app ((equivalence Λ T).functor.obj M)).val.app W m at hv
  rw [hrestriction] at hv
  change (eqToHom (s.extension_obj ((equivalence Λ T).functor.obj M))).val.app W
    ((comparison.hom.app M).val.app W
      (((Mod.extendUnit (coefficientMap a T) M).hom.hom.app W) m)) = _
  have hunit : ((Mod.extendRestrictAdjunction (coefficientMap a T)).unit.app M).hom =
      (Mod.extendUnit (coefficientMap a T) M).hom :=
    Mod.extendRestrictAdjunction_unit_app_hom _ _
  rw [← hunit]
  erw [hv]
  exact section_pair_unit a T s ((equivalence Λ T).functor.obj M) W m

variable [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (modules Λ T)]
  [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (modules Λ' T)]

/-- A normalized scalar-extension transformation is objectwise invertible.
Source: Stacks 03EK and 06YY; scalar-extension generators detect isomorphisms.
(blueprint: lem-sfb-quotient-scalar-section-ordinary-normalized-iso).

Proof: the sheafified pure tensors `1 tensor m` generate the change-of-rings sheaf.
The generator equation identifies the transformation with the canonical extension map;
its inverse is induced by the universal restriction-of-scalars counit. -/
theorem scalar_section_ordinary_normalized_isIso (T : Scheme.{u})
    (model : SectionModel a T)
    (ordinary : QuotientChange.extension a T ⋙
        (equivalence Λ' T).functor ⟶
      (equivalence Λ T).functor ⋙ model.E)
    (hordinary : ∀ (M : Modules Λ T) (W : T.ProEtᵒᵖ) (m : M.X.obj.obj W),
      (((ordinary.app M) ≫ eqToHom (model.obj_eq _)).val.app W)
          (((Mod.extendUnit (ProEtale.coefficientMap a T) M).hom.hom.app W) m) =
        (toSheafify (Scheme.ProEt.topology T)
          (SheafOfModules.changeOfRingsPresheaf (sectionQuotient a T)
            ((equivalence Λ T).functor.obj M)).presheaf).app W
              ((1 : (ring Λ' T).obj.obj W)
                ⊗ₜ[(ring Λ T).obj.obj W,((sectionQuotient a T).hom.app W).hom] m)) :
    ∀ M : Modules Λ T, IsIso (ordinary.app M) := by
  intro M
  obtain ⟨c, hcis, hc⟩ := canonical_section_extension a T M
  let : IsIso c := hcis
  have he : ordinary.app M ≫ eqToHom (model.obj_eq _) = c := by
    apply extension_section_hom_ext a T M
    intro W m
    exact (hordinary M W m).trans (hc W m).symm
  have : IsIso (ordinary.app M ≫ eqToHom (model.obj_eq _)) := by
    rw [he]
    infer_instance
  exact IsIso.of_isIso_comp_right _ (eqToHom (model.obj_eq _))

end AlgebraicGeometry.ProEtale.QuotientSectionTensor
