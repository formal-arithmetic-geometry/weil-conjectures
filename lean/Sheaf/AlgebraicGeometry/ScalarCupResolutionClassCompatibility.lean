/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W4
-/
module

public import Sheaf.AlgebraicGeometry.FieldLinearModuleCohomologyOperations
public import Sheaf.Paper.ModuleCupResolutionData
import all Sheaf.AlgebraicGeometry.ScalarExtCupDegreeZero
import Sheaf.Paper.ModuleCupShiftedUnitChainTensor
import WeilConjectures.CategoryTheory.Monoidal.Instances.CochainComplex
import Mathlib.Algebra.Homology.BifunctorShift

/-! # Scalar cup on resolution classes

Source: Stacks Project, Cohomology, section-cup-product and Tag 0FKV.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped TensorProduct
open Opposite TopologicalSpace
namespace AlgebraicGeometry.Scheme.Modules

/-- The scalar Ext cup is represented by the paired cycle of a module resolution.
Source: Stacks Project, Cohomology, Tags 01F7 and 0FKV, resolution cup comparison.
(blueprint: new-sc-scalar-cup-resolution-class-compatibility).

Proof: Choose injective comparisons for the three acyclic resolutions and use the
cocycle formula defining `moduleExtEquiv`. Evaluation at the unit identifies the
scalar Ext representatives with the section cycles. Exact restriction of scalars
carries the signed Yoneda tensor construction to the sectionwise tensor pairing;
the coefficient map sends pure tensors to `D.pair`. The Leibniz equation gives the
paired target cycle, and the comparison maps identify its class with the target
`D.class`. Naturality and homotopy independence remove the chosen comparisons.
The argument includes degree zero, zero coefficients, and empty schemes.

Audit: the preceding proposed proof is invalid in positive odd bidegrees. The
left-then-right Yoneda tensor uses the left-shift comparison first. Its component
on the (p,q) summand is (-1)^(p*q), whereas `hc` prescribes the unsigned paired
cycle. The private lemmas below verify the scalar product's order and the sign
at (1,1), where it is nontrivial over the rationals. See report.md for the
geometric counterexample and the precise missing-sign calculation. The original
statement is retained for review; it has not been replaced by a weaker statement.
-/
-- STATEMENT-DISPUTED: scalarExtCup composes the left class before the right class.
-- With the unsigned resolution pairing in hc, this introduces (-1)^(p*q).
-- In particular, two degree-one classes yield the negative of the asserted class.
-- The proved private lemmas below exhibit the order, the sign and a nonzero test.
theorem scalarCup_resolution_class_compatibility
    {k : Type w} [Field k] {X : Scheme.{w}}
    (f : X ⟶ Spec (CommRingCat.of k)) (F G : X.Modules) (p q : ℕ)
    (D : CupResolutionPairing F G)
    (a : ((((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj D.left.K).sc p).moduleCatLeftHomologyData.K)
    (b : ((((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj D.right.K).sc q).moduleCatLeftHomologyData.K)
    (c : ((((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj D.target.K).sc (p + q)).moduleCatLeftHomologyData.K)
    (hc : c.val = D.pair p q ⊤ a.val b.val) :
    scalarCohomologyCup f F G p q (D.left.class p a) (D.right.class q b) =
      D.target.class (p + q) c := by
  sorry


section SignAudit
open HomologicalComplex
noncomputable section
attribute [local instance] Sheaf.monoidalCategory HasExt.standard

/-- The scalar cup applies the left Ext class first, with no degree sign inserted.
This follows from exact-functor transport along the right unitor and Ext associativity. -/
private theorem scalarCup_yoneda_order
    {k : Type w} [Field k] {X : Scheme.{w}} {A B : KSheaf X k} {p q : ℕ}
    (a : Abelian.Ext.{w + 1} (𝟙_ (KSheaf X k)) A p)
    (b : Abelian.Ext.{w + 1} (𝟙_ (KSheaf X k)) B q) :
    scalarExtCup a b = a.comp
      ((Abelian.Ext.mk₀ (ρ_ A).inv).comp
        (b.mapExactFunctor (tensorLeft A)) (zero_add q)) rfl := by
  unfold scalarExtCup
  rw [ext_iso_transport (tensorRight (𝟙_ (KSheaf X k)))
    (rightUnitorNatIso (KSheaf X k)) a]
  simp only [rightUnitorNatIso, NatIso.ofComponents_hom_app,
    NatIso.ofComponents_inv_app]
  simp only [← Abelian.Ext.comp_assoc_of_second_deg_zero,
    Abelian.Ext.mk₀_comp_mk₀]
  have hunit : (λ_ (𝟙_ (KSheaf X k))).inv ≫ (ρ_ (𝟙_ (KSheaf X k))).hom = 𝟙 _ := by
    rw [← unitors_equal]
    simp
  rw [hunit, Abelian.Ext.mk₀_id_comp]

set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048

/-- Moving the left shift out before the right shift negates the (1,1) summand.
Source: Mathlib's two summand formulas for mapBifunctorShift₁Iso and Shift₂Iso. -/
private theorem oddShiftTensor_component (K L : CochainComplex (ModuleCat ℚ) ℤ) :
    ιTensorObj (K⟦(1 : ℤ)⟧) (L⟦(1 : ℤ)⟧) 0 0 0 (by decide) ≫
        (CochainComplex.mapBifunctorShift₁Iso K (L⟦(1 : ℤ)⟧)
          (curriedTensor (ModuleCat ℚ)) 1).hom.f 0 ≫
        ((CochainComplex.mapBifunctorShift₂Iso K L
          (curriedTensor (ModuleCat ℚ)) 1).hom⟦(1 : ℤ)⟧').f 0 =
      -(((K.shiftFunctorObjXIso 1 0 1 (by decide)).hom ⊗ₘ
          (L.shiftFunctorObjXIso 1 0 1 (by decide)).hom) ≫
        ιTensorObj K L 1 1 2 (by decide) ≫
        ((K ⊗ L).shiftFunctorObjXIso 1 1 2 (by decide)).inv) := by
  erw [CochainComplex.ι_mapBifunctorShift₁Iso_hom_f_assoc K
    (L⟦(1 : ℤ)⟧) (curriedTensor (ModuleCat ℚ)) 1 0 0 0 (by decide)
      1 1 (by decide) (by decide)]
  change _ ≫ (_ ≫ _ ≫ _) = _
  simp only [CochainComplex.shiftFunctor_map_f',
    CochainComplex.shiftFunctorObjXIso, HomologicalComplex.XIsoOfEq_rfl,
    Iso.refl_inv]
  erw [Category.id_comp]
  erw [CochainComplex.ι_mapBifunctorShift₂Iso_hom_f K L
    (curriedTensor (ModuleCat ℚ)) 1 1 0 1 (by decide) 1 2 (by decide) (by decide)]
  simp only [Int.mul_one, Int.negOnePow_one, Units.neg_smul, one_smul,
    Preadditive.comp_neg, Category.assoc,
    tensorHom_def, curriedTensor_obj_map, curriedTensor_map_app]
  rfl

/-- The unsigned (1,1) summand is not its negative on two shifted rational units.
The normalized single-tensor isomorphism reduces an equality to -1 = 1 in Q. -/
private theorem oddTensorSummand_ne_neg :
    let K := cupSingleModule ℚ 1;
    -(ιTensorObj K K 1 1 2 (by decide)) ≠ ιTensorObj K K 1 1 2 (by decide) := by
  dsimp only
  intro h
  obtain ⟨i, hi⟩ := exists_cupShiftedUnitChainTensor ℚ 1 1
  let K := cupSingleModule ℚ 1
  let e := HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 1 (ModuleCat.of ℚ ℚ)
  let e₂ := HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 2 (ModuleCat.of ℚ ℚ)
  change i.hom.f 2 (e₂.inv 1) =
    (ιTensorObj K K 1 1 2 (by decide)) ((e.inv 1) ⊗ₜ[ℚ] (e.inv 1)) at hi
  have he := ConcreteCategory.congr_hom h ((e.inv 1) ⊗ₜ[ℚ] (e.inv 1))
  change -((ιTensorObj K K 1 1 2 (by decide)) ((e.inv 1) ⊗ₜ[ℚ] (e.inv 1))) =
    (ιTensorObj K K 1 1 2 (by decide)) ((e.inv 1) ⊗ₜ[ℚ] (e.inv 1)) at he
  rw [← hi] at he
  have hh := congrArg (fun x ↦ e₂.hom (i.inv.f 2 x)) he
  simp only [map_neg] at hh
  have hc : i.inv.f 2 (i.hom.f 2 (e₂.inv 1)) = e₂.inv 1 := by
    have hh := ConcreteCategory.congr_hom
      (congrArg (fun f ↦ f.f 2) i.hom_inv_id) (e₂.inv 1)
    change i.inv.f 2 (i.hom.f 2 (e₂.inv 1)) = e₂.inv 1 at hh
    exact hh
  change -e₂.hom (i.inv.f 2 (i.hom.f 2 (e₂.inv 1))) =
    e₂.hom (i.inv.f 2 (i.hom.f 2 (e₂.inv 1))) at hh
  rw [hc, e₂.inv_hom_id_apply] at hh
  norm_num at hh


/-- A concrete test of the disputed unsigned comparison, before localization.
Two single complexes in degree one give different signed and unsigned maps. -/
private theorem oddShiftTensor_not_unsigned :
    let K := cupSingleModule ℚ 1;
    ιTensorObj (K⟦(1 : ℤ)⟧) (K⟦(1 : ℤ)⟧) 0 0 0 (by decide) ≫
        (CochainComplex.mapBifunctorShift₁Iso K (K⟦(1 : ℤ)⟧)
          (curriedTensor (ModuleCat ℚ)) 1).hom.f 0 ≫
        ((CochainComplex.mapBifunctorShift₂Iso K K
          (curriedTensor (ModuleCat ℚ)) 1).hom⟦(1 : ℤ)⟧').f 0 ≠
      ιTensorObj K K 1 1 2 (by decide) := by
  dsimp only
  intro h
  have he := oddShiftTensor_component (cupSingleModule ℚ 1) (cupSingleModule ℚ 1)
  rw [h] at he
  have hi : (ιTensorObj (cupSingleModule ℚ 1) (cupSingleModule ℚ 1) 1 1 2 (by decide)) =
      -ιTensorObj (cupSingleModule ℚ 1) (cupSingleModule ℚ 1) 1 1 2 (by decide) := by
    simp only [CochainComplex.shiftFunctorObjXIso, HomologicalComplex.XIsoOfEq_rfl,
      Iso.refl_hom, Iso.refl_inv] at he
    erw [tensorHom_id, id_whiskerRight] at he
    simp only [Category.id_comp] at he
    exact he
  exact oddTensorSummand_ne_neg hi.symm

end
end SignAudit

end AlgebraicGeometry.Scheme.Modules
