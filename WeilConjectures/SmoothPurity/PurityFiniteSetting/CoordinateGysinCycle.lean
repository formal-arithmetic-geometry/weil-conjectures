/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityGysinStructure
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
/-! # The actual unit cocycle of a Gysin chain lift
Source: latest blueprint, `lem-pur-gysin-structure.proof.md`, second assertion.
(blueprint: def-pur-coordinate-gysin-cycle).
-/
@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.RetractedSupport
open CochainComplex.HomComplex
namespace WeilConjectures.PurityFiniteSetting

/-- The single complex containing the constant sheaf in degree zero.
(blueprint: def-pur-coordinate-gysin-cycle). -/
abbrev gysinSingleComplex (P : PurityFiniteSetting.{u}) (T : Scheme.{u}) :=
  (CochainComplex.singleFunctor (ProSheaves P T) 0).obj (P.constant T)

/-- The closed degree-two component of a chain lift, evaluated before taking homology.
(blueprint: def-pur-coordinate-gysin-cycle). -/
def gysinChainComponent (P : PurityFiniteSetting.{u}) (T : Scheme.{u})
    (I : CochainComplex (ProSheaves P T) ℤ)
    (φ : gysinSingleComplex P T ⟶ I⟦(2 : ℤ)⟧) : P.constant T ⟶ I.X 2 :=
  (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (P.constant T)).inv ≫
    ((Cocycle.equivHomShift φ).val).v 0 2 rfl

/-- The degree-two component is closed, by the cocycle differential equation.
(blueprint: def-pur-coordinate-gysin-cycle). -/
theorem gysinChainComponent_closed (P : PurityFiniteSetting.{u}) (T : Scheme.{u})
    (I : CochainComplex (ProSheaves P T) ℤ)
    (φ : gysinSingleComplex P T ⟶ I⟦(2 : ℤ)⟧) :
    gysinChainComponent P T I φ ≫ I.d 2 3 = 0 := by
  let c : Cocycle (gysinSingleComplex P T) I 2 := Cocycle.equivHomShift φ
  have hc := Cochain.congr_v (Cocycle.δ_eq_zero c 3) 0 3 rfl
  rw [δ_v 2 3 rfl _ 0 3 rfl 2 1 rfl rfl] at hc
  have hd : (gysinSingleComplex P T).d 0 1 = 0 :=
    HomologicalComplex.single_obj_d (.up ℤ) 0 (P.constant T) 0 1
  rw [hd, zero_comp, smul_zero, add_zero] at hc
  simp only [Cochain.zero_v] at hc
  dsimp only [gysinChainComponent]
  rw [Category.assoc]
  simpa only [hc, comp_zero]

/-- The universal kernel comparison identifying cycles of sections with sections of cycles.
(blueprint: def-pur-coordinate-gysin-cycle). -/
def gysinCycleSectionsIso (P : PurityFiniteSetting.{u}) (T : Scheme.{u})
    (I : CochainComplex (ProSheaves P T) ℤ) :
    (((globalSectionsFunctor (Modules P) T).mapHomologicalComplex (.up ℤ)).obj I).cycles 2 ≅
      (globalSectionsFunctor (Modules P) T).obj (I.cycles 2) :=
  (((I.sc 2).map (globalSectionsFunctor (Modules P) T)).cyclesIsoKernel) ≪≫
    (asIso (kernelComparison (I.sc 2).g (globalSectionsFunctor (Modules P) T))).symm ≪≫
    (globalSectionsFunctor (Modules P) T).mapIso (I.sc 2).cyclesIsoKernel.symm

/-- The inverse cycles-of-sections comparison preserves the degree-two cycle inclusion.
Source: the kernel comparison in the explicit coefficient-unit cycle construction.
(blueprint: def-pur-coordinate-gysin-cycle).
Proof: compose with the forward cycle comparison. The sheaf and module cycle-to-kernel
isomorphisms identify their cycle inclusions with the kernel inclusions. The defining
identity of `kernelComparison` then identifies the remaining composite with the mapped
sheaf cycle inclusion. Cancel the forward isomorphism to obtain the stated identity. -/
theorem gysinCycleSectionsIso_inv_i (P : PurityFiniteSetting.{u}) (T : Scheme.{u})
    (I : CochainComplex (ProSheaves P T) ℤ) :
    (gysinCycleSectionsIso P T I).inv ≫
        (((globalSectionsFunctor (Modules P) T).mapHomologicalComplex (.up ℤ)).obj I).iCycles 2 =
      (globalSectionsFunctor (Modules P) T).map (I.iCycles 2) := by
  let E := globalSectionsFunctor (Modules P) T
  let S := I.sc 2
  have hi : S.cyclesIsoKernel.inv ≫ S.iCycles = kernel.ι S.g := by
    simp [ShortComplex.cyclesIsoKernel]
  have hk : (asIso (kernelComparison S.g E)).inv ≫ E.map (kernel.ι S.g) =
      kernel.ι (E.map S.g) := by
    apply (cancel_epi (kernelComparison S.g E)).mp
    change (asIso (kernelComparison S.g E)).hom ≫
      (asIso (kernelComparison S.g E)).inv ≫ _ = _
    simp only [Iso.hom_inv_id_assoc, kernelComparison_comp_ι]
  apply (cancel_epi (gysinCycleSectionsIso P T I).hom).mp
  simp only [Iso.hom_inv_id_assoc]
  symm
  change (S.map E).cyclesIsoKernel.hom ≫
    (asIso (kernelComparison S.g E)).inv ≫ E.map S.cyclesIsoKernel.inv ≫
      E.map S.iCycles = _
  rw [← E.map_comp, hi, hk]
  change (S.map E).cyclesIsoKernel.hom ≫ kernel.ι (S.map E).g = (S.map E).iCycles
  simp [ShortComplex.cyclesIsoKernel]

/-- The actual cycle Γ(φ^0)(1), transported through the universal kernel comparison.
The data use only `φ`, evaluation on the coefficient unit and `liftCycles`; no existence
statement or unproved comparison is used to choose this cycle.
(blueprint: def-pur-coordinate-gysin-cycle). -/
def gysinChainCycle (P : PurityFiniteSetting.{u}) (T : Scheme.{u})
    (I : CochainComplex (ProSheaves P T) ℤ)
    (φ : gysinSingleComplex P T ⟶ I⟦(2 : ℤ)⟧) :
    (((globalSectionsFunctor (Modules P) T).mapHomologicalComplex (.up ℤ)).obj I).cycles 2 :=
  (gysinCycleSectionsIso P T I).inv
    (P.gysinEvaluate T (I.liftCycles (gysinChainComponent P T I φ) 3 (by simp)
      (gysinChainComponent_closed P T I φ)))

/-- The derived morphism represented by a chain lift into `I[2]`.
(blueprint: def-pur-coordinate-gysin-cycle). -/
def gysinChainMorphism (P : PurityFiniteSetting.{u}) (T : Scheme.{u})
    (I : CochainComplex (ProSheaves P T) ℤ)
    (φ : gysinSingleComplex P T ⟶ I⟦(2 : ℤ)⟧) :
    (DerivedCategory.singleFunctor (ProSheaves P T) 0).obj (P.constant T) ⟶
      (DerivedCategory.Q.obj I)⟦(2 : ℤ)⟧ :=
  DerivedCategory.Q.map φ ≫ (DerivedCategory.Q.commShiftIso (2 : ℤ)).hom.app I

/-- Every derived map into a shifted K-injective has a chain lift.
Source: Mathlib `IsKInjective.Qh_map_bijective` and fullness of the homotopy quotient.
(blueprint: def-pur-coordinate-gysin-cycle).
Proof: undo the Q-shift comparison, lift to the homotopy category using K-injectivity,
then lift through its full quotient functor. Naturality of `quotientCompQhIso` gives
exactly the original map. No resolution or chain lift is chosen from an unproved theorem. -/
theorem exists_gysinChainMorphism (P : PurityFiniteSetting.{u}) (T : Scheme.{u})
    (I : CochainComplex (ProSheaves P T) ℤ) [I.IsKInjective]
    (f : (DerivedCategory.singleFunctor (ProSheaves P T) 0).obj (P.constant T) ⟶
      (DerivedCategory.Q.obj I)⟦(2 : ℤ)⟧) :
    ∃ φ : gysinSingleComplex P T ⟶ I⟦(2 : ℤ)⟧, gysinChainMorphism P T I φ = f := by
  let S := gysinSingleComplex P T
  let J := I⟦(2 : ℤ)⟧
  let q := HomotopyCategory.quotient (ProSheaves P T) (.up ℤ)
  let α := DerivedCategory.quotientCompQhIso (ProSheaves P T)
  let g : DerivedCategory.Q.obj S ⟶ DerivedCategory.Q.obj J :=
    f ≫ (DerivedCategory.Q.commShiftIso (2 : ℤ)).inv.app I
  obtain ⟨a, ha⟩ := (CochainComplex.IsKInjective.Qh_map_bijective (q.obj S) J).surjective
    (α.hom.app S ≫ g ≫ α.inv.app J)
  obtain ⟨φ, hφ⟩ := q.map_surjective a
  have hn := α.hom.naturality φ
  dsimp only [Functor.comp_map] at hn
  rw [hφ, ha] at hn
  have hg : DerivedCategory.Q.map φ = g := by
    apply (cancel_epi (α.hom.app S)).mp
    simpa only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id] using hn.symm
  refine ⟨φ, ?_⟩
  dsimp only [gysinChainMorphism]
  rw [hg]
  dsimp only [g]
  simp only [Category.assoc, Iso.inv_hom_id_app]
  exact Category.comp_id f

end WeilConjectures.PurityFiniteSetting
