/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R1
-/
module

public import Sheaf.Paper.FiniteReductionSystem
import Sheaf.Paper.FiniteReductionRestrictTensor

/-!
# Flat models under surjective extension of constant scalars

Source: Stacks Project, Tag 05V4 and Tag 08G1.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped TensorProduct

namespace AlgebraicGeometry.FiniteReduction

section Site
variable {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
    (J : GrothendieckTopology C)
    {A B : Type (u + 1)} [CommRing A] [CommRing B]

omit [EssentiallySmall.{u + 1} C] in
private theorem relations_restrict_equiv (e : B ≃+* A)
    {P : Cᵒᵖ ⥤ ModuleCat.{u + 1} A}
    (hP : Presheaf.HasLocallyTrivialRelations J P) :
    Presheaf.HasLocallyTrivialRelations J (P ⋙ ModuleCat.restrictScalars e.toRingHom) := by
  intro V s q y E hE
  obtain ⟨S, hS, hfac⟩ := hP y (fun l j ↦ e (E l j)) hE
  refine ⟨S, hS, fun W f hf ↦ ?_⟩
  obtain ⟨t, D, z, hD, hz⟩ := hfac f hf
  refine ⟨t, fun j k ↦ e.symm (D j k), z, ?_, ?_⟩
  · ext l k
    apply e.injective
    have h := congrFun (congrFun hD l) k
    simpa only [Matrix.mul_apply, Matrix.zero_apply, map_sum, map_mul, map_zero,
      e.apply_symm_apply] using h
  · intro j
    change P.map f.op (y j) = ∑ k, e (e.symm (D j k)) • z k
    simpa only [RingEquiv.apply_symm_apply] using hz j

/-- Extension of scalars sends flat sheaves to flat sheaves for a surjective map
of Noetherian constant coefficient rings. Source: Stacks Tag 05V4.
(blueprint: lem-pur-finite-reduction-flat-extension).
Proof: identify extension with reduction modulo the kernel followed by the coefficient
ring equivalence. Reduction preserves locally trivial relations. Transporting each
coefficient in a relation through the ring equivalence proves flatness after transport. -/
theorem flat_extend_of_surjective [IsNoetherianRing A] [IsNoetherianRing B]
    (f : A →+* B) (hf : Function.Surjective f)
    {F : Sheaf J (ModuleCat.{u + 1} A)} (hF : ObjectProperty.flat F) :
    ObjectProperty.flat ((extend J f).obj F) := by
  let I := RingHom.ker f
  let e := RingHom.quotientKerEquivOfSurjective hf
  let R := Sheaf.reductionFunctor J f hf
  have hR : ObjectProperty.flat (R.obj F) := by
    apply (Sheaf.flat_iff_hasLocallyTrivialRelations _).mpr
    exact relations_restrict_equiv J e.symm
      (Sheaf.hasLocallyTrivialRelations_of_flat (Sheaf.flat_quotSMulTop_obj (J := J) I hF))
  let U := Sheaf.restrictScalars J f
  have : U.Full := Sheaf.restrictScalars_full J f hf
  let c : ModuleCat.of A (A ⧸ I) ≅ (ModuleCat.restrictScalars f).obj (ModuleCat.of B B) :=
    LinearEquiv.toModuleIso (show (A ⧸ I) ≃ₗ[A]
      ((ModuleCat.restrictScalars f).obj (ModuleCat.of B B)) from
      { toFun := fun x ↦ e x
        invFun := e.symm
        left_inv := e.left_inv
        right_inv := e.right_inv
        map_add' := e.map_add
        map_smul' := by
          intro a x
          change e (Ideal.Quotient.mk I a * x) = f a * e x
          simp [e, I] })
  let c' := (constantSheaf J (ModuleCat.{u + 1} A)).mapIso c
  let i : R ⋙ U ≅ extend J f ⋙ U :=
    Sheaf.reductionFunctorCompRestrictScalarsIso J f hf ≪≫
      (curriedTensor (Sheaf J (ModuleCat.{u + 1} A))).flip.mapIso c' ≪≫
      (extend_restrict_tensor J f).symm
  exact ObjectProperty.prop_of_iso _ (U.preimageIso (i.app F)) hR

end Site
end AlgebraicGeometry.FiniteReduction
