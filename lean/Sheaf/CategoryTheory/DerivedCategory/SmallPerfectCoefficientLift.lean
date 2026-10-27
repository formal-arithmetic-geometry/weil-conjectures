/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group X2
-/
module

public import Sheaf.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
public import Mathlib.Algebra.Category.ModuleCat.Ulift
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.RingTheory.Finiteness.Small
import Mathlib.Algebra.Module.Shrink

/-! # Small carriers for perfect complexes over lifted coefficient rings

Source: blueprint point-perfectness proof, Step 3, small integral models.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace DerivedCategory

/-- A perfect complex over a lifted small ring has a small finite-projective model.
Source: blueprint thm-pod-point-perfectness.proof.md, Step 3, integral model convention;
Mathlib `Module.Finite.small` and `Shrink.linearEquiv`.
(blueprint: lem-sf-small-perfect-coefficient-lift).

Proof: choose a bounded finite-projective representative of C. Restrict its coefficient
ring along the inverse ULift ring equivalence. Each term is small because it is finitely
generated over R. Replace each term by its Shrink carrier and conjugate every differential
by the Shrink linear equivalences. The equations d squared equals zero are preserved by
conjugation. Projectivity and finite generation transport along the coefficient and carrier
equivalences. The termwise equivalences give a chain isomorphism from the displayed lift
back to the chosen representative. Apply Q and compose with its presentation of C.
Replace the lower endpoint by its minimum with the upper endpoint, so the endpoints are
ordered even for a zero complex. No object data are defined using this existence theorem. -/
theorem small_perfect_coefficient_lift (R : Type u) [CommRing R]
    [HasDerivedCategory.{u + 1} (ModuleCat.{u + 1} (ULift.{u + 1, u} R))]
    (C : DerivedCategory (ModuleCat.{u + 1} (ULift.{u + 1, u} R)))
    (hC : IsPerfectRingComplex C) :
    ∃ P : CochainComplex (ModuleCat.{u} R) ℤ,
      (∃ a b : ℤ, a ≤ b ∧ P.IsStrictlyGE a ∧ P.IsStrictlyLE b) ∧
      (∀ i : ℤ, Module.Projective R (P.X i) ∧ Module.Finite R (P.X i)) ∧
      Nonempty (C ≅ Q.obj
        (((ModuleCat.uliftFunctor.{u + 1, u} R ⋙
          ModuleCat.restrictScalars.{u + 1, u + 1, u}
            (ULift.ringEquiv : ULift.{u + 1, u} R ≃+* R).toRingHom
          ).mapHomologicalComplex (.up ℤ)).obj P)) := by
  classical
  let : RingHomInvPair
      (ULift.ringEquiv : ULift.{u + 1, u} R ≃+* R).toRingHom
      (ULift.ringEquiv : ULift.{u + 1, u} R ≃+* R).symm.toRingHom :=
    ⟨by ext x; rfl, by ext x; rfl⟩
  let : RingHomInvPair
      (ULift.ringEquiv : ULift.{u + 1, u} R ≃+* R).symm.toRingHom
      (ULift.ringEquiv : ULift.{u + 1, u} R ≃+* R).toRingHom :=
    ⟨by ext x; rfl, by ext x; rfl⟩
  obtain ⟨M, a, b, ha, hb, ht, ⟨ec⟩⟩ := hC
  let F := ModuleCat.restrictScalars.{u + 1, u, u + 1}
    (ULift.ringEquiv : ULift.{u + 1, u} R ≃+* R).symm.toRingHom
  let N := (F.mapHomologicalComplex (.up ℤ)).obj M
  let e (i : ℤ) : LinearEquiv
      (ULift.ringEquiv : ULift.{u + 1, u} R ≃+* R).toRingHom
      (σ' := (ULift.ringEquiv : ULift.{u + 1, u} R ≃+* R).symm.toRingHom)
      (M.X i) (N.X i) :=
    { toFun := fun x ↦ x
      invFun := fun x ↦ x
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun (r : ULift.{u + 1, u} R) x ↦ rfl }
  have hN (i : ℤ) : Module.Projective R (N.X i) ∧ Module.Finite R (N.X i) := by
    have := (ht i).1
    have := (ht i).2
    exact ⟨Module.Projective.of_equiv (e i),
      Module.Finite.of_surjective (e i).toLinearMap (e i).surjective⟩
  let small (i : ℤ) : Small.{u} (N.X i) := by
    have := (hN i).2
    exact Module.Finite.small R (N.X i)
  let V (i : ℤ) := ModuleCat.of R (Shrink.{u} (N.X i))
  let f (i : ℤ) : V i ≃ₗ[R] N.X i := Shrink.linearEquiv R (N.X i)
  let P : CochainComplex (ModuleCat.{u} R) ℤ :=
    { X := V
      d := fun i j ↦ ModuleCat.ofHom
        ((f j).symm.toLinearMap.comp ((N.d i j).hom.comp (f i).toLinearMap))
      shape := by
        intro i j hij
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro x
        change (f j).symm (N.d i j (f i x)) = 0
        rw [N.shape i j hij]
        exact (f j).symm.map_zero
      d_comp_d' := by
        intro i j k _ _
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro x
        change (f k).symm (N.d j k (f j ((f j).symm (N.d i j (f i x))))) = 0
        rw [LinearEquiv.apply_symm_apply]
        have h := ConcreteCategory.congr_hom (N.d_comp_d i j k) (f i x)
        change N.d j k (N.d i j (f i x)) = 0 at h
        rw [h, map_zero] }
  let G := ModuleCat.uliftFunctor.{u + 1, u} R ⋙
    ModuleCat.restrictScalars.{u + 1, u + 1, u}
      (ULift.ringEquiv : ULift.{u + 1, u} R ≃+* R).toRingHom
  let fLift (i : ℤ) : G.obj (P.X i) ≃ₗ[ULift.{u + 1, u} R] M.X i :=
    { toFun := fun x ↦ f i x.down
      invFun := fun x ↦ ULift.up ((f i).symm x)
      left_inv := fun x ↦ by
        apply ULift.ext
        exact (f i).symm_apply_apply x.down
      right_inv := fun x ↦ (f i).apply_symm_apply x
      map_add' := fun x y ↦ (f i).map_add x.down y.down
      map_smul' := fun r x ↦ (f i).map_smul r.down x.down }
  let ep : (G.mapHomologicalComplex (.up ℤ)).obj P ≅ M :=
    HomologicalComplex.Hom.isoOfComponents (fun i ↦ (fLift i).toModuleIso) (by
      intro i j _
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      change N.d i j (f i x.down) = f j ((f j).symm (N.d i j (f i x.down)))
      exact ((f j).apply_symm_apply _).symm)
  refine ⟨P, ⟨min a b, b, min_le_right _ _, ?_, ?_⟩, ?_, ⟨ec ≪≫ Q.mapIso ep.symm⟩⟩
  · apply (P.isStrictlyGE_iff _).2
    intro i hi
    have : Subsingleton (M.X i) := ModuleCat.isZero_iff_subsingleton.mp
      (M.isZero_of_isStrictlyGE a i (lt_of_lt_of_le hi (min_le_left _ _)))
    have : Subsingleton (N.X i) := this
    exact ModuleCat.isZero_iff_subsingleton.mpr (f i).toEquiv.subsingleton
  · apply (P.isStrictlyLE_iff _).2
    intro i hi
    have : Subsingleton (M.X i) := ModuleCat.isZero_iff_subsingleton.mp
      (M.isZero_of_isStrictlyLE b i hi)
    have : Subsingleton (N.X i) := this
    exact ModuleCat.isZero_iff_subsingleton.mpr (f i).toEquiv.subsingleton
  · intro i
    have := (hN i).1
    have := (hN i).2
    exact ⟨Module.Projective.of_equiv (f i).symm, Module.Finite.equiv (f i).symm⟩

end DerivedCategory
