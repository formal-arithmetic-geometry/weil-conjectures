/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q100
-/
module

public import Sheaf.CategoryTheory.ArithmeticSystemRightAdjointData
import Sheaf.CategoryTheory.ArithmeticSystemFloorExtension
import Sheaf.CategoryTheory.ArithmeticSystemFloorLimitComparison

/-! # The exact arithmetic floor extension of strict semilinear systems

Source: the arithmetic-restriction paragraph of the normalization argument for the
integral adjunction, blueprint smooth purity; Bhatt--Scholze, Definitions 3.5.2--3.5.3
and Lemma 3.5.7 (blueprint: lem-sp-arithmetic-system-right-adjoint).

The natural number `k` denotes positive level `k+1`. All functors in the statement
are normalized on components and transitions. The auxiliary records specify the
actual constructions, rather than arbitrary functors with the same source and target.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
set_option synthInstance.maxSize 2048

universe u v w z

open CategoryTheory CategoryTheory.Limits Opposite

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}]
  [EssentiallySmall.{w} C]

/-- The exact arithmetic floor extension exists with its normalized ordinary and
unbounded derived adjunctions.

Source: arithmetic restriction in the normalization paragraph of the integral
adjunction; Bhatt--Scholze, Definitions 3.5.2--3.5.3 and Lemma 3.5.7
(blueprint: lem-sp-arithmetic-system-right-adjoint).

Proof plan:
1. At positive level k use zero below e and restriction of C_floor(k/e) otherwise.
The block transitions are identities, boundary transitions are those of C, and the
prefix transitions are zero. Composition follows from the original strict transitions.
2. Restriction of scalars is exact by lem-pur-sheaf-ring-derived-coefficient-adjunction.
Componentwise exactness of lem-pur-system-level-left-extension gives exactness of both
functors, with no flatness assumption.
3. Select f_en to obtain the Hom map. Extend g at k by the transition from k to
 e floor(k/e), followed by restriction of g_floor(k/e). Strict transition composition
proves compatibility and the two inverse identities, naturally in both objects.
4. At selected levels the floor is n and restriction is along the identity. This gives
UJ=id, identity counit and identity selected components of the unit; the triangles follow.
5. Exact-functor localization preserves quasi-isomorphisms. Apply the specified
 def-weil-exact-derived-adjunction to the degreewise adjunction, retaining its unit and counit.
6. Forgetting to A commutes with selection. Apply lem-sp-strict-tower-arithmetic-restriction
and the total-limit functor of lem-weil-pbc-ringed-strict-tower-homotopy-limit. Its normalized
limit-map equation gives the selected projection equation, without exact products.
-/
theorem arithmeticSystemRightAdjoint (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w})
    (e : ℕ) (_he : 1 ≤ e) :
    ∃ (r : ℕ ↪o ℕ), (∀ n : ℕ, r n = e * (n + 1) - 1) ∧
      ∃ (hf : ∀ k : ℕ, e ≤ k + 1 → r ((k + 1) / e - 1) ≤ k)
        (R : StrictRingSystem (selectedSystemRings B r) ⥤ StrictRingSystem B)
        (_hadd : R.Additive) (_hlim : PreservesFiniteLimits R)
        (_hcolim : PreservesFiniteColimits R),
        Nonempty (ArithmeticSystemFloorData B e r hf R) ∧
        (∀ (A : Sheaf J CommRingCat.{w})
          (α : (Functor.const ℕᵒᵖ).obj A ⟶ B)
          [HasDerivedCategory.{z} (SheafOfModules.{w}
            (derivedChangeRingIndependentCoefficients J A))]
          [HasDerivedCategory.{z} (ℕᵒᵖ ⥤ SheafOfModules.{w}
            (derivedChangeRingIndependentCoefficients J A))]
          (RF : DerivedCategory.{z} (ℕᵒᵖ ⥤ SheafOfModules.{w}
            (derivedChangeRingIndependentCoefficients J A)) ⥤
            DerivedCategory.{z} (SheafOfModules.{w}
              (derivedChangeRingIndependentCoefficients J A)))
          (η : CategoryTheory.StrictTowerArithmetic.limitComplex _ ⋙ DerivedCategory.Q ⟶
            DerivedCategory.Q ⋙ RF),
          RF.IsRightDerivedFunctor η
            (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ SheafOfModules.{w}
              (derivedChangeRingIndependentCoefficients J A)) (.up ℤ)) →
          (∀ I, CochainComplex.IsKInjective I → IsIso (η.app I)) →
          ∃ (β : (Functor.const ℕᵒᵖ).obj A ⟶ selectedSystemRings B r),
            (∀ n : ℕ, β.app (op n) = α.app (op (r n))) ∧
            ∃ (F : ArithmeticSystemScalarForgetting B A α)
              (G : ArithmeticSystemScalarForgetting (selectedSystemRings B r) A β),
              Nonempty (ArithmeticSystemLimitData B e r R A α β F G RF η)) := by
  have he : 1 ≤ e := _he
  have hpos : 0 < e := he
  let r : ℕ ↪o ℕ := OrderEmbedding.ofStrictMono (fun n : ℕ ↦ e * (n + 1) - 1) (by
    intro m n h
    have hm : 0 < e * (m + 1) := Nat.mul_pos hpos (Nat.succ_pos m)
    have hmn : e * (m + 1) < e * (n + 1) :=
      Nat.mul_lt_mul_of_pos_left (Nat.add_lt_add_right h 1) hpos
    change e * (m + 1) - 1 < e * (n + 1) - 1
    omega)
  have hr (n : ℕ) : r n = e * (n + 1) - 1 := rfl
  have hf (k : ℕ) (h : e ≤ k + 1) : r ((k + 1) / e - 1) ≤ k := by
    rw [hr]
    have hq : 1 ≤ (k + 1) / e := (Nat.le_div_iff_mul_le hpos).2 (by simpa using h)
    have hmul : e * ((k + 1) / e) ≤ k + 1 := by
      simpa [Nat.mul_comm] using Nat.div_mul_le_self (k + 1) e
    rw [Nat.sub_add_cancel hq]
    omega
  obtain ⟨R, hadd, hlim, hcolim, ⟨d⟩⟩ := arithmeticSystemFloorExtension B e he r hr hf
  let : R.Additive := hadd
  let : PreservesFiniteLimits R := hlim
  let : PreservesFiniteColimits R := hcolim
  have hunit (K : CochainComplex (StrictRingSystem B) ℤ) :
      d.adjunction.mapExactDerivedCategory.unit.app (DerivedCategory.Q.obj K) ≫
        R.mapDerivedCategory.map ((systemSubsequence B r).mapDerivedCategoryFactors.hom.app K) ≫
        R.mapDerivedCategoryFactors.hom.app
          (((systemSubsequence B r).mapHomologicalComplex (.up ℤ)).obj K) =
        DerivedCategory.Q.map ((d.adjunction.mapHomologicalComplex (.up ℤ)).unit.app K) := by
    rw [Adjunction.mapExactDerivedCategory, Adjunction.localization_unit_app]
    simp only [CatCommSq.iso, Iso.symm_hom, Category.assoc,
      ← Functor.map_comp_assoc, Iso.inv_hom_id_app]
    erw [CategoryTheory.Functor.map_id]
    simp
  have hcounit (K : CochainComplex (StrictRingSystem (selectedSystemRings B r)) ℤ) :
      (systemSubsequence B r).mapDerivedCategory.map (R.mapDerivedCategoryFactors.hom.app K) ≫
        (systemSubsequence B r).mapDerivedCategoryFactors.hom.app
          ((R.mapHomologicalComplex (.up ℤ)).obj K) ≫
        DerivedCategory.Q.map ((d.adjunction.mapHomologicalComplex (.up ℤ)).counit.app K) =
        d.adjunction.mapExactDerivedCategory.counit.app (DerivedCategory.Q.obj K) := by
    simp [Adjunction.mapExactDerivedCategory, Adjunction.localization_counit_app]
  let D : ArithmeticSystemFloorData B e r hf R :=
    { adjunction := d.adjunction
      level := d.level
      prefix_zero := d.prefix_zero
      selected := d.selected
      transition := d.transition
      map := d.map
      counit := d.counit
      hom_selection := d.hom_selection
      hom_extension := d.hom_extension
      hom_prefix := d.hom_prefix
      unit_selected := d.unit_selected
      quasiIso_restriction := fun f h ↦ by
        let := h
        infer_instance
      quasiIso_extension := fun f h ↦ by
        let := h
        infer_instance
      derived_unit := hunit
      derived_counit := hcounit }
  refine ⟨r, hr, hf, R, hadd, hlim, hcolim, ⟨D⟩, ?_⟩
  intro A α _ _ RF η hRF hη
  let β : (Functor.const ℕᵒᵖ).obj A ⟶ selectedSystemRings B r :=
    { app := fun n ↦ α.app (op (r n.unop))
      naturality := fun X Y f ↦ by
        have h := α.naturality (r.toOrderHom.monotone.functor.op.map f)
        change (𝟙 A) ≫ α.app (op (r Y.unop)) =
          α.app (op (r X.unop)) ≫ (selectedSystemRings B r).map f at h
        exact h }
  have hβ (n : ℕ) : β.app (op n) = α.app (op (r n)) := rfl
  exact ⟨β, hβ, arithmeticSystemFloorLimitComparison B e he r hr hf R d A α β hβ RF η hRF hη⟩

end SheafOfModules
