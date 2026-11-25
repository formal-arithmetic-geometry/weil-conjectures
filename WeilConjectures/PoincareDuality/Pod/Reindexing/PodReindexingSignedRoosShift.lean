/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.PodCompletionReindex.PodCompletionReindexModels
import all WeilConjectures.CategoryTheory.RoosConeCalculus.RoosConeCalculus

/-! # The signed shift of the projection-normalized Roos model

## Implementation details

The shift is obtained by regarding a strict tower as a complex in the category of towers and
applying the native commutation of the Roos functor with shifts.

## References

* [Stacks: Tags 011G, 014E, 0941]
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits Opposite
universe a b
namespace WeilConjectures

variable {A : Type a} [Category.{b} A] [Abelian A] [HasCountableProducts A]

private def towerAsComplex (C : ℕᵒᵖ ⥤ CochainComplex A ℤ) :
    CochainComplex (ℕᵒᵖ ⥤ A) ℤ where
  X i := C ⋙ HomologicalComplex.eval A (.up ℤ) i
  d i j := { app := fun n ↦ (C.obj n).d i j
             naturality := fun _ _ f ↦ (C.map f).comm i j }
  shape i j hij := by ext n; exact (C.obj n).shape i j hij
  d_comp_d' i j k _ _ := by ext n; exact (C.obj n).d_comp_d i j k

attribute [local instance] CategoryTheory.RoosConeCalculus.levelCommShift

private def podNativeRoosShift : PodSignedRoosShift A where
  comparison C r :=
    (Functor.commShiftIso CategoryTheory.roosF
      (self := CategoryTheory.RoosConeCalculus.roosCommShift) r).app (towerAsComplex C)

private theorem podProductShift (C : ℕᵒᵖ ⥤ CochainComplex A ℤ) (r : ℤ) :
    (ProductShift.productShiftIso (CategoryTheory.RoosConeCalculus.levelFunctor (A := A))
      (towerAsComplex C) r).hom = podShiftProduct C r := by
  apply (cancel_mono (piComparison (shiftFunctor (CochainComplex A ℤ) r)
    (fun n : ℕ ↦ C.obj (op n)))).mp
  apply Pi.hom_ext
  intro n
  simp only [Category.assoc, piComparison_comp_π]
  have h := ProductShift.productShiftIso_π
    (CategoryTheory.RoosConeCalculus.levelFunctor (A := A)) (towerAsComplex C) r n
  change (ProductShift.productShiftIso
      (CategoryTheory.RoosConeCalculus.levelFunctor (A := A)) (towerAsComplex C) r).hom ≫
      (shiftFunctor (CochainComplex A ℤ) r).map (Pi.π (fun n : ℕ ↦ C.obj (op n)) n) =
    Pi.π (fun n : ℕ ↦ (C.obj (op n))⟦r⟧) n ≫ 𝟙 _ at h
  exact h.trans (by
    change Pi.π (fun n : ℕ ↦ (C.obj (op n))⟦r⟧) n ≫ 𝟙 _ =
      inv (piComparison (shiftFunctor (CochainComplex A ℤ) r)
        (fun n : ℕ ↦ C.obj (op n))) ≫
      (shiftFunctor (CochainComplex A ℤ) r).map (Pi.π (fun n : ℕ ↦ C.obj (op n)) n)
    rw [← piComparison_comp_π (shiftFunctor (CochainComplex A ℤ) r)]
    simp only [Category.comp_id, ← Category.assoc, IsIso.inv_hom_id, Category.id_comp])

/-- There is a signed Roos shift satisfying the two prescribed projection formulas, the second
with the sign `(-1)^r`. -/
theorem podReindexingSignedRoosShift : ∃ S : PodSignedRoosShift A, S.Laws := by
  refine ⟨podNativeRoosShift, ?_, ?_⟩
  · intro C r
    apply HomologicalComplex.hom_ext
    intro i
    have h := CategoryTheory.RoosConeCalculus.roosShift_v (towerAsComplex C) r i
    change (podNativeRoosShift.comparison C r).hom.f i ≫
        𝟙 _ ≫ (CochainComplex.mappingCocone.fst (podRoosBoundary C)).f (i + r) =
      (CochainComplex.mappingCocone.fst (podRoosBoundary (podShiftTower C r))).f i ≫
        (ProductShift.productShiftIso
          (CategoryTheory.RoosConeCalculus.levelFunctor (A := A))
          (towerAsComplex C) r).hom.f i at h
    simpa only [HomologicalComplex.comp_f, CochainComplex.shiftFunctor_map_f',
      Category.id_comp, podProductShift] using h
  · intro C r i
    have h := CategoryTheory.RoosConeCalculus.roosShift_u (towerAsComplex C) r i
    change (podNativeRoosShift.comparison C r).hom.f i ≫ 𝟙 _ ≫
        (CochainComplex.mappingCocone.snd (podRoosBoundary C)).v
          (i + r) (i - 1 + r) (by omega) =
      r.negOnePow • ((CochainComplex.mappingCocone.snd
        (podRoosBoundary (podShiftTower C r))).v i (i - 1) (by omega) ≫
        (ProductShift.productShiftIso
          (CategoryTheory.RoosConeCalculus.levelFunctor (A := A))
          (towerAsComplex C) r).hom.f (i - 1)) at h
    simpa only [Category.id_comp, podProductShift] using h

end WeilConjectures
