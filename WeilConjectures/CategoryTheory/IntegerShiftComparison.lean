/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Shift.CommShift
public import Mathlib.Algebra.Group.Int.Defs
import WeilConjectures.CategoryTheory.IntTensorFamilyIso
import WeilConjectures.CategoryTheory.Monoidal.IntTensorFamily
import Mathlib.CategoryTheory.Monoidal.Braided.Basic

/-! # Comparison of integer shifts from degree one

Source: integer-word coherence for a category autoequivalence
(blueprint: lem-pur-integer-shift-comparison).
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace CategoryTheory

open MonoidalCategory

attribute [local instance] endofunctorMonoidalCategory

private def tautologicalIntegerFamily : IntTensorFamily (Discrete ℤ) where
  obj n := ⟨n⟩
  zeroIso := Iso.refl _
  addIso _ _ := Iso.refl _
  zero_left _ := Subsingleton.elim _ _
  zero_right _ := Subsingleton.elim _ _
  assoc _ _ _ := Subsingleton.elim _ _

private noncomputable def integerShiftFamily
    (A : Type u) [Category.{v} A] (S : HasShift A ℤ) : IntTensorFamily (A ⥤ A) := by
  letI := S
  exact tautologicalIntegerFamily.map (shiftMonoidalFunctor A ℤ)

private theorem integerShiftFamily_zero
    (A : Type u) [Category.{v} A] (S : HasShift A ℤ) :
    (integerShiftFamily A S).zeroIso = @shiftFunctorZero A ℤ _ _ S := by
  let := S
  apply Iso.ext
  simp [integerShiftFamily, IntTensorFamily.map, tautologicalIntegerFamily,
    shiftFunctorZero, Functor.Monoidal.εIso]

private theorem integerShiftFamily_add
    (A : Type u) [Category.{v} A] (S : HasShift A ℤ) (a b : ℤ) :
    (integerShiftFamily A S).addIso a b = (@shiftFunctorAdd A ℤ _ _ S a b).symm := by
  let := S
  apply Iso.ext
  simp [integerShiftFamily, IntTensorFamily.map, tautologicalIntegerFamily,
    shiftFunctorAdd, Functor.Monoidal.μIso]

/-- Integer shifts on a category which agree up to isomorphism in degree one
have a coherent comparison on the identity functor.

Source: integer-word coherence, as in the equivariant refinement of Stacks Tag 03CI
(blueprint: lem-pur-integer-shift-comparison).

Proof: Regard the two shifts as coherent integer tensor families in the monoidal
category of endofunctors. The integer-family comparison theorem extends the degree
one isomorphism, with its zero and multiplication identities. Insert the identity
functor unitors; those two identities become precisely the CommShift zero and
addition laws.
-/
private theorem integerShiftIdentityComparison
    (A : Type u) [Category.{v} A] (S T : HasShift A ℤ)
    (e : @shiftFunctor A ℤ _ _ S 1 ≅ @shiftFunctor A ℤ _ _ T 1) :
    Nonempty (@Functor.CommShift A A _ _ (𝟭 A) ℤ _ S T) := by
  let P := integerShiftFamily A S
  let Q := integerShiftFamily A T
  let i := IntTensorFamily.iso P Q e
  refine ⟨@Functor.CommShift.mk A A _ _ (𝟭 A) ℤ _ S T i ?_ ?_⟩
  · ext X
    have h := congrArg (fun j ↦ j.hom.app X) (IntTensorFamily.iso_zero P Q e)
    simpa only [Functor.CommShift.isoZero_hom_app, i, P, Q,
      integerShiftFamily_zero, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
      Functor.id_obj, Functor.id_map, Category.comp_id, Category.id_comp] using h
  · intro a b
    ext X
    have h := congr_app (IntTensorFamily.iso_mul P Q e a b (a + b) rfl) X
    simp only [IntTensorFamily.mulIso_rfl, P, Q, integerShiftFamily_add,
      Iso.symm_hom] at h
    rw [← cancel_epi ((@shiftFunctorAdd A ℤ _ _ S a b).inv.app X)]
    simpa [i, P, Q, integerShiftFamily, IntTensorFamily.map,
      tautologicalIntegerFamily, shiftFunctor] using h

/-- A degree-one intertwiner between integer shifts extends coherently along an
 equivalence of categories.

Source: integer-word coherence in the equivariant refinement of Stacks Tag 03CI
(blueprint: lem-pur-integer-shift-comparison).

Proof: Conjugate every target shift by the equivalence and use full faithfulness
to induce a shift on the source, for which the equivalence commutes with shifts.
The given degree-one intertwiner lifts to an isomorphism between the original and
induced source shifts in degree one. The integer-family comparison supplies a
coherent comparison on the identity functor. Compose it with the induced comparison.
-/
theorem integerShiftEquivalenceComparison
    {A : Type u} [Category.{v} A] {B : Type*} [Category* B]
    (S : HasShift A ℤ) (T : HasShift B ℤ) (e : A ≌ B)
    (b : @shiftFunctor A ℤ _ _ S 1 ⋙ e.functor ≅
      e.functor ⋙ @shiftFunctor B ℤ _ _ T 1) :
    Nonempty (@Functor.CommShift A B _ _ e.functor ℤ _ S T) := by
  let := T
  let s (n : ℤ) := e.functor ⋙ shiftFunctor B n ⋙ e.inverse
  let i (n : ℤ) : s n ⋙ e.functor ≅ e.functor ⋙ shiftFunctor B n :=
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _
      (Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ e.counitIso ≪≫
        Functor.rightUnitor _)
  let U := e.fullyFaithfulFunctor.hasShift s i
  let b' : @shiftFunctor A ℤ _ _ S 1 ≅ @shiftFunctor A ℤ _ _ U 1 :=
    ((Functor.whiskeringRight A A B).obj e.functor).preimageIso (b ≪≫ (i 1).symm)
  let c₁ := (integerShiftIdentityComparison A S U b').some
  let c₂ := Functor.CommShift.ofHasShiftOfFullyFaithful e.fullyFaithfulFunctor s i
  let c : @Functor.CommShift A B _ _ ((𝟭 A) ⋙ e.functor) ℤ _ S T :=
    @Functor.CommShift.comp A A B _ _ _ (𝟭 A) e.functor ℤ _ S U T c₁ c₂
  exact ⟨c⟩

end CategoryTheory
