/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V5
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Colim

/-! # Tensor products of native flat-term K-flat complexes -/

@[expose] public section
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
namespace CochainComplex
variable {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{v} C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]

/-- The total tensor of flat-term K-flat complexes is flat-term K-flat.
Source: Stacks Project, Tags 07A2 and 07A4
(blueprint: lem-pur-flat-term-kflat-tensor-native).
Proof: associativity identifies tensoring with the product complex with successive
applications of its two tensor functors, so both preserve quasi-isomorphisms.
Each degree is the countable coproduct of tensors of flat terms. Tensors and
coproducts of flat objects are flat in a Grothendieck abelian category. The degree
sum is unrestricted, so the argument works for unbounded complexes. -/
theorem flat_term_kFlat_tensor (P Q : CochainComplex C ℤ)
    (hP : (HomologicalComplex.quasiIso C (.up ℤ)).kFlat P)
    (hQ : (HomologicalComplex.quasiIso C (.up ℤ)).kFlat Q)
    (hfP : ∀ n, ObjectProperty.flat (P.X n))
    (hfQ : ∀ n, ObjectProperty.flat (Q.X n)) :
    (HomologicalComplex.quasiIso C (.up ℤ)).kFlat (P ⊗ Q) ∧
      ∀ n, ObjectProperty.flat ((P ⊗ Q).X n) := by
  refine ⟨ObjectProperty.prop_tensor hP hQ, ?_⟩
  intro n
  change ObjectProperty.flat
    (∐ fun pq : {pq : ℤ × ℤ // pq.1 + pq.2 = n} ↦ P.X pq.val.1 ⊗ Q.X pq.val.2)
  have := closedUnderColimitsOfShape_flat C
    (Discrete {pq : ℤ × ℤ // pq.1 + pq.2 = n})
  exact ObjectProperty.prop_of_isColimit _ (colimit.isColimit _)
    (fun pq ↦ ObjectProperty.prop_tensor (hfP pq.as.val.1) (hfQ pq.as.val.2))

end CochainComplex
