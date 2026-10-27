/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T5
-/
module

public import Sheaf.Paper.CompleteReductionSectionsModel

/-! # Roos triangle on the derived sections of the actual reductions

Source: Stacks Project, Cohomology on Sites, Tag 0D6K; More on Algebra,
Tags 07KW and 08U5 (blueprint: lem-sfb-reduction-sections-roos-triangle).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CompleteReductionSections

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (U : Scheme.{u})

/-- The strict section fibre is a derived limit of the actual derived reduction sections.
No completeness or cohomological bound is assumed, and transitions are the specified
quotient transitions. The product instance fixes the product in the triangle.

Source: Stacks Project, Tags 0D6K and 0941; More on Algebra, Tag 08U5
(blueprint: lem-sfb-reduction-sections-roos-triangle).

Proof: evaluate I at each n. Evaluation preserves K-injectives, so its ordinary
section complex computes RΓ. The quasi-isomorphism j_n identifies the derived
level with that of the tensor reduction of P. The K-flat computation of derived
scalar extension identifies the latter with integralLevel K n. These
identifications commute with the actual transitions, by naturality of j and of
the scalar-extension comparison. Countable products in abelian groups are exact,
so the product of section complexes represents their derived product.
Localizing the inverse rotation of the mapping-cone triangle defining roosF,
with its standard sign convention, gives the Roos triangle on these evaluated
section complexes. Transport both product vertices by the product of the level
identifications. Projectionwise compatibility sends 1-shift to 1-shift of the
specified derived reduction transitions. This proves the displayed derived-limit
property, without using any cohomology vanishing or Mittag--Leffler property. -/
theorem reduction_sections_roos_triangle
    (K : DerivedCategory (AdicCompletion.Modules l E U))
    (P : CochainComplex (AdicCompletion.Modules l E U) ℤ)
    (hP : (HomologicalComplex.quasiIso (AdicCompletion.Modules l E U) (.up ℤ)).kFlat P)
    (e : DerivedCategory.Q.obj P ≅ K)
    (I : CochainComplex (ℕᵒᵖ ⥤ AdicCompletion.Modules l E U) ℤ)
    (hI : I.IsKInjective)
    (j : Functor.ofOpSequence
      (X := fun n : ℕ ↦ (AdicCompletion.level l E U n).obj P)
      (AdicCompletion.levelStep l E U P) ⟶ I.asFunctor)
    (hj : ∀ n : ℕ, QuasiIso (j.app (op n)))
    [HasProduct (fun n : ℕ ↦
      (rgamma l E U).obj (AdicCompletion.integralLevel l E U K n))] :
    IsDerivedLimit (K := fun n : ℕ ↦
      (rgamma l E U).obj (AdicCompletion.integralLevel l E U K n))
      (fun n : ℕ ↦ (rgamma l E U).map (AdicCompletion.integralStep l E U K n))
      (DerivedCategory.Q.obj (roosF.obj (sectionTower l E U I))) := by sorry

end AlgebraicGeometry.ProEtale.CompleteReductionSections
