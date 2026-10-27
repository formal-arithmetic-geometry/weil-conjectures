/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T5
-/
module

public import Sheaf.Paper.CompleteReductionSectionsModel

/-! # Normalized sections on a resolved strict reduction tower

Source: Stacks Project, Cohomology on Sites, Tags 0D6K, 0A07 and 0941.
(blueprint: lem-sfb-reduction-sections-normalized-resolution).
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

/-- Resolve the actual tensor-reduction tower, retaining its augmentation and the
ordinary-limit normalization of the derived section comparison. This assertion has
no completeness hypothesis and gives no cohomological bound.

Source: Stacks Project, Tags 0D6K, 0A07 and 0941, and Bhatt--Scholze,
Proposition 3.5.1(1) (blueprint: lem-sfb-reduction-sections-normalized-resolution).

Proof: identify internal modules with sectionwise module sheaves, compatibly with
ordinary sections. Transpose the actual tensor-reduction tower to a complex of
strict towers and take its functorial K-injective resolution with injective terms.
Evaluation gives each j_n as a quasi-isomorphism. The compatible tensor units,
followed by j_n, give a by the ordinary-limit universal property. The exact
constant-tower left adjoint implies that lim I is K-injective. Sections commute
with ordinary limits and products. Apply the ringed direct-image/derived-limit
comparison to global sections, identified with direct image to the point.
The strict Roos inclusion on I becomes exactly limitToRoos after sections;
uniqueness of total right derivation gives c and its displayed unit equation.
The inverse of the ordinary-limit/Roos comparison for I, composed with the
Roos map induced by j, identifies Q(a) with the original (unit,0) augmentation.
The latter Roos map is invertible because products of internal module sheaves
are exact on the replete pro-etale site. Thus invertibility of the specified
augmentation implies invertibility of Q(a). No cohomology vanishing is used.
The zero tower and the empty scheme satisfy the same construction. -/
theorem reduction_sections_normalized_resolution
    (P : CochainComplex (AdicCompletion.Modules l E U) ℤ)
    (hP : (HomologicalComplex.quasiIso (AdicCompletion.Modules l E U) (.up ℤ)).kFlat P) :
    ∃ (I : CochainComplex (ℕᵒᵖ ⥤ AdicCompletion.Modules l E U) ℤ)
      (j : Functor.ofOpSequence
        (X := fun n : ℕ ↦ (AdicCompletion.level l E U n).obj P)
        (AdicCompletion.levelStep l E U P) ⟶ I.asFunctor),
      I.IsKInjective ∧ (∀ q : ℤ, Injective (I.X q)) ∧
      (∀ n : ℕ, QuasiIso (j.app (op n))) ∧
      ∃ a : P ⟶ limit I.asFunctor,
        (∀ n : ℕ, a ≫ limit.π I.asFunctor (op n) =
          AdicCompletion.levelUnit l E U P n ≫ j.app (op n)) ∧
        ∃ c : (rgamma l E U).obj (DerivedCategory.Q.obj (limit I.asFunctor)) ≅
            DerivedCategory.Q.obj (roosF.obj (sectionTower l E U I)),
          (sections l E U).rightDerivedFunctorUnit.app
              ((HomotopyCategory.quotient _ _).obj (limit I.asFunctor)) ≫ c.hom =
            DerivedCategory.Q.map (limitToRoos l E U I) ∧
          (IsIso (DerivedCategory.Q.map (AdicCompletion.augmentation l E U P)) →
            IsIso (DerivedCategory.Q.map a)) := by sorry

end AlgebraicGeometry.ProEtale.CompleteReductionSections
