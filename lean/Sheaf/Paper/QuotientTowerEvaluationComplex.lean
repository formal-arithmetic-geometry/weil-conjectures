/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V1
-/
module

public import Sheaf.Paper.ConstantCompletionEquivalence
public import Sheaf.CategoryTheory.ComplexFunctorSquare

/-! # Evaluation of a quotient-tower complex with explicit complex endpoints

Source: Stacks Tags 0940, 0941 and 099M.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory.ConstantCompletion

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (A : Type u) [CommRing A] (I : Ideal A) (n : ℕ)

/-- Ordinary finite evaluation retains the quotient scalar action.
Source: Stacks Tags 0940 and 099M
(blueprint: lem-sf-quotient-tower-evaluation-complex). -/
def quotientEvaluationIso :
    reductionTower J A I false ⋙ (evaluation ℕᵒᵖ (Mod (constant J A))).obj (op n) ≅
      change (quotient J A I n) ⋙ res (quotient J A I n) :=
  Iso.refl _

/-- Finite evaluation with both iterated complex functors visible in its type.
Source: Stacks Tags 0941 and 099M
(blueprint: lem-sf-quotient-tower-evaluation-complex). -/
@[irreducible]
def quotientEvaluationComplexIso :
    (reductionTower J A I false).mapHomologicalComplex (.up ℤ) ⋙
        ((evaluation ℕᵒᵖ (Mod (constant J A))).obj (op n)).mapHomologicalComplex (.up ℤ) ≅
      (change (quotient J A I n)).mapHomologicalComplex (.up ℤ) ⋙
        (res (quotient J A I n)).mapHomologicalComplex (.up ℤ) :=
  mapComplexSquare (reductionTower J A I false)
    ((evaluation ℕᵒᵖ (Mod (constant J A))).obj (op n))
    (change (quotient J A I n)) (res (quotient J A I n))
    (quotientEvaluationIso J A I n)

/-- The explicit comparison retains the identity on every finite quotient complex.
Source: Stacks Tags 0941 and 099M
(blueprint: lem-sf-quotient-tower-evaluation-complex).
Proof: the ordinary evaluated reduction is scalar extension followed by restriction,
with identity comparison. The complex square applies this identity in every degree.
Evaluating the lifted comparison in degree q gives the displayed identity,
including n=0 and all ideals. -/
theorem quotientEvaluationComplexIso_hom_f (P : Cx (constant J A)) (q : ℤ) :
    ((quotientEvaluationComplexIso J A I n).hom.app P).f q = 𝟙 _ := by
  unfold quotientEvaluationComplexIso
  rw [mapComplexSquare_hom]
  rfl

/-- The explicit finite evaluation comparison is the identity chain map.
Source: Stacks Tags 0941 and 099M
(blueprint: lem-sf-quotient-tower-evaluation-complex).
Proof: equality of chain maps is detected in every degree. The preceding degreewise
formula identifies each component with the identity component. -/
theorem quotientEvaluationComplexIso_hom_id (P : Cx (constant J A)) :
    (quotientEvaluationComplexIso J A I n).hom.app P = 𝟙 _ := by
  apply HomologicalComplex.hom_ext
  intro q
  exact quotientEvaluationComplexIso_hom_f J A I n P q

end CategoryTheory.ConstantCompletion
