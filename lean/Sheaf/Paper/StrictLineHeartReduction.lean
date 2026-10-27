/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R9
-/
module

public import Sheaf.Paper.SmoothPurityCoefficientTowersAbelian

/-! # Recovering strict transitions from derived reduction squares

Source: blueprint, tower-geometric gamma proof (1); Stacks 015F, 03CZ, 06YY and 07A6
(blueprint: lem-sp-shifted-single-reduction-detects-transition).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe t u
open CategoryTheory CategoryTheory.Limits Opposite SheafOfModules
namespace AlgebraicGeometry.ProEtale

/-- A compatible derived reduction square between shifted degree-zero sheaves
is the actual strict semilinear square.

Source: blueprint tower-geometric gamma proof (1), removing the common shift;
Stacks 015F, 03CZ, 06YY and 07A6
(blueprint: lem-sp-shifted-single-reduction-detects-transition).

Proof: cancel the common shift using the counit-normalized scalar shift and exact
 evaluation shifts. For each pair m ≤ n, transpose the resulting equality through
 the scalar model's derived adjunction. The representative normalization of this
 adjunction and A.reduction_rep identify the transpose of the canonical reduction
 with the degree-zero single of the actual strict transition. Naturality of the
 adjunction identifies the two transposes with the singles of f_n followed by the
 target transition, and the source transition followed by restriction of f_m.
 Faithfulness of the single embedding gives their equality. This argument only
 composes with the universal derived comparison and never inverts it: neither
 source flatness nor flatness of the quotient coefficients is needed. -/
theorem shifted_single_reduction_detects_transition
    {l : ℕ} [Fact l.Prime] {E : Type u} [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] {T : Scheme.{t}}
    (A : SpCoefficientTowersAbelian l E T) (M N : spCoefficientTowers l E T) (s : ℤ)
    (f : ∀ n : ℕ,
      (spCoefficientEvaluation l E T A.equivalence n).obj M ⟶
        (spCoefficientEvaluation l E T A.equivalence n).obj N) :
    letI := A.hasDerived
    letI := A.equivalenceAdditive
    letI := A.evaluationLimits
    letI := A.evaluationColimits
    let ev := fun n ↦ (spCoefficientEvaluation l E T A.equivalence n).mapDerivedCategory
    let S := DerivedCategory.singleFunctor (spCoefficientTowers l E T) 0
    let e := fun (P : spCoefficientTowers l E T) (n : ℕ) ↦
      ((ev n).commShiftIso s).app (S.obj P) ≪≫
        (shiftFunctor _ s).mapIso
          (((spCoefficientEvaluation l E T A.equivalence n).mapDerivedCategorySingleFunctor
            0).app P)
    let g := fun n ↦ (e M n).hom ≫
      ((DerivedCategory.singleFunctor _ 0).map (f n))⟦s⟧' ≫ (e N n).inv
    (∀ {m n : ℕ} (h : m ≤ n),
      (systemDerivedTensor A.scalar (spCoefficientCommRings l E T) h).map (g n) ≫
          (A.reduction h).app ((S.obj N)⟦s⟧) =
        (A.reduction h).app ((S.obj M)⟦s⟧) ≫ g m) →
      ∀ {m n : ℕ} (h : m ≤ n),
        f n ≫ (A.equivalence.functor.obj N).transition h =
          (A.equivalence.functor.obj M).transition h ≫
            (systemRestriction (spCoefficientCommRings l E T) h).map (f m) := by sorry

end AlgebraicGeometry.ProEtale

attribute [instance high] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
