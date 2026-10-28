/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.IntegralSystemReductionFullyFaithful
import Sheaf.Paper.DerivedCompleteFiniteReductionDetection

/-! Finite quotient evaluations and the Milnor obstruction.

Finite evaluations are not jointly faithful on derived morphisms: for a complete
target the Milnor kernel `lim¹ Hom(A[1], B_n)` survives, and it is nonzero for
`A = O_E`, `B = O_E[2]` over `Spec ℚ`. The unrestricted assertion
`integralSystemReduction_map_ext` was therefore withdrawn (maintainer rollback,
2026-10-28; node lem-pur-integral-system-reduction-map-ext, no Lean attachment).
The proved finite shifted-Hom criterion below is a sufficient condition.
(blueprint: lem-pur-integral-system-reduction-map-ext-finite)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 2048

universe u
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra (Padic l) E]
  [FiniteDimensional (Padic l) E]

/-- Finite shifted Hom groups suffice for joint faithfulness of finite evaluations.

Source: Stacks Project, More on Algebra, Lemma `map-into-Rlim`, and the proved
Milnor argument of `integral_reductions_jointly_faithful`.
(blueprint: lem-pur-integral-system-reduction-map-ext-finite)

Proof: derived completeness gives the target's reduction cone as a homotopy
limit. Finiteness of the shifted Hom groups makes its Milnor map injective.
Naturality of the evaluation comparison transports the given equalities to
scalar reduction. Naturality of the scalar-reduction units then gives equal
images in the Milnor limit. Injectivity and the full-subcategory inclusion give
`p = q`, and applying coherent reduction proves the conclusion.
-/
theorem integralSystemReduction_map_ext_of_finite
    {X : Scheme.{u}}
    {A B : sfIntegralConstructibleCategory l E X}
    (p q : A ⟶ B)
    (hfinite : ∀ n : ℕ, Finite
      (A.obj⟦(1 : ℤ)⟧ ⟶ (sfDerivedReductionRestricted l E X n).obj B.obj))
    (h : ∀ n : ℕ,
      (finiteSystemDerivedEvaluation (integralSystemRings l E)
          (integralSystemTransition l E) X n).map
          ((integralSystemReduction l E X).map p) =
        (finiteSystemDerivedEvaluation (integralSystemRings l E)
          (integralSystemTransition l E) X n).map
          ((integralSystemReduction l E X).map q)) :
    (integralSystemReduction l E X).map p =
      (integralSystemReduction l E X).map q := by
  have hpq : p = q := by
    apply (sfIntegralConstructible l E X).ι.map_injective
    apply derivedComplete_finiteReduction_ext l E X B.property.1 hfinite p.hom q.hom
    intro n
    let e := integralSystemReductionEvaluation l E X n
    apply (cancel_epi (e.hom.app A)).1
    exact (e.hom.naturality p).symm.trans
      ((congrArg (fun z ↦ z ≫ e.hom.app B) (h n)).trans (e.hom.naturality q))
  exact congrArg (fun z ↦ (integralSystemReduction l E X).map z) hpq

end WeilConjectures
