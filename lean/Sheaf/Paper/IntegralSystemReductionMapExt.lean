/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.IntegralSystemReductionFullyFaithful
import Sheaf.Paper.DerivedCompleteFiniteReductionDetection

/-! Finite quotient evaluations and the Milnor obstruction.

The unrestricted extensionality assertion below is disputed: derived localization
of coefficient systems does not make finite evaluations jointly faithful.
The proved finite shifted-Hom criterion records a sufficient condition for the
Milnor obstruction to vanish.
(blueprint: lem-pur-integral-system-reduction-map-ext)
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

/-- Finite evaluations jointly reflect equality after coherent reduction.

STATEMENT-DISPUTED: on an arbitrary scheme, the Milnor kernel
`lim¹ Hom(A[1], B_n)` need not vanish. Joint conservativity of finite evaluations
on objects does not imply joint faithfulness on derived morphisms.

Source of the obstruction: Stacks Project, More on Algebra, Lemma
`map-into-Rlim`; see the counterexample over `Spec ℚ` in the delivery report.
(blueprint: lem-pur-integral-system-reduction-map-ext)

The earlier proposed proof identified derived morphisms with families of their
levelwise images. The Milnor exact sequence has an additional kernel, so this
argument does not prove the assertion as stated. The theorem below with a finite
shifted-Hom hypothesis gives a valid sufficient criterion instead.
-/
theorem integralSystemReduction_map_ext
    {X : Scheme.{u}}
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    {A B : sfIntegralConstructibleCategory l E X}
    (p q : A ⟶ B)
    (h : ∀ n : ℕ,
      (finiteSystemDerivedEvaluation (integralSystemRings l E)
          (integralSystemTransition l E) X n).map
          ((integralSystemReduction l E X).map p) =
        (finiteSystemDerivedEvaluation (integralSystemRings l E)
          (integralSystemTransition l E) X n).map
          ((integralSystemReduction l E X).map q)) :
    (integralSystemReduction l E X).map p =
      (integralSystemReduction l E X).map q := by
  sorry

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
