/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B6
-/
module

public import Sheaf.Paper.LisseCompletedSystemData

/-! # The comparison at one coefficient field and one scheme. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.ProEtale.CompletedLisse
variable (l : ℕ) [Fact l.Prime]

/-- At a fixed base, the completed integral comparison and rational realization exist
with the prescribed continuous-coefficient datum and residue-normalized coefficient isomorphism.
Source: Bhatt--Scholze, Corollary 5.1.5, Lemma 6.8.2 and Proposition 6.8.4(1),(4),
pp.35,58--59 (blueprint: lem-per-lisse-completed-pointwise-comparison).

Proof: For each positive exponent, apply finite-local-systems-twist to the finite quotient
ring. Restrict the equivalence to finite free models by taking a geometric stalk on every
nonempty common trivializing object; the stalk of the constant module is that module.
Inverse image preserves tensor quotients, so the equivalences descend the normalized
transition maps and their equations, uniquely by full faithfulness. This identifies the
etale tower category in Systems with IntegralReductionTower. Transport the given integral
reduction equivalence across the prescribed coefficient isomorphism and compose with this
tower equivalence. Transport its quotient and limit cones as well. The residue equations
for the coefficient isomorphism identify the transported scalar maps with integralScalar;
full faithfulness and the original projection equations give naturality, unit and counit.
These constructions allow rank zero and locally varying rank.
For rational realization, apply the actual scalar-extension functor to the reconstructed
integral modules. The DVR identity l = u * varpi^e, with u a unit and e positive, identifies
localization at l with localization at varpi and with the coefficient field E. Extend the
map on integral Hom A-linearly to E tensor_A Hom; the balancing
relation is the scalar-compatibility equation just obtained. Functoriality and additivity
follow on pure tensors. On a common finite-free chart internal Hom is a finite matrix
module, and its localization is the rational internal Hom. Globally, X is qcqs; degree-zero
bounded-continuity-sections applied to the multiplication-by-uniformizer diagram of these
internal Homs identifies localized sections with rational Hom. Thus the displayed tensor
map is bijective, giving full faithfulness. The zero and empty charts satisfy the same
calculation. All constructions retain the supplied coefficient datum and isomorphism. -/
theorem completed_pointwise_comparison (P : Base.{u} l)
    (c : IntegralLisseReductionEquivalence l P.E P.X)
    (e : lisseIntegerSheafSized l P.E P.X ≅ completedRing l P)
    (he : ∀ n : ℕ, e.hom ≫ limit.π _ (op n) = integralLisseReduction l P.E P.X n ≫
      (c.finiteConstant n).inv) :
    ∃ d : Comparison l P, d.integralComparison = c ∧ d.coefficientIso = e := by sorry

end AlgebraicGeometry.ProEtale.CompletedLisse
