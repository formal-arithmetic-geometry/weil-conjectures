/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V2
-/
module

public import Sheaf.CategoryTheory.Abelian.RightDerived.InjectivelyExactSquare

/-! # Exactness of the explicitly defined derived square boundary

Source: Mathlib, ShortComplex.ShortExact.homology_exact₁/₂/₃; Stacks, Cohomology, 01EB.
(blueprint: lem-sc-injectively-exact-square-boundary-exact).
-/

@[expose] public section

universe u v w

open CategoryTheory

namespace CategoryTheory.InjectivelyExactSquare

variable {C : Type u} [Category.{v} C] [Abelian C] [EnoughInjectives C]

/-- The explicit transported complex connecting map gives the three exactness positions
and the initial injection for the derived sequence of the square.

Source: Mathlib, Algebra/Homology/HomologySequence.lean,
`ShortComplex.ShortExact.homology_exact₁/₂/₃`, and CategoryTheory/Abelian/RightDerived.lean,
`InjectiveResolution.isoRightDerivedObj`, following Stacks Cohomology Lemma 01EB.
(blueprint: lem-sc-injectively-exact-square-boundary-exact).

Proof: The `resolutionSequence` is already proved short exact. Apply Mathlib's
homology_exact₂ at n, homology_exact₃ at n,n+1, and homology_exact₁ at n,n+1. The four
injective-resolution comparison isomorphisms identify the outer homologies with the
right derived functor values. For the middle product complex, cycles are pairs of cycles
and boundaries are pairs of boundaries. The two projections therefore induce an
isomorphism from its degree-n homology to the product of the two degree-n homologies,
with inverse induced by the two inclusions and addition. These constructions are inverse
because the two coordinate projections of their composites are identities. Through this
comparison the map from the first complex is the pair of the derived f₁₂ and f₁₃, and the
map to the last complex is the difference of the derived f₂₄ and f₃₄, by additivity of
homology and `NatTrans.rightDerived_app_eq`. The connecting map after transport is exactly
`boundary` by its definition. Transport of the three exact pairs along these isomorphisms
gives the displayed Function.Exact assertions (using ShortComplex.ab_exact_iff_function_exact).
Finally, in degree zero, the natural-number-indexed complexes have no incoming boundaries.
Homology is the kernel of the outgoing differential. The termwise injective diagonal
therefore restricts to an injective map on these kernels. Transport and the product
comparison give the first assertion. No left-exactness assumption on the functors is used. -/
theorem boundary_exact (S : InjectivelyExactSquare.{u, v, w} C) :
    (∀ (F : C),
        Function.Injective (fun x : (S.X₁.rightDerived 0).obj F ↦
          ((NatTrans.rightDerived S.f₁₂ 0).app F x,
            (NatTrans.rightDerived S.f₁₃ 0).app F x))) ∧
    (∀ (F : C) (n : ℕ),
        Function.Exact
          (fun x : (S.X₁.rightDerived n).obj F ↦
            ((NatTrans.rightDerived S.f₁₂ n).app F x,
              (NatTrans.rightDerived S.f₁₃ n).app F x))
          (fun x : (S.X₂.rightDerived n).obj F × (S.X₃.rightDerived n).obj F ↦
            (NatTrans.rightDerived S.f₂₄ n).app F x.1 -
              (NatTrans.rightDerived S.f₃₄ n).app F x.2) ∧
        Function.Exact
          (fun x : (S.X₂.rightDerived n).obj F × (S.X₃.rightDerived n).obj F ↦
            (NatTrans.rightDerived S.f₂₄ n).app F x.1 -
              (NatTrans.rightDerived S.f₃₄ n).app F x.2)
          (S.boundary F n) ∧
        Function.Exact (S.boundary F n)
          (fun x : (S.X₁.rightDerived (n + 1)).obj F ↦
            ((NatTrans.rightDerived S.f₁₂ (n + 1)).app F x,
              (NatTrans.rightDerived S.f₁₃ (n + 1)).app F x))) := by sorry

end CategoryTheory.InjectivelyExactSquare
