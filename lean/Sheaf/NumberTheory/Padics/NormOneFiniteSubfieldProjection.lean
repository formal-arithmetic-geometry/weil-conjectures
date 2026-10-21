/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NK
-/
module

public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.Topology.Algebra.IntermediateField
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Compactness.Compact
import Mathlib.Order.Zorn

/-! # Norm-one projection onto a finite p-adic subfield

Source: Weil blueprint, main-20261015, `sec-six-functors-basics`,
`sk-thm-sf-ctf-stability-direct-images.proof.md`, paragraph (3), scalar tame-kernel expansion
(blueprint: lem-sfb-norm-one-finite-subfield-projection).

The algebraic closure has the extending nonarchimedean norm. Intermediate fields inherit
that norm and its topology. No completeness of the algebraic closure is required.
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace Padic

/-- A finite intermediate p-adic field admits a contractive linear retraction from the
normed algebraic closure. Bundling continuity records the stated consequence of the bound.

Source: Weil blueprint, main-20261015, `sec-six-functors-basics`,
`sk-thm-sf-ctf-stability-direct-images.proof.md`, paragraph (3), scalar tame-kernel expansion
(blueprint: lem-sfb-norm-one-finite-subfield-projection).

Proof (the node's direct compact-ball and Zorn argument):
1. The restriction of the ambient norm to F is its extending p-adic absolute value by
   lem-weil-l-adic-extension-absolute-value (uniqueness). Every closed ball in F is compact
   by lem-weil-l-adic-extension-proper. The identity on the subspace F is contractive.
2. Given a contractive F-linear partial retraction g on U containing F and x outside U,
   set R_u = ‖x-u‖ and B_u = {b in F | ‖b-g(u)‖ ≤ R_u}. Contractivity and the ultrametric
   inequality give ‖g(u)-g(v)‖ ≤ max R_u R_v. Therefore R_u ≤ R_v implies B_u ⊆ B_v.
   Each ball contains its center and is closed by continuity of the norm.
3. B_0 is a nonempty compact ball. For a finite family, choose a least radius among its
   indices and 0; the corresponding center lies in all its balls and B_0. Thus the closed
   subsets B_0 ∩ B_u have the finite intersection property, including the empty family.
   Apply lem-sfb-compact-closed-finite-intersection inside B_0 to find b in every B_u.
4. Every element of U+Fx has a unique expression u+ax, since x is outside U. Set
   G(u+ax) = g(u)+ab. Uniqueness gives linearity and extension of g. For a ≠ 0 put
   v = -a⁻¹u. Then ‖G(u+ax)‖ = ‖a‖ * ‖b-g(v)‖ ≤ ‖a‖ * ‖x-v‖ = ‖u+ax‖.
   For a = 0 use the bound on g. Hence G is a strictly larger partial retraction.
5. Order the graphs of contractive partial retractions fixing F by inclusion. They form
   a set of subsets of Ω × F. The identity graph belongs to this set. A nonempty chain
   has its union as an upper bound: comparability gives single-valuedness, and any two
   arguments occur together in one member, proving linearity. Fixing F and the bound
   hold pointwise in a chain member. The empty chain is bounded by the identity graph.
6. Apply lem-weil-pbc-zorn-lemma to obtain a maximal graph. If its domain is not all Ω,
   step 4 strictly enlarges it, a contradiction. Its map is the desired retraction.
7. It fixes F and satisfies the asserted bound by construction. Linearity gives
   ‖p(x)-p(y)‖ ≤ ‖x-y‖; choosing δ = ε proves continuity. At 1 the bound is an equality,
   so the norm is one. All compactness used above is in F, without completing Ω.
-/
theorem exists_normOne_finiteSubfield_projection
    (l : ℕ) [Fact l.Prime] (Ω : Type u) [NormedField Ω]
    [NormedAlgebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω] [IsUltrametricDist Ω]
    (F : IntermediateField (Padic l) Ω) [FiniteDimensional (Padic l) F] :
    ∃ p : Ω →L[F] F, (∀ a : F, p (a : Ω) = a) ∧ ∀ x : Ω, ‖p x‖ ≤ ‖x‖ := by
  sorry

end Padic
