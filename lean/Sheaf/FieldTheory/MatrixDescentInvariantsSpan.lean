/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF worker X3
-/
module

public import Sheaf.FieldTheory.MatrixDescentInvariants
public import Mathlib.FieldTheory.KrullTopology
public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.LinearAlgebra.Span.Basic

/-!
# Invariant matrices span after extension of scalars

Source: Stacks Project, Tag 03R6, construction preceding Theorem 03R7.
(blueprint: lem-sc-matrix-descent-invariants-span).
-/

@[expose] public section

universe u

namespace Field

/-- The separable-closure span of twisted invariant matrices is the full matrix space.

Proof: local constancy on the compact absolute Galois group gives a finite image
and an open normal subgroup on whose cosets b is constant. Shrink this subgroup
so it fixes the entries of every b-value and its inverse. Its fixed field L is
finite Galois over K. The identity and composition hypotheses make the twisted
maps a semilinear action, trivial on the subgroup when restricted to Mat_n(L),
hence an action of Gal(L/K). For a in L and a matrix v over L, the sum of
sigma(a) T_sigma(v) over this finite group is invariant, by reindexing the sum.
If the L-span of these invariant sums were proper, choose a nonzero linear
functional annihilating it. For each v, independence of the distinct field
embeddings applied to the resulting identity in a forces every coefficient
lambda(T_sigma(v)) to vanish, including lambda(v). This contradicts the choice
of lambda. Thus invariant matrices span Mat_n(L). The matrix units show that
Mat_n(L) spans Mat_n(SeparableClosure K), giving the asserted span equality.
For n=0 the matrix space is zero and the argument uses the empty basis.
No averaging by division by the group order is involved.

Source: Stacks Project, Tag 03R6, finite descent argument expanded in steps 1--3
of lem-sc-matrix-descent-scalar-map-bijective.
(blueprint: lem-sc-matrix-descent-invariants-span). -/
theorem matrixDescentInvariants_span (K : Type u) [Field K] (n : ℕ)
    (b : (SeparableClosure K ≃ₐ[K] SeparableClosure K) →
      Matrix.GeneralLinearGroup (Fin n) (SeparableClosure K))
    (hb : IsLocallyConstant b)
    (h1 : ∀ M : Matrix (Fin n) (Fin n) (SeparableClosure K),
      (b 1).val * M * ((b 1)⁻¹).val = M)
    (hm : ∀ g h (M : Matrix (Fin n) (Fin n) (SeparableClosure K)),
      (b g).val * ((b h).val * M.map h * ((b h)⁻¹).val).map g * ((b g)⁻¹).val =
        (b (g * h)).val * M.map (g * h) * ((b (g * h))⁻¹).val) :
    Submodule.span (SeparableClosure K)
      (Set.range fun a : matrixDescentInvariants K n b ↦
        (a : Matrix (Fin n) (Fin n) (SeparableClosure K))) = ⊤ := by sorry

end Field
