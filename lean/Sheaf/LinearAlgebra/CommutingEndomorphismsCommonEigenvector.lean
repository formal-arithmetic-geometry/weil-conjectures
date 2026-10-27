/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs

import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.LinearAlgebra.Dimension.RankNullity

/-!
# A common eigenvector for commuting endomorphisms

Source: Milne, *Algebraic Groups* (2017), Lemma 16.11, printed p.327,
finite-family consequence of the invariant-eigenspace argument
(blueprint: lem-sfb-commuting-endomorphisms-common-eigenvector).
-/

@[expose] public section

universe u v w

namespace Module.End

/-- A finite commuting family on a nonzero finite-dimensional vector space over an
algebraically closed field has a nonzero common eigenvector. The index type may be empty.

Source: Milne, *Algebraic Groups* (2017), Lemma 16.11, printed p.327, proof;
finite-family consequence (blueprint: lem-sfb-commuting-endomorphisms-common-eigenvector).

Proof: Induct on the cardinality of the index type, quantifying the induction assertion over
all nonzero finite-dimensional spaces and commuting families of that size. For an empty
family choose any nonzero vector; the scalar family and equations are empty. Otherwise fix
an index i0. By `lem-zl-alg-closed-endomorphism-eigenvalue`
(`Module.End.exists_eigenvalue`), its operator has an eigenvalue a and a nonzero eigenvector z.
The eigenspace E for a is a linear subspace containing z, hence is nonzero. By the subspace
clause of `lem-trf-vector-space-quotient-dimension`
(`FiniteDimensional.finiteDimensional_submodule`), E is finite-dimensional.
For every other index j, commutativity gives T_i0(T_j x) = T_j(T_i0 x) = a • T_j x for
x in E, so T_j restricts to E. The restrictions commute, since their ambient composites agree.
Apply the induction hypothesis on E to the family with i0 removed, obtaining a nonzero common
eigenvector and scalars for the remaining indices. Its image in V is nonzero by injectivity
of the subspace inclusion. Give index i0 the scalar a; membership in E supplies its equation,
and the restricted equations supply every other equation. -/
theorem exists_common_eigenvector_of_commute
    {k : Type u} [Field k] [IsAlgClosed k]
    {V : Type v} [AddCommGroup V] [Module k V] [FiniteDimensional k V] [Nontrivial V]
    {I : Type w} [Finite I] (T : I → Module.End k V)
    (hT : ∀ i j : I, Commute (T i) (T j)) :
    ∃ (x : V) (μ : I → k), x ≠ 0 ∧ ∀ i : I, T i x = μ i • x := by
  sorry

end Module.End
