/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q10
-/
module

public import Sheaf.AlgebraicGeometry.RationalRepresentationComoduleDictionary
public import Sheaf.AlgebraicGeometry.GroupScheme.RationalHighestWeightData
public import Sheaf.AlgebraicGeometry.CentralTorusFaithfulWeightBlocks
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.Topology.Connected.Basic

import Mathlib.RingTheory.SimpleModule.Basic

/-! # A multiplicity-one weight line for a normalized operator algebra

Source: Milne, Algebraic Groups (2017), Exercise 4-2, p.97, Proposition 4.17, p.90,
Propositions 7.29--7.30, p.146, Theorem 12.12, pp.234--235, and Corollary 17.3, p.353.
(blueprint: lem-sfb-normalized-algebra-weight-line-simple)

This is the node's operator-algebra variant of Clifford theory, not a verbatim
statement in Milne. Scalar extensions use R tensor V, canonically symmetric to V tensor R.
The span of the base-changed operators is exactly the image of R tensor A in End_R(R tensor V).
The weight subspace is specified by its full all-algebras membership equivalence.
-/

set_option autoImplicit false

@[expose] public section

universe u

open CategoryTheory
open scoped TensorProduct

namespace AlgebraicGeometry

/-- A nonzero vector in a multiplicity-one torus weight space generates a simple
module over any unital operator algebra normalized scheme-theoretically by G.
Source: Milne, Exercise 4-2, p.97; Proposition 4.17, p.90; Propositions 7.29--7.30,
p.146; Theorem 12.12, pp.234--235; Corollary 17.3, p.353, and the agent assembly.
(blueprint: lem-sfb-normalized-algebra-weight-line-simple)

Proof:
1. The sum S of all simple A-submodules is nonzero by choosing a nonzero stable
   subspace of least positive dimension. Normalization makes rho(g) carry simple
   A-submodules to simple A-submodules, so S is G(k)-stable. Apply
   lem-sfb-smooth-group-rational-point-subspace-test and the universal point to
   make S a rational G-submodule. Rational simplicity gives S = V.
2. Apply lem-sfb-module-socle-complements, namely
   IsSemisimpleModule.of_sSup_simples_eq_top, to obtain A-stable complements.
   They are k-linear because A contains scalar operators. If U is contained in
   M and V = U direct-sum D, then M = U direct-sum (M intersect D), so complements
   also exist inside every A-submodule M.
3. For jointly A,T-stable U contained in M, choose an A-linear retraction p:M to U.
   Conjugation defines a rational T-action on Hom_A(M,U): the normalization identity
   preserves its finite system of A-linearity equations after every scalar extension.
   Apply lem-sfb-split-torus-representation-weight-decomposition to p and to
   End_A(U). Restriction is equivariant and p restricts to the identity, so the
   trivial-character component p_1 still restricts to the identity. Its kernel
   is jointly stable and complements U in M.
4. Induct on dim M for jointly stable M. For nonzero M, apply
   lem-sfb-torus-normalized-simple-submodule to the image of A in End_k(M), which
   remains normalized over every algebra, to obtain a jointly stable simple
   submodule U. Step 3 gives a jointly stable complement of smaller dimension.
   The zero case uses the empty direct sum. Thus V is a finite direct sum of
   T-stable simple A-submodules U_i.
5. Project v to these summands. Every component is in the same weight space.
   Distinct nonzero components would be independent, contradicting dimension one.
   Hence v lies in one U_i. Since 1 belongs to A, Av is nonzero; it is A-stable
   and contained in U_i. Simplicity makes Av = U_i, proving both clauses.
-/
theorem normalized_algebra_weight_line_simple
    (k : Type u) [Field k] [IsAlgClosed k]
    (G : Grp (Over (Spec (.of k)))) [IsAffine G.X.left]
    [Smooth G.X.hom] [ConnectedSpace G.X.left]
    [LocallyOfFiniteType G.X.hom] [QuasiCompact G.X.hom]
    (V : Type u) [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (ρ : RationalRepresentation.NaturalRepresentation (k := k) G.X.left V)
    (hsimple : RationalHighestWeight.IsSimple (G := G)
      (RationalRepresentation.genericCoaction (k := k) G.X.left V ρ))
    (T : Grp (Over (Spec (.of k)))) (iT : T ⟶ G)
    [IsClosedSubgroupScheme iT.hom.hom]
    (r : ℕ) (hsplit : Nonempty (T ≅ MultiplicativeType.splitTorus k r))
    (A : Subalgebra k (Module.End k V))
    (hnormalized : ∀ (R : Type u) [CommRing R] [Algebra k R]
      (g : points G.X R),
      (Submodule.span R {f : Module.End R (R ⊗[k] V) |
        ∃ a : A, f = (a : Module.End k V).baseChange R}).map
          (ρ.action R g).conj.toLinearMap =
        Submodule.span R {f : Module.End R (R ⊗[k] V) |
          ∃ a : A, f = (a : Module.End k V).baseChange R})
    (χ : T ⟶ Grp.mk (StandardGroupSchemes.multiplicative k))
    (Wχ : Submodule k V)
    (hWχ : ∀ w : V, w ∈ Wχ ↔
      ∀ (R : Type u) [CommRing R] [Algebra k R] (t : points T.X R),
        ρ.action R (t ≫ iT.hom.hom) (1 ⊗ₜ[k] w) =
          CentralTorusWeightBlocks.characterScalar χ R t • (1 ⊗ₜ[k] w))
    (hdim : Module.finrank k Wχ = 1) (v : V) (hvχ : v ∈ Wχ) (hv : v ≠ 0) :
    A.toSubmodule.map (LinearMap.applyₗ v) ≠ ⊥ ∧
      ∀ W : Submodule k V, W ≤ A.toSubmodule.map (LinearMap.applyₗ v) →
        (∀ (a : A) (w : V), w ∈ W → (a : Module.End k V) w ∈ W) →
        W = ⊥ ∨ W = A.toSubmodule.map (LinearMap.applyₗ v) := by
  sorry

end AlgebraicGeometry
