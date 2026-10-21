/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.RingTheory.TateAbstractResidueCalculus
import Sheaf.RingTheory.TateResidue.FinitePotentTraceCalculus
import Mathlib.LinearAlgebra.Trace
import Mathlib.RingTheory.Kaehler.Basic

/-! # Sum and intersection identity for Tate residues

Source: J. Tate, *Residues of differentials on curves*, §2, property R5 and its proof,
printed p. 153; §1, T4, printed p. 150
(blueprint: lem-pc-tate-residue-lattice-identity).

The sum and intersection of two admissible subspaces are admissible. Their abstract
residue functionals satisfy the corresponding sum and intersection identity. The notions
`TateResidue.Admissible` and `TateResidue.res` are those of the abstract residue calculus.
-/

@[expose] public section

set_option autoImplicit false

universe u v w

namespace TateResidue

/-- Admissibility is preserved by sums and intersections, and abstract residues satisfy
`res A + res B = res (A ⊔ B) + res (A ⊓ B)` as an equality of k-linear maps.

Source: Tate, *Residues of differentials on curves*, §2, R5 and proof, printed p. 153;
§1, T4, printed p. 150 (blueprint: lem-pc-tate-residue-lattice-identity).

Proof plan, following the eight steps of the node:
1. Put S = A + B and I = A ∩ B. For each f choose finite-dimensional errors E_A, E_B
   with fA ⊆ A + E_A and fB ⊆ B + E_B. Then fS ⊆ S + E_A + E_B. The injection
   V/I → V/A ⊕ V/B maps the image of fI into the finite-dimensional images of fA, fB.
   This proves both admissibility assertions of `lem-pc-tate-abstract-residue-calculus`.
2. Choose V = I ⊕ A₀ ⊕ B₀ ⊕ D with A = I ⊕ A₀ and B = I ⊕ B₀. The corresponding
   coordinate projections obey π_A + π_B = π_S + π_I on each of the four summands.
3. Fix f,g and put Z_L = [π_L m_f, m_g] for L = I,A,B,S. The abstract residue calculus
   identifies res_L(f dg) with its finite-potent trace. The image of Z_L is almost in L.
   On L write Z_L = (π_L - 1)m_fg - m_g(π_L - 1)m_f; both terms have finite image,
   since fL and fgL are almost in L and π_L - 1 kills L.
4. For Z_A,Z_S the successive image bounds are V → S → A → 0 modulo finite spaces.
   Each word of length three has finite image. The sum W_AS of the eight such images
   is finite dimensional and stable under both operators: left multiplication of a
   word gives the image of its first three factors applied to the last factor's value.
   It contains the cube image of every linear combination of the two operators.
5. By `lem-pc-finite-potent-trace-calculus`, the traces of Z_A,Z_S,Z_A-Z_S are their
   ordinary traces on W_AS. Matrix diagonal additivity (`def-weil-endomorphism-trace`)
   gives Tr(Z_A) - Tr(Z_S) = Tr(Z_A-Z_S), without general Tate-trace additivity.
6. For Z_I,Z_B use V → B → I → 0 modulo finite spaces. The same eight-word construction
   gives W_IB, stable under both and containing the three cube images. Restricted
   ordinary traces give Tr(Z_I) - Tr(Z_B) = Tr(Z_I-Z_B).
7. The projection identity gives Z_A-Z_S = [(π_A-π_S)m_f,m_g]
   = [(π_I-π_B)m_f,m_g] = Z_I-Z_B. Substitute the residue formulas and rearrange in k.
8. The generators-and-relations construction of `def-weil-pbc-kahler-differentials`
   makes the f dg span Ω¹ over k. The residues are k-linear by the abstract residue
   calculus, so the identity on these generators is an equality of linear maps.
-/
theorem residue_lattice_identity
    {k : Type u} [Field k] {C : Type v} [CommRing C] [Algebra k C]
    {V : Type w} [AddCommGroup V] [Module k V] [Module C V] [IsScalarTower k C V]
    (A B : Submodule k V) (hA : Admissible C A) (hB : Admissible C B) :
    Admissible C (A ⊔ B) ∧ Admissible C (A ⊓ B) ∧
      res C A + res C B = res C (A ⊔ B) + res C (A ⊓ B) := by
  sorry

end TateResidue
