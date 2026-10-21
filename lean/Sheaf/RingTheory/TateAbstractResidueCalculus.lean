/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.RingTheory.TateResidue.Residue
public import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-! # Abstract Tate residue and its basic invariances

Source: J. Tate, *Residues of differentials on curves*, §1, T1–T5, pp. 149–151;
§2, Theorem 1, formula (*), and R1–R2, pp. 151–153
(blueprint: lem-pc-tate-abstract-residue-calculus).

The existing `TateResidue.Admissible`, `Module.End.IsFinitePotent`,
`Module.End.tateTrace`, and `TateResidue.res` supply the actual constructions.
`Submodule.AlmostLE` expresses finite-dimensionality modulo a subspace by a
finite-dimensional space of representatives. The exponent in `IsFinitePotent` may be
zero; this is equivalent to requiring a positive exponent, since the next image is a
subspace of the previous image. Tate trace is normalized by
`Module.End.tateTrace_eq_trace_restrict` on every finite-dimensional stable subspace
containing a power image.

## Main statements

- `TateResidue.abstract_residue_calculus`: the characterization by the commutator
  with one projected multiplication, uniqueness, invariance, and vanishing.
-/

@[expose] public section

set_option autoImplicit false

universe u v w w'

namespace TateResidue

/-- The unique residue functional is characterized by every projection onto the admissible
subspace, with the unprojected second multiplication. It is invariant under isomorphisms
of pairs and passage to a submodule containing the subspace, and has the stated vanishing
properties.

Source: Tate, *Residues of differentials on curves*, §1, T1–T5 and Propositions 1–2;
§2, Theorem 1, formula (*), and R1–R2, pp. 149–153
(blueprint: lem-pc-tate-abstract-residue-calculus).

Proof plan:
1. Choose a complementary subspace and its projection using
   `lem-trf-vector-subspace-complement`. Apply `lem-pc-finite-potent-trace-calculus`
   to compute traces on finite-dimensional stable subquotients.
2. Use `lem-pc-tate-endomorphism-ideals`: the multiplication operators lie in E;
   E1 and E2 are ideals, and E0 is finite-potent with a linear trace. The trace of
   a commutator vanishes for a pair in E0 × E or E1 × E2.
3. A lift F of f lies in E1 and satisfies F - m_f in E2. The projection times m_f
   is a lift. Lifts add, scale, and multiply; commutators of two lifts lie in E0.
4. The trace q(f,g) of a commutator of lifts is independent of both lifts, by the
   first trace-zero rule. It is bilinear and alternating. The second trace-zero
   rule replaces the second lift by m_g, giving exactly the displayed commutator.
5. Expand [F,GH] = [FG,H] + [HF,G] and apply linearity on E0. This proves
   q(f,gh) = q(fg,h) + q(fh,g). Also q(f,c) = 0 for c in k.
6. In the free-module presentation of `def-weil-pbc-kahler-differentials`, send
   f[g] to q(f,g). The identities above kill every coefficient multiple of the
   additive, Leibniz, and scalar relations. Descend to a k-linear functional.
   Since the f dg span the differentials over k, this functional is unique.
7. For the ambient comparison set B = A + gA and
   D = B ∩ m_f⁻¹(A) ∩ m_fg⁻¹(A). Admissibility makes B/D finite-dimensional;
   the commutator maps V into B and kills D. Trace additivity identifies its
   trace with the trace on B/D. These spaces and this operator are unchanged
   inside any C-submodule W containing A, proving ambient invariance.
8. A C-linear pair isomorphism conjugates the projection and the commutator.
   Cyclicity of finite-potent trace identifies their traces, proving invariance.
9. For finite-dimensional A use zero lifts; for finite-dimensional V/A use the
   commuting multiplication operators themselves as lifts. Their traces vanish.
10. If f and g preserve A, use the commuting lifts m_f π and m_g π. The value
    on f dg is zero. If every scalar preserves A, spanning gives a zero functional.
-/
theorem abstract_residue_calculus
    {k : Type u} [Field k] {C : Type v} [CommRing C] [Algebra k C]
    {V : Type w} [AddCommGroup V] [Module k V] [Module C V] [IsScalarTower k C V]
    (A : Submodule k V) (hA : Admissible C A) :
    (∀ r : KaehlerDifferential k C →ₗ[k] k,
      (∀ (π : Module.End k V), (∀ x : V, π x ∈ A) → (∀ a ∈ A, π a = a) →
        ∀ f g : C,
          (π * act k f * act k g - act k g * π * act k f).IsFinitePotent ∧
          r (f • KaehlerDifferential.D k C g) =
            (π * act k f * act k g - act k g * π * act k f).tateTrace) ↔ r = res C A) ∧
    (∀ (V' : Type w') [AddCommGroup V'] [Module k V'] [Module C V']
      [IsScalarTower k C V'] (A' : Submodule k V') (e : V ≃ₗ[C] V'),
      A.map (e.restrictScalars k).toLinearMap = A' → res C A = res C A') ∧
    (∀ W : Submodule C V, A ≤ W.restrictScalars k →
      res C (A.comap (W.subtype.restrictScalars k)) = res C A) ∧
    ((FiniteDimensional k A ∨ FiniteDimensional k (V ⧸ A)) → res C A = 0) ∧
    (∀ f g : C, (∀ a ∈ A, f • a ∈ A) → (∀ a ∈ A, g • a ∈ A) →
      res C A (f • KaehlerDifferential.D k C g) = 0) ∧
    ((∀ f : C, ∀ a ∈ A, f • a ∈ A) → res C A = 0) := by
  sorry

end TateResidue
