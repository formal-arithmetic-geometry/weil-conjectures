/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NF
-/
module

public import Sheaf.Topology.NormedScalarProfiniteCechExact
public import Sheaf.Topology.ContinuousMapCondensedRing
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.Topology.Category.Profinite.Limits
public import Mathlib.Topology.Metrizable.Basic
import Sheaf.NumberTheory.Padics.CountableClosedFiniteCover
import Sheaf.NumberTheory.Padics.ExtensionIntegersDvr
import Sheaf.Topology.FiniteQuotientFiberProduct
import Mathlib.Topology.Baire.LocallyCompactRegular
import Mathlib.Topology.Baire.Lemmas

/-!
# Noncomplete algebraic scalars: a Cech counterexample and local contraction

Source: main-20261015 blueprint, `sec-six-functors-basics/`
`sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md`, paragraph (3),
agent-formulated analytic input, corrected by the NI split's eight-step counterexample
and split-cover contraction (blueprint: lem-sfb-norm-algcl-profinite-cech-exact).

The blueprint motivates this auxiliary but does not assert global Cech exactness.
The coefficient field below is an algebraic closure of Q_l, with its extended norm,
not its completion. The tuple spaces and coordinate deletions are the existing ones.
Positive degree is indexed by `n + 1`, including degree one when `n = 0`.
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory

namespace Profinite.NormAlgclCech

/-- Insert a first coordinate having the same image as every old coordinate.
Source: node proof, step 7, extra-coordinate contraction
(blueprint: lem-sfb-norm-algcl-profinite-cech-exact). -/
def prepend {V T : Profinite.{v}} (q : C(T, V)) (r : ℕ) (s : T)
    (x : scalarCechTuples q r) (hs : ∀ i : Fin r, q s = q (x.val i)) :
    scalarCechTuples q (r + 1) :=
  ⟨Fin.cons s x.val, by
    intro i j
    cases i using Fin.cases <;> cases j using Fin.cases
    · rfl
    · exact hs _
    · exact (hs _).symm
    · exact x.property _ _⟩

/-- The exact tuple appearing in the split-cover primitive formula.
Source: node statement, clause (2), and proof, step 7
(blueprint: lem-sfb-norm-algcl-profinite-cech-exact). -/
def sectionInsert {V T : Profinite.{v}} (q : C(T, V)) (σ : C(V, T))
    (hσ : Function.RightInverse σ q) (n : ℕ) (x : scalarCechTuples q (n + 1)) :
    scalarCechTuples q (n + 2) :=
  prepend q (n + 1) (σ (q (x.val 0))) x
    (fun i ↦ (hσ (q (x.val 0))).trans (x.property 0 i))

/-- The existing explicit profinite pullback, with its subspace topology.
Source: node statement, clause (2), and proof, step 8; Stacks 08ZY, 0A2P
(blueprint: lem-sfb-norm-algcl-profinite-cech-exact). -/
abbrev baseChange {V T : Profinite.{v}} (q : C(T, V)) : Profinite.{v} :=
  CompHausLike.pullback (CompHausLike.ofHom _ q) (CompHausLike.ofHom _ q)

/-- The first projection q' of the diagonal base change, as an actual continuous map.
Source: node statement, clause (2), and proof, step 8
(blueprint: lem-sfb-norm-algcl-profinite-cech-exact). -/
abbrev projection {V T : Profinite.{v}} (q : C(T, V)) : C(baseChange q, T) :=
  (CompHausLike.pullback.fst (CompHausLike.ofHom _ q) (CompHausLike.ofHom _ q)).hom.hom

/-- Forget the common base point in the nerve of q': (s;t_i) maps to (t_i).
Source: node proof, step 8, the coordinate description of pullback of a cochain
(blueprint: lem-sfb-norm-algcl-profinite-cech-exact). -/
def forgetBase {V T : Profinite.{v}} (q : C(T, V)) (r : ℕ)
    (x : scalarCechTuples (projection q) r) : scalarCechTuples q r :=
  ⟨fun i ↦ (x.val i).val.2, fun i j ↦
    (x.val i).property.symm.trans
      ((congrArg q (x.property i j)).trans (x.val j).property)⟩

/-- Insert the common base point s, giving the displayed local primitive f(s,t_0,...).
Source: node statement, clause (2), and proof, step 8
(blueprint: lem-sfb-norm-algcl-profinite-cech-exact). -/
def baseInsert {V T : Profinite.{v}} (q : C(T, V)) (n : ℕ)
    (x : scalarCechTuples (projection q) (n + 1)) : scalarCechTuples q (n + 2) :=
  prepend q (n + 1) (x.val 0).val.1 (forgetBase q (n + 1) x)
    (fun i ↦ (x.val 0).property.trans ((forgetBase q (n + 1) x).property 0 i))

/-- Global positive Cech exactness fails for all-continuous algebraic-closure-valued
cochains, but the specified split-cover and diagonal-base-change primitives exist in
all positive degrees. Every equality is an equality of actual Omega-valued functions.

Source: main-20261015 blueprint, direct-images proof, paragraph (3), motivating the
agent auxiliary; the reviewed NI correction and proof steps 1--8 of this DAG node
(blueprint: lem-sfb-norm-algcl-profinite-cech-exact). The blueprint itself makes no
such global exactness assertion. Step 2 uses Stanford Weil II seminar L19,
Proposition 1.1.9, first bullet, p. 3; step 6 uses Stacks 0CQN; step 8 uses 08ZY, 0A2P.

Proof:
1. Use lem-sfb-countable-split-profinite-cover: nonempty metrizable profinite T,V
   admit a surjection q with singleton fibres except for countably many double fibres
   {t_k^-,t_k^+}. Each oriented off-diagonal pair is clopen in the relation space.
   Every nonempty open U in T contains both points of a double fibre of arbitrarily
   large index. No section of q is assumed.
2. Apply lem-sfb-algcl-countable-closed-finite-cover with E=Q_l to obtain increasing
   closed finite intermediate fields F_j exhausting Omega. For any continuous g,
   the closed subsets g^{-1}(F_j) cover T.
3. By lem-weil-l-adic-extension-integers-dvr choose a uniformizer pi_k in F_k.
   Choose b_k in Omega with b_k^2=pi_k. If b_k were in F_k, the uniformizer
   decomposition and norm-one units would give |pi_k|^{2m}=|pi_k|, hence 2m=1
   for an integer m, impossible since 0<|pi_k|<1. Multiply b_k by a large
   nonnegative power of l to obtain a_k outside F_k with |a_k|<=l^{-k}.
4. Define f on the relation by f(x,x)=0, f(t_k^-,t_k^+)=a_k, and the reverse
   value -a_k. The fibre classification defines every value in Omega. Truncating
   at k<N gives a continuous function on finitely many clopen singleton loci.
   Its uniform error is at most l^{-N}; the ultrametric inequality proves
   continuity of f directly into Omega, with no infinite sum or completion.
5. On each individual fibre choose the potential 0 on its first point and a_k
   on its second point. Then f(x,y)=u(y)-u(x), so the three-term alternating
   sum on every fibre triple is zero. This proves the 1-cocycle equation;
   no continuity of these separate fibrewise potentials is claimed.
6. If d^0 g=f with g continuous, Baire (lem-sfb-baire-closed-cover-interior)
   applied to the closed cover g^{-1}(F_j) gives a nonempty open U contained
   in one g^{-1}(F_j). Choose k>=j with both t_k^-,t_k^+ in U. Their g-value
   difference is a_k in F_j, hence in F_k, contradicting step 3.
7. If q sigma=id, sectionInsert is continuous by its coordinate formula.
   Composing f with it gives g. Evaluate d f=0 on (sigma(v),t_0,...,t_n).
   The first summand is f; the others are minus d g. Equal-image equations
   identify sigma(q(t_i)) on every face, including deletion of t_0.
   Thus d g=f, also in degree one.
8. The existing explicit pullback is profinite and its first projection has
   the continuous diagonal section s maps to (s,s), hence is surjective.
   Its nerve is (s;t_0,...,t_n) with all q-images equal. forgetBase is the
   coordinate pullback, continuous and commuting with every deletion.
   The pulled-back f is therefore a continuous cocycle. Step 7 with the
   diagonal section gives h(s;t_0,...)=f(s,t_0,...) and d h=q^* f.
   For the empty surjection the same formulas are the unique zero functions.
-/
theorem normAlgclProfiniteCech_counterexample_and_local_contraction
    (l : ℕ) [Fact l.Prime] (Ω : Type u) [NormedField Ω] [Algebra (Padic l) Ω]
    [IsAlgClosure (Padic l) Ω]
    (hΩ : ∀ a : Padic l, ‖algebraMap (Padic l) Ω a‖ = ‖a‖) :
    (∃ (T V : Profinite.{v}), Nonempty T ∧ Nonempty V ∧
      TopologicalSpace.MetrizableSpace T ∧ TopologicalSpace.MetrizableSpace V ∧
      ∃ (q : C(T, V)), Function.Surjective q ∧
        ∃ f : C(scalarCechTuples q 2, Ω),
          (∀ x : scalarCechTuples q 3,
            ∑ j : Fin 3, (-1 : Ω) ^ j.val * f (scalarCechDelete q 2 j x) = 0) ∧
          ¬ ∃ g : C(scalarCechTuples q 1, Ω),
            ∀ x : scalarCechTuples q 2,
              ∑ j : Fin 2, (-1 : Ω) ^ j.val * g (scalarCechDelete q 1 j x) = f x) ∧
    (∀ (T V : Profinite.{v}) (q : C(T, V)), Function.Surjective q →
      ∀ (σ : C(V, T)) (hσ : Function.RightInverse σ q) (n : ℕ)
        (f : C(scalarCechTuples q (n + 2), Ω)),
        (∀ x : scalarCechTuples q (n + 3),
          ∑ j : Fin (n + 3), (-1 : Ω) ^ j.val * f (scalarCechDelete q (n + 2) j x) = 0) →
        ∃ g : C(scalarCechTuples q (n + 1), Ω),
          (∀ x : scalarCechTuples q (n + 1), g x = f (sectionInsert q σ hσ n x)) ∧
          ∀ x : scalarCechTuples q (n + 2),
            ∑ j : Fin (n + 2), (-1 : Ω) ^ j.val * g (scalarCechDelete q (n + 1) j x) = f x) ∧
    (∀ (T V : Profinite.{v}) (q : C(T, V)), Function.Surjective q →
      ∀ (n : ℕ) (f : C(scalarCechTuples q (n + 2), Ω)),
        (∀ x : scalarCechTuples q (n + 3),
          ∑ j : Fin (n + 3), (-1 : Ω) ^ j.val * f (scalarCechDelete q (n + 2) j x) = 0) →
        ∃ F : C(scalarCechTuples (projection q) (n + 2), Ω),
          (∀ x : scalarCechTuples (projection q) (n + 2), F x = f (forgetBase q (n + 2) x)) ∧
          ∃ h : C(scalarCechTuples (projection q) (n + 1), Ω),
            (∀ x : scalarCechTuples (projection q) (n + 1), h x = f (baseInsert q n x)) ∧
            ∀ x : scalarCechTuples (projection q) (n + 2),
              ∑ j : Fin (n + 2), (-1 : Ω) ^ j.val *
                h (scalarCechDelete (projection q) (n + 1) j x) = F x) := by
  sorry

end Profinite.NormAlgclCech
