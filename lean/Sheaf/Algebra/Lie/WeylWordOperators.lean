module

public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# Weyl operators on the rational vector space of words

Source: Milne, Algebraic Groups (2017), Theorem 23.63, first proof, printed p.504;
the explicit word recursion is the agent-supplied supporting construction in the DAG
(blueprint: lem-sfb-weyl-word-operators).

The vector space is `List I →₀ ℚ`, with basis vector `Finsupp.single w 1` for each word `w`.
The empty list is the empty word. No multiplication on this vector space is needed.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

noncomputable section

namespace LieAlgebra.WeylWord

/-- The sum of row `i` of `B` over the letters of a word, with empty sum zero.
Source: agent-supplied construction supporting Milne, Theorem 23.63, printed p.504
(blueprint: lem-sfb-weyl-word-operators). -/
def weight {I : Type u} (B : I → I → ℚ) (i : I) (w : List I) : ℚ :=
  (w.map (B i)).sum

/-- Prepending a letter, extended linearly to finitely supported word combinations.
Source: agent-supplied construction supporting Milne, Theorem 23.63, printed p.504
(blueprint: lem-sfb-weyl-word-operators). -/
def lowering {I : Type u} (i : I) : Module.End ℚ (List I →₀ ℚ) :=
  Finsupp.lmapDomain ℚ ℚ (List.cons i)

/-- The diagonal operator with eigenvalue `lam i - weight B i w` on the basis word `w`.
Source: agent-supplied construction supporting Milne, Theorem 23.63, printed p.504
(blueprint: lem-sfb-weyl-word-operators). -/
def cartan {I : Type u} (B : I → I → ℚ) (lam : I → ℚ) (i : I) :
    Module.End ℚ (List I →₀ ℚ) :=
  Finsupp.linearCombination ℚ (fun w ↦ (lam i - weight B i w) • Finsupp.single w 1)

open Classical in
/-- The raising operator on basis words, recursively defined on the shorter tail.
The scalar correction occurs exactly when the leading letter equals the raising index.
Source: agent-supplied construction supporting Milne, Theorem 23.63, printed p.504
(blueprint: lem-sfb-weyl-word-operators). -/
def raisingWord {I : Type u} (B : I → I → ℚ) (lam : I → ℚ) (i : I) :
    List I → (List I →₀ ℚ)
  | [] => 0
  | j :: w => lowering j (raisingWord B lam i w) +
      (if i = j then (lam i - weight B i w) • Finsupp.single w 1 else 0)

/-- Linear extension of the recursively constructed raising operator on basis words.
Source: agent-supplied construction supporting Milne, Theorem 23.63, printed p.504
(blueprint: lem-sfb-weyl-word-operators). -/
def raising {I : Type u} (B : I → I → ℚ) (lam : I → ℚ) (i : I) :
    Module.End ℚ (List I →₀ ℚ) :=
  Finsupp.linearCombination ℚ (raisingWord B lam i)

open Classical in
/-- The four Weyl commutator identities for the explicitly constructed word operators.
There are no symmetry, diagonal, sign or rank assumptions on the rational matrix `B`.

Source: agent-supplied supporting construction for Milne, Algebraic Groups (2017),
Theorem 23.63, first proof, printed p.504; Bourbaki VIII, section 4, no.2 is cited
there for the surrounding normal-form argument, not for these explicit formulas
(blueprint: lem-sfb-weyl-word-operators).

Proof plan:
1. The recursion on the tail constructs a finite word combination at every word. Extend
   from the word basis by linearity. The weights satisfy `β_i(j :: w) = B i j + β_i(w)`.
2. Both Cartan composites multiply each basis word by the same product of rational
   scalars, so their commutator is zero, using `def-wf-lie-algebra`.
3. The recursion directly gives `[E_i,F_j] = δ_ij H_i` on each word, hence on all vectors.
4. The weight identity gives `[H_i,F_j] = -B i j F_j` on each word.
5. For `D = H_i E_j - E_j H_i`, induct on the word. At the empty word both sides of
   `D(w) = B i j E_j(w)` vanish. On `F_k w`, expand using steps 3 and 4 to obtain
   `F_k D(w) - B i k F_k E_j(w) + δ_jk H_i H_j(w) - δ_jk H_j H_i(w)
   + B i k E_j F_k(w)`. Step 2 cancels the Cartan terms; step 3 reduces the other
   correction to `δ_jk B i k H_j(w)`. Use the induction hypothesis and
   `δ_jk B i k = δ_jk B i j`, then step 3 again, to finish. Extend by linearity.
6. The calculations impose no condition on `B`. When `I` is empty there are no index
   pairs, and the vector space has just the empty word as its basis. -/
theorem commutator_relations {I : Type u} [Finite I] (B : I → I → ℚ) (lam : I → ℚ) :
    ∀ i j : I,
      ⁅cartan B lam i, cartan B lam j⁆ = 0 ∧
      ⁅raising B lam i, lowering j⁆ = (if i = j then cartan B lam i else 0) ∧
      ⁅cartan B lam i, raising B lam j⁆ = B i j • raising B lam j ∧
      ⁅cartan B lam i, lowering j⁆ = (-B i j) • lowering j := by
  sorry

end LieAlgebra.WeylWord
