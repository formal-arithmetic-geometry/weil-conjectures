/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF stage-2 worker E1
-/
module

public import Sheaf.Algebra.Homology.ZigzagModule
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import Mathlib.Algebra.Category.ModuleCat.Abelian

/-!
# Row-cycle lifts to a zig-zag

Source: Stacks Project, Algebra, Lemma Tag 00M1, proof lines 18464--18481
(blueprint: lem-weil-pbc-double-complex-row-cycle-lifts-to-zigzag).
-/

@[expose] public section

open CategoryTheory DirectSum

namespace HomologicalComplex₂

variable {R : Type*} [CommRing R]

/-- (blueprint: lem-weil-pbc-double-complex-row-cycle-lifts-to-zigzag)
In a first-quadrant homological double complex whose rows are exact in positive
horizontal degrees, every cycle in the cokernel of the first horizontal map
has a representative which extends to a zig-zag. The row-cokernel complex
`Aʳᵗ` is `A.opcycles 0`, formed in the abelian category of chain complexes:
its degree `q` is the cokernel of `d₁,ᵩ : A₁,ᵩ → A₀,ᵩ`, with projection
`π = A.pOpcycles 0` and differential induced by `δ`. The hypothesis `hcycle`
says that `πₙ(x)` is a cycle of `Aʳᵗ` (automatic at `n = 0`, where there is
no outgoing differential). Row exactness is `ShortComplex.Exact` of
`Aₚ₊₁,ᵩ → Aₚ,ᵩ → Aₚ₋₁,ᵩ` for `p ≥ 1`.

Source: Stacks Project, Algebra, Lemma Tag 00M1 (`lemma-no-spectral-sequence`),
proof lines 18464--18481. Proof, following the node's five steps:

1. If `n = 0`, take the tuple with sole entry `x`. The conditions defining
   `zigzagCycles` are empty (def-weil-pbc-double-complex-zigzag-module).
2. For `0 ≤ k ≤ n`, inductively construct entries `aⱼ,ₙ₋ⱼ` for `0 ≤ j ≤ k`,
   starting with `a₀,ₙ = x`, with `d aⱼ,ₙ₋ⱼ = δ aⱼ₋₁,ₙ₋ⱼ₊₁` for `1 ≤ j ≤ k`.
   The initial partial tuple consists just of `x`.
3. For `n > 0`, the cycle condition says that `δ x` belongs to the kernel of
   the projection onto the row cokernel, hence to the image of `d`. Choose
   `a₁,ₙ₋₁` with `d a₁,ₙ₋₁ = δ x` (def-weil-pbc-module-chain-complex-homology).
4. For `2 ≤ k ≤ n`, put `y = δ aₖ₋₁,ₙ₋ₖ₊₁`. Commutation gives
   `d y = δ d aₖ₋₁,ₙ₋ₖ₊₁ = δ δ aₖ₋₂,ₙ₋ₖ₊₂ = 0`. Row exactness at the
   positive horizontal position `k - 1` gives `aₖ,ₙ₋ₖ` with `d aₖ,ₙ₋ₖ = y`
   (def-weil-pbc-exact-sequence), preserving all previously chosen entries.
5. At `k = n`, assemble the finite tuple in `zigzagTotal A n`. Its adjacent
   equations are precisely those defining `zigzagCycles A n`, and its `(0,n)`
   component remains `x` (def-weil-pbc-double-complex-zigzag-module). -/
theorem row_cycle_lifts_to_zigzag
    (A : HomologicalComplex₂ (ModuleCat R) (ComplexShape.down ℕ)
      (ComplexShape.down ℕ))
    (hrow : ∀ (p q : ℕ), 0 < p →
      (ShortComplex.mk ((A.d (p + 1) p).f q) ((A.d p (p - 1)).f q)
        (by rw [← HomologicalComplex.comp_f, A.d_comp_d,
          HomologicalComplex.zero_f])).Exact)
    (n : ℕ)
    (x : (A.X 0).X n)
    (hcycle : ∃ c : (A.opcycles 0).cycles n,
      (A.opcycles 0).iCycles n c = (A.pOpcycles 0).f n x) :
    ∃ a : zigzagTotal A n,
      a ∈ zigzagCycles A n ∧
        DirectSum.component R (ZigzagIndex n)
          (fun i : ZigzagIndex n => (A.X i.1.1).X i.1.2)
          ⟨(0, n), by omega⟩ a = x := by
  sorry

end HomologicalComplex₂
