/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q21
-/
module

public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.NumberTheory.Padics.IntegersProfiniteTower
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.Data.Matrix.Block
public import Mathlib.Topology.Sets.Opens

/-!
# Local splitting of a continuous integral dominating pivot

Source: Hemo--Richarz--Scholbach, arXiv:2305.18131, proof of Theorem 6.12(2),
finite extension case, pp. 18–19. This is the agent auxiliary pivot lemma extracted
from the continuous integral Smith argument, not a theorem stated verbatim in HRS
(blueprint: lem-sfb-continuous-integral-pivot-splitting).

The positive matrix dimensions are written `1 + n` and `1 + m`, using the index
sets `Fin 1 ⊕ Fin n` and `Fin 1 ⊕ Fin m` so that the first coordinate is explicit.
-/

@[expose] public section

universe u v

namespace Padic

/-- A continuous integral matrix whose entries are divisible by `π ^ e`, with the first
entry a unit times `π ^ e` at `t₀`, admits a continuous local integral pivot splitting.
The inverse changes of basis are also entrywise continuous. The residual sizes `n`, `m`
may be zero. No constancy assumption on any cokernel is made.

Source: Hemo--Richarz--Scholbach, arXiv:2305.18131, proof of Theorem 6.12(2),
finite extension case, pp. 18–19; agent continuous integral pivot variant
(blueprint: lem-sfb-continuous-integral-pivot-splitting).

Proof: (1) Divide every entry of `G` by `π ^ e`. Divisibility and continuous uniformizer
 division give a continuous integral matrix `q` with `G = π ^ e • q`. The first entry of
 `q` is a unit at `t₀`. Shrink to its open unit locus `U`, where its inverse is continuous.
(2) Apply the explicit unit-pivot Schur formula to `q` on `U`: first use the column
 transvection `R₀`, then the row transvection `L₁`, and finally scale the first row by
 the inverse pivot using `L₀`. The combined factor is `L₀ * L₁`. These matrices and their
 inverses have continuous entries, and give the block matrix with corner `1` and
 continuous residual block `H₀`.
(3) Rescale this identity by `π ^ e`, retain `L = L₀ * L₁` and `R = R₀`, and set
 `H = π ^ e • H₀`. This gives the stated block identity and continuity of `H`.
(4) If either residual index set is empty, interpret the same formulas as empty blocks.
 The finite matrix products and continuity assertions still hold, including the `1 × 1`
 case. These four steps are the proof recorded in the DAG. -/
theorem continuous_integral_pivot_splitting
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E]
    (π : coefficientExtensionIntegers l E)
    (hπ : Ideal.span ({π} : Set (coefficientExtensionIntegers l E)) =
      coefficientExtensionMaximalIdeal l E)
    (T : Type v) [TopologicalSpace T] (m n : ℕ)
    (G : T → Matrix (Fin 1 ⊕ Fin n) (Fin 1 ⊕ Fin m) (coefficientExtensionIntegers l E))
    (hG : ∀ (i : Fin 1 ⊕ Fin n) (j : Fin 1 ⊕ Fin m),
      @Continuous T (coefficientExtensionIntegers l E) _
        (coefficientExtensionIntegersTopology l E) (fun t ↦ G t i j))
    (e : ℕ) (t₀ : T)
    (hdiv : ∀ (t : T) (i : Fin 1 ⊕ Fin n) (j : Fin 1 ⊕ Fin m), π ^ e ∣ G t i j)
    (hpivot : ∃ a : (coefficientExtensionIntegers l E)ˣ,
      G t₀ (Sum.inl 0) (Sum.inl 0) = π ^ e * (a : coefficientExtensionIntegers l E)) :
    ∃ U : TopologicalSpace.Opens T, t₀ ∈ U ∧
      ∃ (L : U → Matrix.GeneralLinearGroup (Fin 1 ⊕ Fin n) (coefficientExtensionIntegers l E))
        (R : U → Matrix.GeneralLinearGroup (Fin 1 ⊕ Fin m) (coefficientExtensionIntegers l E))
        (H : U → Matrix (Fin n) (Fin m) (coefficientExtensionIntegers l E)),
        (∀ i j : Fin 1 ⊕ Fin n,
          @Continuous U (coefficientExtensionIntegers l E) _
            (coefficientExtensionIntegersTopology l E) (fun t ↦ L t i j)) ∧
        (∀ i j : Fin 1 ⊕ Fin n,
          @Continuous U (coefficientExtensionIntegers l E) _
            (coefficientExtensionIntegersTopology l E) (fun t ↦ (L t)⁻¹ i j)) ∧
        (∀ i j : Fin 1 ⊕ Fin m,
          @Continuous U (coefficientExtensionIntegers l E) _
            (coefficientExtensionIntegersTopology l E) (fun t ↦ R t i j)) ∧
        (∀ i j : Fin 1 ⊕ Fin m,
          @Continuous U (coefficientExtensionIntegers l E) _
            (coefficientExtensionIntegersTopology l E) (fun t ↦ (R t)⁻¹ i j)) ∧
        (∀ (i : Fin n) (j : Fin m),
          @Continuous U (coefficientExtensionIntegers l E) _
            (coefficientExtensionIntegersTopology l E) (fun t ↦ H t i j)) ∧
        ∀ t : U,
          (L t : Matrix (Fin 1 ⊕ Fin n) (Fin 1 ⊕ Fin n) (coefficientExtensionIntegers l E)) *
            G t.val *
            (R t : Matrix (Fin 1 ⊕ Fin m) (Fin 1 ⊕ Fin m) (coefficientExtensionIntegers l E)) =
          Matrix.fromBlocks
            (fun (_i _j : Fin 1) ↦ π ^ e) 0 0 (H t) := by
  sorry

end Padic
