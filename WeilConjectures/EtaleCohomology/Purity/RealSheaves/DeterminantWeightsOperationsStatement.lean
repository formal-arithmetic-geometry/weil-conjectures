/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.DetWeightExterior
public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.DetWeightOperations
public import WeilConjectures.RepresentationTheory.Dual



/-! # Determinant weights of tensor operations

Source: literature/blueprint/latest/blueprint/part-weights-riemann-hypothesis/
  sec-determinant-weights/sec-determinant-weights-of-tensor-and-exterior-powers/
  sk-prop-walg-determinant-weights/_section.md, clauses (1), (2), and (3)
  (blueprint: sk-prop-walg-determinant-weights).

The determinant-weight set of a representation is rendered by membership in the existing
`detWeightMultiset`.  The rank-counted multiset in the exterior clause is the existing
`rankDetWeightMultiset`, which repeats each composition-factor weight by the factor's dimension.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry
namespace WeilGroup

variable {K : Type u} [Field K] [Finite K] {C : Scheme.{u}}
  {p : C ⟶ Spec (.of K)} [IsCurve p] (W : WeilGroup p)
  {l : ℕ} [Fact l.Prime] [Fact (ringChar K ≠ l)]
  [SmoothOfRelativeDimension 1 p] [GeometricallyConnected p] [W.IsEtaleQuotient]
  {V V' : Type u} [AddCommGroup V] [Module (PadicAlgCl l) V]
  [FiniteDimensional (PadicAlgCl l) V] [Nontrivial V]
  [AddCommGroup V'] [Module (PadicAlgCl l) V']
  [FiniteDimensional (PadicAlgCl l) V'] [Nontrivial V']
  (ρ : Representation (PadicAlgCl l) W.carrier V)
  (ρ' : Representation (PadicAlgCl l) W.carrier V')
  (ι : PadicAlgCl l →+* ℂ)

/--
For nonzero lisse Weil representations, determinant weights of tensor products add,
exterior-power weights are sums of rank-counted constituent weights, and duality negates
all constituent weights.

Source: literature/blueprint/latest/blueprint/part-weights-riemann-hypothesis/
  sec-determinant-weights/sec-determinant-weights-of-tensor-and-exterior-powers/
  sk-prop-walg-determinant-weights/_section.md, clauses (1), (2), and (3)
  (blueprint: sk-prop-walg-determinant-weights).

The first clause is the equality of the set of entries of the tensor-product
`detWeightMultiset` with the pairwise sum of the two input sets.  The second clause uses
`rankDetWeightMultiset`: a sub-multiset of cardinality `r` is exactly a choice of the
multiplicities `n_a` bounded by the dimensions of the composition factors and summing to
`r`.  The third clause is the equality between the dual constituent-weight set and the
pointwise negation of the original set.

Proof (node steps 1-6; blueprint proof paragraphs 1-4):

1. Choose composition series of `V` and `V'`, with factors `A_a` and `B_b`
   (`sk-r-linear-library`), lisse Weil subquotients on the same curve (`sk-d-real-weil`).
   All nonzero factors and their tensor, exterior and dual constructions have finite
   geometric determinant (`sk-d-real-detweights`), as `sk-p-readout` requires; they stay
   continuous on the geometric subgroup.  `λ_ι` is the real weight character of `sk-d-weights`.
2. Apply `sk-p-central` to `M = V^ss ⊕ V'^ss = ⊕ A_a ⊕ ⊕ B_b`: a central element
   `z = h ρ_M(s)^N`, `N > 0`, acting on `A_a`, `B_b` by nonzero scalars `c_a`, `c'_b`
   (stable subquotients carry the induced actions, `sk-i-restriction`).  By `sk-p-readout`,
   `γ_a = λ_ι(c_a) / N` and `dw_ι(B_b) = λ_ι(c'_b) / N`.
3. Clause (1): `z` acts on `A_a ⊗ B_b` by `c_a c'_b`, hence on each of its simple factors,
   whose weight is `γ_a + dw_ι(B_b)` by `sk-p-readout` and additivity of `λ_ι`.  Each
   `A_a ⊗ B_b` is nonzero, and the tensor filtration of `sk-r-linear-library` identifies
   the simple factors of `V ⊗ V'` with those of these pieces: both inclusions (as sets).
4. Clause (2): for an admissible tuple `(n_a)` the graded piece `⊗_a ⋀^{n_a} A_a` of
   `⋀^r V` is nonzero and `z` acts on it by `∏_a c_a^{n_a}`, so each simple factor has weight
   `∑_a n_a γ_a`; the exterior filtration of `sk-r-linear-library` identifies these factors
   with those of `⋀^r V` (both inclusions; `r = 0` gives the trivial line, `r = dim V` the
   determinant line).  The existing
   `AlgebraicGeometry.WeilGroup.detWeight_subquotient_exteriorPower` is the constituent-level
   form of this clause.
5. Clause (3): the reversed annihilator filtration of a composition series of `V`
   (dual-filtration clause of `sk-r-linear-library`) has quotients `A_a^∨`, each simple since
   a stable `B ⊂ A_a^∨` would give a stable annihilator `B^⊥ ⊂ A_a`
   (`def-real-weil-representation-operations`); so it is a composition series of `V^∨`.
6. The contragredient of `A` has matrix `(R⁻¹)ᵀ` for `R = ρ_A(s)`, so
   `det(s | A^∨) = det(s | A)⁻¹`, `dim A^∨ = dim A`, and `λ_ι(a⁻¹) = -λ_ι(a)` gives
   `dw_ι(A^∨) = -dw_ι(A)`; with step 5 this gives `DW(V^∨) = -DW(V)`.
-/
theorem determinantWeightSet_operations
    (hρ : W.IsLisse l ρ) (hρ' : W.IsLisse l ρ')
    (r : ℕ) (hr : r ≤ Module.finrank (PadicAlgCl l) V) :
    {a : ℝ | a ∈ W.detWeightMultiset l (ρ.tprod ρ') ι} =
        Set.image2 (fun a b : ℝ ↦ a + b)
          {a : ℝ | a ∈ W.detWeightMultiset l ρ ι}
          {b : ℝ | b ∈ W.detWeightMultiset l ρ' ι} ∧
      {a : ℝ | a ∈ W.detWeightMultiset l (ρ.exteriorPower r) ι} =
        Set.image Multiset.sum
          {T : Multiset ℝ | T ≤ W.rankDetWeightMultiset l ρ ι ∧ T.card = r} ∧
      {a : ℝ | a ∈ W.detWeightMultiset l ρ.dual ι} =
        Set.image (fun a : ℝ ↦ -a) {a : ℝ | a ∈ W.detWeightMultiset l ρ ι} := by
  sorry

end WeilGroup
end AlgebraicGeometry
