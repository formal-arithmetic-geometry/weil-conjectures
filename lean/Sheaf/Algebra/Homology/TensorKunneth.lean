/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
import Mathlib.Algebra.Homology.Bifunctor
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.Algebra.DirectSum.Module

/-!
# The field-linear Kunneth isomorphism

Source: Stacks Project, Varieties, Tag 0BED, `lemma-kunneth`, the tensor-total Cech
step `equation-kunneth-on-cech` (blueprint: lem-sc-qcoh-cech-total-tensor-iso).
-/

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory DirectSum
open scoped TensorProduct

namespace HomologicalComplex

/-- Source: Stacks Project, Varieties, Tag 0BED, `lemma-kunneth`, the field-linear
identification in `equation-kunneth-on-cech`
(blueprint: lem-sc-qcoh-cech-total-tensor-iso).

For bounded-below cochain complexes over a field, the direct sum of the tensor products
of their cohomologies is the cohomology of their total tensor complex. The equation on
cycle representatives specifies the canonical map, including its well-definedness:
`iCycles` includes a cocycle, and `homologyπ` takes its cohomology class. The total tensor
complex `mapBifunctor A B (curriedTensor _) (ComplexShape.up ℤ)` (as recorded on
def-pc-tensor-complex-sheaves) uses the differential `d_A ⊗ 1 + (-1)^p 1 ⊗ d_B`.

Proof (the three elementary steps of the node):
1. In every degree choose complements `Z_A = B_A ⊕ H_A` and `A = Z_A ⊕ C_A`, and
similarly for `B`. The differential identifies `C_A^p` with `B_A^(p+1)`. Thus each
complex splits into its cohomology with zero differential and contractible two-term
pieces; the inverse of the differential on each two-term piece is a contracting homotopy.
2. Distribute these splittings through the total tensor direct sums. A tensor summand
with a contractible first factor is contracted by `h_A ⊗ 1`; a summand with a contractible
second factor is contracted by `(-1)^p 1 ⊗ h_B`. In both cases the mixed differential
terms have opposite signs and cancel. Only `H_A ⊗ H_B`, with zero differential, survives.
3. A tensor of cocycles is a cocycle. Replacing either representative by a boundary
changes the tensor by a boundary, by the signed Leibniz differential. Hence the class
map is well defined and bilinear. On the surviving summand it is exactly its inclusion,
so it is an isomorphism in every integer degree. -/
theorem tensor_kunneth {k : Type u} [Field k]
    (A B : CochainComplex (ModuleCat.{u} k) ℤ)
    (hA : ∃ m : ℤ, ∀ p : ℤ, p < m → IsZero (A.X p))
    (hB : ∃ m : ℤ, ∀ q : ℤ, q < m → IsZero (B.X q)) (n : ℤ) :
    ∃ e : (⨁ s : {pq : ℤ × ℤ // pq.1 + pq.2 = n},
      (A.homology s.1.1) ⊗[k] (B.homology s.1.2)) ≃ₗ[k]
      (mapBifunctor A B (curriedTensor (ModuleCat.{u} k)) (ComplexShape.up ℤ)).homology n,
      ∀ (s : {pq : ℤ × ℤ // pq.1 + pq.2 = n})
        (a : A.cycles s.1.1) (b : B.cycles s.1.2),
        ∃ z : (mapBifunctor A B (curriedTensor (ModuleCat.{u} k)) (ComplexShape.up ℤ)).cycles n,
          (mapBifunctor A B (curriedTensor (ModuleCat.{u} k)) (ComplexShape.up ℤ)).iCycles n z =
            ιMapBifunctor A B (curriedTensor (ModuleCat.{u} k)) (ComplexShape.up ℤ)
              s.1.1 s.1.2 n s.2
              ((A.iCycles s.1.1 a) ⊗ₜ[k] (B.iCycles s.1.2 b)) ∧
          e (DirectSum.lof k _ _ s
            ((A.homologyπ s.1.1 a) ⊗ₜ[k] (B.homologyπ s.1.2 b))) =
              (mapBifunctor A B (curriedTensor (ModuleCat.{u} k))
                (ComplexShape.up ℤ)).homologyπ n z :=
  by
  sorry

end HomologicalComplex
