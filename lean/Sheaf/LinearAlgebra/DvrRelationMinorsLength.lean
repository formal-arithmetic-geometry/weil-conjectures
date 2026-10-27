/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NU
-/
module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Length
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.Data.Finset.Sort
import Sheaf.LinearAlgebra.DvrMatrixSmithPowers
import Sheaf.LinearAlgebra.Matrix.MinorIdeal
import WeilConjectures.LinearAlgebra.Matrix.CauchyBinet

/-!
# Torsion length from maximal-rank relation minors

Source: Bosch--Lütkebohmert--Raynaud, Néron Models, §3.3 Lemma 2 and its proof,
printed p.66, PDF page 72; the finite free relation-module calculation
(blueprint: lem-sfb-dvr-relation-minors-length).
-/

@[expose] public section

universe u v

namespace Matrix

/-- The torsion in a finite free relation quotient over a DVR has finite length,
equal to the least valuation of its minors of size equal to its fraction-field row rank.
Here `hvA` says that `vA` is the valuation of the given DVR, and `hvπ` normalizes it.
`IsLeast` records an attained minimum, including the empty minor at rank zero.

Source: Bosch--Lütkebohmert--Raynaud, Néron Models, §3.3 Lemma 2 and proof,
printed p.66, PDF page 72 (blueprint: lem-sfb-dvr-relation-minors-length).

Proof:
1. If q = 0, all rows vanish over the fraction field and hence over A. The quotient
   is free and has zero torsion. The size-zero determinant is 1 with valuation zero.
   This also covers either matrix dimension being zero.
2. Apply lem-sfb-dvr-matrix-smith-powers to write D = UPV, whose nonzero diagonal
   entries are π^(e i). Over F, U preserves the row span and V induces an invertible
   coordinate change. The nonzero diagonal rows are independent, so their number is q.
   Put E = sum of the exponents.
3. The row-vector map x ↦ xV identifies the quotient with the diagonal quotient,
   which is the sum of A/(π^(e i)) for i < q and a free summand A^(N-q). The first
   summand is killed by the nonzero π^E, while the free summand is torsion-free.
   Hence the torsion submodule is the sum of the cyclic quotients. Submodule chains
   and their strict inclusions correspond under this isomorphism, preserving length.
4. For each exponent e, submodules of A/(π^e) correspond to ideals containing (π^e).
   By lem-weil-pbc-dvr-unit-times-uniformizer-power, these are exactly (π^j),
   0 ≤ j ≤ e, ordered in reverse exponent order. Thus the cyclic length is e,
   including e = 0 when the quotient is zero.
5. Apply lem-weil-pbc-length-additive-short-exact inductively to the split exact
   sequences adjoining one cyclic summand. This gives finite torsion length E.
6. By lem-weil-pbc-cauchy-binet, applied twice, every q-minor of UPV is an A-linear
   combination of q-minors of P. Apply the same expansion to U⁻¹DV⁻¹ to get the
   reverse inclusion. Therefore their minor ideals (def-trf-minor-ideal) coincide.
7. Only the leading q-minor of D can be nonzero, and it is π^E. Consequently the
   common minor ideal is the nonzero principal ideal (π^E).
8. There are finitely many minors and at least one is nonzero. Choose one of least
   valuation d. Unit-times-power factorization shows it generates (π^d), and all
   other minors belong to that ideal, including zero minors. Equality with (π^E)
   forces d = E by divisibility in both directions and normalization of the valuation.
   Unit pivots, free quotient summands, and zero minors remain allowed throughout.
-/
theorem length_torsion_quotient_eq_min_valuation_minors
    {A : Type u} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    {F : Type v} [Field F] [Algebra A F] [IsFractionRing A F]
    (π : A) (hπ : IsLocalRing.maximalIdeal A = Ideal.span {π})
    (vA : AddValuation F (WithTop ℤ))
    (hvA : ∀ x : F, 0 ≤ vA x ↔ x ∈ Set.range (algebraMap A F))
    (hvπ : vA (algebraMap A F π) = 1)
    (s N : ℕ) (P : Matrix (Fin s) (Fin N) A)
    (q : ℕ)
    (hq : q = Module.finrank F
      (Submodule.span F (Set.range (fun i : Fin s ↦ fun j : Fin N ↦
        algebraMap A F (P i j))))) :
    ∃ ℓ : ℕ,
      Module.length A (Submodule.torsion A
        ((Fin N → A) ⧸ Submodule.span A (Set.range P))) = (ℓ : ℕ∞) ∧
      IsLeast
        (Set.range (fun ST :
          {S : Finset (Fin s) // S.card = q} ×
            {T : Finset (Fin N) // T.card = q} ↦
          vA (algebraMap A F ((P.submatrix
            (ST.1.val.orderEmbOfFin ST.1.property)
            (ST.2.val.orderEmbOfFin ST.2.property)).det))))
        (ℓ : WithTop ℤ) := by
  sorry

end Matrix
