/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.Algebra.Homology.FiniteTwistingTotalizationData
import WeilConjectures.Algebra.Homology.FiniteTwistingTotalizationStructure
import WeilConjectures.Algebra.Homology.FiniteTwistingTotalizationFlatness

/-! # Finite twisting totalization: construction

Source: latest blueprint, sk-i-additivity.proof.md, Filtered operations (routine),
lines 12-24 (blueprint: lem-trf-finite-filtered-totalization-base). The existence of the
filtered total complex of a finite twisting family, with its flatness properties.
-/

/- The flat-model packet includes this proved construction together with its existing helpers. -/

@[expose] public section
set_option autoImplicit false
universe u v w
open CategoryTheory CategoryTheory.Limits
namespace CochainComplex
variable {C : Type u} [Category.{v} C] [EssentiallySmall.{w} C]
  {J : GrothendieckTopology C}
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
  (R : Sheaf J CommRingCat.{w})
variable {R} {a b : ℤ}

/-- The finite upper triangular totalization of a twisting family exists, with its
square-zero differential and, under flat terms, K-flat total complex and tails.
This is the construction part of the finite twisting assembly; the comparison map is
`exists_finiteTwistingTotalization_comparison`.
Source: latest blueprint, sk-i-additivity.proof.md, Filtered operations (routine),
lines 12-24 (steps 1-3 of lem-trf-filtered-mapping-cylinder-step).

Proof:
1. Put `P^n = ⨁_p G_p^n` (finite biproduct, `finiteTwistingModuleBiproducts`), with the
   identity as `coordinates`. Define the differential as the finite matrix with diagonal
   entry `(p,p)` equal to `d_p^n`, entry `(p,q)` for `p < q` equal to `τ_pq^n`, and zero
   below the diagonal; this is the `differential` field. In the square `d^{n+1} ∘ d^n`
   the diagonal entries are `d_p d_p = 0`; the entries below the diagonal vanish; the
   entry `(p,q)` for `p < q` is the Maurer--Cartan expression of `D.maurerCartan`, zero.
   Hence `P` is a cochain complex, and the first conjunct is `P.d_comp_d`.
2. Every nonzero entry raises the weight, so the summands of weight `≥ r` form a
   subcomplex `F^r P` (def-sp-filtration); this gives `tailCoordinates`, `tailInclusion`,
   `F^a = ⊤`, `F^(b+1) = ⊥` and finiteness. The summand projections split every tail
   inclusion degreewise (`degreewiseSplit`). Projection to weight `p` kills `F^(p+1)`,
   and on the quotient the off-diagonal entries vanish, leaving `d_p`: this is
   `gradedIso`, with `gradedProjection` by construction (def-sp-filtered-complex-
   subquotients). Outside `[a,b]` consecutive tails agree and the grade is zero.
3. Let `N` be the maximum of upper bounds `N_p` of the `G_p` (`D.bounded`). The terms
   of `P` and of every `F^r P` vanish above `N` and are finite direct sums of flat
   module sheaves, hence flat (lem-pc-kflat-closure, the empty sum included). By
   lem-pc-bounded-above-flat-kflat-site (Stacks 06YQ) they are K-flat. The assumed
   K-flatness of each `G_p` is not needed.
(blueprint: lem-trf-finite-filtered-totalization-base) -/
theorem exists_finiteTwistingTotalization_base
    (a b : ℤ) (hab : a ≤ b) (D : FiniteTwistingFamily R a b) :
    ∃ M : FiniteTwistingTotalization D,
      (∀ n : ℤ, M.P.d n (n + 1) ≫ M.P.d (n + 1) (n + 1 + 1) = 0) ∧
      (((∀ (p : ↥(Finset.Icc a b)) (n : ℤ),
          SheafOfModules.IsFlatOnSite (J := J) (R := R) ((D.G p).X n)) ∧
        (∀ p : ↥(Finset.Icc a b), (D.G p).IsKFlatIndependentCoefficients)) →
        M.P.IsKFlatIndependentCoefficients ∧
          ∀ r : ℤ, IsKFlatIndependentCoefficients (J := J) (R := R)
            (M.F.step r : CochainComplex (ringedSiteModules.{w}
              ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R)) ℤ)) := by
  obtain ⟨M, hM⟩ := exists_finiteTwistingTotalization_structure a b hab D
  refine ⟨M, hM, ?_⟩
  intro hflat
  exact finiteTwistingTotalization_kflat_of_flat a b hab D M hflat

end CochainComplex
