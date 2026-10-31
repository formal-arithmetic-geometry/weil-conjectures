/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.NormalizedModelIntegralAdjunction

/-! # Full faithfulness of current integral reduction

Source: latest blueprint, sec-smooth-purity, composition-comparisons, integral clause.
(blueprint: lem-sp-current-composition-reduction-faithful).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.ProEtale.CompositionComparisons
open IntegralDirectImageTower NormalizedIntegralAdjunction

/-- Current constructible reduction into full constructible towers is fully faithful.
Source: latest blueprint, normalized reduction equivalence and integral criterion;
composition-comparisons proof, integral descent paragraph.
(blueprint: lem-sp-current-composition-reduction-faithful).

Proof in words:
1. The finite-type qc scheme T over a field is Noetherian. Map the nonzero scalar l from k
into each residue field; since p != l this gives the invertibility needed for the tower
reconstruction adjunction.
2. Identify the pulled-back spIntegralCondensed coefficient ring with the continuous
integer-ring model by the normalized coefficient comparison. Its section equivalence
and the normalized completed-ring scalar restriction give the equivalence with the
completed section-module category used by sp_normalized_equivalence.
3. The internal integral criterion identifies bounded constant-model constructibility
with derived completeness plus constructibility of the first reduction. The all-reduction
criterion therefore puts its image in sfIntegralConstructible. All functors and their
quotient maps are identified by the fixed coefficient normalization, so the forward
functor of the normalized-tower equivalence is the displayed reduction.
4. An equivalence is fully faithful. Compose its forward functor with the full inclusion
of normalized constructible towers into constructible towers, and transport through the
coefficient equivalence. Proof irrelevance identifies the supplied membership h with
the same lift's membership proof. This gives the claimed fully faithful structure.
The empty scheme and the zero object are included in the equivalence and criterion. -/
theorem reductionFullyFaithful
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (hpl : p ≠ l)
    (s : Presentation l E) (T : Scheme.{u})
    [T.Over (Spec (.of k))]
    [IsSeparated (T ↘ Spec (.of k))] [LocallyOfFiniteType (T ↘ Spec (.of k))]
    [QuasiCompact (T ↘ Spec (.of k))]
    (h : ∀ M : Constructible l E T,
      spConstructibleTorTowers l E T (s.towers T)
        ((red l E s T).obj M.obj)) :
    Nonempty ((reduction l E s T h).FullyFaithful) := by
  sorry

end AlgebraicGeometry.ProEtale.CompositionComparisons
