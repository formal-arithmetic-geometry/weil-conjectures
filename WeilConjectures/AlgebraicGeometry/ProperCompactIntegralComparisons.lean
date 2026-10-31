/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.OrdinaryCompactCohomology
public import WeilConjectures.AlgebraicGeometry.CompactSupportCoefficientAction
public import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-! # Intermediate comparisons for proper compact support -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
open AlgebraicallyClosedCoefficients (Coefficient)

/-- The proper comparison at this coefficient level.
Source: literature/blueprint/latest/blueprint/sec-zeta-weil/sk-input-weights/
prop-weil-proper-compact-coincidence.proof.md, first paragraph
(blueprint: lem-weil-proper-compact-integral-comparisons).

Proof: Compare c with the identity compactification through a common refinement on the
entire coherent quotient system. The proper finite normalization commutes with quotient
restriction, so its maps form an isomorphism of these towers, not only termwise maps.
Apply the total derived limit and the recorded projection-normalized compact realization.
At the identity compactification cancel the identity-open system functor. The resulting
ordinary system image identifies with completed derived direct image on complete inputs.
This gives the first natural comparison. The chosen compact and ordinary image values
are Roos vertices for these same towers. Transport along the tower comparison, and use
the triangle axiom on their common one-minus-shift map to identify the two vertices.
The resulting isomorphism lies in the full constructible subcategory, giving the second
clause. Zero inputs and empty schemes give zero towers; the argument includes n=1.
-/
theorem properCompactIntegralComparisons
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (Y : Scheme.{u})
    [Y.Over (Spec (CommRingCat.of D.k))]
    [IsProper (Y ↘ Spec (CommRingCat.of D.k))]
    (c : Compactification (Y ↘ Spec (CommRingCat.of D.k)))
    (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] :
    letI : (Spec (CommRingCat.of D.k)).Over (Spec (CommRingCat.of D.k)) := ⟨𝟙 _⟩
    Nonempty (sfCompactSupportFiniteIntegralFunctor l D.k (finiteFieldDatumPrimeUnit D l hl)
        c E ⋙ (sfIntegralConstructible l E (Spec (.of D.k))).ι ≅
      (sfIntegralConstructible l E Y).ι ⋙
        sfCompletedDerivedDirectImage l E (Y ↘ Spec (.of D.k))) ∧
    ∀ K : sfIntegralConstructibleCategory l E Y,
      Nonempty (sfIntegralCompactSupportValue l E D.k (finiteFieldDatumPrimeUnit D l hl)
        c K ≅ integralImage D l hl E Y K) := by
  sorry

end WeilConjectures
