/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N0
-/
module

public import Sheaf.Paper.PbcRationalCategory
public import Sheaf.Paper.LocalizedTStructure
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.CategoryTheory.Idempotents.Pretriangulated
import WeilConjectures.CategoryTheory.Idempotents.TStructure

/-! # Finite-stage rational categories are Karoubian

Source: literature/blueprint/master/blueprint/sec-smooth-base-change/sk-rem-rest/
thm-weil-pbc-finite-stage-karoubian.md, node thm-weil-pbc-finite-stage-karoubian,
order 1433 (blueprint: thm-weil-pbc-finite-stage-karoubian).
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Idempotents
open AlgebraicGeometry

namespace AlgebraicGeometry.Scheme

/-- For a finite extension of `ℚ_[l]`, the raw rational constructible category on a
finite-dimensional noetherian scheme is idempotent complete, and its canonical Karoubi
inclusion is an exact equivalence.

Source: literature/blueprint/master/blueprint/sec-smooth-base-change/sk-rem-rest/
thm-weil-pbc-finite-stage-karoubian.md, node thm-weil-pbc-finite-stage-karoubian,
order 1433 (blueprint: thm-weil-pbc-finite-stage-karoubian).

Proof: identify the category with the raw scalar localization from
`def-weil-pbc-rational-category`. The theorem `pbc_localized_tstructure` supplies a
triangulated structure and a bounded t-structure on this same category under the
stated hypotheses. Apply the bounded-t-structure Karoubian theorem
`CategoryTheory.Triangulated.TStructure.isIdempotentComplete_of_bounded` to split every
idempotent. Apply
`CategoryTheory.Triangulated.TStructure.isEquivalence_toKaroubi_and_isTriangulated_of_bounded`
to obtain that the canonical functor to the Karoubi envelope is an exact equivalence.
-/
theorem finite_stage_karoubian
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (T : Scheme.{u}) [IsNoetherian T]
    [hDim : Fact (∃ m : ℕ, topologicalKrullDim T ≤ m)]
    [hInv : Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t))] :
    IsIdempotentComplete (PbcRationalCategory T (pbcIntegralDatum l E)
      (pbcUniformizer l E)) ∧
      (toKaroubi (PbcRationalCategory T (pbcIntegralDatum l E)
        (pbcUniformizer l E))).IsEquivalence ∧
        (toKaroubi (PbcRationalCategory T (pbcIntegralDatum l E)
          (pbcUniformizer l E))).IsTriangulated := by
  obtain ⟨t, _, ht, _⟩ := pbc_localized_tstructure T l E
  have hbounded : ∀ X, t.bounded X := by
    rw [ht]
    exact fun _ ↦ trivial
  exact ⟨t.isIdempotentComplete_of_bounded hbounded,
    t.isEquivalence_toKaroubi_and_isTriangulated_of_bounded hbounded⟩

end AlgebraicGeometry.Scheme
