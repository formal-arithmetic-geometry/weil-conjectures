/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF contributors
-/
module

public import WeilConjectures.Blowup.AdmissibleBlowup
public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Invertible

/-!
# Cartier boundary after an admissible blow-up

Source: the blueprint of the Weil conjectures, chapter `sec-nagata-compactification`,
node `sk-lem-nagata-boundary-divisor`, order 9 (blueprint: sk-lem-nagata-boundary-divisor).
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

/-- For a quasi-compact open of a quasi-compact quasi-separated scheme, an admissible
blow-up has a scheme-theoretically dense inverse image of the open whose complement is
cut out by an effective Cartier ideal. The proof chooses a finite-type ideal supported
on the complement (the quasi-coherent finite-type ideal lemma), blows it up, and uses
principalization to make its extension invertible. The support of the extension is the
inverse image of the original support, hence the complement of the inverse image of the
open. The complement of an effective Cartier divisor is scheme-theoretically dense.
(blueprint: sk-lem-nagata-boundary-divisor) -/
theorem exists_admissibleBlowup_boundaryDivisor
    {T : Scheme.{u}} [CompactSpace T] [QuasiSeparatedSpace T]
    (U : T.Opens) (hU : IsCompact (U : Set T)) :
    ∃ (B : IsAdmissible T U) (J : B.I.blowup.IdealSheafData),
      IsSchemeTheoreticallyDominant (B.I.blowupMap ⁻¹ᵁ U).ι ∧
        J.IsInvertible ∧
          (J.support : Set B.I.blowup) =
            ((B.I.blowupMap ⁻¹ᵁ U : B.I.blowup.Opens) : Set B.I.blowup)ᶜ := by
  sorry

end AlgebraicGeometry
