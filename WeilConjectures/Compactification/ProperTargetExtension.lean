/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.Blowup.AdmissibleBlowup

/-!

# Extension of a morphism to a proper target after an admissible blow-up

If `X` is quasi-compact and quasi-separated, `U ⊆ X` is a dense quasi-compact open and
`y : Y ⟶ S` is proper, then every morphism `U ⟶ Y` over `S` extends to the whole of a
`U`-admissible blow-up of `X`.

This is the corollary of the partial-section extension theorem
(`AlgebraicGeometry.exists_admissibleBlowup_extend_section`) obtained by taking `V = U`
there: the resulting graph `W ↪ X' ×ₛ Y` is closed, hence `W ⟶ X'` is proper as well as an
open immersion, so its image is open, closed and dense in `X'`, therefore all of `X'`.

## Main results

- `AlgebraicGeometry.exists_admissibleBlowup_extend_of_isProper`: the extension statement
  above.

-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

/-- Blueprint `sk-cor-nagata-sketch-proper-extension`: Extension to a proper target.

Let `X` be quasi-compact and quasi-separated over `S`, let `U ⊆ X` be a dense quasi-compact
open and let `y : Y ⟶ S` be proper. Then every `S`-morphism `U ⟶ Y` extends to a morphism
`X' ⟶ Y` defined on all of a `U`-admissible blow-up `X'` of `X`. -/
theorem exists_admissibleBlowup_extend_of_isProper {S X Y : Scheme.{u}} [CompactSpace X]
    [QuasiSeparatedSpace X] (x : X ⟶ S) {y : Y ⟶ S} [IsProper y] {U : X.Opens}
    (hU : IsCompact (U : Set X)) (hUdense : Dense (U : Set X)) (f : U.toScheme ⟶ Y)
    (hf : f ≫ y = U.ι ≫ x) :
    ∃ (B : IsAdmissible X U) (g : B.I.blowup ⟶ Y), g ≫ y = B.I.blowupMap ≫ x ∧
      (B.I.blowupMap ⁻¹ᵁ U).ι ≫ g = (B.I.blowupMap ∣_ U) ≫ f := by
  sorry

end AlgebraicGeometry
