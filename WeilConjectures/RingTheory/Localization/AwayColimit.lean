/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.RingTheory.ProEtale.IndZariski

/-!
# A localization is the filtered colimit of its principal localizations

Let `P` be a commutative ring and `S ⊆ P` a submonoid. Ordering `S` by divisibility, the
localizations `P_f` (`f ∈ S`) form a filtered diagram of commutative rings whose colimit is
`S⁻¹P` (Stacks, Lemma 10.9.9). The diagram and the cocone of `R`-algebras are
`Algebra.IndZariski.awayDiag` and `Algebra.IndZariski.awayCocone`; here we record that the
cocone is also a colimit in `CommRingCat`.

## Main statements

- `CommRingCat.localization_colimit_principalLocalizations`

## References

- Stacks Project, Lemma 10.9.9, <https://stacks.math.columbia.edu/tag/00CR>
-/

@[expose] public section

universe u

open CategoryTheory Limits Algebra.IndZariski

namespace CommRingCat

/-- Let `S ⊆ P` be a submonoid, preordered by divisibility. (1) `S` is filtered. (2) The
localizations `P_f`, `f ∈ S`, with the maps `P_f → P_g` for `f ∣ g` (which are compatible with
`P → P_f`) form a diagram of commutative rings. (3) `S⁻¹P` with the maps `P_f → S⁻¹P` is a
colimit of this diagram in `CommRingCat`, and the maps `P_f → S⁻¹P` are compatible with the
localization maps from `P`.
(blueprint: `lem-weil-pbc-localization-colimit-principal-localizations`) -/
theorem localization_colimit_principalLocalizations (P : Type u) [CommRing P]
    (S : Submonoid P) :
    IsFiltered (AwayIndex S) ∧
    (∀ (f g : AwayIndex S) (h : f ≤ g),
      (awayDvdHom P (A := Localization.Away f.val) (B := Localization.Away g.val) h).toRingHom.comp
        (algebraMap P _) = algebraMap P _) ∧
    Nonempty (IsColimit ((forget₂ (CommAlgCat.{u} P) CommRingCat.{u}).mapCocone
      (Cocone.mk _ (awayCocone P S (Localization S))))) ∧
    ∀ f : AwayIndex S, (awayToLocalization P S (Localization S) f).toRingHom.comp
      (algebraMap P (Localization.Away f.val)) = algebraMap P (Localization S) := by
  refine ⟨inferInstance, fun f g h ↦ ?_, ⟨isColimitOfPreserves _
    (awayColimitPresentation P S (Localization S)).isColimit⟩, fun f ↦ ?_⟩
  · ext x
    exact (awayDvdHom P h).commutes x
  · ext x
    exact (awayToLocalization P S (Localization S) f).commutes x

end CommRingCat
