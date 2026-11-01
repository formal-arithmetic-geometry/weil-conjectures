/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.FiniteFreeCoefficients.Sites.NormalizedStageComparisonObligations
import WeilConjectures.SixFunctors.FiniteFreeCoefficients.NormalizedStageClosedEtaleIsomorphism
import WeilConjectures.SixFunctors.FiniteFreeCoefficients.NormalizedStageClosedProIsomorphism

/-! Closed exceptional stage comparison on ctf objects.

Source: blueprint latest, lem-coef-finite-free-extension.proof.md. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option Elab.async false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.FiniteCoefficientAdjoints
open scoped CategoryTheory.Functor
namespace WeilConjectures.FiniteFreeCoefficients

/-- The fixed closed coefficient counit transpose is invertible on either site's ctf domain.

Source: blueprint latest, lem-coef-finite-free-extension.proof.md, paragraphs 1--2.
(blueprint: lem-sf-normalized-stage-closed-isomorphism-data).

Proof: Split on the site flag `pro`. For `false` the assertion is the ordinary closed stage
comparison `normalized_stage_closed_etale_isomorphism` (finite-stage direct-image invertibility
and identification of the compactification mate with the lower-star transpose `closedMap`). For
`true` it is the pro-etale closed stage comparison `normalized_stage_closed_pro_isomorphism`
(constructible etale origin, Tor reflection, and invertibility of the three factors of
`proClosedMap`, using the ordinary case on the origin). -/
theorem normalized_stage_closed_isomorphism_data
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type (u + 1)) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))] [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))]
    (Z : Scheme.{u}) [Z.Over (Spec (.of D.k))]
    [IsSeparated (Z ↘ Spec (.of D.k))] [LocallyOfFiniteType (Z ↘ Spec (.of D.k))]
    [QuasiCompact (Z ↘ Spec (.of D.k))]
    (i : Z ⟶ X) [IsClosedImmersion i] [i.IsOver (Spec (.of D.k))] :
    ∀ (pro : Bool) {s t : Stage l E} (a : Arrow s t) (M : Sites.D pro s.ring X),
      Sites.Ctf pro s.ring X M → IsIso (Sites.stageClosedMap pro a i M) := by
  intro pro s t a M hM
  cases pro
  · exact normalized_stage_closed_etale_isomorphism D l hl E X Z i a M hM
  · exact normalized_stage_closed_pro_isomorphism D l hl E X Z i a M hM

end WeilConjectures.FiniteFreeCoefficients
