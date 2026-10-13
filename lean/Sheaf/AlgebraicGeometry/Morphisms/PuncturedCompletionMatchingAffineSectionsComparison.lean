/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.Morphisms.PuncturedCompletionMatchingSections

/-! # The localized ring equivalence behind the punctured section comparison

Source: Stacks Project, Tags 0BLH, 05ER and 05EU.
(blueprint: new-sbc-punctured-completion-matching-affine-sections-comparison)
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.CompletionGluingData

/-- The localized first projection is the underlying ring map of an equivalence.

Source: Stacks Project, Tag 05ER, with the algebra compatibility of Tag 05EU.
The finite principal-open affine charts of the finite morphism `q` form the
formal-gluing datum of Tag 05ER.  Its degree-zero compatible sections are the
explicit pullback `D.matchingRing`; localizing at `f` identifies degree zero
with the section ring on the corresponding chart.  Under the sheaf
identification of sections on an affine scheme, this localized projection is
exactly the `appTop` map displayed below.  The compatibility with addition and
multiplication is the algebra compatibility in Tag 05EU, so the localized
isomorphism is a `RingEquiv`.
(blueprint: new-sbc-punctured-completion-matching-affine-sections-comparison)
-/
theorem exists_puncturedMap_basicOpen_appTop_ringEquiv
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    {U : (Spec (.of A)).Opens}
    (hU : ∀ x : Spec (.of A), x ∈ U ↔ x ≠ IsLocalRing.closedPoint A)
    {Y : Scheme.{u}} {q : Y ⟶ U.toScheme} [IsFinite q]
    {E : Scheme.{u}} {s : E ⟶ Spec
      (.of (AdicCompletion (IsLocalRing.maximalIdeal A) A))} [IsFinite s]
    (D : CompletionGluingData A U q E s) (f : A)
    (hf : (PrimeSpectrum.basicOpen f : (Spec (.of A)).Opens) ≤ U) :
    ∃ e : Γ(((D.modelMap ∣_ U) ⁻¹ᵁ
        (U.ι ⁻¹ᵁ PrimeSpectrum.basicOpen f)).toScheme, ⊤) ≃+*
        Γ((D.puncturedMap ⁻¹ᵁ ((D.modelMap ∣_ U) ⁻¹ᵁ
          (U.ι ⁻¹ᵁ PrimeSpectrum.basicOpen f))).toScheme, ⊤),
      (e : _ → _) =
        (D.puncturedMap ∣_ ((D.modelMap ∣_ U) ⁻¹ᵁ
          (U.ι ⁻¹ᵁ PrimeSpectrum.basicOpen f))).appTop.hom := by
  sorry

end AlgebraicGeometry.Scheme.CompletionGluingData
