/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q51
-/
module

public import Sheaf.Paper.CondensedERealizationDefinitions
import Sheaf.Paper.CondensedERealizationSystem
import Sheaf.Paper.CondensedERealizationSystemExchange

/-! # Continuous field realization with its ordered exchange comparison

Source: Bhatt--Scholze, Proposition 6.8.14(2), Remark 6.8.15.
(blueprint: lem-weil-pbc-condensed-e-realization)
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u

namespace WeilConjectures

/-- Rationalized integral constructible coefficients have the canonical condensed
continuous E-realization, simultaneously for all separated finite-type k-schemes.
All operation, adjunction, composition and ordered-exchange comparisons are retained.
Source: Bhatt--Scholze, Lemmas 4.2.12--4.2.13, Proposition 6.8.14(2), Remark 6.8.15;
the additional archived local-presentation bridge and ordered-exchange comparison are
those specified by the blueprint (blueprint: lem-weil-pbc-condensed-e-realization).

Proof:
1. Finite-type schemes over k are Noetherian and finite dimensional, and l is a unit
in their stalks. Identify point-pullback coefficients with continuous functions using
weakly contractible affine covers. Integral coefficients are the inverse limit of
finite quotients; localization gives E-valued functions locally, without a global
bound on denominators on non-quasi-compact site objects. The local-presentation
bridge identifies stratified presentations with stratified finite locally free sheaves.
2. Exact scalar localization sends an integral complex to its derived scalar extension
and sends a localized morphism to the same morphism divided by its uniformizer power.
3. Use the bounded-below compactness theorem on the multiplication-by-uniformizer
telescope. Exact filtered colimits and extension/restriction adjunction identify every
shifted Hom with its scalar localization, proving full faithfulness.
4. Lisse rational sheaves admit constructible integral lattices. Lift morphisms and
cones by full faithfulness, clearing denominators on one arrow. Refine a stratification
to open layers of successive reduced closed complements, apply the exact open-closed
sequence, and induct on dimension. Bounded truncation triangles then yield integral
models for every bounded complex, without adding a Karoubi envelope.
5. Ordinary inverse image preserves the local finite perfect descriptions and is
already complete there. Its completion unit identifies it with the prescribed completed
pullback. Exact localization commutes with inverse image and gives the pull comparison.
6. Integral constructible direct-image finiteness and completeness identify the integral
restriction with ordinary image. The qcqs continuity comparison gives the rational
push comparison, normalized by extension/restriction adjunction, with the stated units
and counits. All morphisms here are qcqs by the finite-type separated hypotheses.
7. Pullback comparisons commute with identity and composition because the actual
coefficient maps are point-pullback composition maps. Tensor localization transports
these same comparisons and their units and counits.
8. Strict-tower mate normalization identifies the transported finite-level exchanges
with the actual ringed adjunction mate. Apply Rlim to its equation, cancel the specified
projection and direct-image/limit comparisons, and retain the completion units. The
ordered completed exchange therefore rationalizes to precisely the rational mate.
The unit, composition-square and counit equations from steps 5--7 identify its J-image
with the archived condensed exchange, as an equality of the specified arrows. -/
theorem condensedE_realization (l : ℕ) [Fact l.Prime]
    (E : Type u) [NormedField E] [NormedAlgebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)] :
    ∃ D : CondensedERealization.Data l E k, Nonempty (CondensedERealization.Exchange l E k D) := by
  obtain ⟨D⟩ := condensedE_realization_system l E k
  exact ⟨D, condensedE_realization_system_exchange l E k D⟩

end WeilConjectures
