/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H1
-/
module

public import Sheaf.RingTheory.JapaneseDomain

/-!
# Localization of N-1 and Japanese domains

Source: Stacks Project, Algebra, Lemma 10.161.3 (Tag 032G), using Lemma 10.36.11
(Tag 0307) (blueprint: lem-weil-pbc-localization-n2-domain).
-/

@[expose] public section

universe u v w

set_option autoImplicit false

/-- Localizing a domain away from zero preserves its fraction field and the N-1 and N-2
conditions. Source: Stacks Project, Algebra, Tag 032G, using Tag 0307
(blueprint: lem-weil-pbc-localization-n2-domain).

Proof: Since `0 ∉ S`, the localization embeds in `K` by `r/s ↦ r/s`, so it is a domain.
Every nonzero `r/s` is invertible in `K`, and every fraction of elements of `R` is a
fraction of their images in the localization. Thus `K` is still the fraction field.
For any extension field `L/K`, elements of `S` are already units in `L`, so localizing
`L` at `S` leaves it unchanged. Tag 0307
(`lem-weil-pbc-integral-closure-commutes-localization`) therefore identifies the integral
closure of the localized ring in `L` with the localization of `integralClosure R L`.
If `c₁, …, cₙ` generate that closure over `R`, their images generate its localization:
`c/s = ∑ᵢ (rᵢ/s)(cᵢ/1)` whenever `c = ∑ᵢ rᵢ cᵢ`. This uses
`def-weil-finitely-generated-module` and `def-weil-pbc-module-localization`.
Apply this first with `L = K` for N-1, then with every finite extension `L/K` for N-2,
as in `def-weil-pbc-japanese-domain`. No Noetherian or separability assumption is needed.
The existential algebra structure is pinned down by the displayed fraction formula;
it supplies the canonical map rather than assuming the conclusions as instances. -/
theorem localization_isN1_isN2 (R : Type u) (K : Type v)
    [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
    (S : Submonoid R) (hS : (0 : R) ∉ S) :
    ∃ (hD : IsDomain (Localization S)) (a : Algebra (Localization S) K),
      letI := hD
      letI := a
      ∃ (hF : IsFractionRing (Localization S) K),
        letI := hF
        IsScalarTower R (Localization S) K ∧
        Function.Injective (algebraMap (Localization S) K) ∧
        (∀ (r : R) (s : S),
          algebraMap (Localization S) K (IsLocalization.mk' (Localization S) r s) =
            algebraMap R K r / algebraMap R K (s : R)) ∧
        (IsN1 R K → IsN1 (Localization S) K) ∧
        (IsN2 R K → IsN2 (Localization S) K) := by
  sorry
