/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
module

public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.Regular.RegularSequence
public import Mathlib.RingTheory.RingHom.Flat
import Sheaf.Paper.FlatLocalCriterionNonzerodivisor
import Sheaf.RingTheory.RegularLocalGeneratorsRegularSequence

/-!
# Flatness over a regular local ring

Source: Stacks Project, Algebra, Lemma 10.128.2 (Tag 07DY)
(blueprint: lem-weil-pbc-flat-over-regular).
-/

@[expose] public section

universe u v

namespace RingHom

/-- A local homomorphism of Noetherian local rings is flat if a regular system of parameters
of the regular local source maps to a regular sequence in the target.
Source: Stacks Project, Algebra, Lemma 10.128.2 (Tag 07DY)
(blueprint: lem-weil-pbc-flat-over-regular).

Proof: Let `R_i` and `S_i` be the quotients by the first `i` parameters and their images.
The map induces local homomorphisms `R_i → S_i` of Noetherian local rings
(def-weil-pbc-noetherian-ring). These quotients are nonzero: the final quotient of `S` is
nonzero by regularity (def-weil-pbc-regular-sequence), and all earlier quotients surject onto
it; the source quotients map to them. Their maximal ideals are the images of the original
maximal ideals, and the successive quotients are by the next parameter.
At the final index, `R_d = R / m_R` is a field, so `S_d` is flat over `R_d`
(lem-weil-pbc-module-over-field-flat). Regularity of `R` and generation of its maximal ideal
by `d = dim R` parameters imply that these parameters form a regular sequence in `R`
(lem-weil-pbc-regular-local-generators-regular-sequence, def-weil-regular-scheme).
Thus each next parameter is a nonzerodivisor both on the source quotient and on the target
quotient, the latter by the assumed regular sequence (def-weil-pbc-regular-sequence).
Apply the local criterion modulo a nonzerodivisor to `R_{i-1} → S_{i-1}`, with the finite
`S_{i-1}`-module `S_{i-1}` and this parameter in the maximal ideal
(lem-weil-pbc-flat-local-criterion-nonzerodivisor). Flatness of `S_i` over `R_i` gives
flatness of `S_{i-1}` over `R_{i-1}`. Descending induction ends at `S` flat over `R`,
i.e. the given map is flat (def-weil-pbc-flat-ring-map). If `d = 0`, the field base case
already gives the conclusion. -/
theorem flat_of_regular_parameters {R : Type u} {S : Type v}
    [CommRing R] [CommRing S] [IsRegularLocalRing R] [IsLocalRing S] [IsNoetherianRing S]
    (φ : R →+* S) [IsLocalHom φ] (d : ℕ) (x : List R)
    (hd : ringKrullDim R = (d : WithBot ℕ∞)) (hx : x.length = d)
    (hgen : Ideal.ofList x = IsLocalRing.maximalIdeal R)
    (hreg : RingTheory.Sequence.IsRegular S (x.map φ)) : φ.Flat := by
  sorry

end RingHom
