/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q50
-/
module

public import Sheaf.RingTheory.ExcellentRing
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Sheaf.RingTheory.JTwoResidueFieldCriterion
import WeilConjectures.RingTheory.IntGRing
import WeilConjectures.RingTheory.IntegerPrimeLocalizations
import Sheaf.AlgebraicGeometry.IsRegularScheme
import Sheaf.RingTheory.RegularRingUniversallyCatenary

/-!
# Excellence of the ring of integers

Source: Stacks Project, More on Algebra, Proposition 15.53.3, Tag 07QW,
proposition-ubiquity-excellent, item (3) (blueprint: lem-trf-integers-excellent).
-/

@[expose] public section

/- The proof follows Tag 07QW, item (3), with the J-2 verification expanded using
   Tags 07PJ and 07PC and universal catenarity supplied by Tags 00NM and 00NQ. -/

namespace Int

/-- The integer ring is excellent.

Source: Stacks Project, More on Algebra, Proposition 15.53.3, Tag 07QW,
proposition-ubiquity-excellent, item (3) (blueprint: lem-trf-integers-excellent).

Proof:
1. By `lem-weil-pbc-z-localizations-dvr`, the integers are Noetherian, their primes are
   `(0)` and `(p)` for rational primes `p`, the localization at `(0)` is `ℚ`, and the
   localization at `(p)` is a one-dimensional Noetherian local ring with principal
   maximal ideal. The field localization is regular by
   `lem-weil-pbc-field-regular-ring`; the other localization is regular local by the
   one-generator, dimension-one characterization in `def-weil-regular-scheme`. Thus
   every prime localization is regular local, so `ℤ` is regular.
2. The G-ring condition is exactly `lem-weil-pbc-z-g-ring`, giving the geometrically
   regular formal fibres required for excellence.
3. At `(0)`, the residue field is `ℚ`. A finite purely inseparable extension of `ℚ` is
   trivial by the characteristic-zero clause of
   `def-weil-pbc-finite-purely-inseparable-extension`. Taking the image of `ℤ` as the
   finite subalgebra gives a nonempty regular open in its spectrum.
4. At `(p)`, the residue field is `ℤ/pℤ = 𝔽_p`: Bezout identifies the quotient of the
   localization by its maximal ideal with this field. In a finite purely inseparable
   extension of `𝔽_p`, an element has a `p^n`-power in `𝔽_p`; the Frobenius power map
   is additive and fixes the prime field, so the element equals that power's value.
   The extension is therefore trivial. The image of `𝔽_p` is finite over `ℤ`, has
   fraction field itself, and has a nonempty regular spectrum by
   `lem-weil-pbc-field-regular-ring`.
5. Apply `lem-exc-j2-residue-field-criterion` to these witnesses. Together with
   Noetherianity, it gives openness of the regular locus in every finite type
   `ℤ`-algebra, which is J-2.
6. Apply `lem-trf-regular-ring-universally-catenary` to the Noetherian regular ring
   `ℤ` to obtain universal catenarity.
7. By `def-exc-excellent-ring`, the Noetherian, G-ring and J-2 properties make `ℤ`
   quasi-excellent, and universal catenarity then makes it excellent.
-/
theorem isExcellent : IsExcellent ℤ := by
  sorry

end Int

end
