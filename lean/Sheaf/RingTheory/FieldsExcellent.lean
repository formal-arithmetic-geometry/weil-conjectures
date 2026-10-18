/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q40
-/
module

public import Sheaf.RingTheory.ExcellentRing
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.RingTheory.RingHom.Flat
import Sheaf.RingTheory.GRing
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.RingTheory.FiniteType
import Sheaf.RingTheory.PolynomialRingMaximalChainHeightDifference
import Sheaf.RingTheory.JTwoResidueFieldCriterion

/-!
# Excellence of fields

Source: Stacks Project, More on Algebra, Proposition 07QW, clause (1)
(blueprint: lem-exc-fields-excellent).
-/

@[expose] public section

set_option autoImplicit false

universe u

/-- Every field, regarded as a commutative ring, is excellent.

Source: Stacks Project, More on Algebra, Tags 07PX, 07PJ, 07QT, and 07QW, clause (1);
Algebra, Tag 00OR (blueprint: lem-exc-fields-excellent).

Proof (the five steps of the node):
1. By `lem-weil-pbc-field-regular-ring`, `k` is Noetherian and regular, its only prime
   is zero, and its localization there is `k`. By `def-weil-pbc-adic-completion`, its
   zero-adic completion is also `k`: all quotients in positive degree are `k`, all
   transition maps are identities, and the degree-zero coordinate is uniquely determined.
   The canonical completion map is therefore the identity.
2. The identity is flat (`def-weil-pbc-flat-ring-map`): multiplication and tensoring
   with one identify tensoring with `k` with the identity on modules. Its unique fibre
   is `k`. For every finite purely inseparable extension `k' / k`, multiplication and
   tensoring with one identify the base-changed fibre with the field `k'`, which is
   Noetherian and regular by `lem-weil-pbc-field-regular-ring`. Thus the completion map
   is regular and `k` is a G-ring by `def-weil-pbc-g-ring`, without a perfectness assumption.
3. Apply `lem-exc-j2-residue-field-criterion` to `k`. For every finite purely inseparable
   residue-field extension `L / k`, take the subalgebra `B = L`. It is module-finite
   by `def-weil-pbc-finite-purely-inseparable-extension`; its fractions exhaust `L`
   since each element is its own numerator over one. Its whole spectrum is a nonempty
   regular open, by `lem-weil-pbc-field-regular-ring`. The criterion gives J-2.
4. Present any finite type `k`-algebra `A` as a quotient of a polynomial ring in `n`
   variables (`def-weil-pbc-finite-type-algebra`). Pullback identifies its prime ideals
   with the primes containing the kernel and preserves strictness and saturation of
   chains. By `lem-weil-pbc-polynomial-ring-maximal-chain-height-difference`, their
   lengths are bounded by `n`, and saturated chains between fixed endpoints have the
   difference of the pulled-back prime heights as length. Thus `A` is catenary; for
   the zero algebra there are no prime pairs. This gives universal catenarity of `k`.
5. Combine Noetherianity, the G-ring condition, J-2, and universal catenarity using
   `def-exc-excellent-ring`.
-/
theorem isExcellent_of_field (k : Type u) [Field k] : IsExcellent k := by
  sorry
