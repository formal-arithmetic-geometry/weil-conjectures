/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R3
-/
module

public import Sheaf.AlgebraicGeometry.SectionRingVeroneseFractionMap
public import Sheaf.AlgebraicGeometry.SectionFractionPresentation

/-! # The kernel of the explicit map on Veronese numerator sections

Source: Stacks Project, Properties, equation module-invert-s (Tag 0B5L),
Lemma 01PW(2), and the Veronese localization in the proof of Lemma 01Q1.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory DirectSum

namespace AlgebraicGeometry.Scheme.Modules

/-- The transition relations are exactly the kernel of the explicitly constructed fraction map.
Source: Stacks Project, Properties, equation module-invert-s (Tag 0B5L),
Lemma 01PW(2), and the Veronese localization in the proof of Lemma 01Q1.
(blueprint: lem-sc-section-ring-veronese-fraction-kernel)

Proof: write `T_n` for `sectionRingVeroneseNumeratorIso` on global sections and `ι_n`
for the direct-sum injection in the numerator presentation. The inverse identification
sends a section `t` to the homogeneous ring element `a_n(t) = of_(nd)(T_n⁻¹(t))`.
Tensor-power coherence gives
`a_(n+b)(mulTensorPowSection(s) n b t) = a_n(t) * s^b`.
To check this equality, restrict to an open set trivializing the invertible module `L`.
In the chosen generator, `T_n` identifies the generator to its `nd`-th tensor power,
the section-ring product multiplies the coefficient functions, and the transition
multiplies the coefficient by the `b`-th power of the coefficient of `s`. Both sides
are therefore the same function times the same generator. Equality of sections glues
from these opens. The same calculation shows that scalar multiplication by a global
function corresponds to multiplication by its degree-zero image in the section ring.

Consequently every transition difference
`ι_n(t) - ι_(n+b)(mulTensorPowSection(s) n b t)` maps to zero: its two images are
`a_n(t)/s^n` and `(a_n(t)*s^b)/s^(n+b)`. Every global-function scalar multiple also
maps to zero by the scalar calculation. Additivity now proves that the entire submodule
span of the transition differences lies in the additive kernel.

Conversely take a finite sum `z = sum_n ι_n(t_n)` in the kernel, with finite support `I`.
Choose `N` at least every index in `I`. Subtract, for each index `n`, the defining relation
with `b = N-n`. Modulo the relation submodule, `z` is thus the single generator `ι_N(t)`,
where `t` is the sum of the transitioned numerators. Its image is `a_N(t)/s^N = 0`.
The localization equality criterion supplies a natural number `k` with
`s^k * a_N(t) = 0`. By the coherence equality and injectivity of the direct-sum injection
and of `T_(N+k)⁻¹`, the transition of `t` from degree `N` to degree `N+k` is zero.
The relation with indices `N,k` then says that `ι_N(t)` belongs to the relation submodule.
Adding back the previously subtracted relations shows that `z` belongs to it as well.
An empty support gives `z=0` immediately. This proves the reverse kernel inclusion.

The argument uses powers and finite supports only: `d=0` is allowed, and if `s` is
zero or nilpotent the localization criterion still supplies a killing power; the same
transition makes every numerator class zero. No reducedness or nonzero-divisor
hypothesis is used. This is a kernel computation for a fixed explicit map, not an
existence statement about an unspecified equivalence.
-/
theorem sectionRingVeroneseFractionMap_kernel
    (X : Scheme.{u}) (L : X.Modules) [L.IsInvertible]
    (d : ℕ) (s : sectionRingGrade L d) :
    (sectionFractionRelations (L.tensorPow d) (𝟙_ X.Modules) (s.val d)).toAddSubgroup =
      (sectionRingVeroneseFractionMap X L d s).ker := by sorry

end AlgebraicGeometry.Scheme.Modules
