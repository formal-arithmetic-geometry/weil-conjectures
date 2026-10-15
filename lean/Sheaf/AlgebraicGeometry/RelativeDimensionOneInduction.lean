/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NN
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Sheaf.AlgebraicGeometry.CumulativeUniversalBaseChangeProperty
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Limits
import Sheaf.AlgebraicGeometry.UniversalBaseChangeFailureDatum
import Sheaf.AlgebraicGeometry.UniversalCurveTestVanishing

/-!
# The induction step in relative dimension one

Source: blueprint, sec-smooth-base-change/sk-lem-induction,
node sbc-lem-rel-dim-one-induction; Stacks Project, Tag 0EYU, second proof
(blueprint: sbc-lem-rel-dim-one-induction).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Etale

/-- An affine smooth relative curve with affine source satisfies universal base change
in degree `q` if it does in all nonnegative degrees through `q - 1`; consequently it
satisfies the cumulative universal property through `q`.
Source: blueprint, sec-smooth-base-change/sk-lem-induction,
node sbc-lem-rel-dim-one-induction; Stacks Project, Tag 0EYU, second proof
(blueprint: sbc-lem-rel-dim-one-induction).

Proof plan: Suppose universal base change in degree `q` fails. By
`sbc-lem-bc-universal-test`, the cumulative universal lower-degree assumption gives two
Cartesian squares over an affine integral normal base with algebraically closed function
field `L`, and a dominant geometric generic map from `Spec K`, together with a divisor
`d` of `n` whose constant cyclic sheaf has nonzero degree-`q` higher direct image along
the horizontal map. Dominance extends the injection from the normal domain to `K` to
an inclusion of its fraction field `L` into `K`. By
`lem-weil-pbc-affine-morphism-permanence` and
`lem-sbc-smooth-relative-dimension-permanence`, the base-changed curve remains affine
smooth of relative dimension one, with affine source. Pulling back the inverse of `n`
shows it is a unit on this base; writing `n = d * a` shows that `d` is a unit there too.
Now `sbc-thm-universal-test-vanishing` makes that higher direct image zero since `q ≥ 1`,
a contradiction. Finally, a nonnegative degree at most `q` either equals `q` or is at
most `q - 1`, giving the cumulative conclusion. -/
theorem universalBaseChangeProperty_relativeDimensionOne_induction
    {X S : Scheme.{u}} (f : X ⟶ S) [IsAffineHom f]
    [SmoothOfRelativeDimension 1 f] [IsAffine X]
    (n : ℕ) (hn : 0 < n) (hinv : IsUnit (n : Γ(S, ⊤)))
    (q : ℕ) (hq : 1 ≤ q)
    (hprev : CumulativeUniversalBaseChangeProperty f n hn hinv (q - 1)) :
    UniversalBaseChangeProperty (ULift.{u + 1} (ZMod n)) f (q : ℤ) ∧
      CumulativeUniversalBaseChangeProperty f n hn hinv q := by
  sorry

end AlgebraicGeometry.Etale
