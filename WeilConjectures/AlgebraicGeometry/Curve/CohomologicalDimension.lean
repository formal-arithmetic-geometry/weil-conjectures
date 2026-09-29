/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import WeilConjectures.AlgebraicGeometry.Curve
public import WeilConjectures.AlgebraicGeometry.Sites.Gm

/-!
# The étale cohomological dimension of a curve

The étale cohomological dimension of a curve over an algebraically closed field is at most two,
and at most one if the curve is affine: `H^q(C_ét, F) = 0` for every torsion abelian sheaf `F`
(`CategoryTheory.Sheaf.IsTorsion`) and `q ≥ 3`, resp. `q ≥ 2`.

Neither statement needs smoothness, connectedness, or `char k` to be prime to the torsion of
`F`.

## Main statements

- `AlgebraicGeometry.IsCurve.subsingleton_sheafH_of_three_le`: `H^q(C, F) = 0` for `q ≥ 3`.
- `AlgebraicGeometry.IsCurve.subsingleton_sheafH_of_two_le_of_isAffine`: `H^q(C, F) = 0` for
  `q ≥ 2` on an affine curve.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.IsCurve

variable {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}}

/-- **Vanishing in high degrees.** Let `C` be a curve over an algebraically closed field `k`.
Then `H^q(C_ét, F) = 0` for `q ≥ 3` and every torsion abelian sheaf `F` on `C_ét`: the étale
cohomological dimension of a curve over an algebraically closed field is at most two. The
sharper bound for affine `C` is
`AlgebraicGeometry.IsCurve.subsingleton_sheafH_of_two_le_of_isAffine`.
(blueprint: `sk-prop-cd`) -/
@[stacks 03SC "(1)"]
theorem subsingleton_sheafH_of_three_le (f : C ⟶ Spec (.of k)) [IsCurve f]
    (F : Sheaf C.smallEtaleTopology AddCommGrpCat.{u + 1}) (hF : F.IsTorsion) (q : ℕ)
    (hq : 3 ≤ q) : Subsingleton (Sheaf.H F q) :=
  -- Proof sketch: after reducing to a smooth integral curve, the cohomology of `F` is compared
  -- with that of its pushforward from the generic point. The function field `k(C)` has
  -- cohomological dimension at most one, because every finite separable extension `L` of
  -- `k(C)` is `C₁` by Tsen's theorem `IsQuasiAlgClosed.of_trdeg_le_one`, hence has
  -- `Br(L) = 0` by `IsQuasiAlgClosed.subsingleton_cohomologicalBrauerGroup`. The `p`-primary
  -- part in characteristic `p` goes through the Artin–Schreier sequence.
  sorry

/-- **Cohomological dimension of an affine curve.** Let `C` be an affine curve over an
algebraically closed field `k`. Then `H^q(C_ét, F) = 0` for `q ≥ 2` and every torsion abelian
sheaf `F` on `C_ét`: the étale cohomological dimension of an affine curve over an
algebraically closed field is at most one.
(blueprint: `sk-prop-cd-affine`) -/
@[stacks 03SC "(2)"]
theorem subsingleton_sheafH_of_two_le_of_isAffine (f : C ⟶ Spec (.of k)) [IsCurve f]
    [IsAffine C] (F : Sheaf C.smallEtaleTopology AddCommGrpCat.{u + 1}) (hF : F.IsTorsion)
    (q : ℕ) (hq : 2 ≤ q) : Subsingleton (Sheaf.H F q) :=
  -- Proof sketch: degrees `q ≥ 3` are `subsingleton_sheafH_of_three_le`. In degree two one
  -- reduces to `F = ℤ/n` on a smooth integral affine curve. For `n` prime to `char k` the
  -- Kummer sequence identifies `H²(C, μₙ)` with `Pic(C)/n`, which vanishes because `Pic(C)`
  -- is `n`-divisible; the `p`-primary part is the Artin–Schreier sequence.
  sorry

end AlgebraicGeometry.IsCurve
