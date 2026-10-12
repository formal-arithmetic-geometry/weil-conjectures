/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import WeilConjectures.AlgebraicGeometry.Curve
public import WeilConjectures.AlgebraicGeometry.Sites.Kummer

/-!
# The `p`-cohomological dimension of a smooth curve in characteristic `p`

Let `C` be a smooth separated connected curve over an algebraically closed field `k` of
characteristic `p > 0`. The Artin–Schreier sequence `0 → 𝐅_p → 𝔾ₐ → 𝔾ₐ → 0`, the comparison of
the étale and Zariski cohomology of `𝒪_C` and the Lang–Steinberg surjectivity of `F - 1` on
`H¹(C, 𝒪_C)` show that `Hᵠ(C, 𝐅_p) = 0` for `q > 1`. The étale sheaf `𝔾ₐ` and the comparison
are not available yet; the statement is recorded without proof.

## Main statements

- `AlgebraicGeometry.IsConnectedCurve.subsingleton_sheafH_constantZMod_of_charP`: the vanishing
  of `Hᵠ(C, 𝐅_p)` for `q > 1`.
-/

@[expose] public section

universe u

namespace AlgebraicGeometry

/-- **Artin–Schreier vanishing on a smooth curve.** Let `C` be a smooth separated connected
curve over an algebraically closed field `k` of characteristic `p > 0`. Then for the constant
sheaf `𝐅_p = ℤ/p` one has `Hᵠ(C, 𝐅_p) = 0` for `q > 1`.
(blueprint: `lem-sc-artin-schreier-dimension`) -/
theorem IsConnectedCurve.subsingleton_sheafH_constantZMod_of_charP {k : Type u} [Field k]
    [IsAlgClosed k] {C : Scheme.{u}} (f : C ⟶ Spec (.of k)) [IsConnectedCurve f] [Smooth f]
    (p : ℕ) [Fact p.Prime] [CharP k p] (q : ℕ) (hq : 1 < q) :
    Subsingleton (Sheaf.H (C.constantZMod p) q) :=
  sorry

end AlgebraicGeometry
