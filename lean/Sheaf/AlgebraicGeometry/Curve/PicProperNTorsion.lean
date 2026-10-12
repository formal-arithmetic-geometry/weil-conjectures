/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J1, reviewer R-pnt1212
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import WeilConjectures.AlgebraicGeometry.Curve
public import WeilConjectures.AlgebraicGeometry.Picard.Group
import Sheaf.AlgebraicGeometry.Curve.PicardDecomposition
import Sheaf.AlgebraicGeometry.Curve.ProperProjective
import Sheaf.AlgebraicGeometry.SmoothProjectiveCurve
import Sheaf.AlgebraicGeometry.Variety
import WeilConjectures.AlgebraicGeometry.AbelianVariety.Final
import WeilConjectures.AlgebraicGeometry.AbelianVariety.Jacobian
import WeilConjectures.AlgebraicGeometry.Curve.RiemannRoch
import WeilConjectures.AlgebraicGeometry.DensePoints
import WeilConjectures.AlgebraicGeometry.GroupScheme.Defs
import WeilConjectures.AlgebraicGeometry.Picard.Jacobian
import WeilConjectures.AlgebraicGeometry.Regular

/-!
# Torsion and divisibility of the Picard group of a proper curve

Source: Weil-conjectures blueprint, sec-curve-estimates/sk-thm-curveestimate,
lem-sc-pic-proper-ntorsion (blueprint: lem-sc-pic-proper-ntorsion).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- Source: Weil-conjectures blueprint, sec-curve-estimates/sk-thm-curveestimate,
lem-sc-pic-proper-ntorsion (blueprint: lem-sc-pic-proper-ntorsion).
For a proper smooth connected curve over an algebraically closed field, with `n` prime to
its characteristic, the Picard group's `n`-torsion is `(ℤ/n)^(2g)`, its multiplication-by-`n`
cokernel is `ℤ/n`, and its degree-zero part is `n`-divisible. The group law of `Pic(C)` is
written multiplicatively (tensor product), so multiplication by `n` is `powMonoidHom n`,
`Pic(C)[n]` is its kernel, the cokernel is the quotient by its range, and `ℤ/n` and
`(ℤ/n)^(2g)` appear as `Multiplicative (ZMod n)` and `Multiplicative (Fin (2g) → ZMod n)`.

Proof, following the node's four steps:
1. By def-sc-curves the dimension is one, hence lem-sc-proper-dim-one-projective makes the
curve projective. By lem-sc-smooth-regular its local rings are domains. Finite type over a
field gives Noetherianity by lem-weil-pbc-finite-type-over-noetherian. Distinct irreducible
components are disjoint and the finitely many components are open, so connectedness gives
integrality. Thus def-pc-curve and def-pc-smooth-projective-curve apply. A rational point
exists by lem-pc-rational-points-dense; prop-pc-xk-integral gives geometric integrality.
Now thm-sc-jacobian-representability identifies def-sc-pic0 with the rational points of the
Jacobian, an abelian variety of dimension `g`; lem-pc-genus-agrees-sc identifies its genus
with def-sc-genus.
2. By lem-sc-pic-proper-decomposition the degree sequence splits as `ℤ ⊕ Pic⁰(C)`.
Clause (d) of thm-av-final makes the second factor `n`-divisible. The hypothesis on `n`
implies `n ≥ 1`; the case `n = 1` is immediate.
3. By def-sc-mult-n the torsion of the Jacobian's rational points is the rational points of
its torsion scheme. Clause (c) of thm-av-final identifies this with `(ℤ/n)^(2g)`.
Multiplication is componentwise in the decomposition and `ℤ[n] = 0` for positive `n`, so
this also identifies the Picard group's torsion.
4. The multiplication image in the decomposition is `nℤ ⊕ n Pic⁰(C)`. Divisibility makes
the second summand all of `Pic⁰(C)`, so the cokernel is `ℤ/n`, including `n = 1`. -/
theorem Scheme.Hom.pic_proper_ntorsion
    {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}}
    (f : C ⟶ Spec (.of k)) [IsConnectedCurve f] [Smooth f] [IsProper f]
    (n : ℕ) (_hn : (n : k) ≠ 0) :
    Nonempty ((powMonoidHom n : C.Pic →* C.Pic).ker ≃*
      Multiplicative (Fin (2 * f.genus) → ZMod n)) ∧
    Nonempty (C.Pic ⧸ (powMonoidHom n : C.Pic →* C.Pic).range ≃* Multiplicative (ZMod n)) ∧
    (∀ L : C.Pic, L ∈ f.picZero → ∃ M : C.Pic, M ∈ f.picZero ∧ M ^ n = L) :=
  sorry

end AlgebraicGeometry
