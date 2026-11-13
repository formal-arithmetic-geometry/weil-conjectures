/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import WeilConjectures.AlgebraicGeometry.Curve
public import WeilConjectures.AlgebraicGeometry.Picard.Group
import WeilConjectures.AlgebraicGeometry.Curve.PicProperNTorsionTorsion
import WeilConjectures.AlgebraicGeometry.Curve.PicProperNTorsionCoker
import WeilConjectures.AlgebraicGeometry.Curve.PicProperNTorsionDiv

/-!
# Torsion and divisibility of the Picard group of a proper curve

## Implementation details

The group law of `Pic(C)` is written multiplicatively (tensor product), so multiplication by `n`
is `powMonoidHom n`, `Pic(C)[n]` is its kernel, the cokernel is the quotient by its range, and
`ℤ/n` and `(ℤ/n)^(2g)` appear as `Multiplicative (ZMod n)` and
`Multiplicative (Fin (2g) → ZMod n)`.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/--
For a proper smooth connected curve over an algebraically closed field, with `n` prime to
its characteristic, the Picard group's `n`-torsion is `(ℤ/n)^(2g)`, its multiplication-by-`n`
cokernel is `ℤ/n`, and its degree-zero part is `n`-divisible. -/
theorem Scheme.Hom.pic_proper_ntorsion
    {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}}
    (f : C ⟶ Spec (.of k)) [IsConnectedCurve f] [Smooth f] [IsProper f]
    (n : ℕ) (_hn : (n : k) ≠ 0) :
    Nonempty ((powMonoidHom n : C.Pic →* C.Pic).ker ≃*
      Multiplicative (Fin (2 * f.genus) → ZMod n)) ∧
    Nonempty (C.Pic ⧸ (powMonoidHom n : C.Pic →* C.Pic).range ≃* Multiplicative (ZMod n)) ∧
    (∀ L : C.Pic, L ∈ f.picZero → ∃ M : C.Pic, M ∈ f.picZero ∧ M ^ n = L) := by
  have ht := Scheme.Hom.pic_proper_ntorsion_torsion f n _hn
  have hc := Scheme.Hom.pic_proper_ntorsion_coker f n _hn
  have hd := Scheme.Hom.pic_proper_ntorsion_div f n _hn
  exact ⟨ht, hc, hd⟩

end AlgebraicGeometry
