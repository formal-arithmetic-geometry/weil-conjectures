/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralHom.Reduction.IntegralHomReductionModels
public import WeilConjectures.SixFunctors.IntegralHom.Two.TwoTermFreeHomTensorCoordinateMap

/-! # Components of the two-term free Hom--tensor exchange

We show that a chain map given by the signed evaluation formula is a degreewise isomorphism
when the coefficient complex has precisely two free rank-one terms.

## References

* [Stacks, Tag 0A8X]
* [Stacks, Tag 08J7]
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe t u
open CategoryTheory CategoryTheory.Limits Opposite

namespace WeilConjectures.IntegralHom

variable (Y : AlgebraicGeometry.Scheme.{t})
  (R : Sheaf (AlgebraicGeometry.Scheme.ProEt.topology Y) CommRingCat.{max u (t + 1)})

/-- A chain map with the signed evaluation formula is invertible in every degree
when its coefficient complex has precisely two free rank-one terms.
Neither Hom input is bounded, and no condition is imposed on the differential of Q. -/
theorem twoTermFreeHomTensor_component_isIso
    (P I Q : CochainComplex (Modules.{t, u} Y R) ℤ)
    (hzero : ∀ k : ℤ, k ≠ -1 → k ≠ 0 → IsZero (Q.X k))
    (eNeg : Q.X (-1) ≅ (show Modules.{t, u} Y R from SheafOfModules.unit
      ((sheafCompose (AlgebraicGeometry.Scheme.ProEt.topology Y)
        (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj R)))
    (eZero : Q.X 0 ≅ (show Modules.{t, u} Y R from SheafOfModules.unit
      ((sheafCompose (AlgebraicGeometry.Scheme.ProEt.topology Y)
        (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj R)))
    (f : ((totalTensor Y R).obj
        (homComplex.{t + 1, t, max u (t + 1), max u (t + 1)} (R := R) P I)).obj Q ⟶
      homComplex.{t + 1, t, max u (t + 1), max u (t + 1)} (R := R) P
        (((totalTensor Y R).obj I).obj Q))
    (hf : IsSignedHomTensor Y R P I Q f) (j : ℤ) : IsIso (f.f j) := by
  obtain ⟨g, hg, hformula⟩ :=
    twoTermFreeHomTensor_coordinate_exists Y R P I Q hzero eNeg eZero j
  have hfg := twoTermFreeHomTensor_coordinate_unique Y R P I Q hzero eNeg eZero f g hf j hformula
  rw [hfg]
  exact hg

end WeilConjectures.IntegralHom
