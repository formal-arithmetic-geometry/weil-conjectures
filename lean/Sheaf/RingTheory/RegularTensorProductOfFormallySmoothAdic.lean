/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.RingTheory.FormallySmoothAdic
public import Sheaf.RingTheory.GRing
import Sheaf.RingTheory.FormallySmoothAdicBaseChange
import Sheaf.RingTheory.PurelyInseparableBaseChangeLocalRing
import Sheaf.RingTheory.RegularLocalLocalization
import Sheaf.RingTheory.RegularLocalOfFormallySmoothAdic

/-! Intermediate regularity assertion for a purely inseparable base change.
(blueprint: lem-weil-pbc-fs-adic-field-geometrically-regular-regular-base-change) -/

@[expose] public section

open scoped TensorProduct

universe u v

namespace Algebra

/-- A finite purely inseparable base change of a formally smooth adic local algebra is regular.
The proof follows Steps 1--4 of Tag 07EL: base-change formal smoothness, upgrade the adic
topology from the extended maximal ideal to the unique maximal ideal, apply Tag 07EI, and
localize at primes. The tensor-factor swap is handled by `Algebra.TensorProduct.comm`.
(blueprint: lem-weil-pbc-fs-adic-field-geometrically-regular-regular-base-change) -/
theorem isRegularRing_tensorProduct_of_formallySmoothAdic
    (k : Type u) (C : Type v) (k' : Type (max u v))
    [Field k] [CommRing C] [Algebra k C] [IsNoetherianRing C] [IsLocalRing C]
    [Field k'] [Algebra k k'] [Module.Finite k k'] [IsPurelyInseparable k k']
    (h : FormallySmoothAdic k C (IsLocalRing.maximalIdeal C)) :
    IsRegularRing (k' ⊗[k] C) := by
  sorry

end Algebra
