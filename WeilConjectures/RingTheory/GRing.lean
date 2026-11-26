/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import Mathlib.RingTheory.AdicCompletion.Algebra

/-!
# G-rings and regular ring maps

We define geometric regularity of algebras over a field, regular ring maps, and G-rings.

## Main definitions

* `Algebra.IsGeometricallyRegular`: geometric regularity over a field.
* `RingHom.IsRegular`: flat maps with geometrically regular fibres.
* `IsGRing`: Noetherian rings with regular local completion maps.

## Implementation details

Geometric regularity is defined through finite purely inseparable extensions, using the
equivalent condition (2) of Stacks 0381.

## References

* [Stacks, Tags 0382, 0381] (condition (2))
* [Stacks, Tags 07BZ, 07GH]
-/

@[expose] public section

universe u v

namespace Algebra

/-- A Noetherian algebra over a field is geometrically regular when base change to every finite
purely inseparable field extension is a regular ring. -/
def IsGeometricallyRegular (k : Type u) (A : Type v)
    [Field k] [CommRing A] [Algebra k A] : Prop :=
  IsNoetherianRing A ∧
    ∀ (k' : Type (max u v)) [Field k'] [Algebra k k'] [Module.Finite k k']
      [IsPurelyInseparable k k'], IsRegularRing (TensorProduct k k' A)

end Algebra

namespace RingHom

/-- A regular ring map is flat and has Noetherian, geometrically regular fibres at every prime.
The Noetherian condition is part of `Algebra.IsGeometricallyRegular`. -/
def IsRegular {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (f : R →+* S) : Prop :=
  letI : Algebra R S := f.toAlgebra
  f.Flat ∧ ∀ (p : Ideal R) [p.IsPrime],
    Algebra.IsGeometricallyRegular p.ResidueField (p.Fiber S)

end RingHom

/-- A G-ring is a Noetherian ring whose map from every prime localization to its adic
completion at the maximal ideal is regular. -/
def IsGRing (R : Type u) [CommRing R] : Prop :=
  IsNoetherianRing R ∧ ∀ (p : Ideal R) [p.IsPrime],
    RingHom.IsRegular
      (algebraMap (Localization.AtPrime p)
        (AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime p))
          (Localization.AtPrime p)))
