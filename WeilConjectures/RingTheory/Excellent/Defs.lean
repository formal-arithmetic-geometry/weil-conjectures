/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.RegularLocalRing.Defs

/-!
# G-rings, analytically unramified rings and Japanese rings

This file records several classical notions from the theory of excellent rings.

## Main definitions

- `Algebra.IsGeometricallyRegular k A`: a Noetherian `k`-algebra which stays regular after every
  finite purely inseparable base field extension (Stacks 0382).
- `Algebra.IsRegularMap R Λ`: a flat ring map with Noetherian geometrically regular fibres
  (Stacks 07BZ).
- `IsGRing R`: a Noetherian ring whose local rings have regular formal fibres (Stacks 07GH).
- `IsAnalyticallyUnramified R`: a local ring whose completion is reduced.
- `IsN1 R`, `IsN2 R`: N-1 and N-2 (Japanese) domains (Stacks 032F).
-/

@[expose] public section

universe u v

open IsLocalRing
open scoped TensorProduct

namespace Algebra

/-- A Noetherian `k`-algebra `A` is *geometrically regular over `k`* if for every finite purely
inseparable field extension `k'/k` the ring `k' ⊗[k] A` is regular.
(blueprint: `def-weil-pbc-g-ring`) -/
def IsGeometricallyRegular (k : Type u) [Field k] (A : Type v) [CommRing A] [Algebra k A] :
    Prop :=
  IsNoetherianRing A ∧ ∀ (k' : Type u) [Field k'] [Algebra k k'] [Module.Finite k k']
    [IsPurelyInseparable k k'], IsRegularRing (k' ⊗[k] A)

/-- A ring map `R → Λ` is *regular* if it is flat and every fibre ring `κ(𝔭) ⊗[R] Λ` is
Noetherian and geometrically regular over `κ(𝔭)` (Stacks 07BZ).
(blueprint: `def-weil-pbc-g-ring`) -/
def IsRegularMap (R : Type u) [CommRing R] (Λ : Type v) [CommRing Λ] [Algebra R Λ] : Prop :=
  Module.Flat R Λ ∧ ∀ (p : Ideal R) [p.IsPrime],
    IsNoetherianRing (p.Fiber Λ) ∧ IsGeometricallyRegular p.ResidueField (p.Fiber Λ)

end Algebra

/-- A commutative ring `R` is a *G-ring* if it is Noetherian and for every prime `𝔭` the map
`R_𝔭 → (R_𝔭)^∧` to the `𝔭R_𝔭`-adic completion is regular (Stacks 07GH).
(blueprint: `def-weil-pbc-g-ring`) -/
def IsGRing (R : Type u) [CommRing R] : Prop :=
  IsNoetherianRing R ∧ ∀ (p : Ideal R) [p.IsPrime],
    Algebra.IsRegularMap (Localization.AtPrime p)
      (AdicCompletion (maximalIdeal (Localization.AtPrime p)) (Localization.AtPrime p))

/-- A local ring `A` is *analytically unramified* if its `𝔪`-adic completion is reduced.
(blueprint: `def-weil-pbc-analytically-unramified`) -/
def IsAnalyticallyUnramified (A : Type u) [CommRing A] [IsLocalRing A] : Prop :=
  IsReduced (AdicCompletion (maximalIdeal A) A)

/-- A prime `𝔭` of a local ring `A` is *analytically unramified* if the local ring `A/𝔭` is, i.e.
the `(𝔪/𝔭)`-adic completion of `A/𝔭` is reduced.
(blueprint: `def-weil-pbc-analytically-unramified`) -/
def Ideal.IsAnalyticallyUnramified {A : Type u} [CommRing A] [IsLocalRing A] (p : Ideal A) :
    Prop :=
  IsReduced (AdicCompletion ((maximalIdeal A).map (Ideal.Quotient.mk p)) (A ⧸ p))

/-- A domain `R` is *N-1* if its integral closure in its fraction field is a finite `R`-module.
(blueprint: `def-weil-pbc-japanese-domain`) -/
def IsN1 (R : Type u) [CommRing R] [IsDomain R] : Prop :=
  Module.Finite R (integralClosure R (FractionRing R))

/-- A domain `R` is *N-2* (or *Japanese*) if for every finite extension `L` of its fraction field
`K` the integral closure of `R` in `L` is a finite `R`-module.
(blueprint: `def-weil-pbc-japanese-domain`) -/
def IsN2 (R : Type u) [CommRing R] [IsDomain R] : Prop :=
  ∀ (L : Type u) [Field L] [Algebra (FractionRing R) L] [FiniteDimensional (FractionRing R) L],
    letI : Algebra R L := ((algebraMap (FractionRing R) L).comp
      (algebraMap R (FractionRing R))).toAlgebra
    Module.Finite R (integralClosure R L)
