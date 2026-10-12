/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G3
-/
module

public import Mathlib.RingTheory.LocalRing.RingHom.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Sheaf.RingTheory.FormallySmoothAdic
public import Sheaf.RingTheory.GRing
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Localization.Submodule
import Sheaf.AlgebraicGeometry.DegreePExtensionRegular
import Sheaf.FieldTheory.PurelyInseparablePthRootTower
import Sheaf.RingTheory.CompleteLocalDomainFiniteOverRegular
import Sheaf.RingTheory.Derivation.CompletionAndLocalization
import Sheaf.RingTheory.Derivation.DetectNonPthPower
import Sheaf.RingTheory.Derivation.FormallySmoothAdicExtension
import Sheaf.RingTheory.FiniteModuleComplete
import Sheaf.RingTheory.FormallySmoothAdicBaseChange
import Sheaf.RingTheory.FormallySmoothAdicClosedFiber
import Sheaf.RingTheory.FsAdicLiftOverFiniteCoefficientMap
import Sheaf.RingTheory.GeometricallyRegularFieldExtension
import Sheaf.RingTheory.LocalizationOfRegularRing
import Sheaf.RingTheory.RegularLocalOfFlatWithRegularClosedFiber

/-!
# Geometric regularity of the generic fibre of a complete local domain

Source: Stacks Project, More on Algebra, Proposition 07PM, proof of (4) to (1).
(blueprint: lem-weil-pbc-formally-smooth-complete-local-generic-fiber)
-/

@[expose] public section

universe u v

namespace Algebra

/-- The generic fibre of an adically formally smooth map out of a complete local domain
is geometrically regular.
Source: Stacks Project, More on Algebra, Proposition 07PM, proof of (4) to (1),
after replacing the base by its quotient at a prime.
(blueprint: lem-weil-pbc-formally-smooth-complete-local-generic-fiber)

Proof: Choose a complete regular coefficient subring A₀ of A, finite with the same residue
field, by Algebra 032D. Lift the formally smooth closed fibre to a formally smooth complete
local A₀-algebra C using Remark 07NS, obtaining B = C tensor over A₀ with A. The fraction
field K of A is finite over K₀ = Frac(A₀), so tensor associativity and Algebra 0381 reduce
geometric regularity to C tensor over A₀ with K₀. Flatness and regularity of the closed
fibre (07NQ), regular local ascent (031E), and localization make this ring regular.
In characteristic zero this suffices. In characteristic p, induct on the degree of a finite
purely inseparable extension L/K₀. Choose its last degree-p step M[z]/(z^p-f) by Fields
09HI. A finite A₀-subalgebra A' of M with fraction field M is obtained by multiplying a
basis by denominators so the basis elements become integral. If f = c/e, replace f by
e^p f = e^(p-1)c and its root by e times that root, so f lies in A'. Lemma 07PH gives a
derivation of A' nonzero on f. Base change 07EG preserves formal smoothness; finite-module
completeness 00MA and 07PL extend this derivation to C tensor A', and localization extends
it to C tensor M. Its value on f is a unit because its nonzero value in A' becomes
invertible in M. Lemma 07PG proves regularity of the degree-p extension. Tensor
associativity identifies this extension with C tensor L, completing the induction.
Geometric regularity over K₀ now gives it over the finite extension K, using 0381 for
all finite field extensions of K. Noetherianity follows from localization of B.
-/
theorem isGeometricallyRegular_genericFiber_of_formallySmoothAdic
    {A : Type u} {B : Type v} {K : Type u}
    [CommRing A] [CommRing B] [Field K] [Algebra A B] [Algebra A K]
    [IsDomain A] [IsNoetherianRing A] [IsNoetherianRing B]
    [IsLocalRing A] [IsLocalRing B] [IsLocalHom (algebraMap A B)]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    [IsAdicComplete (IsLocalRing.maximalIdeal B) B] [IsFractionRing A K]
    (hfs : FormallySmoothAdic A B (IsLocalRing.maximalIdeal B)) :
    IsGeometricallyRegular K (TensorProduct A K B) := by sorry

end Algebra
