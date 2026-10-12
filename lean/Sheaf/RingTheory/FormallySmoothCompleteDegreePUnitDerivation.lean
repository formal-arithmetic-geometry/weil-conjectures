/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J1
-/
module

public import Sheaf.RingTheory.FormallySmoothAdic
public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.LocalRing.RingHom.Basic
public import Mathlib.RingTheory.AdicCompletion.Basic
import Sheaf.FieldTheory.PurelyInseparablePthRootTower
import Sheaf.RingTheory.Derivation.DetectNonPthPower
import Sheaf.RingTheory.FormallySmoothAdicBaseChange
import Sheaf.RingTheory.FiniteModuleComplete
import Sheaf.RingTheory.Derivation.FormallySmoothAdicExtension
import Sheaf.RingTheory.Derivation.CompletionAndLocalization
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.TensorProduct.MvPolynomial
import Mathlib.RingTheory.TensorProduct.Quotient

/-!
# A degree-p presentation with a unit derivation

Source: Stacks Project, More on Algebra, Proposition 07PM, last two paragraphs.
(blueprint: lem-weil-pbc-fs-complete-degree-p-unit-derivation)
-/

@[expose] public section

universe u v w

namespace Algebra

attribute [-instance] IntermediateField.module' in
/-- A degree-p purely inseparable base change of a formally smooth complete algebra
has a polynomial quotient presentation whose constant term admits a unit derivative.
Source: Stacks Project, More on Algebra, Proposition 07PM, final paragraph.
(blueprint: lem-weil-pbc-fs-complete-degree-p-unit-derivation)

Proof: Fields 09HI presents L/M as M[z]/(z^p-g), with g not a pth power in M.
Choose a finite K-basis of M. Each basis vector has a p-power in K. Multiplying
by a nonzero denominator in A puts that p-power in A, hence makes the rescaled
vector integral. Adjoining these integral vectors gives a finite A-subalgebra A'
of M with fraction field M. Write g = c/e in that fraction field and replace g
by e^p g = e^(p-1)c and its root beta by e beta. Thus f0 lies in A', is not a
pth power in M, and L = M[z]/(z^p-f0). By 07PH choose D0 : A' -> A' nonzero
on f0; A' is finite type over the complete Noetherian local A. Base change 07EG
makes C tensor_A A' formally smooth over A' for the extended maximal ideal of C.
It is finite over C, so 00MA makes it complete for that ideal. Lemma 07PL extends
D0 to this tensor product. Localize at the nonzero elements of A' and use tensor
associativity to identify the resulting ring with C tensor_A M. The localization
formula for derivations produces D, and its value on the image of f0 equals the
image of D0(f0). This is a unit, since D0(f0) is nonzero in M. Tensor the quotient
presentation of L with C tensor_A M; polynomial base change and quotient base
change identify the result with (C tensor_A M)[z]/(z^p-f0). Tensor commutativity
transports both the presentation and the derivation to M tensor_A C. This gives
the claimed f, D and ring isomorphism. Regularity is not needed in this construction.
If the generic fibre is zero, its unique element is a unit and all the displayed
rings are zero; the same construction applies. Prime p includes p = 2, the
coefficient field can be imperfect, and no positive number of variables is needed. -/
theorem exists_degree_p_presentation_unit_derivation_of_formallySmoothAdic
    (A : Type u) (C : Type v) (K : Type u) (L : Type w)
    [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A]
    [CommRing C] [IsLocalRing C] [IsNoetherianRing C]
    [Field K] [Field L] [Algebra A C] [Algebra A K] [Algebra K L] [Algebra A L]
    [IsScalarTower A K L] [IsFractionRing A K] [Module.Finite K L]
    [IsPurelyInseparable K L]
    [IsLocalHom (algebraMap A C)]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    [IsAdicComplete (IsLocalRing.maximalIdeal C) C]
    (p : ℕ) [Fact p.Prime] [CharP K p]
    (M : IntermediateField K L) [Algebra A M] [IsScalarTower A K M]
    (hdegree : Module.finrank M L = p)
    (hfs : FormallySmoothAdic A C (IsLocalRing.maximalIdeal C)) :
    ∃ (f : TensorProduct A M C) (D : Derivation ℤ (TensorProduct A M C)
      (TensorProduct A M C)), IsUnit (D f) ∧
      Nonempty ((Polynomial (TensorProduct A M C) ⧸
        Ideal.span {Polynomial.X ^ p - Polynomial.C f}) ≃+* TensorProduct A L C) := by sorry

end Algebra
