/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q14
-/
module

public import Sheaf.Paper.WeilComplexTraceFunction
public import Sheaf.Paper.FourierSetting
public import WeilConjectures.FourierTransform.Classical
public import WeilConjectures.Mathlib.NumberTheory.LegendreSymbol.AddCharacter

/-!
# Trace functions and the classical finite-field Fourier transform

Source: Weil blueprint main-20261015, sec-fourier-transform/sk-def-trace/_section.md
(blueprint: sk-def-trace).

The trace clause is `WeilConjectures.weilTraceFunction` from def-fd-trace-function:
the alternating local trace on all cohomology stalks of a common-stage Weil complex.
The classical transform below specializes the existing `FiniteField.fourierTransform`
to the actual subfield F_(q^n) of the fixed algebraic closure. Its induced character
is psi_n = psi composed with the field trace, as in `AddChar.compTrace`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
namespace WeilConjectures

/-- The canonical finite field F_(q^n), equipped with an enumeration for finite sums.
The cardinality and inclusion are the existing finite-field datum, not new choices
of a field or of an embedding.
Source: blueprint sk-def-trace and its finite-field setting (blueprint: sk-def-trace). -/
@[instance_reducible]
def fourierTraceExtensionFintype (D : FiniteFieldDatum.{u}) (n : ℕ) (hn : 1 ≤ n) :
    Fintype (D.extensionSubfield n hn) :=
  let hcard := (FiniteField.exists_unique_subfield_of_closure D.p D.a D.q D.prime
    D.exponent_pos D.cardinality_eq D.k₀ D.card_base D.k n hn).choose_spec.2.1
  let hq : D.q ≠ 0 := D.cardinality_eq.symm ▸ pow_ne_zero D.a D.prime.ne_zero
  letI : Finite (D.extensionSubfield n hn) :=
    Nat.finite_of_card_ne_zero (hcard.symm ▸ pow_ne_zero n hq)
  Fintype.ofFinite (D.extensionSubfield n hn)

/-- The classical transform fhat(y) = sum_x f(x) psi_n(x*y) on F_(q^n), where
psi_n = psi composed with Tr_(F_(q^n)/k₀). This is the existing unnormalized
finite-field Fourier transform, with the setting and the finite extension fixed.
The trace-function clause in the same source is the imported `weilTraceFunction`.
Source: blueprint main-20261015, sk-def-trace/_section.md (blueprint: sk-def-trace). -/
def classicalFiniteFieldFourierTransform (F : FourierSetting.{u})
    (ψ : AddChar F.field.k₀ F.coefficients.Qbar) (n : ℕ) (hn : 1 ≤ n)
    (f : F.field.extensionSubfield n hn → F.coefficients.Qbar)
    (y : F.field.extensionSubfield n hn) : F.coefficients.Qbar :=
  letI := fourierTraceExtensionFintype F.field n hn
  letI := (F.field.extensionEmbedding n hn).toAlgebra
  FiniteField.fourierTransform ψ f y

end WeilConjectures
