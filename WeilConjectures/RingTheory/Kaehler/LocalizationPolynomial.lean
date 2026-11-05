/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.Etale.Kaehler
public import Mathlib.RingTheory.Kaehler.Polynomial

/-!
# Kähler differentials of a localization of a polynomial ring

If `T` is a localization of the polynomial ring `R[X_k : k ∈ σ]`, then `Ω[T⁄R]` is free over `T`
with basis the differentials `d X_k`.
-/

@[expose] public section

open Module

namespace KaehlerDifferential

variable (R : Type*) [CommRing R] (σ : Type*) (T : Type*) [CommRing T] [Algebra R T]
  [Algebra (MvPolynomial σ R) T] [IsScalarTower R (MvPolynomial σ R) T]
  (M : Submonoid (MvPolynomial σ R)) [IsLocalization M T]

end KaehlerDifferential
