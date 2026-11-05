/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Spectrum.Maximal.Defs
public import Mathlib.RingTheory.Spectrum.Prime.RingHom
public import Mathlib.RingTheory.Jacobson.Ideal
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.Ideal.GoingUp

/-!
# Jacobson radical descends through an integral overring

Source: Stacks Project, Varieties Lemma 09N2 proof, paragraph beginning
“Moreover, `Spec(B') -> Spec(A)` is surjective” (blueprint:
lem-sc-integral-overring-jacobson-power).
-/

@[expose] public section

universe u v w

