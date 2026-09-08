/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.EssentialFiniteness
public import Mathlib.RingTheory.RingHom.FiniteType
public import Mathlib.RingTheory.RingHom.QuasiFinite
public import Mathlib.RingTheory.RingHom.Unramified
public import Mathlib.RingTheory.Unramified.LocalStructure

/-!
# Unramified ring maps of finite type are quasi-finite

A formally unramified algebra of essentially finite type is quasi-finite
(`Algebra.QuasiFinite`, a low-priority instance in `Mathlib.RingTheory.Unramified.LocalStructure`).
This file records the corresponding statement for ring homomorphisms, which is what the
scheme-theoretic machinery of `AlgebraicGeometry.HasRingHomProperty` consumes.

## Main results

- `RingHom.QuasiFinite.of_formallyUnramified_of_finiteType`: a formally unramified ring
  homomorphism of finite type is quasi-finite.
-/

@[expose] public section

universe u

namespace RingHom

/-- A formally unramified ring homomorphism of finite type is quasi-finite. -/
theorem QuasiFinite.of_formallyUnramified_of_finiteType {R S : Type u} [CommRing R]
    [CommRing S] {f : R →+* S} (h₁ : f.FormallyUnramified) (h₂ : f.FiniteType) : f.QuasiFinite := by
  algebraize [f]
  exact inferInstanceAs (Algebra.QuasiFinite _ _)

end RingHom
