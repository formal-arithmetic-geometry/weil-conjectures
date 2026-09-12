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
public import Mathlib.RingTheory.Spectrum.Prime.Noetherian
public import Mathlib.RingTheory.Unramified.LocalStructure
public import WeilConjectures.Mathlib.RingTheory.LocalRing.ResidueField.Fiber

/-!
# Quasi-finite ring homomorphisms

This file records two facts about `RingHom.QuasiFinite` that the scheme-theoretic machinery of
`AlgebraicGeometry.HasRingHomProperty` consumes: that a formally unramified ring homomorphism of
finite type is quasi-finite, and that the fibre ring of a quasi-finite local homomorphism is
Artinian, hence zero dimensional.

## Main results

- `RingHom.QuasiFinite.of_formallyUnramified_of_finiteType`: a formally unramified ring
  homomorphism of finite type is quasi-finite.
- `RingHom.QuasiFinite.isArtinianRing_fiberRing`: the fibre ring of a quasi-finite homomorphism
  out of a local ring is Artinian.
- `RingHom.QuasiFinite.ringKrullDim_fiberRing_eq_zero`: the fibre ring of a quasi-finite local
  homomorphism of local rings is zero dimensional.
-/

@[expose] public section

open IsLocalRing

universe u v

namespace RingHom

/-- A formally unramified ring homomorphism of finite type is quasi-finite. -/
theorem QuasiFinite.of_formallyUnramified_of_finiteType {R S : Type u} [CommRing R]
    [CommRing S] {f : R →+* S} (h₁ : f.FormallyUnramified) (h₂ : f.FiniteType) : f.QuasiFinite := by
  algebraize [f]
  exact inferInstanceAs (Algebra.QuasiFinite _ _)

/-- The fibre ring of a **quasi-finite** homomorphism out of a local ring is Artinian: it is a
finite-dimensional algebra over the residue field of the source. -/
theorem QuasiFinite.isArtinianRing_fiberRing {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    [IsLocalRing R] {f : R →+* S} (hf : f.QuasiFinite) : IsArtinianRing f.fiberRing := by
  algebraize [f]
  exact (Ideal.Fiber.algEquivFiberRing R S).toRingEquiv.isArtinianRing

/-- The fibre ring of a **quasi-finite** local homomorphism of local rings is zero dimensional. -/
theorem QuasiFinite.ringKrullDim_fiberRing_eq_zero {R : Type u} {S : Type v} [CommRing R]
    [CommRing S] [IsLocalRing R] [IsLocalRing S] {f : R →+* S} [IsLocalHom f]
    (hf : f.QuasiFinite) : ringKrullDim f.fiberRing = 0 :=
  have := hf.isArtinianRing_fiberRing
  ringKrullDimZero_iff_ringKrullDim_eq_zero.mp inferInstance

end RingHom
