/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q04
-/
module

public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.Algebra.Module.Projective
import Sheaf.RingTheory.LocalizedFiniteModuleSpread
import Sheaf.RingTheory.RegularLocalFiniteModuleResolution
import Sheaf.RingTheory.BoundedFiniteFreeResolution
import Sheaf.AlgebraicGeometry.IsRegularScheme
import Sheaf.RingTheory.K0ClassTrivialInvertible
import Sheaf.TraceFormula.InvertibleModuleK0Class

/-!
# Picard group of a regular-local localization

Source: Stacks Project, More on Algebra, Tag 0AFZ (lemma-regular-local-Pic-zero),
read with Tags 0B8I and 00NX (blueprint: lem-trf-regular-local-pic-zero).
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace RingTheory

/--
A finite projective module over a localization of a regular local ring is free of rank one
when all of its prime localizations are free of rank one, hence it is isomorphic to the ring.
Source: Stacks Project, More on Algebra, Tag 0AFZ, lemma-regular-local-Pic-zero, line 36780,
read with Tags 0B8I and 00NX (blueprint: lem-trf-regular-local-pic-zero).

Proof: (1) The hypotheses identify `P` as a finite locally free rank-one module. (2) Apply
`lem-trf-localized-finite-module-spread` to descend `P` to a finite `A`-module. (3) Apply
`lem-weil-pbc-regular-local-finite-module-resolution` and
`stage3-b4-bounded-finite-free-resolution` to resolve that module by finite free modules over
`A`, then localize the resolution. (4) Apply `lem-trf-invertible-module-k0-class` to compute
the class of `P` in `K₀(A_f)` as an integer multiple of `[A_f]`. (5) Apply
`lem-trf-k0-class-trivial-invertible` to the rank-one localizations and the equality from step
4, obtaining a linear equivalence `P ≃ₗ[A_f] A_f`.
-/
theorem regularLocalPicardZero
    (A : Type u) [CommRing A] [IsRegularLocalRing A] (f : A)
    (P : Type v) [AddCommGroup P] [Module (Localization.Away f) P]
    [Module.Finite (Localization.Away f) P]
    [Module.Projective (Localization.Away f) P]
    (hP : ∀ (q : Ideal (Localization.Away f)) [q.IsPrime],
      Nonempty (LocalizedModule q.primeCompl P ≃ₗ[Localization.AtPrime q]
        Localization.AtPrime q)) :
    Nonempty (P ≃ₗ[Localization.Away f] Localization.Away f) := by
  sorry

end RingTheory
