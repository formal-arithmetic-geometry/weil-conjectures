/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF contributors
-/
module

public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.Algebra.Module.Projective

/-!
# Restriction of scalars preserves finite projectivity

Source: `WeilConjectures/AlgebraicGeometry/Modules/FinitePushforward.lean`,
theorem `isFiniteLocallyFree_pushforward`, lines 228-242
(blueprint: lem-pc-finite-flat-restriction-projective).
-/

@[expose] public section

universe u v w

namespace Module

/--
(blueprint: lem-pc-finite-flat-restriction-projective)

Source: `WeilConjectures/AlgebraicGeometry/Modules/FinitePushforward.lean`,
theorem `isFiniteLocallyFree_pushforward`, lines 228-242.

Let `A → B` be a map of commutative rings with `B` finite, finitely presented as an
`A`-algebra, and flat over `A`. If `M` is a finitely presented projective `B`-module, then
`M`, regarded as an `A`-module, is finitely presented and projective over `A`.

Proof.
*Step 1 (finite presentation over `A`).* `B` is a finite `A`-module and a finitely presented
`A`-algebra, so `B` is a finitely presented `A`-module
(`Module.FinitePresentation.of_finite_of_finitePresentation`). Since `M` is finitely presented
over `B`, transitivity of finite presentation (`Module.FinitePresentation.trans`) shows that `M`
is a finitely presented `A`-module.
*Step 2 (flatness over `A`).* `M` is projective over `B`, hence flat over `B`. As `B` is flat
over `A`, transitivity of flatness (`Module.Flat.trans`) shows that `M` is a flat `A`-module.
*Step 3 (projectivity over `A`).* By Steps 1 and 2, `M` is a finitely presented flat
`A`-module, hence projective over `A` (`Module.Flat.projective_of_finitePresentation`).
Together with Step 1 this is the claim.
-/
theorem finite_flat_restriction_projective
    (A : Type u) (B : Type v) (M : Type w)
    [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup M] [Module B M] [Module A M] [IsScalarTower A B M]
    [Module.Finite A B] [Algebra.FinitePresentation A B] [Module.Flat A B]
    [Module.FinitePresentation B M] [Module.Projective B M] :
    Module.FinitePresentation A M ∧ Module.Projective A M := by
  sorry

end Module
