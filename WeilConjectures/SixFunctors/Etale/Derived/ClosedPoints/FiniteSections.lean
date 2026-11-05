/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.ClosedPoints.Support
public import WeilConjectures.ConstructibleSheaf.KernelCokernel
public import WeilConjectures.ConstructibleSheaf.Noetherian
public import WeilConjectures.ConstructibleSheaf.SpecializationCriterion

/-!
# Sheaves supported at closed points with finitely many global sections

Let `K` be a separably closed field, `X` a Noetherian scheme locally of finite type over `K`,
`Λ` a finite ring and `Q` an étale sheaf of `Λ`-modules on `X` whose stalks vanish at the
non-closed points. If `Γ(X, Q)` is finite, then `Q` is constructible
(`AlgebraicGeometry.Etale.isConstructibleSheaf_of_isZero_sheafFiber_of_finite`): `Q` is globally
generated (`AlgebraicGeometry.Etale.isGloballyGenerated_of_isZero_sheafFiber`), hence a quotient
of the finite sum `⊕_{s ∈ Γ(X, Q)} Λ_X` of constant sheaves, and quotients of constructible
sheaves on a Noetherian scheme are constructible.

This is the step of Deligne's proof of the finiteness of nearby cycles (SGA 4½, [Th. finitude],
proof of 3.2) controlling the part of a sheaf supported at closed points by its global sections.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

open Scheme

variable {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ]

namespace Etale

end Etale

end AlgebraicGeometry
