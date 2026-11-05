/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SmoothPurity.TateTwistPullback
public import WeilConjectures.TraceFormula.DualizableShift
public import WeilConjectures.TateTwist.LocallyFree
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LocallyFreeDualizable

/-!

# The shifted Tate twists are dualizable

For a separated `k`-scheme of finite type `X`, the shifted Tate twist `ℚ̄_ℓ,X(d)[n]` is a
dualizable object of `Dᵇc(X)⟦ℚ̲̄_ℓ⟧` (blueprint `det-def-sp-tate-twist-locally-free` (3),
subsection `sk-prop-an`): `ℚ̄_ℓ,X(d)` is locally free of rank one, and shifts of dualizable
objects are dualizable.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

variable {X : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]

end AlgebraicGeometry.ProEtale.CondensedRing
