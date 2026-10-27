/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilObject.BoundedConstructible.Defs

/-!
# The canonical bounded constructible Weil unit

The unit construction shared by the local trace API and the model-Frobenius trace API.
Its definition is extracted unchanged from `WeilConjectures.TraceFormula.Slop.Main` so
the local trace API can use it without importing the model trace formula.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory Endofunctor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable {ℓ : ℕ} [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]
  {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  {Φ : X ⟶ X}

namespace WeilBoundedConstructible

variable (ℓ Φ) in
/-- The *constant Weil object* `ℚ̄_ℓ,X` for `Φ`: the unit `ℚ̄_ℓ,X` of `Dᵇc(X)⟦ℚ̲̄_ℓ⟧` with the
structure isomorphism `LΦ^* ℚ̄_ℓ,X ≅ ℚ̄_ℓ,X` of the monoidal functor `LΦ^*`. -/
noncomputable def unit : WeilBoundedConstructible ℓ Φ :=
  IsoAlgebra.mk (𝟙_ _)
    (Functor.Monoidal.εIso (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ Φ)).symm

end WeilBoundedConstructible

end AlgebraicGeometry.ProEtale.CondensedRing
