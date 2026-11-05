/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.NearbyCycles.Kunneth
import WeilConjectures.TraceFormula.OrdinaryKunnethGlobal

/-!
# The ordinary Künneth formula for global sections over a field

For a cartesian square `P = X ×_K Y` of separated `K`-schemes of finite type and bounded
constructible `ℚ̄_ℓ`-complexes `A` on `X` and `B` on `Y`, the ordinary Künneth map
`RΓ(X, A) ⊗ RΓ(Y, B) ⟶ RΓ(P, Lp₁^* A ⊗ Lp₂^* B)` (`ProEtale.CondensedRing.lowerStarKunnethMap'`
of the two squares over `Spec K`) is an isomorphism
(`ProEtale.CondensedRing.isIso_lowerStarKunnethMap'_of_isPullback`; blueprint
`sk-lem-sf-kunneth-star`, for `fᵢ : Xᵢ ⟶ Spec K`).

The proof is `ProEtale.CondensedRing.isIso_lowerStarKunnethMap'_of_isPullback_point` of
`WeilConjectures.TraceFormula.OrdinaryKunnethGlobal`, for the morphisms of `Over (Spec K)`
defined by the square. That module is imported privately: it imports the six functors on `Dᵇc`,
whose instances would change the elaboration of statements on the ambient derived categories in
the importing modules.
-/

public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable {ℓ : ℕ} [Fact ℓ.Prime]

variable {K : Type u} [Field K] [Fact (ringChar K).Prime] [Fact (ringChar K ≠ ℓ)]
  {X Y P : Over (Spec (.of K))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  [LocallyOfFiniteType P.hom] [QuasiCompact P.hom] [IsSeparated P.hom]

end AlgebraicGeometry.ProEtale.CondensedRing
