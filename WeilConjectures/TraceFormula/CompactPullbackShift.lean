/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ShriekCompositionShift
public import WeilConjectures.TraceFormula.CompactPullback

/-!
# The pullback on compactly supported cohomology commutes with the shifts

The pullback `h^♯ : RΓ_c(X, -) ⟶ RΓ_c(Y, Lh^* -)` along a proper morphism `h : Y ⟶ X`
(`ProEtale.CondensedRing.compactPullback`) is assembled from the unit of `Lh^* ⊣ Rh_*`, the
identification `Rh_! ≅ Rh_*` and the composition isomorphism `Rh_! ⋙ Ra_{X!} ≅ Ra_{Y!}`, which
all commute with the shifts. Hence so does `h^♯`
(`ProEtale.CondensedRing.commShift_compactPullback`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]
  {X Y : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]

end AlgebraicGeometry.ProEtale.CondensedRing
