/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.OpenCoverTensorPullbackComparison

/-! # Recovery of a global morphism by a prescribed local family

## References

* [Stacks, Tags 01ZR and 0095]
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- Every member of the pulled-back cover recovers the restriction of the given map. -/
def localMapRecovery {X Y : Scheme.{u}} (p : Y ⟶ X) (U : X.OpenCover.{u})
    (F G : X.Modules)
    (δ : (Scheme.Modules.tensorPullback p).obj F ⟶
      (Scheme.Modules.tensorPullback p).obj G)
    (r : ∀ α, (Scheme.Modules.pullback (U.f α)).obj F ⟶
      (Scheme.Modules.pullback (U.f α)).obj G) : Prop :=
  ∀ α,
    let t := Scheme.Modules.openCoverTensorPullbackComparison p U α
    t.inv.app F ≫ (Scheme.Modules.pullback (U.pullbackHom p α)).map (r α) ≫
      t.hom.app G =
    (Scheme.Modules.pullback ((U.pullback₁ p).f α)).map δ

end AlgebraicGeometry
