/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction
import WeilConjectures.AlgebraicGeometry.Modules.PullbackTilde

/-!
# Pullback of associated modules on affine schemes

## References

* [Stacks Project, Tag 01I9](https://stacks.math.columbia.edu/tag/01I9)
* [Stacks Project, Tag 01I7](https://stacks.math.columbia.edu/tag/01I7)
* [Stacks Project, Tag 01BJ](https://stacks.math.columbia.edu/tag/01BJ)
-/

@[expose] public section

universe u

open CategoryTheory Opposite
open scoped TensorProduct ChangeOfRings

namespace AlgebraicGeometry.Scheme.Modules

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Pullback of `M` tilde along `Spec φ` is naturally the tilde of `S ⊗[R] M`.
The comparison takes the pullback-unit image of the canonical section of `m` to
that of `1 ⊗ m`. The unit is the canonical tensor-formula adjunction unit. -/
theorem exists_tensorPullback_tilde_iso {R S : CommRingCat.{u}} (φ : R ⟶ S) :
    ∃ θ : tilde.functor R ⋙ tensorPullback (Spec.map φ) ≅
        ModuleCat.extendScalars φ.hom ⋙ tilde.functor S,
      ∀ (M : ModuleCat.{u} R) (m : M),
        (θ.hom.app M).app ⊤
          (((Classical.choose (exists_tensorPullbackAdjunction (Spec.map φ))).unit.app
            (tilde M)).app ⊤ (tilde.toOpen M ⊤ m)) =
          tilde.toOpen ((ModuleCat.extendScalars φ.hom).obj M) ⊤
            ((ModuleCat.extendRestrictScalarsAdj φ.hom).unit.app M m) := by
  let adj := Classical.choose (exists_tensorPullbackAdjunction (Spec.map φ))
  let adj₁ := (tilde.adjunction.comp adj).ofNatIsoRight (pushforwardSpecMapCompΓIso φ)
  let adj₂ := (ModuleCat.extendRestrictScalarsAdj φ.hom).comp tilde.adjunction
  refine ⟨adj₁.leftAdjointUniq adj₂, ?_⟩
  intro M m
  have h := congr($((adj₁.unit_leftAdjointUniq_hom_app adj₂ M)) m)
  exact h

end AlgebraicGeometry.Scheme.Modules
