/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Segre
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist

/-!
# The twisting sheaf and the Segre morphism

The pullback of `𝒪(1)` along the relative Segre morphism `ℙ(n; S) ×_S ℙ(m; S) ⟶ ℙ(n × m; S)`
is the external tensor product `𝒪(1) ⊠ 𝒪(1)`. This is what makes a tensor product of very ample
modules very ample (`AlgebraicGeometry.IsVeryAmple.tensorObj`).

## Main statements

- `AlgebraicGeometry.ProjectiveSpace.nonempty_twistRestrict_segre_iso`:
  `segre^* 𝒪(1) ≅ pr₁^* 𝒪(1) ⊗ pr₂^* 𝒪(1)`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

namespace AlgebraicGeometry.ProjectiveSpace

variable (n m : Type u) (S : Scheme.{u})

/-- Blueprint `lem-chow-segre`: The Segre embedding is a closed immersion (the consequence
`𝒪(1) ⊠ 𝒪(1)` recorded in its detailed form).

**The pullback of `𝒪(1)` along the relative Segre morphism is `𝒪(1) ⊠ 𝒪(1)`**, the tensor
product of the pullbacks of `𝒪(1)` along the two projections of `ℙ(n; S) ×_S ℙ(m; S)`: the
coordinate `W_{k,l}` pulls back to the product `Xₖ ⊗ Yₗ` of the coordinates (Stacks 01WD). -/
theorem nonempty_twistRestrict_segre_iso :
    Nonempty (twistRestrict (segre n m S) 1 ≅
      twistRestrict (pullback.fst (ℙ(n; S) ↘ S) (ℙ(m; S) ↘ S)) 1 ⊗
        twistRestrict (pullback.snd (ℙ(n; S) ↘ S) (ℙ(m; S) ↘ S)) 1) :=
  sorry

end AlgebraicGeometry.ProjectiveSpace
