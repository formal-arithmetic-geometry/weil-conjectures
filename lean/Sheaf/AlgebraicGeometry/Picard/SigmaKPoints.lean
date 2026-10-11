/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
module

public import WeilConjectures.AlgebraicGeometry.Picard.Defs

/-!
# The normalized Picard functor at the base field

Source: blueprint `sec-picard-framework/sk-def-picard-pic/lem-pc-sigma-k-points.md`
(blueprint: lem-pc-sigma-k-points).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- The canonical identification of the normalized Picard functor at `Spec k` with `Pic X`.
Source: blueprint `sec-picard-framework/sk-def-picard-pic/lem-pc-sigma-k-points.md`
(blueprint: lem-pc-sigma-k-points).

Proof: at `T = Spec k`, the first projection identifies the base change with `X`, and
identifies the base-changed section with `σ` (def-pc-base-change). By
`def-pc-pic-sigma-functor`, normalized classes form the kernel of pullback along this
section. Every invertible module on `Spec k` is trivial (lem-pc-pic-of-field), so this
pullback is zero and every class is normalized. Forgetting normalization is therefore
bijective; composing it with pullback along the inverse first projection gives the
canonical bijection with `X.Pic` (def-sc-picard-group). No trivialization is retained. -/
theorem bijective_picardFunctorNormalized_kPoints (k : Type u) [Field k] (X : Scheme.{u})
    [X.Over (Spec (.of k))] (σ : Spec (.of k) ⟶ X)
    (hσ : σ ≫ (X ↘ Spec (.of k)) = 𝟙 (Spec (.of k))) :
    Function.Bijective
      (fun L : (picardFunctorNormalized (X ↘ Spec (.of k)) σ hσ).toFunctor.obj
          (.op (Over.mk (𝟙 (Spec (.of k))))) ↦
        Scheme.Pic.map (inv (pullback.fst (X ↘ Spec (.of k)) (𝟙 (Spec (.of k))))) L.val) := by
  sorry

end AlgebraicGeometry
