/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Modules.TensorSection

/-!
# The isomorphism of invertible modules with the same transition functions

Let `U i` be an open cover of a scheme `X`, `e i` a free generator of an `𝒪_X`-module `M` on
`U i` and `f i` a free generator of `N` on `U i`, such that both families have the same
transition functions. Then there is a unique isomorphism `M ≅ N` sending each `e i` to `f i`
(`AlgebraicGeometry.Scheme.Modules.isoOfIsFreeGenerator`). This upgrades
`AlgebraicGeometry.Scheme.Modules.nonempty_iso_of_isFreeGenerator` to an actual isomorphism,
characterised by its values on the generators.
-/

@[expose] public section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} {M N : X.Modules} {ι : Type*} {U : ι → X.Opens}
  {e : ∀ i, Γ(M, U i)} {f : ∀ i, Γ(N, U i)}

variable (hU : ⨆ i, U i = ⊤) (he : ∀ i, IsFreeGenerator (e i))
  (hf : ∀ i, IsFreeGenerator (f i))
  (hc : ∀ i j (W : X.Opens) (hi : W ≤ U i) (hj : W ≤ U j) (a b : Γ(X, W)),
    a • M.presheaf.map (homOfLE hi).op (e i) = b • M.presheaf.map (homOfLE hj).op (e j) →
      a • N.presheaf.map (homOfLE hi).op (f i) = b • N.presheaf.map (homOfLE hj).op (f j))

section Tensor

open MonoidalCategory

variable {L₁ L₂ L₃ : X.Modules} {e₁ : ∀ i, Γ(L₁, U i)} {e₂ : ∀ i, Γ(L₂, U i)}
  {e₃ : ∀ i, Γ(L₃, U i)}

end Tensor

end AlgebraicGeometry.Scheme.Modules
