/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.CechModuleBaseChange

/-!
# Base change of sections over an affine open of the base

Consider a cartesian square of schemes
```
Y --g'--> X
|         |
f'        f
v         v
T --g---> S
```
with `S = Spec A` affine, and an affine open `W` of `T` with `B = Γ(T, W)`. For a quasi-coherent
`𝒪_X`-module `ℱ` and an affine open `U` of `X`, the map
`B ⊗[A] Γ(ℱ, U) ⟶ Γ(g'^* ℱ, g'⁻¹ U ⊓ f'⁻¹ W)`, `b ⊗ m ↦ b • (g'^* m)|`, is bijective
(`AlgebraicGeometry.Scheme.Modules.bijective_sectionsBaseChangeOpen`). This is
`AlgebraicGeometry.Scheme.Modules.bijective_sectionsModuleBaseChange` with the affine scheme `T`
replaced by an affine open of an arbitrary scheme `T`.
-/

@[expose] public section

universe u

open CategoryTheory Limits TensorProduct Opposite

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y S T : Scheme.{u}} {f : X ⟶ S} {f' : Y ⟶ T} {g : T ⟶ S} {g' : Y ⟶ X}
  (H : IsPullback g' f' f g) (ℱ : X.Modules) (W : T.Opens)
  [Algebra Γ(S, ⊤) Γ(T, W)]
  (hg : algebraMap Γ(S, ⊤) Γ(T, W) = (g.appLE ⊤ W (le_top.trans g.preimage_top.ge)).hom)

end AlgebraicGeometry.Scheme.Modules
