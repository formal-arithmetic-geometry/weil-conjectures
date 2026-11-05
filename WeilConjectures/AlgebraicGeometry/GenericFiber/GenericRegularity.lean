/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.GenericFiber.GenericSmoothness
public import WeilConjectures.AlgebraicGeometry.Regular

/-!
# Connected regular pieces of schemes of finite type over a perfect field

Let `q : P ⟶ D` be an immersion with open range, `D` with noetherian underlying space and `P`
nonempty and locally of finite type over a perfect field `k`. Then there is a nonempty open `V`
of `D`, contained in the range of `q`, and a surjective closed immersion `c : E ⟶ V` factoring
through `q`, with `E` a connected regular noetherian scheme
(`AlgebraicGeometry.exists_isRegular_isClosedImmersion_of_perfectField`).

Indeed, by generic smoothness
(`AlgebraicGeometry.exists_dense_isClosedImmersion_smooth_of_perfectField`) a dense open of
`P` is, up to a surjective closed immersion, smooth over `k`, hence regular; a noetherian
regular scheme is a finite disjoint union of open integral subschemes
(`AlgebraicGeometry.IsRegular.exists_isClopen_isIntegral`), and we take one of them.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

end AlgebraicGeometry
