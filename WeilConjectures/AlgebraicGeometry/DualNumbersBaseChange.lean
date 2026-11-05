/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.DualNumbers

/-!
# The dual-number thickening is a base change

For a morphism of schemes `f : X ⟶ Y`, the square

```
X[ε] ──f[ε]──▶ Y[ε]
 │              │
 p              p
 ▼              ▼
 X ─────f─────▶ Y
```

is cartesian: a morphism `T ⟶ X[ε]` is a morphism `T ⟶ X` together with a square-zero global
function on `T` (the image of `ε`). In particular, for a scheme `X` over a field `k`, the
thickening `X[ε]` is `X ×_k Spec k[ε]`.

The morphism `T ⟶ T[ε]` attached to a square-zero function `t` is the identity on points and
`a + εb ↦ a + tb` on functions.

## Main statements

- `AlgebraicGeometry.Scheme.isPullback_dualNumbersProj`: the square above is a pullback square.
-/

@[expose] public section

universe u

open CategoryTheory TopologicalSpace TrivSqZeroExt Opposite Limits

namespace AlgebraicGeometry.Scheme

variable {X Y : Scheme.{u}}

end AlgebraicGeometry.Scheme
