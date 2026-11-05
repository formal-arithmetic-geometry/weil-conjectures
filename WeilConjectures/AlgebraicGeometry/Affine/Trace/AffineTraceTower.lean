/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Line
public import WeilConjectures.Compactification.Defs

/-!
# The coordinate tower used by the affine-space trace

Source: blueprint sec-smooth-purity/sk-prop-an, Steps 5(b) and 6
(blueprint: def-amb-affine-trace-tower).

## Main definitions

- `affineTraceTower`, `affineTraceProjection`, `affineTraceMap`: the ordered tower.
- `affineTraceToAffineSpace`: its canonical polynomial-coordinate identification.
- `affineTraceLineCompactification`: each standard projective-line compactification.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

end AlgebraicGeometry
