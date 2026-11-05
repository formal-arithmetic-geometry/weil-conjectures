/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Curve
public import WeilConjectures.AlgebraicGeometry.Sites.TorsionSheaf
public import WeilConjectures.ConstructibleSheaf.Defs

/-!
# Curve coefficient pairs

Let `k` be an algebraically closed field. A *curve coefficient pair* `(C, F)` over `k`
consists of a curve `C` over `k` (separated of finite type of dimension at most one,
`AlgebraicGeometry.IsCurve`) and a torsion abelian sheaf `F` on the small étale site of `C`.

## Main definitions

- `AlgebraicGeometry.CurveCoefficientPair`: a curve coefficient pair
  (blueprint: `def-weil-pbc-curve-setting`).
- `AlgebraicGeometry.CurveCoefficientPair.IsConstructible`: the sheaf `F` of a curve
  coefficient pair is constructible, i.e. `AlgebraicGeometry.Scheme.IsConstructibleSheaf F`
  (blueprint: `def-weil-pbc-constructible-torsion`).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

namespace CurveCoefficientPair

end CurveCoefficientPair

end AlgebraicGeometry
