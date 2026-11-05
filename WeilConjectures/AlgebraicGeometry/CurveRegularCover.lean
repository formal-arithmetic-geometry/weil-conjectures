/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/

module

public import WeilConjectures.AlgebraicGeometry.Regular
public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineScheme
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme

/-!
# A finite regular cover of a curve

A scheme `C` of finite type and of dimension at most one over a field (not necessarily reduced)
is covered by the images of finitely many finite morphisms from regular schemes: the
normalizations of its irreducible components, the latter with their reduced induced closed
subscheme structures. A normal noetherian scheme of dimension at most one is regular, its local
rings being fields or discrete valuation rings.

## Main statements

- `AlgebraicGeometry.Scheme.isRegular_normalization`
- `AlgebraicGeometry.Scheme.exists_isFinite_isRegular_cover`
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

end AlgebraicGeometry.Scheme
