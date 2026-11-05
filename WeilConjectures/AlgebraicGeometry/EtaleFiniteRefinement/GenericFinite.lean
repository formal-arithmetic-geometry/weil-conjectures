/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module
public import WeilConjectures.AlgebraicGeometry.Morphisms.QuasiFiniteFactorization
public import Mathlib.AlgebraicGeometry.Morphisms.IsIso

/-!
# Quasi-finite separated morphisms are finite away from a closed subset

`AlgebraicGeometry.Scheme.Hom.exists_isFinite_morphismRestrict`: a quasi-compact, separated,
locally quasi-finite morphism of finite type over a qcqs base is finite over the complement of
the closed image of the boundary in a Zariski main theorem compactification. This is the first
step towards a stratification over which a quasi-compact étale morphism is finite, the input to
[Stacks 03SA] left open in
`AlgebraicGeometry.Scheme.isConstructibleSheaf_etaleLowerShriek_constantSheaf_of_stratification`.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

end AlgebraicGeometry.Scheme
