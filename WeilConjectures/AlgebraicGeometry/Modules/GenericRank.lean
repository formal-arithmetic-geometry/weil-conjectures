/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Modules.LocallyTrivial
public import WeilConjectures.Mathlib.AlgebraicGeometry.Noetherian

/-!
# The generic rank of the tensor unit

The generic rank `AlgebraicGeometry.Scheme.Modules.genericRank` of a sheaf of modules on an
irreducible scheme and its basic API live in
`WeilConjectures.Mathlib.AlgebraicGeometry.Noetherian`, which knows nothing of the monoidal
structure of `X.Modules`. This file records the one statement that needs both: the generic rank
of the tensor unit is `1`, the tensor unit being the structure sheaf.

## Main results

* `AlgebraicGeometry.Scheme.Modules.genericRank_tensorUnit`
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-- **The generic rank of the tensor unit is `1`**, the tensor unit being the structure sheaf. -/
lemma genericRank_tensorUnit [IsIntegral X] : genericRank (𝟙_ X.Modules) = 1 :=
  (genericRank_congr (tensorUnitIsoUnit X)).trans genericRank_unit

end AlgebraicGeometry.Scheme.Modules
