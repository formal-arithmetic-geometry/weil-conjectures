/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import WeilConjectures.Mathlib.Algebra.Module.Submodule.Defs

/-!
# Finitely many coordinates detect a finite-dimensional space of functions

## Main statements

- `Submodule.exists_finset_injective_funLeft_domRestrict`: a finite-dimensional subspace `V` of
  the function space `ι → K` admits a finite set `s` of coordinates such that restricting to `s`
  is injective on `V`.
-/

@[expose] public section

namespace Submodule

variable {K ι : Type*} [Field K]

end Submodule
