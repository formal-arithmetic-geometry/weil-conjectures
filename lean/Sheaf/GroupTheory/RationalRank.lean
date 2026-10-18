/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q15
-/
module

public import Mathlib.LinearAlgebra.Dimension.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Basic

/-!
# Rational rank of an abelian group

Source: Temkin, *Stable modification of relative curves*, §2.1, notation preceding
Lemma 2.1.2 (blueprint: def-trf-rational-rank).
-/

@[expose] public section

set_option autoImplicit false

universe u

open scoped TensorProduct

namespace AddCommGroup

/-- The rational rank of an abelian group is the dimension of its rationalization.
The tensor factors are ordered as `ℚ ⊗[ℤ] G` to use the canonical scalar action on
Mathlib's left tensor factor; tensor symmetry identifies this with `G ⊗[ℤ] ℚ`.
Source: Temkin, §2.1, notation before Lemma 2.1.2 (blueprint: def-trf-rational-rank). -/
noncomputable def rationalRank (G : Type u) [AddCommGroup G] : Cardinal.{u} :=
  Module.rank ℚ (ℚ ⊗[ℤ] G)

end AddCommGroup
