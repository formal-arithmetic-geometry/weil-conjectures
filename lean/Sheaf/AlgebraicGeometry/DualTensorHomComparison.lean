/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R2
-/
module

public import WeilConjectures.AlgebraicGeometry.Modules.HomTensor.Basic

/-! # Identifying the sheaf dual-tensor comparison with the categorical comparison

Source: Stacks Project, Modules, Example 0FNV, the canonical tensor-to-endomorphism map.
(blueprint: lem-ag-dual-tensor-hom-comparison)
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

/-- The sheafified dual-tensor-to-Hom map is the canonical closed-category comparison.

Source: Stacks Project, Modules, Example 0FNV, canonical tensor-to-endomorphism map;
the two maps here are its natural generalization with arbitrary target `N`.

Proof: transpose both maps under the tensor-Hom adjunction. The categorical comparison
transposes, by definition, to associativity followed by evaluation of `M` against its
dual and multiplication of the resulting scalar on `N`. The sheaf comparison is the
sheafification of the presheaf map sending `phi tensor n` to `m ↦ phi(m) n`.
By the construction of the sheaf tensor-Hom adjunction through sheafification,
its transpose is the sheafification of that same evaluation-and-multiplication map.
On any open and any pure tensor `m tensor (phi tensor n)`, both presheaf maps send
this to `phi(m) n`. Tensor induction proves equality on all sections. Sheafification
preserves this equality, and naturality of its tensor and unit comparisons identifies
the endpoints. Injectivity of transposition gives the stated equality. No local
freeness assumption is needed.

(blueprint: lem-ag-dual-tensor-hom-comparison) -/
theorem dualTensorHom_eq_ihomUnitTensorToIhom {X : Scheme.{u}} (M N : X.Modules) :
    dualTensorHom M N = MonoidalClosed.ihomUnitTensorToIhom M N := by
  sorry

end AlgebraicGeometry.Scheme.Modules
