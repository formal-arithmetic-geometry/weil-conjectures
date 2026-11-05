/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.AdicCompletion.Functoriality
public import Mathlib.Algebra.Module.Submodule.Pointwise
public import Mathlib.RingTheory.Finiteness.Cardinality

/-!
# Finiteness of modules which are adically separated for a principal ideal

Let `R` be a commutative ring which is `ϖ`-adically precomplete for an element `ϖ`. A
`ϖ`-adically separated `R`-module `N` with `N ⧸ ϖN` finitely generated is finitely generated
(`Module.Finite.of_isHausdorff_span_singleton`): lift generators of `N ⧸ ϖN` and apply
`surjective_of_mkQ_comp_surjective` to the free module they span, which is precomplete
(`IsPrecomplete.pi_span_singleton`).
-/

@[expose] public section

variable {R : Type*} [CommRing R]

