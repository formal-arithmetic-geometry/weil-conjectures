/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Ring.RingHomExtensionDefsSupplement
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import Mathlib.Algebra.Module.Projective
public import Mathlib.RingTheory.Finiteness.Defs

/-! # Transport of a module Hom comparison to the one-point ring site

Source: Stacks Project, more-algebra.tex, base change for RHom and
Lemma 0A6A.
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite TensorProduct

namespace CategoryTheory

private theorem point_eq (U : (Discrete PUnit.{u + 1})ᵒᵖ) :
    U = op ⟨PUnit.unit⟩ := by
  rcases U with ⟨⟨⟨⟩⟩⟩
  rfl

end CategoryTheory
