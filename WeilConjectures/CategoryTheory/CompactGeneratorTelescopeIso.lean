/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.CompactObject
public import WeilConjectures.CategoryTheory.WeakTriangulatedGenerator
import WeilConjectures.CategoryTheory.CompactHomHocolim
import Mathlib.CategoryTheory.Functor.OfSequence
import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.Algebra.DirectSum.Module

/-!
# Recognizing a generator approximation telescope

Source: Stacks Project, Derived Categories, Tag 09SN, lemma-write-as-colimit,
proof: vanishing of the cone of the comparison map.
(blueprint: lem-pc-compact-generator-telescope-iso).
-/

@[expose] public section

universe w v u

open CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [IsTriangulated C] [HasCoproducts.{max w v} C]

-- The Brown telescope proof, generalized from coproduct universe v to max w v.

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

end CategoryTheory
