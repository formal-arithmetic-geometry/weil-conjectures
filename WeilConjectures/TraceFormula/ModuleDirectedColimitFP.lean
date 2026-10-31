/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.CategoryTheory.Category.Preorder
import WeilConjectures.Algebra.ModuleDirectedColimitFinitePresentation
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.Algebra.Module.ULift
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-! # Directed colimits of finitely presented modules

Source: Stacks Project, Algebra, Tag 00HA (blueprint: lem-trf-module-directed-colimit-fp).
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace Module

/-- Every module is a small directed colimit of finitely presented modules. The functor
encodes the transition maps and their identity and composition laws, while the cocone
encodes the compatible maps to the given module. The index type lives in the universe
`max u v` of the ring and the module: the source index set of pairs (finite set of
generators, finite set of relations) is a set of subsets of `Q` and of finitely supported
functions `Q → R`. Source: Stacks Project, Algebra, Tag 00HA
(blueprint: lem-trf-module-directed-colimit-fp).

Proof (blueprint, after Stacks, Algebra, Tag 058G, theorem-lazard, paragraph beginning
"First recall that any module M can be written as the colimit of a directed system of
finitely presented modules"):
1. This is the same module-colimit theorem as lem-trf-module-finitely-presented-directed-colimit;
   instantiate its module variable `M` with `Q`.
2. That node's directed-system data includes the identity and composition equations for the
   transition maps and the compatibility equation for the cocone maps (the defining equations
   of a directed system and a cocone), so it supplies every displayed clause here: the
   functor laws of `F` and the naturality of the cocone `c`.
3. Its finite-presentation convention is exactly def-sc-finitely-presented-module
   (`Module.FinitePresentation`), and its colimit is the colimit of
   def-weil-pbc-category-colimit (`IsColimit c` with `c.pt = ModuleCat.of R Q`). -/
theorem exists_small_directed_colimit_finitePresentation
    (R : Type u) [CommRing R] (Q : Type v) [AddCommGroup Q] [Module R Q] :
    ∃ (I : Type (max u v)) (p : PartialOrder I) (n : Nonempty I)
      (d : IsDirected I (p.toLE.le)),
      ∃ (F : @Functor I (@Preorder.smallCategory I p.toPreorder) (ModuleCat.{v} R)
          inferInstance),
        (∀ i, Module.FinitePresentation R (F.obj i)) ∧
        ∃ (c : Cocone F), c.pt = ModuleCat.of R Q ∧ Nonempty (IsColimit c) := by
  sorry

end Module
