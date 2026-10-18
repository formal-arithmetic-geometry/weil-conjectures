/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.Algebra.Module.ULift
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.LinearAlgebra.FreeModule.Basic

/-! # Every module is a directed colimit of finitely presented modules

Source: Stacks Project, Algebra, Tag 058G, proof of Lazard's theorem, paragraph beginning
"For the converse, first recall that any module M can be written as the colimit of a
 directed system of finitely presented modules"
(blueprint: lem-trf-module-finitely-presented-directed-colimit).
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace Module

/-- Every module is a colimit of a small nonempty directed poset of finitely presented modules.
Source: Stacks Project, Algebra, Tag 058G, proof of Lazard's theorem
(blueprint: lem-trf-module-finitely-presented-directed-colimit).

The common universe `max u v` accommodates the finite free modules over `R`, their quotients,
and the index set. The cocone vertex is the canonical universe lift of `M`; this is the same
module via `ULift.moduleEquiv`. Functoriality supplies identity and composition for the
transition maps, and cocone naturality supplies compatibility of the maps to `M`.

Proof:
1. Form the free module `P = M →₀ R`, with basis vectors indexed by `M`
   (def-weil-pbc-free-module). The linear combination map `p : P →ₗ[R] M` is surjective;
   write `K` for its kernel.
2. Index by pairs `(J, N)`, where `J` is a finite subset of `M` and `N` is a finitely generated
   submodule of `P`, supported on `J` and contained in `K`. Componentwise inclusion is a
   partial order, and the pairs form a set in the common universe.
3. The pair `(∅, 0)` gives nonemptiness. Union of the finite supports and sum of the finitely
   generated relation submodules give a common upper bound for any two pairs.
4. At `(J, N)` take `P_J / N`. A finite generating list of `N` supplies a map from a finite
   free module onto `N`; the quotient therefore has a finite presentation
   (def-sc-finitely-presented-module), also when the generators or relations are empty.
5. Inclusion of supports and relations induces the transition maps. Quotient formulas give
   their identity and composition laws. The maps induced by `p` are a compatible cocone.
6. Given any compatible cocone to `T`, use the singleton stages to assign an image in `T`
   to every basis vector of `P`. Extend by finite linear combinations to a linear map
   `h : P →ₗ[R] T`. Compatibility identifies its restriction to each `P_J` with the given
   stage map followed by the quotient map.
7. For `x ∈ K`, the stage with its finite support and relation submodule `R x` kills `x`.
   Hence `h` vanishes on `K` and descends uniquely along the surjection `p` to `M`.
8. The descended map factors all the stage maps; singleton stages prove uniqueness.
   This is exactly `IsColimit` (def-weil-pbc-category-colimit). -/
theorem exists_directed_colimit_finitePresentation
    (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M] :
    ∃ (I : Type (max u v)) (p : PartialOrder I) (_ : Nonempty I)
      (_ : IsDirected I p.toLE.le),
      ∃ (F : @Functor I (@Preorder.smallCategory I p.toPreorder)
          (ModuleCat.{max u v} R) inferInstance),
        (∀ i, Module.FinitePresentation R (F.obj i)) ∧
        ∃ (c : Cocone F), c.pt = ModuleCat.of R (ULift.{u} M) ∧
          Nonempty (IsColimit c) := by
  sorry

end Module
