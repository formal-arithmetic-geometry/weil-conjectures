/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF worker H1
-/
import Sheaf.CategoryTheory.DiscreteModulesAbelian
import Mathlib.Topology.LocallyConstant.Algebra

/-!
# Coinduced embeddings of discrete continuous modules

Source: Stacks Project, etale-cohomology.tex, Tag 04JP,
label definition-G-module-continuous; Tag 0DVG, label section-continuous-group-cohomology.
The coinduced embedding is the agent-written comparison ingredient
(blueprint: lem-exc-coinduced-discrete-embedding).
-/

universe u v w

open CategoryTheory

namespace Rep

/-- Discrete continuous modules admit the natural injective orbit-map embedding into
continuous functions with right translation. `LocallyConstant G M.obj.V` is exactly
`Cont(G, M)` with discrete codomain, and its module operations are pointwise.
The linear equivalences identify the coinduced objects with those function modules.

Source: Stacks Project, etale-cohomology.tex, Tag 04JP,
label definition-G-module-continuous; Tag 0DVG, label section-continuous-group-cohomology
(blueprint: lem-exc-coinduced-discrete-embedding).

Proof: (1) Pointwise operations give the function module, and precomposition by right
multiplication gives a linear left action: translating successively by `k` then `h`
evaluates at `x * h * k`, and translation by one is the identity.
(2) `lem-exc-coinduced-functions-open-stabilizer` supplies an open normal subgroup
under whose right translations any continuous function is invariant. Its stabilizer
contains that subgroup, so is open; hence the coinduced object belongs to
`DiscreteContinuousRep`, the category used in `lem-exc-discrete-modules-abelian`.
(3) The orbit map is locally constant on the open left cosets of each element's
stabilizer. It is linear pointwise and equivariant since `(x * h) m = x (h m)`.
Evaluation at one proves injectivity. Equivariant linear maps commute with the orbit
maps pointwise, giving naturality; on functions the coinduced map is postcomposition. -/
theorem exists_coinduced_discrete_embedding
    (G : Type u) [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (A : Type v) [Ring A] [Finite A] :
    ∃ D : DiscreteContinuousRep.{v, u, max u w} A G ⥤
        DiscreteContinuousRep.{v, u, max u w} A G,
      ∃ e : ∀ M : DiscreteContinuousRep.{v, u, max u w} A G,
        (D.obj M).obj.V ≃ₗ[A] LocallyConstant G M.obj.V,
      ∃ ι : 𝟭 (DiscreteContinuousRep.{v, u, max u w} A G) ⟶ D,
        (∀ (M : DiscreteContinuousRep.{v, u, max u w} A G)
          (h : G) (f : (D.obj M).obj.V) (x : G),
          e M ((D.obj M).obj.ρ h f) x = e M f (x * h)) ∧
        (∀ (M N : DiscreteContinuousRep.{v, u, max u w} A G) (a : M ⟶ N)
          (f : (D.obj M).obj.V) (x : G),
          e N ((D.map a).hom.hom f) x = a.hom.hom (e M f x)) ∧
        (∀ (M : DiscreteContinuousRep.{v, u, max u w} A G) (m : M.obj.V) (x : G),
          e M ((ι.app M).hom.hom m) x = M.obj.ρ x m) ∧
        (∀ M : DiscreteContinuousRep.{v, u, max u w} A G,
          Function.Injective (ι.app M).hom.hom) := by
  sorry

end Rep
