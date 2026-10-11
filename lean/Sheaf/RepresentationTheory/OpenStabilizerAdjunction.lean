/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
import Mathlib.CategoryTheory.Adjunction.Basic
import Sheaf.RepresentationTheory.DiscreteContinuousRep

/-!
# The open-stabilizer right adjoint

Source: Stacks Project, Injectives, Tag 04JF, proof of Lemma 19.3.1
(blueprint: lem-exc-rg-open-stabilizer-adjoint).
-/

universe u v w

open CategoryTheory

namespace ModuleCat

/-- (blueprint: lem-exc-rg-open-stabilizer-adjoint) Stacks, Tag 04JF.
The functor forgetting the open-stabilizer condition. -/
noncomputable abbrev forgetDiscreteGModule (R : Type u) (G : Type v) [Ring R] [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] :
    Rep.DiscreteContinuousRep.{u, v, w} R G ⥤ Rep.{w} R G :=
  CategoryTheory.ObjectProperty.ι _

/-- (blueprint: lem-exc-rg-open-stabilizer-adjoint) Stacks, Tag 04JF.
The full inclusion of discrete `R`-linear `G`-modules in all `R[G]`-modules is fully faithful
and preserves monomorphisms. The right adjoint sends a module to its open-stabilizer submodule:
the counit is injective and its image consists exactly of the elements with open stabilizer.

For the proof, morphisms in the full subcategory are precisely the equivariant linear maps.
For a monomorphism, the kernel of its underlying linear map is a `G`-stable submodule of its
source, and its elements still have open stabilizers. Its inclusion is therefore a morphism
in the full subcategory. Monicity makes this inclusion zero, so the underlying map is
injective and hence monic in the ambient representation category.

The open-stabilizer elements form a submodule: the stabilizer of a sum contains the
intersection of the two stabilizers, and the stabilizer of a scalar multiple contains the
original stabilizer. Conjugation carries the stabilizer of `x` to that of `g • x`, so this
submodule is `G`-stable and inherits the action. Every equivariant map from a discrete
module lands in this submodule, because it carries stabilizers into stabilizers.
Restriction and inclusion give inverse natural Hom-set bijections, yielding the adjunction.
The counit identifies the right adjoint with that submodule and its induced action.
Injectivity of objects has the meaning of `CategoryTheory.Injective` from
`def-sp-injective-resolutions`. -/
theorem openStabilizerAdjunction (R : Type u) (G : Type v) [Ring R] [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] :
    (forgetDiscreteGModule.{u, v, w} R G).Full ∧
      (forgetDiscreteGModule.{u, v, w} R G).Faithful ∧
      (∀ ⦃N N' : Rep.DiscreteContinuousRep.{u, v, w} R G⦄ (f : N ⟶ N'),
        Mono f → Mono ((forgetDiscreteGModule.{u, v, w} R G).map f)) ∧
      ∃ (u : Rep.{w} R G ⥤ Rep.DiscreteContinuousRep.{u, v, w} R G)
        (adj : forgetDiscreteGModule.{u, v, w} R G ⊣ u),
        ∀ M : Rep.{w} R G,
          Function.Injective (adj.counit.app M).hom ∧
            ∀ x : M, x ∈ Set.range (adj.counit.app M).hom ↔
              IsOpen {g : G | M.ρ g x = x} := by
  sorry

end ModuleCat
