/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H1
-/
import Sheaf.Paper.DerivedHomMayerVietoris
import Sheaf.Algebra.Homology.ModuleStalkFunctor
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators

/-!
# Surjectivity near a stalk for a finite type target

Source: Stacks Project, Sheaves of Modules, Lemma 17.9.4, Tag 01B8
(blueprint: lem-weil-pbc-module-finite-type-surjective-on-stalk).
-/

universe u

open CategoryTheory Opposite TopologicalSpace

namespace AlgebraicGeometry.RingedSpace

/-- A morphism to a finite type module sheaf on a ringed space which is surjective at one
stalk is surjective as a sheaf map on an open neighbourhood of that point. The conclusion
spells out sheaf surjectivity as local lifting on an open cover, as the node does.

Source: Stacks Project, Sheaves of Modules, Lemma 17.9.4, Tag 01B8
(blueprint: lem-weil-pbc-module-finite-type-surjective-on-stalk).

Proof:
1. By def-weil-pbc-module-finite-type-presentation (1), choose finitely many
sections generating `F` on a neighbourhood `U₀` of `x`, or equivalently an
epimorphism from a finite free module sheaf to `F` there.
2. Lift their germs using surjectivity at `x`. By def-weil-pbc-module-stalk,
each lift is represented by a section near `x`, and equality of germs holds on
a smaller neighbourhood. Intersect these finitely many neighbourhoods with `U₀`
to obtain one neighbourhood `U` where every generator has a lift in `G`.
3. For any section over an open `W ≤ U`, the generating epimorphism gives local
coefficients on a cover of `W`, by lem-weil-pbc-ringed-space-module-exactness-local-lifting (1).
Substitute the lifted generators into those linear combinations. Linearity of
`φ` (def-weil-sheaf-of-modules-category) makes them local lifts of the section.
With no generators take `U = U₀`; all local sections vanish and their lifts are zero. -/
theorem exists_surjective_neighbourhood_of_surjective_stalk (X : RingedSpace.{u})
    {G F : SheafOfModules.{u} (moduleRings X)} (φ : G ⟶ F) (x : X) [F.IsFiniteType]
    (hφ : Function.Surjective ((moduleStalkFunctor X x).map φ)) :
    ∃ U : Opens X, x ∈ U ∧
      ∀ (W : Opens X), W ≤ U → ∀ t : F.val.obj (op W),
        ∃ (I : Type u) (V : I → Opens X) (hV : ∀ i, V i ≤ W)
          (g : ∀ i, G.val.obj (op (V i))),
          (⨆ i, V i) = W ∧
            ∀ i, φ.val.app (op (V i)) (g i) =
              F.val.map (homOfLE (hV i)).op t := by
  sorry

end AlgebraicGeometry.RingedSpace
