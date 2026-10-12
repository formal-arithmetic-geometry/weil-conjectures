/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
module

public import Sheaf.AlgebraicGeometry.TensorPullback
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
import Sheaf.Algebra.Homology.RingedSpaceModuleExactnessLocalLifting
import Sheaf.AlgebraicGeometry.Coherent
import Sheaf.AlgebraicGeometry.TensorPullbackStructureSheaf

/-!
# Finite type is preserved by module pullback

Source: Stacks Project, Modules, Lemma 01B6 (lemma-pullback-finite-type),
(blueprint: lem-weil-pbc-module-pullback-finite-type).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

/-- For a morphism of schemes, the pullback of a finite type module is finite type.

Source: Stacks Project, Modules, Lemma 01B6 (lemma-pullback-finite-type),
(blueprint: lem-weil-pbc-module-pullback-finite-type).

The hypothesis `[G.IsFiniteType]` renders that every point of the target has an open
neighbourhood on which a finite direct sum of the structure sheaf surjects onto `G`.
The conclusion says the same for `tensorPullback f G`; the local proof takes the inverse
image of the neighbourhood and uses the same finite number of summands. The second
conjunct records this explicitly for every surjection on an open `V`: `(Opens.map f.base).obj V`
is `f⁻¹ V`, and `free (ULift (Fin n))` is the direct sum of `n` structure sheaves.

Proof, following the four steps of the node:
1. For `x : X`, choose a finite generating surjection on a neighbourhood `V` of `f(x)`
   using `pqf-def-coherent` (01B5), and put `U = f⁻¹ V`. The restriction along the open
   inclusions is module restriction (`lem-weil-pbc-module-restriction-open-immersion-colimits`)
   and is isomorphic to pullback
   (`lem-weil-pbc-open-immersion-module-pullback-restriction`). The composition
   isomorphisms of `def-pc-module-pullback` identify `(f^* G)|_U` with `f'^*(G|_V)`
   for the restricted morphism `f' : U → V` (the reduction of 01B3).
2. The surjection is an epimorphism by
   `lem-weil-pbc-ringed-space-module-exactness-local-lifting`. Pull it back along `f'`;
   `lem-weil-pbc-module-pullback-epi-direct-sum` (01AJ) preserves this epimorphism.
3. The same direct-sum lemma and `lem-weil-pbc-module-pullback-structure-sheaf`
   identify `f'^*(O_V^{⊕ n})` with `O_U^{⊕ n}`, including `n = 0`.
4. Compose the epimorphism with these isomorphisms. The local-lifting lemma makes
   it a sheaf surjection. Thus the same `n` works on `U = f⁻¹ V`; choosing `V` at
   each `f(x)` gives finite type by `pqf-def-coherent`.
-/
theorem tensorPullback_isFiniteType (X Y : Scheme.{u}) (f : X ⟶ Y) (G : Y.Modules)
    [G.IsFiniteType] :
    ((tensorPullback f).obj G).IsFiniteType ∧
      ∀ (V : Y.Opens) (n : ℕ)
        (φ : SheafOfModules.free (R := Y.ringCatSheaf.over V) (ULift.{u} (Fin n)) ⟶
          G.over V),
        Epi φ →
          ∃ ψ : SheafOfModules.free
            (R := X.ringCatSheaf.over ((TopologicalSpace.Opens.map f.base).obj V))
            (ULift.{u} (Fin n)) ⟶
              ((tensorPullback f).obj G).over ((TopologicalSpace.Opens.map f.base).obj V),
            Epi ψ := by
  sorry

end AlgebraicGeometry.Scheme.Modules
