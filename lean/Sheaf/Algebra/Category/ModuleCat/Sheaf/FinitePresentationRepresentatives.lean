/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
import Sheaf.Paper.DerivedHomMayerVietoris
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent

/-!
# A set of representatives of finite-presentation module sheaves

Source: Stacks Project, Modules, Lemma 01BC and Definition 01BN
(blueprint: lem-weil-pbc-module-finite-presentation-representatives).
-/

universe u

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.RingedSpace

/-- Finite-presentation modules on a ringed space have a set of isomorphism representatives.
Source: Stacks Project, Modules, Lemma 01BC, restricted using Definition 01BN
(blueprint: lem-weil-pbc-module-finite-presentation-representatives).

Proof:
1. A finite presentation gives a finite set of local generators, hence finite type;
   finite presentation is invariant under isomorphism
   (def-weil-pbc-module-finite-type-presentation).
2. The triples `(U, r, K)`, where `U` is open, `r` is a natural number and `K` is a
   submodule sheaf of the finite free module on `U`, form a set. Choose the cokernel
   `Q` of each inclusion. Covers indexed by subsets of the opens, together with such
   triples and gluing isomorphisms satisfying the cocycle condition, also form a set `D`:
   submodule sheaves and morphisms are families of subsets and functions on sets of sections
   (def-weil-sheaf-of-modules-category).
3. Glue the local cokernels for each datum in `D` and choose one resulting module `Phi(d)`
   (lem-weil-pbc-glue-sheaves-of-modules, existence clause).
4. For any finite-type module, choose local finite-free epimorphisms and their kernels.
   Each epimorphism is a cokernel of its kernel
   (def-weil-pbc-exact-sequence; lem-weil-pbc-abelian-exact-epi-cokernel).
   The chosen cokernels are therefore isomorphic to the local restrictions of the module.
   These isomorphisms induce gluing isomorphisms with the cocycle condition, hence a datum.
5. The local isomorphisms from `Phi(d)` to the given module agree on overlaps, as do their
   inverses. Glue both families; uniqueness shows that their composites are identities
   (lem-weil-pbc-glue-sheaves-of-modules, morphism clause).
6. Restrict `D` to the subset where `Phi(d)` has finite presentation. Step 1 and the
   isomorphism of step 5 show that this subset represents every finite-presentation module.
   No uniqueness of the representing index is asserted. -/
theorem exists_finitePresentation_representatives
    (X : RingedSpace.{u}) :
    ∃ (I : Type u) (G : I → SheafOfModules.{u} (moduleRings X)),
      (∀ i : I, (G i).IsFinitePresentation) ∧
      ∀ F : SheafOfModules.{u} (moduleRings X), F.IsFinitePresentation →
        ∃ i : I, Nonempty (F ≅ G i) := by
  sorry

end AlgebraicGeometry.RingedSpace
