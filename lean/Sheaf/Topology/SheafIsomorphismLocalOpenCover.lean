/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
module

public import Sheaf.Paper.DerivedHomMayerVietoris
import Sheaf.Topology.GlueSheavesOfModules

/-!
# Isomorphisms of sheaf modules are local on an open cover

Source: Stacks Project, Sheaves, Section 00AK, Lemma 04TN
(blueprint: lem-weil-pbc-sheaf-isomorphism-local-open-cover).
-/

@[expose] public section

universe u₂ v₂ w₂

open CategoryTheory TopologicalSpace Opposite

namespace AlgebraicGeometry

/-- A morphism of modules on a ringed space is an isomorphism exactly when its
restriction to every member of an open cover is an isomorphism.

Source: Stacks Project, Sheaves, Section 00AK, Lemma 04TN
(blueprint: lem-weil-pbc-sheaf-isomorphism-local-open-cover).
Proof:
1. Restriction preserves identities and composition, and repeated restriction agrees
   with restriction to the smaller open: all maps have the same components
   (`def-weil-sheaf-of-modules-category`, `def-weil-pbc-module-finite-type-presentation`).
2. A global two-sided inverse restricts to a two-sided inverse on each cover member.
3. The local inverses agree on overlaps: both restrict to two-sided inverses of the
   same restricted morphism, and a two-sided inverse is unique.
4. Apply `lem-weil-pbc-glue-sheaves-of-modules` (1) to glue these compatible linear
   maps to a global module morphism.
5. Its composites with the original morphism restrict to identities on every cover
   member. The uniqueness clause of that gluing lemma makes both global composites
   identities, giving the required two-sided inverse.
-/
theorem sheaf_module_isIso_iff_isIso_over_open_cover
    (X : RingedSpace.{u₂}) (I : Type w₂) (U : I → Opens X)
    (hcover : ⨆ i, U i = ⊤)
    (M N : SheafOfModules.{max u₂ v₂} (moduleRings X))
    (α : M ⟶ N) :
    IsIso α ↔ ∀ i : I, IsIso (α.over (U i)) := by
  sorry

end AlgebraicGeometry
