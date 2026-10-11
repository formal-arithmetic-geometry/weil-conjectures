/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
import Sheaf.Paper.DerivedHomMayerVietoris
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Topology.Sheaves.Sheaf
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.Algebra.Category.Grp.FilteredColimits

/-!
# Kernel of the sheafified sectionwise quotient

Source: Stacks Project, Sheaves of Modules, Tag 01AH; Sites, Tags 00WB and 00WK
(blueprint: lem-weil-pbc-sheaf-cokernel-local-image).
-/

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace AlgebraicGeometry.RingedSpace

/-- The kernel of the map to the sheafified sectionwise quotient consists precisely of
sections locally in the image. The quotient map is epic and annihilates the original map.
`X` is a ringed space with module sheaves over `moduleRings X`. The presheaf
`cokernel φ.val` is the sectionwise quotient, since presheaf-module evaluation preserves
cokernels. The equality `hq` ties `q` to the canonical composite: the quotient projection
followed by the unit of module sheafification; it is construction data, rather than a
condition on the original morphism.

Source: Stacks Project, Sheaves of Modules, Tag 01AH; Sites, Tags 00WB and 00WK
(blueprint: lem-weil-pbc-sheaf-cokernel-local-image).

Proof:
1. The sectionwise quotient maps commute with restrictions. Their composite with the
sheafification unit is `q`, and annihilates `φ`. Module sheafification has the ordinary
underlying sheafification (lem-weil-pbc-module-sheafification-underlying-sets).
2. By lem-weil-pbc-site-sheafification-sections-local (00WB/00WK), a quotient class maps
to zero precisely when it vanishes on an open cover. A zero quotient class means that
the restricted section lies in the range of the corresponding component of `φ`.
3. Locally image sections are closed under restriction and module operations: refine
covers for addition and use linearity for scalar multiplication. They glue by the sheaf
axiom for `G`. Thus the sectionwise criterion identifies this subsheaf with the kernel.
4. The map `φ` factors through the local-image subsheaf, since its sections are images.
Every section of the sheafified quotient locally comes from a quotient class, which
lifts to a section of `G`. Two morphisms agreeing after `q` therefore agree locally on
all sections, and hence agree by the sheaf axiom. This proves `Epi q`; Step 1 gives the
zero composite (def-weil-pbc-sheafification, def-weil-sheaf-of-modules-category). -/
theorem sheafified_cokernel_local_image (X : RingedSpace.{u})
    {F G : SheafOfModules.{u} (moduleRings X)} (φ : F ⟶ G)
    (q : G ⟶ (PresheafOfModules.sheafification (𝟙 (moduleRings X).obj)).obj (cokernel φ.val))
    (hq : q.val = cokernel.π φ.val ≫
      (PresheafOfModules.sheafificationAdjunction (𝟙 (moduleRings X).obj)).unit.app
        (cokernel φ.val)) :
    (∀ (V : Opens X) (s : G.val.obj (op V)),
      q.val.app (op V) s = 0 ↔
        ∀ x : X, x ∈ V → ∃ (W : Opens X) (hWV : W ≤ V),
          x ∈ W ∧ ∃ t : F.val.obj (op W),
            φ.val.app (op W) t = G.val.map (homOfLE hWV).op s) ∧
      Epi q ∧ φ ≫ q = 0 := by
  sorry

end AlgebraicGeometry.RingedSpace
