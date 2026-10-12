/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.Modules.ExteriorSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free

/-! # Exterior sheafification on a finite-free open

Source: the coordinate expansion of determinant inversion in Stacks Project, Tag 0BRT,
recorded in `lem-sc-exterior-dual-local-frames`, step 2.
(blueprint: lem-sc-exterior-sheaf-local-free-comparison).
-/

@[expose] public section

universe u

open CategoryTheory Opposite
namespace AlgebraicGeometry.Scheme.Modules

/-- On a finite-free open, exterior sheafification preserves sectionwise exterior powers
and gives the free sheaf indexed by increasing subsets.
Source: step 2 of `lem-sc-exterior-dual-local-frames`, expanding determinant inversion in
Stacks Project, Tag 0BRT (lemma-smooth-proper); Mathlib `Module.Basis.exteriorPower`.
(blueprint: lem-sc-exterior-sheaf-local-free-comparison).

Proof: on each W contained in U, use the trivialization to identify M(W) with O(W)^r.
The increasing wedges of the standard generators form a basis of its nth exterior power.
Its coordinates identify that exterior module with O(W) indexed by the n-element subsets
of Fin r. Since the coordinates of the original generators commute with restriction,
the induced exterior coordinate maps commute with restriction too: check this on pure
wedges, whose coordinates are determinants, and use that ring restriction preserves
finite sums and products. They therefore identify the restricted exterior presheaf with
a finite product of the structure sheaf, which is a sheaf. Sheafification restricted to
U has the same universal property as sheafification on the localized site, because its
covers are exactly the covers of smaller opens. The unit is consequently an isomorphism
there, and gives both the asserted free sheaf isomorphism and bijectivity on every V
contained in U. For n=0 the index is a singleton; for n>r it is empty. No hypothesis that
the ring is nonzero is used, so empty opens and zero rings are also covered. -/
theorem exteriorSheaf_local_free_comparison (X : Scheme.{u}) (M : X.Modules)
    (n : ℕ) (U : X.Opens) (r : ℕ)
    (e : M.over U ≅ SheafOfModules.free (ULift.{u} (Fin r))) :
    Nonempty ((exteriorSheaf M n).over U ≅
      SheafOfModules.free (ULift.{u} (Set.powersetCard (Fin r) n))) ∧
    ∀ (V : X.Opens) (g : V ⟶ U),
      Function.Bijective
        (((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
          (exteriorSheafPresheaf M n)).app (op V)) := by sorry

end AlgebraicGeometry.Scheme.Modules
