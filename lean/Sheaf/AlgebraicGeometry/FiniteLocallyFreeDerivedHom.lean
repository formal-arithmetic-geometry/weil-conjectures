/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q1
-/
import Sheaf.AlgebraicGeometry.DerivedCategory
import Sheaf.Algebra.Homology.DerivedInternalHom
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree

/-!
# Derived internal Hom from a finite locally free sheaf

Source: Stacks Project, Cohomology of Sheaves, Tag 08DQ, Lemma 20.50.5,
specialized to a finite locally free module in degree zero
(blueprint: lem-sc-finite-locally-free-derived-hom).
-/

universe u w

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace AlgebraicGeometry

/-- For a finite locally free `P`, derived internal Hom from `P[0]` to `L[0]` is
ordinary sheaf Hom in degree zero. In particular its positive cohomology sheaves
(the higher sheaf Exts) vanish. The finite rank may vary over the open cover.

Source: Stacks Project, Cohomology of Sheaves, Tag 08DQ (the case `K = P[0]`)
(blueprint: lem-sc-finite-locally-free-derived-hom).

Proof:
1. On a trivializing cover the dual of `P` is finite free. By
   `lem-sc-ext-tensor-exact`, tensoring with this dual is exact, and
   `lem-sc-ext-evaluation` identifies it naturally with sheaf Hom from `P`
   (`def-pur-sheaf-hom`). Thus `T = Hom(P,-)` is exact.
2. By `def-pur-derived-internal-hom`, a K-injective resolution `L[0] → I`
   computes derived Hom as the Hom complex from `P[0]` to `I`, namely `T(I)`.
   Exactness of `T` identifies its degree-`n` cohomology with `T(H^n(I))`:
   this is `Hom(P,L)` for `n = 0` and zero otherwise. In particular all
   positive sheaf Exts vanish. The truncation quasi-isomorphisms identify this
   complex in `D(O_Y)` (`def-pc-derived-category`) with `Hom(P,L)[0]`. -/
theorem finiteLocallyFree_derivedInternalHom_single
    (Y : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (P L : SheafOfModules.{u} (moduleRings Y.toRingedSpace))
    [SheafOfModules.IsFiniteLocallyFree.{u, u, u} P] :
    Nonempty
      ((derivedInternalHom (Opens.grothendieckTopology Y) Y.toRingedSpace.sheaf).obj
        (op ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj P),
          (DerivedCategory.singleFunctor
            (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj L) ≅
        (DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj
            (SheafOfModules.homObj (R := Y.toRingedSpace.sheaf) P L)) ∧
    ∀ i : ℤ, 0 < i →
      IsZero ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) i).obj
          ((derivedInternalHom (Opens.grothendieckTopology Y) Y.toRingedSpace.sheaf).obj
            (op ((DerivedCategory.singleFunctor
              (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj P),
              (DerivedCategory.singleFunctor
                (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj L))) := by
  sorry

end AlgebraicGeometry
