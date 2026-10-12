/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J1
-/
module

public import Mathlib.Topology.Sheaves.Module
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Sheaf.Paper.DerivedHomMayerVietoris
import Sheaf.Topology.OpenRestrictionAdjunction

/-!
# Restriction of colimits of sheaves of modules to an open

Source: Stacks Project, Modules, Tags 01AH (2), 01AJ (2), and Sheaves, Tag 00A0
(blueprint: lem-weil-pbc-ringed-space-colimit-restriction).

The ringed space `(X, 𝒪_X)` is `X : RingedSpace`, its modules live on the landed
`AlgebraicGeometry.moduleRings X`, and restriction to an open `U` is Mathlib's
`SheafOfModules.overFunctor (moduleRings X) U` into `SheafOfModules ((moduleRings X).over U)`
(the site `Over U` has exactly the opens `W ⊆ U` as objects).
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry

namespace TopologicalSpace.Opens

/-- Restriction carries any colimit cocone of sheaves of modules to a colimit cocone, and
its vertex is the sheafification of the sectionwise colimit on the open.
Source: Stacks Project, Modules, Tags 01AH (2), 01AJ (2); Sheaves, Tag 00A0
(blueprint: lem-weil-pbc-ringed-space-colimit-restriction).

Proof:
1. Restriction evaluates the module sheaf and its morphisms on opens contained in `U`.
   Covers there are covers in `X`, so this is a functor and carries cocones to cocones
   (def-weil-sheaf-of-modules-category, def-weil-pbc-module-finite-type-presentation).
2. Restriction is left adjoint to direct image along the open inclusion
   (lem-weil-pbc-ringed-space-open-restriction-adjunction). Left adjoints preserve colimits
   (lem-weil-pbc-left-adjoint-preserves-colimits), proving the first clause.
3. The presheaf `P` with its coprojections is the sectionwise colimit
   (lem-weil-pbc-presheaf-modules-colimits-sectionwise). Every cocone into a sheaf factors
   uniquely through `P`, then uniquely through its module sheafification
   (def-weil-presheaf-modules-sheafification; existence of underlying sheafification is
   def-weil-pbc-sheafification). Hence its sheafification is also a colimit.
4. The colimit universal property (def-weil-pbc-category-colimit) gives the unique map from
   this sheafification to the restricted vertex. The reverse comparison exists as well.
   Their composites are identities by uniqueness, so the comparison is an isomorphism.

`sheafificationHomEquiv` sends `u` to `η ≫ u.val`, so the displayed equations are exactly
`ι_i ≫ η ≫ u.val = (c_i|_U).val`. Uniqueness is among all morphisms satisfying the equations,
not merely among isomorphisms. -/
theorem module_colimit_restriction (X : RingedSpace.{u}) (U : Opens X)
    (I : Type u) [SmallCategory I]
    (D : I ⥤ SheafOfModules.{u} (moduleRings X)) (c : Cocone D) (hc : IsColimit c) :
    Nonempty (IsColimit ((SheafOfModules.overFunctor.{u} (moduleRings X) U).mapCocone c)) ∧
      ∃ u : (PresheafOfModules.sheafification.{u} (𝟙 ((moduleRings X).over U).obj)).obj
            (PresheafOfModules.colimitPresheafOfModules
              (D ⋙ SheafOfModules.overFunctor.{u} (moduleRings X) U ⋙
                SheafOfModules.forget ((moduleRings X).over U))) ⟶
          (SheafOfModules.overFunctor.{u} (moduleRings X) U).obj c.pt,
        IsIso u ∧
        (∀ i : I, (PresheafOfModules.colimitCocone
              (D ⋙ SheafOfModules.overFunctor.{u} (moduleRings X) U ⋙
                SheafOfModules.forget ((moduleRings X).over U))).ι.app i ≫
            PresheafOfModules.sheafificationHomEquiv.{u} (𝟙 ((moduleRings X).over U).obj) u =
          (SheafOfModules.forget ((moduleRings X).over U)).map
            ((SheafOfModules.overFunctor.{u} (moduleRings X) U).map (c.ι.app i))) ∧
        ∀ v : (PresheafOfModules.sheafification.{u} (𝟙 ((moduleRings X).over U).obj)).obj
              (PresheafOfModules.colimitPresheafOfModules
                (D ⋙ SheafOfModules.overFunctor.{u} (moduleRings X) U ⋙
                  SheafOfModules.forget ((moduleRings X).over U))) ⟶
            (SheafOfModules.overFunctor.{u} (moduleRings X) U).obj c.pt,
          (∀ i : I, (PresheafOfModules.colimitCocone
                (D ⋙ SheafOfModules.overFunctor.{u} (moduleRings X) U ⋙
                  SheafOfModules.forget ((moduleRings X).over U))).ι.app i ≫
              PresheafOfModules.sheafificationHomEquiv.{u} (𝟙 ((moduleRings X).over U).obj) v =
            (SheafOfModules.forget ((moduleRings X).over U)).map
              ((SheafOfModules.overFunctor.{u} (moduleRings X) U).map (c.ι.app i))) → v = u := by
  sorry

end TopologicalSpace.Opens
