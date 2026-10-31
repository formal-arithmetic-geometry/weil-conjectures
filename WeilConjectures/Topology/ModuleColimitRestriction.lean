/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Topology.Sheaves.Module
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.AlgebraicGeometry.DerivedHomMayerVietorisSupplement
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful

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

private theorem sheafification_fac
    {C : Type u} [Category C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u}) [HasSheafify J AddCommGrpCat.{u}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    {A P : PresheafOfModules.{u} R.obj} {S G : SheafOfModules.{u} R}
    (i : A ⟶ P) (a : A ⟶ S.val)
    (e : S ≅ (PresheafOfModules.sheafification (𝟙 R.obj)).obj P)
    (he : (PresheafOfModules.toPresheaf R.obj).map (a ≫ e.hom.val) =
      (PresheafOfModules.toPresheaf R.obj).map i ≫ toSheafify J P.presheaf)
    (k : S ⟶ G) :
    i ≫ PresheafOfModules.sheafificationHomEquiv (𝟙 R.obj) (e.inv ≫ k) =
      a ≫ k.val := by
  apply (PresheafOfModules.toPresheaf R.obj).map_injective
  rw [Functor.map_comp, PresheafOfModules.toPresheaf_map_sheafificationHomEquiv_def,
    ← Category.assoc, ← he, ← Functor.map_comp]
  congr 1
  rw [SheafOfModules.comp_val, Category.assoc,
    ← Category.assoc e.hom.val e.inv.val k.val,
    ← SheafOfModules.comp_val e.hom e.inv, e.hom_inv_id, SheafOfModules.id_val,
    Category.id_comp]

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
  classical
  let R := (moduleRings X).over U
  let F := SheafOfModules.overFunctor.{u} (moduleRings X) U
  let c' := F.mapCocone c
  have : PreservesColimitsOfSize.{u, u} F :=
    (SheafOfModules.overPushforwardOverAdj (R := moduleRings X) U).leftAdjoint_preservesColimits
  have hc' : IsColimit c' := isColimitOfPreserves F hc
  refine ⟨⟨hc'⟩, ?_⟩
  obtain ⟨s, ⟨hs⟩, e, he⟩ :=
    ((moduleSheaves_colimits_forgetful R).2.2.2.2.2 I).2.2.2 (D ⋙ F)
  let k := hs.coconePointUniqueUpToIso hc'
  let u := e.inv ≫ k.hom
  have hu (i : I) :
      (PresheafOfModules.colimitCocone
          ((D ⋙ F) ⋙ SheafOfModules.forget R)).ι.app i ≫
        PresheafOfModules.sheafificationHomEquiv (𝟙 R.obj) u =
      (SheafOfModules.forget R).map (F.map (c.ι.app i)) := by
    change _ = (c'.ι.app i).val
    calc
      _ = (s.ι.app i).val ≫ k.hom.val :=
        sheafification_fac R _ (s.ι.app i).val e (he i) k.hom
      _ = (c'.ι.app i).val := by
        rw [← SheafOfModules.comp_val]
        exact congrArg SheafOfModules.Hom.val (hs.comp_coconePointUniqueUpToIso_hom hc' i)
  refine ⟨u, inferInstance, hu, ?_⟩
  intro v hv
  apply (PresheafOfModules.sheafificationHomEquiv (𝟙 R.obj)).injective
  apply (PresheafOfModules.isColimitColimitCocone
    ((D ⋙ F) ⋙ SheafOfModules.forget R)).hom_ext
  intro i
  exact (hv i).trans (hu i).symm

end TopologicalSpace.Opens
