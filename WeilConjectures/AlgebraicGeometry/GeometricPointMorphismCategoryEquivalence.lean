/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.FieldTheory.IsAlgClosed.Basic
import WeilConjectures.AlgebraicGeometry.EtaleFiniteRefinement.GeometricLifts
import WeilConjectures.Mathlib.CategoryTheory.Elements

@[expose] public section

open CategoryTheory Opposite
universe u v
namespace AlgebraicGeometry.Scheme
/-- Category equivalence induced by a morphism of geometric points (Stacks, Tag 04FN). -/
theorem geometricPointMorphism_category_equivalence
    {S : Scheme.{u}} {k k' : Type u} [Field k] [IsAlgClosed k]
    [Field k'] [IsAlgClosed k'] (s : Spec (.of k) ⟶ S) (s' : Spec (.of k') ⟶ S)
    (a : Spec (.of k) ⟶ Spec (.of k')) (ha : a ≫ s' = s) :
    let b : Over.mk s ⟶ Over.mk s' := Over.homMk a ha
    let α : (pointSmallEtale s').fiber ⟶ (pointSmallEtale s).fiber :=
      Functor.whiskerLeft (Etale.forget S) (coyoneda.map b.op)
    (NatTrans.mapElements α).IsEquivalence := by
  let b : Over.mk s ⟶ Over.mk s' := Over.homMk a ha
  let α : (pointSmallEtale s').fiber ⟶ (pointSmallEtale s).fiber :=
    Functor.whiskerLeft (Etale.forget S) (coyoneda.map b.op)
  change (NatTrans.mapElements α).IsEquivalence
  obtain ⟨β, hβ⟩ := Spec.map_surjective a
  have hbij (U : S.Etale) : Function.Bijective (α.app U) := by
    constructor
    · intro x y hxy
      apply Over.OverMorphism.ext
      apply SpecMap_comp_injective β
      rw [hβ]
      exact congrArg Over.Hom.left hxy
    · intro x
      obtain ⟨y, hy, hys⟩ := U.hom.exists_SpecMap_comp_eq_of_isSepClosed β s' x.left
        (by simpa [hβ, ha] using x.w)
      refine ⟨Over.homMk y hys, ?_⟩
      apply Over.OverMorphism.ext
      change a ≫ y = x.left
      rwa [hβ] at hy
  have : IsIso α := by
    have (U : S.Etale) : IsIso (α.app U) :=
      (ConcreteCategory.isIso_iff_bijective _).mpr (hbij U)
    exact NatIso.isIso_of_isIso_app _
  exact (NatIso.mapElements (asIso α)).isEquivalence_functor

end AlgebraicGeometry.Scheme
