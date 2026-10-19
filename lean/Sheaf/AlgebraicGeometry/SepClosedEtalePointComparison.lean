/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q3
-/
module

public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.CategoryTheory.Sites.Point.Category
public import WeilConjectures.AlgebraicGeometry.EtaleFiniteRefinement.GeometricLifts
public import WeilConjectures.Mathlib.AlgebraicGeometry.ResidueField

/-! # Comparing etale points after extending a separably closed field

Source: Stacks Project, Tag 04FN; etale lifts are unchanged by extending a separably
closed field. (blueprint: lem-exc-sep-closed-etale-point-comparison)
-/

@[expose] public section

universe u w t

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme

variable {S : Scheme.{u}} {k k' : Type u} [Field k] [IsSepClosed k]
  [Field k'] [IsSepClosed k']
  (s : Spec (.of k) ⟶ S) (s' : Spec (.of k') ⟶ S)
  (β : CommRingCat.of k ⟶ CommRingCat.of k') (hβ : Spec.map β ≫ s = s')

/-- The natural bijection on etale lifts. Injectivity is injectivity of
precomposition with a field extension. Surjectivity is the separably closed
etale lifting lemma. Source: Stacks Project, Tag 04FN.
(blueprint: lem-exc-sep-closed-etale-point-comparison) -/
noncomputable def sepClosedEtaleFiberIso :
    (pointSmallEtale s).fiber ≅ (pointSmallEtale s').fiber := by
  let b : Over.mk s' ⟶ Over.mk s := Over.homMk (Spec.map β) hβ
  let α : (pointSmallEtale s).fiber ⟶ (pointSmallEtale s').fiber :=
    Functor.whiskerLeft (Etale.forget S) (coyoneda.map b.op)
  have hbij (U : S.Etale) : Function.Bijective (α.app U) := by
    constructor
    · intro x y hxy
      apply Over.OverMorphism.ext
      exact SpecMap_comp_injective β (congrArg Over.Hom.left hxy)
    · intro x
      obtain ⟨y, hy, hys⟩ := U.hom.exists_SpecMap_comp_eq_of_isSepClosed β s x.left
        (by simpa [hβ] using x.w)
      exact ⟨Over.homMk y hys, Over.OverMorphism.ext hy⟩
  have : ∀ U, IsIso (α.app U) := fun U ↦
    (ConcreteCategory.isIso_iff_bijective _).mpr (hbij U)
  have : IsIso α := NatIso.isIso_of_isIso_app α
  exact asIso α

/-- The induced isomorphism of geometric points. Source: Stacks Project, Tag 04FN.
(blueprint: lem-exc-sep-closed-etale-point-comparison) -/
noncomputable def sepClosedEtalePointIso : pointSmallEtale s' ≅ pointSmallEtale s where
  hom := ⟨(sepClosedEtaleFiberIso s s' β hβ).hom⟩
  inv := ⟨(sepClosedEtaleFiberIso s s' β hβ).inv⟩
  hom_inv_id := GrothendieckTopology.Point.hom_ext
    (sepClosedEtaleFiberIso s s' β hβ).inv_hom_id
  inv_hom_id := GrothendieckTopology.Point.hom_ext
    (sepClosedEtaleFiberIso s s' β hβ).hom_inv_id

/-- Extension of a separably closed point does not change stalks in any category
with the required colimits. The inverse comes from the inverse bijection on lifts;
the point category identities prove the inverse identities on stalks.
Source: Stacks Project, Tag 04FN.
(blueprint: lem-exc-sep-closed-etale-point-comparison) -/
noncomputable def sepClosedEtaleStalkIso (B : Type w) [Category.{t} B]
    [Limits.HasColimitsOfSize.{u, u} B] :
    (pointSmallEtale s).sheafFiber (A := B) ≅ (pointSmallEtale s').sheafFiber where
  hom := (sepClosedEtalePointIso s s' β hβ).hom.sheafFiber
  inv := (sepClosedEtalePointIso s s' β hβ).inv.sheafFiber
  hom_inv_id := by
    rw [← GrothendieckTopology.Point.Hom.sheafFiber_comp, Iso.inv_hom_id,
      GrothendieckTopology.Point.Hom.sheafFiber_id]
  inv_hom_id := by
    rw [← GrothendieckTopology.Point.Hom.sheafFiber_comp, Iso.hom_inv_id,
      GrothendieckTopology.Point.Hom.sheafFiber_id]

/-- The stalk comparison keeps a representative and extends its lift.
Source: Stacks Project, Tag 04FN.
(blueprint: lem-exc-sep-closed-etale-point-comparison) -/
theorem sepClosedEtaleStalkIso_germ (B : Type w) [Category.{t} B]
    [Limits.HasColimitsOfSize.{u, u} B] (F : Sheaf S.smallEtaleTopology B)
    (U : S.Etale) (x : (pointSmallEtale s).fiber.obj U) :
    (pointSmallEtale s).toPresheafFiber U x F.obj ≫
      (sepClosedEtaleStalkIso s s' β hβ B).hom.app F =
        (pointSmallEtale s').toPresheafFiber U
          ((sepClosedEtaleFiberIso s s' β hβ).hom.app U x) F.obj := by
  exact (pointSmallEtale s).toPresheafFiber_presheafFiberDesc
    (fun V y ↦ (pointSmallEtale s').toPresheafFiber V
      ((sepClosedEtaleFiberIso s s' β hβ).hom.app V y) F.obj) (by
      intro V W f y
      rw [(pointSmallEtale s').toPresheafFiber_w]
      congr 1) U x

end AlgebraicGeometry.Scheme
