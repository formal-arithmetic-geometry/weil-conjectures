/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q3
-/
module

public import Sheaf.CategoryTheory.ScalarModuleSheaves
public import Sheaf.CategoryTheory.ScalarDiscreteRepresentations
public import Mathlib.CategoryTheory.Sites.Point.Basic
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.Algebra.Category.Grp.AB

/-! # Scalar enhancement of a geometric stalk equivalence

Source: Stacks Project, Tag 04JQ, transport of scalars across the abelian equivalence.
(blueprint: lem-exc-scalar-stalk-transport)
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u v
open CategoryTheory Opposite

namespace CategoryTheory.ScalarObject

variable {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
  (p : GrothendieckTopology.Point.{u} J)
  (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (R : Type v) [CommRing R]


/-- Scalar multiplication is a morphism of module sheaves over a commutative ring. -/
def moduleSheafScalar (F : Sheaf J (ModuleCat.{max (u + 1) v} R)) (a : R) : F ⟶ F :=
  ⟨{ app := fun U ↦ ModuleCat.ofHom (a • LinearMap.id)
     naturality := fun U V f ↦ by ext x; exact ((F.obj.map f).hom.map_smul a x).symm }⟩

/-- A module stalk takes the scalar sheaf map to scalar multiplication. -/
theorem sheafFiber_moduleSheafScalar (F : Sheaf J (ModuleCat.{max (u + 1) v} R))
    (a : R) (x : (p.sheafFiber (A := ModuleCat.{max (u + 1) v} R)).obj F) :
    p.sheafFiber.map (moduleSheafScalar J R F a) x = a • x := by
  let : Limits.PreservesColimitsOfSize.{u, u}
      (forget₂ (ModuleCat.{max (u + 1) v} R) AddCommGrpCat.{max (u + 1) v}) :=
    ModuleCat.forget₂PreservesColimitsOfSize.{max (u + 1) v, v, u, u} R
  let : Limits.PreservesFilteredColimitsOfSize.{u, u}
      (CategoryTheory.forget AddCommGrpCat.{max (u + 1) v}) :=
    Limits.preservesFilteredColimitsOfSize_shrink.{u, max (u + 1) v, u, max (u + 1) v} _
  let : Limits.PreservesFilteredColimitsOfSize.{u, u}
      (CategoryTheory.forget (ModuleCat.{max (u + 1) v} R)) := Limits.comp_preservesFilteredColimits
    (forget₂ (ModuleCat.{max (u + 1) v} R) AddCommGrpCat.{max (u + 1) v})
    (CategoryTheory.forget AddCommGrpCat.{max (u + 1) v})
  obtain ⟨U, z, t, rfl⟩ := p.toPresheafFiber_jointly_surjective (P := F.obj) x
  change p.presheafFiber.map (moduleSheafScalar J R F a).hom
    (p.toPresheafFiber U z F.obj t) = a • p.toPresheafFiber U z F.obj t
  rw [p.toPresheafFiber_naturality_apply]
  exact (p.toPresheafFiber U z F.obj).hom.map_smul a t

/-- An abelian stalk equivalence lifts to module sheaves, with the same underlying
stalk comparison. Transport scalar actions through the endomorphism ring equivalence.
Naturality of the abelian comparison for the scalar sheaf maps proves linearity.
The comparison of stalks with forgetting scalars preserves germs and is bijective;
hence its linear lift is a natural isomorphism.
Source: Stacks Project, Tag 04JQ.
(blueprint: lem-exc-scalar-stalk-transport) -/
theorem scalarStalkTransport :
    let D := Rep.DiscreteContinuousRep.{0, u, max (u + 1) v} ℤ G
    let H : D ⥤ AddCommGrpCat.{max (u + 1) v} := ObjectProperty.ι _ ⋙
      Rep.RepToAction ℤ G ⋙ Action.forget (ModuleCat.{max (u + 1) v} ℤ) G ⋙
      forget₂ (ModuleCat.{max (u + 1) v} ℤ) AddCommGrpCat
    let Q := sheafCompose J (forget₂ (ModuleCat.{max (u + 1) v} R) AddCommGrpCat)
    let W : Rep.DiscreteContinuousRep.{v, u, max (u + 1) v} R G ⥤
        ModuleCat.{max (u + 1) v} R := ObjectProperty.ι _ ⋙
      Rep.RepToAction R G ⋙ Action.forget (ModuleCat.{max (u + 1) v} R) G
    ∀ (E : Sheaf J AddCommGrpCat.{max (u + 1) v} ≌ D)
      (i : E.functor ⋙ H ≅ p.sheafFiber),
    ∃ (T : Sheaf J (ModuleCat.{max (u + 1) v} R) ≌
        Rep.DiscreteContinuousRep.{v, u, max (u + 1) v} R G)
      (j : T.functor ⋙ W ≅ p.sheafFiber),
      ∀ (F : Sheaf J (ModuleCat.{max (u + 1) v} R)) (g : G)
          (X : C) (x x' : p.fiber.obj X) (z : F.obj.obj (op X)),
        (i.hom.app (Q.obj F)) ((E.functor.obj (Q.obj F)).obj.ρ g
          ((i.inv.app (Q.obj F)) (p.toPresheafFiber X x (Q.obj F).obj z))) =
            p.toPresheafFiber X x' (Q.obj F).obj z →
        (j.hom.app F) ((T.functor.obj F).obj.ρ g
          ((j.inv.app F) (p.toPresheafFiber X x F.obj z))) =
            p.toPresheafFiber X x' F.obj z := by
  classical
  dsimp only
  intro E i
  let Q := sheafCompose J (forget₂ (ModuleCat.{max (u + 1) v} R) AddCommGrpCat)
  let H := (ObjectProperty.ι
    (fun M : Rep.{max (u + 1) v} ℤ G ↦ ∀ x : M.V, IsOpen {g : G | M.ρ g x = x})) ⋙
    Rep.RepToAction ℤ G ⋙ Action.forget (ModuleCat.{max (u + 1) v} ℤ) G ⋙
    forget₂ (ModuleCat.{max (u + 1) v} ℤ) AddCommGrpCat
  let W := (ObjectProperty.ι
    (fun M : Rep.{max (u + 1) v} R G ↦ ∀ x : M.V, IsOpen {g : G | M.ρ g x = x})) ⋙
    Rep.RepToAction R G ⋙ Action.forget (ModuleCat.{max (u + 1) v} R) G
  let : Limits.HasFiniteBiproducts (Sheaf J AddCommGrpCat.{max (u + 1) v}) :=
    Limits.HasFiniteBiproducts.of_hasFiniteProducts
  let : E.functor.Additive := Functor.additive_of_preserves_binary_products E.functor
  let T := ((moduleSheafEquivalence.{u + 1, u, v} J R).trans
    (equivalence (R := R) E)).trans (discreteRepEquivalence.{v, u, max (u + 1) v} R G).symm
  let γ := p.sheafFiberCompIso (forget₂ (ModuleCat.{max (u + 1) v} R) AddCommGrpCat)
  let α : Q ⋙ E.functor ⋙ H ≅ p.sheafFiber ⋙
      forget₂ (ModuleCat.{max (u + 1) v} R) AddCommGrpCat :=
    Functor.isoWhiskerLeft Q i ≪≫ γ
  have hlin (F : Sheaf J (ModuleCat.{max (u + 1) v} R)) (a : R)
      (x : (T.functor.obj F).obj.V) :
      (α.hom.app F) (a • x) =
        a • (show (p.sheafFiber (A := ModuleCat.{max (u + 1) v} R)).obj F from
          (α.hom.app F) x) := by
    have h := ConcreteCategory.congr_hom (α.hom.naturality (moduleSheafScalar J R F a)) x
    change (α.hom.app F) (a • x) =
      p.sheafFiber.map (moduleSheafScalar J R F a) ((α.hom.app F) x) at h
    rw [sheafFiber_moduleSheafScalar] at h
    exact h
  let f (F : Sheaf J (ModuleCat.{max (u + 1) v} R)) :
      (T.functor ⋙ W).obj F ⟶ p.sheafFiber.obj F := ModuleCat.ofHom
    { toFun := α.hom.app F
      map_add' := map_add _
      map_smul' := hlin F }
  let j : T.functor ⋙ W ≅ p.sheafFiber := NatIso.ofComponents
    (fun F ↦ (LinearEquiv.ofBijective (f F).hom
      (ConcreteCategory.bijective_of_isIso (α.hom.app F))).toModuleIso)
    (fun {F F'} q ↦ by
      ext x
      exact ConcreteCategory.congr_hom (α.hom.naturality q) x)
  refine ⟨T, j, ?_⟩
  intro F g X x x' z hi
  have hj (t : (T.functor.obj F).obj.V) :
      (j.hom.app F) t = (γ.hom.app F) ((i.hom.app (Q.obj F)) t) := rfl
  have hγ (y : p.fiber.obj X) :
      (γ.hom.app F) (p.toPresheafFiber X y (Q.obj F).obj z) =
        p.toPresheafFiber X y F.obj z :=
    ConcreteCategory.congr_hom
      (p.toPresheafFiber_presheafFiberCompIso_hom_app
        (forget₂ (ModuleCat.{max (u + 1) v} R) AddCommGrpCat) X y F.obj) z
  have hinv : (j.inv.app F) (p.toPresheafFiber X x F.obj z) =
      (i.inv.app (Q.obj F)) (p.toPresheafFiber X x (Q.obj F).obj z) := by
    apply (ConcreteCategory.bijective_of_isIso (j.hom.app F)).1
    rw [j.inv_hom_id_app_apply, hj, i.inv_hom_id_app_apply, hγ]
  rw [hinv, hj]
  change (γ.hom.app F) ((i.hom.app (Q.obj F))
    ((E.functor.obj (Q.obj F)).obj.ρ g
      ((i.inv.app (Q.obj F)) (p.toPresheafFiber X x (Q.obj F).obj z)))) = _
  rw [hi, hγ]

end CategoryTheory.ScalarObject
