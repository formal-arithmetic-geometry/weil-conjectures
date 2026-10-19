/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF worker H2
-/
module

public import Mathlib.RepresentationTheory.Rep.Basic
public import Mathlib.Algebra.Ring.ULift
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-!
# Representations and modules over a lifted group ring

Source: Stacks Project, Injectives, Section G-modules, immediately before Tag 04JF.
(blueprint: lem-exc-rg-representation-lifted-group-algebra-equivalence).
-/

@[expose] public section

universe u v w t

open CategoryTheory

namespace Rep

-- Extend the commuting coefficient and group actions to the group ring.
private noncomputable def actionAdd
    {R : Type u} [Ring R] {G : Type v} [Group G] (X : Rep.{w} R G) :
    G →* AddMonoid.End X where
  toFun g := (X.ρ g).toAddMonoidHom
  map_one' := by ext x; exact LinearMap.congr_fun X.ρ.map_one x
  map_mul' g h := by ext x; exact LinearMap.congr_fun (X.ρ.map_mul g h) x

private noncomputable def liftedAction
    {R : Type u} [Ring R] {G : Type v} [Group G] (X : Rep.{w} R G) :
    MonoidAlgebra (ULift.{t} R) G →+* AddMonoid.End X :=
  MonoidAlgebra.liftNCRingHom
    ((Module.toAddMonoidEnd R X).comp ULift.ringEquiv.toRingHom) (actionAdd X)
    (fun a g ↦ by
      ext x
      exact ((X.ρ g).map_smul a.down x).symm)

private noncomputable def liftedObj
    {R : Type u} [Ring R] {G : Type v} [Group G] (X : Rep.{w} R G) :
    ModuleCat.{w} (MonoidAlgebra (ULift.{t} R) G) :=
  letI := Module.compHom X (liftedAction X)
  ModuleCat.of _ X

private lemma lifted_single
    {R : Type u} [Ring R] {G : Type v} [Group G] (X : Rep.{w} R G) (g : G)
    (a : ULift.{t} R) (x : X) :
    (MonoidAlgebra.single g a) • (show liftedObj.{u, v, w, t} X from x) = a.down • X.ρ g x := by
  change liftedAction X (MonoidAlgebra.single g a) x = _
  unfold liftedAction
  rw [MonoidAlgebra.liftNCRingHom_single]
  rfl

private noncomputable def liftedMap
    {R : Type u} [Ring R] {G : Type v} [Group G] {X Y : Rep.{w} R G} (f : X ⟶ Y) :
    liftedObj.{u, v, w, t} X ⟶ liftedObj Y :=
  ModuleCat.ofHom (X := liftedObj.{u, v, w, t} X) (Y := liftedObj Y) {
    toFun := fun x ↦ f.hom x
    map_add' := fun x y ↦ f.hom.map_add x y
    map_smul' := by
      intro a x
      induction a using MonoidAlgebra.induction_linear with
      | zero => simp
      | add a b ha hb => simp only [add_smul, map_add, ha, hb]
      | single g r =>
        change f.hom (liftedAction X (MonoidAlgebra.single g r) x) =
          liftedAction Y (MonoidAlgebra.single g r) (f.hom x)
        simp only [liftedAction, MonoidAlgebra.liftNCRingHom_single]
        change f.hom (r.down • X.ρ g (show X from x)) = r.down • Y.ρ g (f.hom x)
        exact (f.hom.toLinearMap.map_smul r.down (X.ρ g x)).trans
          (congrArg (fun y ↦ r.down • y) (hom_comm_apply f g x))
  }

private noncomputable def liftedFunctor
    {R : Type u} [Ring R] {G : Type v} [Group G] : Rep.{w} R G ⥤
    ModuleCat.{w} (MonoidAlgebra (ULift.{t} R) G) where
  obj := liftedObj
  map := liftedMap
  map_id X := by ext x; rfl
  map_comp f g := by ext x; rfl

-- Restrict scalars to coefficients and recover the group action from basis elements.
private noncomputable def coeffInclusion
    {R : Type u} [Ring R] {G : Type v} [Group G] : R →+* MonoidAlgebra (ULift.{t} R) G :=
  MonoidAlgebra.singleOneRingHom.comp ULift.ringEquiv.symm.toRingHom

private noncomputable abbrev restrictedObj
    {R : Type u} [Ring R] {G : Type v} [Group G]
    (M : ModuleCat.{w} (MonoidAlgebra (ULift.{t} R) G)) :
    ModuleCat.{w} R :=
  (ModuleCat.restrictScalars (coeffInclusion (R := R) (G := G))).obj M

private noncomputable def restrictedAction
    {R : Type u} [Ring R] {G : Type v} [Group G]
    (M : ModuleCat.{w} (MonoidAlgebra (ULift.{t} R) G)) :
    Representation R G (restrictedObj M) where
  toFun g := {
    toFun := fun x ↦ MonoidAlgebra.single g (1 : ULift.{t} R) • (show M from x)
    map_add' := fun x y ↦ smul_add _ x y
    map_smul' := by
      intro r x
      change MonoidAlgebra.single g (1 : ULift.{t} R) •
        (coeffInclusion (G := G) r • (show M from x)) =
        coeffInclusion (G := G) r • (MonoidAlgebra.single g (1 : ULift.{t} R) • (show M from x))
      simp [coeffInclusion, ← mul_smul, MonoidAlgebra.single_mul_single]
  }
  map_one' := by
    ext x
    change MonoidAlgebra.single (1 : G) (1 : ULift.{t} R) • (show M from x) = x
    simp [← MonoidAlgebra.one_def]
  map_mul' g h := by
    ext x
    change MonoidAlgebra.single (g * h) (1 : ULift.{t} R) • (show M from x) =
      MonoidAlgebra.single g (1 : ULift.{t} R) •
        (MonoidAlgebra.single h (1 : ULift.{t} R) • (show M from x))
    simp [← mul_smul, MonoidAlgebra.single_mul_single]

private noncomputable def restrictedRep
    {R : Type u} [Ring R] {G : Type v} [Group G]
    (M : ModuleCat.{w} (MonoidAlgebra (ULift.{t} R) G)) :
    Rep.{w} R G := Rep.of (restrictedAction M)

private noncomputable def restrictedMap
    {R : Type u} [Ring R] {G : Type v} [Group G]
    {M N : ModuleCat.{w} (MonoidAlgebra (ULift.{t} R) G)} (f : M ⟶ N) :
    restrictedRep M ⟶ restrictedRep N :=
  Rep.ofHom {
    toFun := fun x ↦ f.hom x
    map_add' := fun x y ↦ f.hom.map_add x y
    map_smul' := fun r x ↦ f.hom.map_smul (coeffInclusion (G := G) r) x
    isIntertwining' g := by
      ext x
      exact f.hom.map_smul (MonoidAlgebra.single g 1) x
  }

private noncomputable def restrictedFunctor
    {R : Type u} [Ring R] {G : Type v} [Group G] :
    ModuleCat.{w} (MonoidAlgebra (ULift.{t} R) G) ⥤ Rep.{w} R G where
  obj := restrictedRep
  map := restrictedMap
  map_id M := by ext x; rfl
  map_comp f g := by ext x; rfl

-- Both composites have the original actions, so their comparison maps are identities.
private lemma recovered_scalar
    {R : Type u} [Ring R] {G : Type v} [Group G] (X : Rep.{w} R G) (r : R) (x : X) :
    r • (show restrictedRep (liftedObj.{u, v, w, t} X) from x) = r • x := by
  change MonoidAlgebra.single (1 : G) (ULift.up r : ULift.{t} R) •
    (show liftedObj.{u, v, w, t} X from x) = r • x
  rw [lifted_single]
  simp

private lemma recovered_group
    {R : Type u} [Ring R] {G : Type v} [Group G] (X : Rep.{w} R G) (g : G) (x : X) :
    (restrictedRep (liftedObj.{u, v, w, t} X)).ρ g x = X.ρ g x := by
  change MonoidAlgebra.single g (1 : ULift.{t} R) • (show liftedObj.{u, v, w, t} X from x) = _
  rw [lifted_single]
  simp

private noncomputable def liftedUnit
    {R : Type u} [Ring R] {G : Type v} [Group G] (X : Rep.{w} R G) :
    X ≅ restrictedRep (liftedObj.{u, v, w, t} X) :=
  Rep.mkIso <| Representation.Equiv.mk {
    toFun := fun x ↦ x
    invFun := fun x ↦ x
    left_inv := fun _ ↦ rfl
    right_inv := fun _ ↦ rfl
    map_add' := fun _ _ ↦ rfl
    map_smul' := fun r x ↦ (recovered_scalar.{u, v, w, t} X r x).symm
  } (fun g ↦ by ext x; exact (recovered_group.{u, v, w, t} X g x).symm)

private lemma recovered_algebra
    {R : Type u} [Ring R] {G : Type v} [Group G]
    (M : ModuleCat.{w} (MonoidAlgebra (ULift.{t} R) G))
    (a : MonoidAlgebra (ULift.{t} R) G) (x : M) :
    a • (show liftedObj (restrictedRep M) from x) = a • x := by
  induction a using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => simp only [add_smul, ha, hb]
  | single g r =>
    change liftedAction (restrictedRep M) (MonoidAlgebra.single g r) x = _
    unfold liftedAction
    rw [MonoidAlgebra.liftNCRingHom_single]
    change MonoidAlgebra.single (1 : G) (ULift.up r.down : ULift.{t} R) •
      (MonoidAlgebra.single g (1 : ULift.{t} R) • x) = MonoidAlgebra.single g r • x
    simp [← mul_smul, MonoidAlgebra.single_mul_single]

private noncomputable def liftedCounit
    {R : Type u} [Ring R] {G : Type v} [Group G]
    (M : ModuleCat.{w} (MonoidAlgebra (ULift.{t} R) G)) :
    liftedObj (restrictedRep M) ≅ M :=
  LinearEquiv.toModuleIso (R := MonoidAlgebra (ULift.{t} R) G)
    (X₁ := liftedObj (restrictedRep M)) (X₂ := M) {
    toFun := fun x ↦ (show M from x)
    invFun := fun x ↦ (show liftedObj (restrictedRep M) from x)
    left_inv := fun _ ↦ rfl
    right_inv := fun _ ↦ rfl
    map_add' := fun _ _ ↦ rfl
    map_smul' := fun a x ↦ recovered_algebra M a x
  }

/-- The representation/group-ring equivalence does not change the carrier universe.
The group ring acts by finite sums of coefficient multiples of translates, and restriction
recovers the original actions. The identity maps give the unit and counit, exactly as in
the lifted equivalence below. No size assumption is needed for an equivalence; size is
needed only when applying an existence theorem for injective modules.

Source: Stacks Project, Injectives, Section G-modules, immediately before Tag 04JF
(blueprint: lem-exc-rg-representation-lifted-group-algebra-equivalence). -/
theorem representation_liftedGroupAlgebra_equivalence_anyUniverse
    (R : Type u) [Ring R] (G : Type v) [Group G] :
    Nonempty (Rep.{w} R G ≌ ModuleCat.{w} (MonoidAlgebra (ULift.{t} R) G)) := by
  exact ⟨{
    functor := liftedFunctor
    inverse := restrictedFunctor
    unitIso := NatIso.ofComponents (liftedUnit.{u, v, w, t}) (by intro X Y f; ext x; rfl)
    counitIso := NatIso.ofComponents liftedCounit (by intro X Y f; ext x; rfl)
    functor_unitIso_comp X := by ext x; rfl
  }⟩

/-- (blueprint: lem-exc-rg-representation-lifted-group-algebra-equivalence)
Source: Stacks Project, Injectives, Section G-modules, immediately before Tag 04JF:
R-linear G-actions are the same as modules over the group ring.

Proof: replace R by its isomorphic lifted ring using the ring isomorphism
`ULift.ringEquiv`. On a representation V, let a group-ring element act by the finite
sum of its coefficients acting on the corresponding translates of V. The representation
law, R-linearity of the action, and the convolution multiplication prove the module
laws, including for noncommutative R: the group action commutes with all R-scalars.
An intertwining map commutes with this finite sum and is therefore group-ring linear.
Conversely restrict a group-ring module along the inclusion of R and let g act by the
singleton basis element at g with coefficient 1. Multiplication of these basis elements
proves the action law; they commute with constant coefficients, proving R-linearity.
A group-ring linear map is then an intertwining map. Restriction followed by extension
recovers the original action, and extension followed by restriction recovers the original
module action by expansion in singleton basis elements. Identity maps on the underlying
additive groups give the natural unit and counit isomorphisms and their triangle laws.
No carrier changes universe: all carriers lie in max u v w, and the coefficient lift
merely allows the group-ring embedding theorem to run at this same carrier universe. -/
theorem representation_liftedGroupAlgebra_equivalence
    (R : Type u) [Ring R] (G : Type v) [Group G] :
    Nonempty (Rep.{max u v w} R G ≌
      ModuleCat.{max u v w} (MonoidAlgebra (ULift.{w} R) G)) := by
  exact representation_liftedGroupAlgebra_equivalence_anyUniverse.{u, v, max u v w, w} R G

end Rep
