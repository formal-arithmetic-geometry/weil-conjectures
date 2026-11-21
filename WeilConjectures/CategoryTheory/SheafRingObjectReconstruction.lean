/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Sites.CartesianMonoidal
public import Mathlib.CategoryTheory.Sites.Whiskering
public import Mathlib.CategoryTheory.Monoidal.Ring
public import Mathlib.Algebra.Category.Ring.Limits

/-!
# Sectionwise reconstruction of a commutative ring sheaf

## References

* Stacks Project, Section 00YR, proof of Proposition 00YV (rings as sextuples).
-/

@[expose] public section

universe u v w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable (R : CommRingObjCat (Sheaf J (Type (max u v w)))) (U : Cᵒᵖ)
private abbrev sadd (a b : R.X.obj.obj U) : R.X.obj.obj U :=
  (AddMonObj.add (X := R.X)).hom.app U (a, b)
private abbrev szero : R.X.obj.obj U :=
  (AddMonObj.zero (X := R.X)).hom.app U PUnit.unit
private abbrev sneg (a : R.X.obj.obj U) : R.X.obj.obj U :=
  (AddGrpObj.neg (X := R.X)).hom.app U a
private abbrev smul (a b : R.X.obj.obj U) : R.X.obj.obj U :=
  (MonObj.mul (X := R.X)).hom.app U (a, b)
private abbrev sone : R.X.obj.obj U :=
  (MonObj.one (X := R.X)).hom.app U PUnit.unit

private abbrev sectionAddGroup : AddCommGroup (R.X.obj.obj U) where
  add := sadd R U
  zero := szero R U
  neg := sneg R U
  add_assoc a b c := congrArg (fun f => f.hom.app U ((a, b), c))
    (AddMonObj.add_assoc R.X)
  zero_add a := congrArg (fun f => f.hom.app U (PUnit.unit, a))
    (AddMonObj.zero_add R.X)
  add_zero a := congrArg (fun f => f.hom.app U (a, PUnit.unit))
    (AddMonObj.add_zero R.X)
  add_comm a b := (congrArg (fun f => f.hom.app U (a, b))
    (IsCommAddMonObj.add_comm R.X)).symm
  neg_add_cancel a := congrArg (fun f => f.hom.app U a) (AddGrpObj.left_neg R.X)
  nsmul := @nsmulRec _ ⟨szero R U⟩ ⟨sadd R U⟩
  zsmul := @zsmulRec _ ⟨szero R U⟩ ⟨sadd R U⟩ ⟨sneg R U⟩
    (@nsmulRec _ ⟨szero R U⟩ ⟨sadd R U⟩)

private abbrev sectionMonoid : CommMonoid (R.X.obj.obj U) where
  mul := smul R U
  one := sone R U
  mul_assoc a b c := congrArg (fun f => f.hom.app U ((a, b), c))
    (MonObj.mul_assoc R.X)
  one_mul a := congrArg (fun f => f.hom.app U (PUnit.unit, a))
    (MonObj.one_mul R.X)
  mul_one a := congrArg (fun f => f.hom.app U (a, PUnit.unit))
    (MonObj.mul_one R.X)
  mul_comm a b := (congrArg (fun f => f.hom.app U (a, b))
    (IsCommMonObj.mul_comm R.X)).symm

private abbrev sectionCommRing : CommRing (R.X.obj.obj U) := by
  letI := sectionAddGroup R U
  letI := sectionMonoid R U
  exact {
    left_distrib := fun a b c => congrArg (fun f => f.hom.app U (a, (b, c)))
      (RingObj.mul_add R.X)
    right_distrib := fun a b c => congrArg (fun f => f.hom.app U ((a, b), c))
      (RingObj.add_mul R.X)
    mul_zero := by
      intro a
      have h : a * (0 + 0) = a * 0 + a * 0 :=
        congrArg (fun f => f.hom.app U (a, (0, 0))) (RingObj.mul_add R.X)
      simpa using h
    zero_mul := by
      intro a
      have h : (0 + 0) * a = 0 * a + 0 * a :=
        congrArg (fun f => f.hom.app U ((0, 0), a)) (RingObj.add_mul R.X)
      simpa using h }

private def reconstructedPresheaf
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    (R : CommRingObjCat (Sheaf J (Type (max u v w)))) :
    Cᵒᵖ ⥤ CommRingCat.{max u v w} where
  obj U := @CommRingCat.of (R.X.obj.obj U) (sectionCommRing R U)
  map {U V} f := by
    letI := sectionCommRing R U
    letI := sectionCommRing R V
    exact CommRingCat.ofHom {
      toFun := R.X.obj.map f
      map_zero' := (congrArg (fun g => g PUnit.unit)
        ((AddMonObj.zero (X := R.X)).hom.naturality f)).symm
      map_one' := (congrArg (fun g => g PUnit.unit)
        ((MonObj.one (X := R.X)).hom.naturality f)).symm
      map_add' := fun a b => (congrArg (fun g => g (a, b))
        ((AddMonObj.add (X := R.X)).hom.naturality f)).symm
      map_mul' := fun a b => (congrArg (fun g => g (a, b))
        ((MonObj.mul (X := R.X)).hom.naturality f)).symm }
  map_id U := by
    ext x
    exact congrArg (fun g => g x) (R.X.obj.map_id U)
  map_comp f g := by
    ext x
    exact congrArg (fun k => k x) (R.X.obj.map_comp f g)

/-- An internal commutative ring object can be realized on exactly the same
underlying sheaf by a sheaf of commutative rings.

Stacks Project, Section 00YR, proof of Proposition 00YV (rings as sextuples). -/
theorem sheafRingObject_sectionwise_reconstruction
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    (R : CommRingObjCat (Sheaf J (Type (max u v w)))) :
    ∃ (A : Sheaf J CommRingCat.{max u v w})
      (h : R.X = (sheafCompose J (forget CommRingCat.{max u v w})).obj A),
      ∀ (U : Cᵒᵖ),
        (∀ a b : R.X.obj.obj U,
          (eqToIso h).hom.hom.app U ((AddMonObj.add (X := R.X)).hom.app U (a, b)) =
            (show A.obj.obj U from (eqToIso h).hom.hom.app U a) +
              (show A.obj.obj U from (eqToIso h).hom.hom.app U b)) ∧
        (∀ t : (𝟙_ (Sheaf J (Type (max u v w)))).obj.obj U,
          (eqToIso h).hom.hom.app U ((AddMonObj.zero (X := R.X)).hom.app U t) =
            (0 : A.obj.obj U)) ∧
        (∀ a : R.X.obj.obj U,
          (eqToIso h).hom.hom.app U ((AddGrpObj.neg (X := R.X)).hom.app U a) =
            -(show A.obj.obj U from (eqToIso h).hom.hom.app U a)) ∧
        (∀ a b : R.X.obj.obj U,
          (eqToIso h).hom.hom.app U ((MonObj.mul (X := R.X)).hom.app U (a, b)) =
            (show A.obj.obj U from (eqToIso h).hom.hom.app U a) *
              (show A.obj.obj U from (eqToIso h).hom.hom.app U b)) ∧
        (∀ t : (𝟙_ (Sheaf J (Type (max u v w)))).obj.obj U,
          (eqToIso h).hom.hom.app U ((MonObj.one (X := R.X)).hom.app U t) =
            (1 : A.obj.obj U)) := by
  let P := reconstructedPresheaf R
  have hP : P ⋙ forget CommRingCat.{max u v w} = R.X.obj := by
    refine Functor.ext (fun U => rfl) ?_
    intro U V f
    rfl
  have hSheaf : Presheaf.IsSheaf J P := by
    let : HasLimitsOfSize.{v, max v u} CommRingCat.{max u v w} :=
      hasLimitsOfSizeShrink.{v, max v u, max u v w, max u v w} _
    let : PreservesLimitsOfSize.{v, max v u} (forget CommRingCat.{max u v w}) :=
      preservesLimitsOfSize_shrink.{max v u, max u v w, v, max u v w} _
    let : ReflectsLimitsOfSize.{v, max v u} (forget CommRingCat.{max u v w}) :=
      reflectsLimits_of_reflectsIsomorphisms
    apply Presheaf.isSheaf_of_isSheaf_comp J P (forget CommRingCat.{max u v w})
    rw [hP]
    exact R.X.property
  let A : Sheaf J CommRingCat.{max u v w} := ⟨P, hSheaf⟩
  have h : R.X = (sheafCompose J (forget CommRingCat.{max u v w})).obj A := by
    rfl
  refine ⟨A, h, ?_⟩
  intro U
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro a b
    rfl
  · intro t
    cases t
    rfl
  · intro a
    rfl
  · intro a b
    rfl
  · intro t
    cases t
    rfl

end CategoryTheory
