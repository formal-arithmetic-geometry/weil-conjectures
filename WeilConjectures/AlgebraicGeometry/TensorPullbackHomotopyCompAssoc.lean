/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction
public import Mathlib.Algebra.Homology.HomotopyCategory

/-! Associativity of the pinned tensor pullback comparisons on homotopy categories.

## References

* [Stacks Project, Tag 0D5S](https://stacks.math.columbia.edu/tag/0D5S)
-/

@[expose] public section

universe u₁
open CategoryTheory
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace AlgebraicGeometry

set_option maxHeartbeats 600000 in
-- Elaborating the six pinned adjunctions and termwise comparison needs a larger heartbeat budget.
/-- The tensor pullback composition mates are associative after passage to homotopy. -/
theorem tensorPullback_homotopy_comp_assoc
    (a : ∀ {X Y : Scheme.{u₁}} (f : X ⟶ Y), (Scheme.Modules.tensorPullback f).Additive)
    {W X Y Z : Scheme.{u₁}} (h : W ⟶ X) (f : X ⟶ Y) (g : Y ⟶ Z)
    (H : HomotopyCategory Z.Modules (ComplexShape.up ℤ)) :
    let T {X Y : Scheme.{u₁}} (f : X ⟶ Y) :=
    (Scheme.Modules.tensorPullback f).mapHomotopyCategory (ComplexShape.up ℤ)
    let t {X Y Z : Scheme.{u₁}} (f : X ⟶ Y) (g : Y ⟶ Z) :=
    Functor.mapHomotopyCategoryCompIso
      ((conjugateIsoEquiv
        (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction (f ≫ g)))
        ((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction g)).comp
          (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction f)))).symm
        (Scheme.Modules.pushforwardComp f g).symm) (ComplexShape.up ℤ)
    (T h).map ((t f g).hom.app H) ≫ (t h (f ≫ g)).hom.app H =
      (t h f).hom.app ((T g).obj H) ≫ (t (h ≫ f) g).hom.app H := by
  dsimp only
  let b {X Y : Scheme.{u₁}} (k : X ⟶ Y) :=
    Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction k)
  have hi := Adjunction.leftAdjointCompIso_assoc
    (b g) (b f) (b h) (b (f ≫ g)) (b (h ≫ f)) (b (h ≫ f ≫ g))
    (Scheme.Modules.pushforwardComp f g) (Scheme.Modules.pushforwardComp h f)
    (Scheme.Modules.pushforwardComp (h ≫ f) g)
    (Scheme.Modules.pushforwardComp h (f ≫ g)) (by
      ext M U
      simp)
  obtain ⟨P, rfl⟩ := HomotopyCategory.quotient_obj_surjective H
  let e {X Y Z : Scheme.{u₁}} (f : X ⟶ Y) (g : Y ⟶ Z) :=
    Adjunction.leftAdjointCompIso (b g) (b f) (b (f ≫ g))
      (Scheme.Modules.pushforwardComp f g)
  let U {X Y : Scheme.{u₁}} (f : X ⟶ Y) :=
    (Scheme.Modules.tensorPullback f).mapHomologicalComplex (ComplexShape.up ℤ)
  let tc {X Y Z : Scheme.{u₁}} (f : X ⟶ Y) (g : Y ⟶ Z) :=
    Functor.mapHomologicalComplexCompIso (e f g) (ComplexShape.up ℤ)
  let q := HomotopyCategory.quotient W.Modules (ComplexShape.up ℤ)
  change q.map ((U h).map ((tc f g).hom.app P)) ≫ q.map ((tc h (f ≫ g)).hom.app P) =
    q.map ((tc h f).hom.app ((U g).obj P)) ≫ q.map ((tc (h ≫ f) g).hom.app P)
  rw [← Functor.map_comp, ← Functor.map_comp]
  apply congrArg q.map
  ext i : 1
  have hh := congrArg (fun e ↦ e.hom.app (P.X i)) hi
  change (Scheme.Modules.tensorPullback h).map ((e f g).hom.app (P.X i)) ≫
      (e h (f ≫ g)).hom.app (P.X i) =
    (e h f).hom.app ((Scheme.Modules.tensorPullback g).obj (P.X i)) ≫
      (e (h ≫ f) g).hom.app (P.X i)
  simpa only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.associator_inv_app, Category.id_comp] using hh.symm

end AlgebraicGeometry
