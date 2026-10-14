/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.SingleComplexBaseChangeStalkCondition
public import Sheaf.AlgebraicGeometry.CanonicalPullbackTensorComparison
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Adjunction
public import WeilConjectures.Algebra.Homology.Monoidal.MapHomologicalComplex
public import Sheaf.AlgebraicGeometry.PinnedStalkTensor
import Sheaf.AlgebraicGeometry.ModulePinnedTensorStalkSquare
import Sheaf.AlgebraicGeometry.ModulePullbackTensor
import Sheaf.Algebra.Category.ModuleCat.Sheaf.StalkTensor
import Sheaf.AlgebraicGeometry.Modules.TensorPullbackStalk

/-! # Stalk compatibility of a specified tensor pullback chain map

Source: Stacks Project, perfect.tex, Tag 0DJA(1), using Tag 0BYJ.
(blueprint: lem-pc-pinned-tensor-square-left-summand).
-/

@[expose] public section

universe u w
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open AlgebraicGeometry
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace AlgebraicGeometry

@[instance_reducible] local instance pinnedTensorSquareLeftSummandInstance1 (Y : Scheme.{u}) :
    MonoidalCategory (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) :=
  SheafOfModules.monoidalCategory Y.sheaf

local instance pinnedTensorSquareLeftSummandInstance2 (Y : Scheme.{u}) :
    MonoidalPreadditive (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) :=
  modulePreadditive Y

local instance pinnedTensorSquareLeftSummandInstance3
    (Y : Scheme.{u}) : (curriedTensor Y.Modules).PreservesZeroMorphisms :=
  SheafOfModules.preservesZeroMorphisms_curriedTensor Y.sheaf

local instance pinnedTensorSquareLeftSummandInstance4 (Y : Scheme.{u}) (M : Y.Modules) :
    ((curriedTensor Y.Modules).obj M).PreservesZeroMorphisms :=
  SheafOfModules.preservesZeroMorphisms_curriedTensor_obj Y.sheaf M

/-- Pullback route on one tensor summand, in explicit stalk coordinates.

Proof: invert the pinned source injection equation by cancelling its degree-n hom.
Map this equation under scalar extension. Rewrite the degree-n pullback-stalk
comparison using its specified component. Its naturality moves the sheaf tensor
summand injection through this comparison; the restriction equation for the actual
ring map identifies scalar extension with extension along g'.stalkMap z. Map hχ under
the target stalk functor. The bifunctor-map summand equation moves identity tensor a
to identity tensor a.f q. The target module tensor-stalk naturality equation then
moves this map to identity tensor S(a)_q. The target pinned injection equation
identifies its injection followed by e'.hom_n. The module tensor pullback/stalk
square on P.X p and Q.X q gives δ_G followed by κ_P,p tensor κ_Q,q: represent the two
stalk vectors by sections on a common neighborhood, use the canonical tensor-stalk
and pullback tensor generator formulas, and check the scalar-extension tensorator
on one tensor a pure tensor. Extension-of-scalars extensionality and tensor induction
extend this equality to every element of this single summand. A categorical diagram
chase combines the six equations after postcomposition with e'.hom_n, and cancels
e'.inv_n followed by e'.hom_n to obtain the displayed formula. No coproduct
extensionality or chain-map
extensionality occurs here. Zero stalk rings, zero modules, and unbounded complexes
are allowed, since the calculation is in the two modules in degrees p and q.
Source: Stacks Project, perfect.tex, Tag 0DJA(1), using Tag 0BYJ; Modules, Tags 01CD
and 01CB; Sheaves, Tag 0098.
(blueprint: lem-pc-pinned-tensor-square-left-summand). -/
theorem pinned_tensor_square_left_summand
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X X' S S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (sq : IsPullback g' f' f g)
    (P Q : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (N : CochainComplex (SheafOfModules.{u} (moduleRings X'.toRingedSpace)) ℤ)
    (a : ((Scheme.Modules.tensorPullback g').mapHomologicalComplex (.up ℤ)).obj Q ⟶ N)
    (χ : ((Scheme.Modules.tensorPullback g').mapHomologicalComplex (.up ℤ)).obj
        (pullbackTensorTotal X P Q) ≅
      pullbackTensorTotal X'
        (((Scheme.Modules.tensorPullback g').mapHomologicalComplex (.up ℤ)).obj P)
        (((Scheme.Modules.tensorPullback g').mapHomologicalComplex (.up ℤ)).obj Q))
    (hχ : ∀ (p q n : ℤ) (h : p + q = n),
      (Scheme.Modules.tensorPullback g').map
          (HomologicalComplex.ιMapBifunctor P Q (curriedTensor _) (.up ℤ) p q n h) ≫
        χ.hom.f n =
      ((Classical.choose (Scheme.Modules.module_pullback_tensor g')) (P.X p) (Q.X q)).hom ≫
        HomologicalComplex.ιMapBifunctor
          (((Scheme.Modules.tensorPullback g').mapHomologicalComplex (.up ℤ)).obj P)
          (((Scheme.Modules.tensorPullback g').mapHomologicalComplex (.up ℤ)).obj Q)
          (curriedTensor _) (.up ℤ) p q n h) (z : X') (n p q : ℤ) (h : p + q = n) :
    letI := SingleComplexBaseChange.leftAlgebra f g' z
    letI := SingleComplexBaseChange.rightAlgebra f f' g g' sq z
    letI := (SingleComplexBaseChange.tensorMap f f' g g' sq z).toAlgebra
    let R := SingleComplexBaseChange.R f g' z
    let A := SingleComplexBaseChange.A g' z
    let B := SingleComplexBaseChange.B f' z
    let C := SingleComplexBaseChange.C z
    let F := (ModuleCat.extendScalars.{u, u, u}
      ((algebraMap (TensorProduct R A B) C).comp
        (algebraMap A (TensorProduct R A B)))).mapHomologicalComplex (.up ℤ)
    let S := (RingedSpace.moduleStalkFunctor X'.toRingedSpace z).mapHomologicalComplex
      (.up ℤ)
    let U := SingleComplexBaseChange.stalkComplex g' z P
    let V := SingleComplexBaseChange.stalkComplex g' z Q
    let H := (Scheme.Modules.tensorPullback g').mapHomologicalComplex (.up ℤ)
    let e := Classical.choose (exists_pinned_stalk_tensor X (g' z))
    let e' := Classical.choose (exists_pinned_stalk_tensor X' z)
    let σ : U ⊗ V ≅ SingleComplexBaseChange.stalkComplex g' z
      (pullbackTensorTotal X P Q) := (e P Q).symm
    let G := ModuleCat.extendScalars.{u, u, u}
      ((algebraMap (TensorProduct R A B) C).comp
        (algebraMap A (TensorProduct R A B)))
    let ι := G.map (HomologicalComplex.ιMapBifunctor U V
      (curriedTensor _) (.up ℤ) p q n h)
    ι ≫ (F.map σ.hom ≫
          (SingleComplexBaseChange.tensorStalkIso f f' g g' sq z
            (pullbackTensorTotal X P Q)).hom ≫
          S.map (χ.hom ≫
            HomologicalComplex.mapBifunctorMap (𝟙 _) a (curriedTensor _) (.up ℤ))).f n =
      Functor.OplaxMonoidal.δ G (U.X p) (V.X q) ≫
      ((SingleComplexBaseChange.tensorStalkIso f f' g g' sq z P).hom.f p ⊗ₘ
        (SingleComplexBaseChange.tensorStalkIso f f' g g' sq z Q).hom.f q) ≫
      (𝟙 _ ⊗ₘ (S.map a).f q) ≫
      HomologicalComplex.ιMapBifunctor (S.obj (H.obj P)) (S.obj N)
        (curriedTensor _) (.up ℤ) p q n h ≫ (e' (H.obj P) N).inv.f n := by sorry

end AlgebraicGeometry
