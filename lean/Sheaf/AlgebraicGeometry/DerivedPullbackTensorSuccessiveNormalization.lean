/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.MixedHomTensorPullbackIso

/-! # Normalization of the successive tensor pullback route

Source: Stacks Project, cohomology.tex, Tags 079U, 08HY and 0D5S.
(blueprint: lem-sc-derived-pullback-tensor-successive-normalization).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
universe u w
open CategoryTheory MonoidalCategory
noncomputable section
namespace AlgebraicGeometry
variable [∀ Z : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]

/-- Normalization of the successive tensor-pullback route on K-flat complexes.
Source: Stacks Project, cohomology.tex, Tags 079U and 0D5S.
(blueprint: lem-sc-derived-pullback-tensor-successive-normalization).

Proof: normalize the g tensorator and the f tensorator by their defining K-flat
coordinate equations. Naturality of the f tensorator moves the g counits to
its inputs. The factorization equation for the composition comparison at P and N
turns the final composite-arrow counits into the successive counits followed by
the ordinary pullback composition maps. Naturality of the localization tensor
map moves these composition maps to the total complex. At each (p,q) summand,
the ordinary tensor composition equation identifies the resulting map with the
given phi: transpose under the pinned tensor-pullback adjunctions and test on
pure tensor sections. Both transposes send s tensor t to the tensor of the same
successive unit images. Tensor universality and the adjunction bijection prove
the module equality; joint epimorphy of the total-complex summand inclusions
proves the chain equality. Localize it. This proves only the successive route's
normalization; comparison with the direct derived tensorator and cancellation
are performed in the importing theorem. Zero complexes and identity morphisms
satisfy the same calculation, as do the unique maps on empty schemes.
-/
theorem derivedPullback_tensor_successive_normalization
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (P N : CochainComplex (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) ℤ)
    (hP : P.IsKFlat) (hN : N.IsKFlat)
    (φ : ((Scheme.Modules.tensorPullback (f ≫ g)).mapHomologicalComplex (.up ℤ)).obj
        (pullbackTensorTotal Z P N) ≅
      pullbackTensorTotal X
        (((Scheme.Modules.tensorPullback (f ≫ g)).mapHomologicalComplex (.up ℤ)).obj P)
        (((Scheme.Modules.tensorPullback (f ≫ g)).mapHomologicalComplex (.up ℤ)).obj N))
    (hφ :
      letI := pullbackDescentModuleTensor Z
      letI := pullbackDescentModuleTensor X
      letI := SheafOfModules.preservesZeroMorphisms_curriedTensor Z.sheaf
      letI := SheafOfModules.preservesZeroMorphisms_curriedTensor X.sheaf
      letI := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj Z.sheaf
      letI := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj X.sheaf
      ∀ (p q n : ℤ) (h : p + q = n),
        (Scheme.Modules.tensorPullback (f ≫ g)).map
            (HomologicalComplex.ιMapBifunctor P N (curriedTensor _) (.up ℤ) p q n h) ≫
          φ.hom.f n =
        ((Classical.choose (Scheme.Modules.module_pullback_tensor (f ≫ g)))
          (P.X p) (N.X q)).hom ≫
          HomologicalComplex.ιMapBifunctor
            (((Scheme.Modules.tensorPullback (f ≫ g)).mapHomologicalComplex (.up ℤ)).obj P)
            (((Scheme.Modules.tensorPullback (f ≫ g)).mapHomologicalComplex (.up ℤ)).obj N)
            (curriedTensor (SheafOfModules.{u} (moduleRings X.toRingedSpace)))
            (.up ℤ) p q n h) :
    let c : ∀ {U V W : Scheme.{u}} (a : U ⟶ V) (b : V ⟶ W),
        derivedPullback b ⋙ derivedPullback a ≅ derivedPullback (a ≫ b) :=
      fun a b ↦ (Classical.choose (Classical.choose_spec (Classical.choose_spec
        (Classical.choose_spec exists_derivedPullbackComposition)))) a b
    let H := (HomotopyCategory.quotient _ (.up ℤ)).obj (pullbackTensorTotal Z P N)
    let β := Functor.mapHomotopyCategoryCompIso
      ((conjugateIsoEquiv
        (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction (f ≫ g)))
        ((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction g)).comp
          (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction f)))).symm
        (Scheme.Modules.pushforwardComp f g).symm) (.up ℤ)
    ((derivedPullback f).map ((mixedHomTensorPullbackIso g).hom.app
        (DerivedCategory.Q.obj P, DerivedCategory.Q.obj N)) ≫
      (mixedHomTensorPullbackIso f).hom.app
        ((derivedPullback g).obj (DerivedCategory.Q.obj P),
          (derivedPullback g).obj (DerivedCategory.Q.obj N)) ≫
      ((c f g).hom.app (DerivedCategory.Q.obj P) ⊗ₘ
        (c f g).hom.app (DerivedCategory.Q.obj N))) ≫
      (((SingleComplexBaseChange.counit (f ≫ g)).app
          ((HomotopyCategory.quotient _ (.up ℤ)).obj P) ⊗ₘ
        (SingleComplexBaseChange.counit (f ≫ g)).app
          ((HomotopyCategory.quotient _ (.up ℤ)).obj N)) ≫
        pullbackTensorModelMap X
          (((Scheme.Modules.tensorPullback (f ≫ g)).mapHomologicalComplex (.up ℤ)).obj P)
          (((Scheme.Modules.tensorPullback (f ≫ g)).mapHomologicalComplex (.up ℤ)).obj N)) =
    (derivedPullback f).map ((derivedPullback g).map (pullbackTensorModelMap Z P N)) ≫
      (derivedPullback f).map ((SingleComplexBaseChange.counit g).app H) ≫
      (SingleComplexBaseChange.counit f).app
        (((Scheme.Modules.tensorPullback g).mapHomotopyCategory (.up ℤ)).obj H) ≫
      DerivedCategory.Qh.map (β.hom.app H) ≫ DerivedCategory.Q.map φ.hom := by sorry

end AlgebraicGeometry
