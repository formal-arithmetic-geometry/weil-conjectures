/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.KFlat
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.Topology.Sheaves.Abelian
public import Mathlib.Algebra.Homology.Single
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
import WeilConjectures.Algebra.Homology.OpenRestrictionTensorNatural
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HasSheafComposeForgetCommRingCat

/-! # Open restriction of ordinary tensor homology

Open restriction commutes with the homology of the tensor product with a degree-zero sheaf.

## References

* Stacks Project, Tags 03DH and 01CD
* Stacks Project, Tag 0DJQ (local tensor calculation)
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory

attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits

namespace CochainComplex

set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Additivity of the localized tensor. -/
noncomputable local instance localizedTensorPreadditive
    {X : TopCat.{u}} (R : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u})
    (U : TopologicalSpace.Opens X) :
    letI := SheafOfModules.monoidalCategory (R.over U)
    MonoidalPreadditive (SheafOfModules.{u} ((sheafCompose
      ((Opens.grothendieckTopology X).over U)
      (forget₂ CommRingCat.{u} RingCat.{u})).obj (R.over U))) :=
  Classical.choice (SheafOfModules.tensorClosed (R.over U)).1

/-- Exact open restriction commutes with the homology of tensor with a degree-zero sheaf. -/
theorem open_localized_tensor_homology_iso
    {X : TopCat.{u}} (R : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u})
    (U : TopologicalSpace.Opens X)
    (hzero : (SheafOfModules.overFunctor.{u} ((sheafCompose
      (Opens.grothendieckTopology X)
      (forget₂ CommRingCat.{u} RingCat.{u})).obj R) U).PreservesZeroMorphisms)
    (P : CochainComplex (SheafOfModules.{u} ((sheafCompose
      (Opens.grothendieckTopology X)
      (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ)
    (F : SheafOfModules.{u} ((sheafCompose (Opens.grothendieckTopology X)
      (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) (i : ℤ) :
    letI := hzero
    Nonempty (((SheafOfModules.overFunctor.{u} ((sheafCompose
      (Opens.grothendieckTopology X)
      (forget₂ CommRingCat.{u} RingCat.{u})).obj R) U).obj
      ((mapBifunctor P ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj F)
        (@curriedTensor _ _ (SheafOfModules.monoidalCategory R))).homology i)) ≅
      ((mapBifunctor (C₁ := SheafOfModules.{u} ((sheafCompose
        ((Opens.grothendieckTopology X).over U)
        (forget₂ CommRingCat.{u} RingCat.{u})).obj (R.over U)))
        (((SheafOfModules.overFunctor.{u} ((sheafCompose
        (Opens.grothendieckTopology X)
        (forget₂ CommRingCat.{u} RingCat.{u})).obj R) U).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj P : CochainComplex (SheafOfModules.{u} ((sheafCompose
          ((Opens.grothendieckTopology X).over U)
          (forget₂ CommRingCat.{u} RingCat.{u})).obj (R.over U))) ℤ)
        ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
          ((SheafOfModules.overFunctor.{u} ((sheafCompose
            (Opens.grothendieckTopology X)
            (forget₂ CommRingCat.{u} RingCat.{u})).obj R) U).obj F))
        (@curriedTensor _ _ (SheafOfModules.monoidalCategory (R.over U)))).homology i)) :=
  by
  classical
  let := hzero
  let A := (sheafCompose (Opens.grothendieckTopology X)
    (forget₂ CommRingCat.{u} RingCat.{u})).obj R
  let V := SheafOfModules.overFunctor.{u} A U
  have : V.Additive := by
    constructor
    intro M N f g
    ext W x
    rfl
  have : PreservesFiniteLimits V := by
    let G := SheafOfModules.toSheaf.{u} (A.over U)
    let H := (Opens.grothendieckTopology X).overPullback AddCommGrpCat.{u} U
    have : PreservesFiniteLimits H := by dsimp [H]; infer_instance
    let e : V ⋙ G ≅ SheafOfModules.toSheaf.{u} A ⋙ H := Iso.refl _
    have : PreservesFiniteLimits (SheafOfModules.toSheaf.{u} A ⋙ H) :=
      comp_preservesFiniteLimits _ _
    have : PreservesFiniteLimits (V ⋙ G) := preservesFiniteLimits_of_natIso e.symm
    exact preservesFiniteLimits_of_reflects_of_preserves V G
  have : PreservesFiniteColimits V := by
    dsimp [V, SheafOfModules.overFunctor]
    infer_instance
  let := SheafOfModules.monoidalCategory R
  let : MonoidalCategory (SheafOfModules.{u} (A.over U)) :=
    SheafOfModules.monoidalCategory (R.over U)
  let := Classical.choice (SheafOfModules.tensorClosed R).1
  let : MonoidalPreadditive (SheafOfModules.{u} (A.over U)) :=
    Classical.choice (SheafOfModules.tensorClosed (R.over U)).1
  let VC := V.mapHomologicalComplex (.up ℤ)
  obtain ⟨e, he⟩ := SheafOfModules.exists_open_localized_tensor_natural R U
  let d : tensorRight F ⋙ V ≅ V ⋙ tensorRight (V.obj F) :=
    NatIso.ofComponents (fun M ↦ e M F) (by
      intro M M' f
      simpa using (he M M' F F f (𝟙 F)))
  let dC := ((Functor.mapHomologicalComplexCompIso (Iso.refl (tensorRight F ⋙ V))
    (.up ℤ)).app P) ≪≫ ((NatIso.mapHomologicalComplex d (.up ℤ)).app P) ≪≫
      ((Functor.mapHomologicalComplexCompIso (Iso.refl (V ⋙ tensorRight (V.obj F)))
        (.up ℤ)).app P).symm
  let K := mapBifunctor P ((HomologicalComplex.single _ (.up ℤ) 0).obj F)
    (curriedTensor _)
  let c := VC.mapIso (mapBifunctorSingle₂Iso (curriedTensor _) F P) ≪≫ dC ≪≫
    (mapBifunctorSingle₂Iso (curriedTensor _) (V.obj F) (VC.obj P)).symm
  exact ⟨((K.sc i).mapHomologyIso V).symm ≪≫
    (HomologicalComplex.homologyFunctor _ (.up ℤ) i).mapIso c⟩

end CochainComplex
