/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H3
-/
module

public import Sheaf.AlgebraicGeometry.DerivedCategory
public import Sheaf.Algebra.Homology.KFlat
public import Sheaf.AlgebraicGeometry.TensorPullback
public import Sheaf.Algebra.Homology.ModuleStalkFunctor
public import WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Homology.Single
public import Mathlib.Topology.Sheaves.Abelian

/-! # RelativeTensorStalkGlobalHomology

(blueprint: lem-pc-relative-tensor-stalk-global-homology).
-/

@[expose] public section

universe u w v
open CategoryTheory CategoryTheory.Limits TopologicalSpace
open CategoryTheory.MonoidalCategory

namespace AlgebraicGeometry.Scheme

/-- Global stalk computation for a prescribed K-flat relative representative.
Source: Stacks Project, Cohomology of Sheaves, Tags 06YB, 08CG, 09U9;
Sheaves Tags 008H and 0098; Modules Tag 01AG.
Proof: form the inverse-image ringed space with underlying space X. The canonical
inverse-image ring stalk isomorphism identifies its stalk ring with A=O_Y,f(y).
Take M to be the actual module stalk of F restricted along that isomorphism.
The stalk criterion makes P_y K-flat. Exactness of stalks sends q to a
quasi-isomorphism; the germ formula for the inverse-image ring map identifies
its target with the restriction along f.stalkMap of the module stalk of K.
A K-flat complex computes its derived tensor with every complex, so Q of the
total tensor of P_y and M[0] is isomorphic to Q of that restricted stalk of K
tensored in the derived category with M[0]. Stalks commute with total tensor,
single complexes and homology. Taking homology and forgetting scalars gives
the displayed isomorphisms for all i with this same M. This works for zero
modules, unbounded complexes and every integer i.
(blueprint: lem-pc-relative-tensor-stalk-global-homology). -/
theorem relativeTensor_stalk_global_homology_iso
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (y : X)
    [HasDerivedCategory.{v} (ModuleCat.{u} (Y.presheaf.stalk (f y)))]
    (P : CochainComplex (SheafOfModules.{u} ((sheafCompose
      (Opens.grothendieckTopology X)
      (forget₂ CommRingCat.{u} RingCat.{u})).obj
        (TopCat.Sheaf.inverseImageRing f.base Y.sheaf))) ℤ)
    (hP : CochainComplex.IsKFlat (R := TopCat.Sheaf.inverseImageRing f.base Y.sheaf) P)
    (q : P ⟶ ((SheafOfModules.restrictScalars
      ((sheafCompose (Opens.grothendieckTopology X)
        (forget₂ CommRingCat.{u} RingCat.{u})).map
          (Modules.tensorPullbackRingMap f))).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj K) (hq : QuasiIso q) :
    ∀ F : SheafOfModules.{u} ((sheafCompose
          (Opens.grothendieckTopology X)
          (forget₂ CommRingCat.{u} RingCat.{u})).obj
            (TopCat.Sheaf.inverseImageRing f.base Y.sheaf)),
      ∃ M : ModuleCat.{u} (Y.presheaf.stalk (f y)), ∀ i : ℤ,
          Nonempty ((TopCat.Sheaf.forget AddCommGrpCat.{u} X.carrier ⋙
            TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y).obj
              ((SheafOfModules.toSheaf _).obj
                ((CochainComplex.mapBifunctor P
                  ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj F)
                  (@MonoidalCategory.curriedTensor _ _ (SheafOfModules.monoidalCategory
                    (TopCat.Sheaf.inverseImageRing f.base Y.sheaf)))).homology i)) ≅
            (forget₂ (ModuleCat.{u} (Y.presheaf.stalk (f y))) AddCommGrpCat.{u}).obj
              ((DerivedCategory.homologyFunctor
                (ModuleCat.{u} (Y.presheaf.stalk (f y))) i).obj
                  (DerivedCategory.Q.obj
                    (((ModuleCat.restrictScalars (f.stalkMap y).hom).mapHomologicalComplex
                      (.up ℤ)).obj
                        (((RingedSpace.moduleStalkFunctor X.toRingedSpace y).mapHomologicalComplex
                          (.up ℤ)).obj K)) ⊗
                    (DerivedCategory.singleFunctor
                      (ModuleCat.{u} (Y.presheaf.stalk (f y))) 0).obj M))) := by sorry

end AlgebraicGeometry.Scheme
