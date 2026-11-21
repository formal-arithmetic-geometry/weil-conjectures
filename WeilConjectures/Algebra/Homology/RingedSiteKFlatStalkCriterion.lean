/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Sites.RingedSitePoint
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.CategoryTheory.Functor.ReflectsIso.Jointly
public import Mathlib.CategoryTheory.Monoidal.Closed.Braided
import all WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import all WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
import WeilConjectures.Algebra.Homology.RingedSitePointUniversalTensor
import WeilConjectures.Algebra.Homology.RingedSitePointKFlatResolution
import WeilConjectures.Algebra.Homology.RingedSitePointAcyclic
import WeilConjectures.Algebra.Homology.RingedSitePointTensor
import WeilConjectures.Algebra.Homology.UniversalAcyclicModuleKFlat

/-!
# K-flatness and stalks of a ringed site

A complex of modules on a ringed site is K-flat if and only if its stalks are K-flat.

## References

* [Stacks Project, Cohomology on Sites, Tag 0DEN](https://stacks.math.columbia.edu/tag/0DEN)
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v w t
open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject
namespace CochainComplex

private theorem module_tensor_acyclic_of_kFlat
    {A : Type w} [CommRing A] (K F : CochainComplex (ModuleCat.{w} A) ℤ)
    (hK : (HomologicalComplex.quasiIso (ModuleCat.{w} A) (.up ℤ)).kFlat K)
    (hF : F.Acyclic) : (mapBifunctor F K (MonoidalCategory.curriedTensor _)).Acyclic := by
  let T := MonoidalCategory.tensorRight K
  have hz : QuasiIso (0 : (0 : CochainComplex (ModuleCat.{w} A) ℤ) ⟶ F) := by
    rw [quasiIso_iff]
    intro i
    exact (quasiIsoAt_iff_exactAt _ i
      ((HomologicalComplex.acyclic_of_isZero _ (isZero_zero _)) i)).2 (hF i)
  have hmap : QuasiIso (T.map (0 : (0 : CochainComplex (ModuleCat.{w} A) ℤ) ⟶ F)) :=
    hK.2 _ hz
  have htzero : (T.obj (0 : CochainComplex (ModuleCat.{w} A) ℤ)).Acyclic :=
    HomologicalComplex.acyclic_of_isZero _ (T.map_isZero (isZero_zero _))
  exact fun i ↦ (exactAt_iff_of_quasiIsoAt
    (T.map (0 : (0 : CochainComplex (ModuleCat.{w} A) ℤ) ⟶ F)) i).1 (htzero i)

private theorem module_kFlat_of_cone
    {A : Type w} [CommRing A] (P K : CochainComplex (ModuleCat.{w} A) ℤ)
    (q : P ⟶ K)
    (hP : (HomologicalComplex.quasiIso (ModuleCat.{w} A) (.up ℤ)).kFlat P)
    (hC : (HomologicalComplex.quasiIso (ModuleCat.{w} A) (.up ℤ)).kFlat
      (mappingCone q)) :
    (HomologicalComplex.quasiIso (ModuleCat.{w} A) (.up ℤ)).kFlat K := by
  rw [← HomotopyCategory.kFlat_quotient_obj_iff] at hP hC ⊢
  have : MonoidalPreadditive (ModuleCat.{w} A) := inferInstance
  have (X Y Z : GradedObject ℤ (ModuleCat.{w} A)) :
      GradedObject.HasGoodTensor₁₂Tensor X Y Z := inferInstance
  have (X Y Z : GradedObject ℤ (ModuleCat.{w} A)) :
      GradedObject.HasGoodTensorTensor₂₃ X Y Z := inferInstance
  have (X Y Z W : GradedObject ℤ (ModuleCat.{w} A)) :
      GradedObject.HasTensor₄ObjExt X Y Z W := inferInstance
  let Q := (HomotopyCategory.quasiIso (ModuleCat.{w} A) (.up ℤ)).kFlat
  exact Q.ext_of_isTriangulatedClosed₂ (mappingCone.triangleh q)
    (HomotopyCategory.mappingCone_triangleh_distinguished q) hP hC

/-- K-flat complexes have K-flat stalks at every topos point, and a specified conservative
family of points detects K-flatness. There is no flat-term or boundedness hypothesis, and the
family may be empty. -/
theorem ringedSite_kFlat_stalk_criterion
    {C : Type u} [Category.{v} C] [EssentiallySmall.{w} C]
    (J : Precoverage C)
    (R : Sheaf J.toGrothendieck CommRingCat.{w})
    (K : CochainComplex (SheafOfModules.{w}
      ((sheafCompose J.toGrothendieck (forget₂ CommRingCat.{w} RingCat.{w})).obj R)) ℤ) :
    (∀ (p : GeometricMorphism (Type w) (Sheaf J.toGrothendieck (Type w)))
      (s : RingedSitePoint R p),
      IsKFlatIndependentCoefficients (R := R) K →
        (HomologicalComplex.quasiIso (ModuleCat.{w} s.ring) (.up ℤ)).kFlat
          ((s.modules.mapHomologicalComplex (.up ℤ)).obj K)) ∧
    (∀ (I : Type t)
      (p : I → GeometricMorphism (Type w) (Sheaf J.toGrothendieck (Type w)))
      (s : ∀ i : I, RingedSitePoint R (p i)),
      JointlyReflectIsomorphisms (fun i : I ↦ (p i).inverse) →
      (∀ i : I,
        (HomologicalComplex.quasiIso (ModuleCat.{w} (s i).ring) (.up ℤ)).kFlat
          (((s i).modules.mapHomologicalComplex (.up ℤ)).obj K)) →
      IsKFlatIndependentCoefficients (R := R) K) := by
  constructor
  · intro p s hK
    let := SheafOfModules.isMonoidal_W_independentCoefficients R
    let := SheafOfModules.monoidalCategory R
    let := SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients R
    let := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients R
    obtain ⟨P, q, hP, hq, hPp⟩ := s.exists_kFlat_resolution K
    let E := mappingCone q
    have hE : E.IsKFlatIndependentCoefficients :=
      (SheafOfModules.kFlat_cone_independent R P K q).1 hP hK
    have hEa : E.Acyclic := (mappingCone.quasiIso_iff_acyclic q).1 hq
    have hEp : (HomologicalComplex.quasiIso (ModuleCat.{w} s.ring) (.up ℤ)).kFlat
        ((s.modules.mapHomologicalComplex (.up ℤ)).obj E) := by
      apply kFlat_of_acyclic_tensor_finitePresentation
      intro M hM
      exact s.acyclic_tensor_finitePresentation E
        (SheafOfModules.tensor_acyclic R E hE hEa) M hM
    let S := s.modules.mapHomologicalComplex (.up ℤ)
    have hCone : (HomologicalComplex.quasiIso (ModuleCat.{w} s.ring) (.up ℤ)).kFlat
        (mappingCone (S.map q)) :=
      ObjectProperty.prop_of_iso _ (mappingCone.mapHomologicalComplexIso q s.modules) hEp
    exact module_kFlat_of_cone _ _ (S.map q) hPp hCone
  · intro I p s hp hK
    let := SheafOfModules.isMonoidal_W_independentCoefficients R
    let := SheafOfModules.monoidalCategory R
    let := SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients R
    let := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients R
    intro F hF
    apply (CategoryTheory.RingedSitePoint.acyclic_iff p s hp _).2
    intro i
    have he := (exactFunctor_iff _).1 ((s i).exact)
    have : PreservesFiniteLimits (s i).modules := he.1
    have : PreservesFiniteColimits (s i).modules := he.2
    have hFp : (((s i).modules.mapHomologicalComplex (.up ℤ)).obj F).Acyclic :=
      fun n ↦ (hF n).map (s i).modules
    have ht := module_tensor_acyclic_of_kFlat _ _ (hK i) hFp
    obtain ⟨e⟩ := (s i).tensor F K
    exact fun n ↦ (ht n).of_iso e.symm

end CochainComplex
