/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingedKoszulSystem
public import WeilConjectures.CategoryTheory.RingedExtendedCech
public import WeilConjectures.CategoryTheory.RingedSectionLocalization
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.RingTheory.Localization.Away.Basic
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
public import Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.Algebra.Homology.HomComplex
public import WeilConjectures.CategoryTheory.RingedCompletionUnit
public import WeilConjectures.CategoryTheory.RingedDerivedRestriction
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationIsIso
public import WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationComm
public import WeilConjectures.Algebra.Homology.HomComplexComponents
public import WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationNaturality
public import WeilConjectures.CategoryTheory.RingedStrictTowerHomotopyLimit
public import WeilConjectures.CategoryTheory.RingedSiteGrothendieckAbelian
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Triangulated.Functor
public import Mathlib.Algebra.Homology.Functor
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import WeilConjectures.Algebra.Homology.KInjectiveProductsTermwise
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
public import WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Products
public import WeilConjectures.Algebra.Homology.TowerEvaluationKInjective
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
public import Mathlib.CategoryTheory.Adjunction.Evaluation
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import WeilConjectures.Algebra.Homology.RingedInternalHomExactRestrictionSupplement
public import Mathlib.Algebra.Homology.Double
public import Mathlib.CategoryTheory.Endomorphism
public import WeilConjectures.CategoryTheory.RingedToposMorphismSupplement
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
import WeilConjectures.AlgebraicGeometry.ScalarLocalizationPullback
import all WeilConjectures.AlgebraicGeometry.CechPullbackComplex
import all WeilConjectures.CategoryTheory.RingedLocalizationFactorRestriction
import all WeilConjectures.CategoryTheory.RingedKoszulSystem
import all WeilConjectures.CategoryTheory.RingedExtendedCech
import all WeilConjectures.CategoryTheory.RingedSectionLocalization
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all Mathlib.RingTheory.Localization.Away.Basic
import all WeilConjectures.Algebra.Homology.DerivedInternalHom
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
import all Mathlib.Algebra.Homology.Monoidal
import all WeilConjectures.Algebra.Homology.HomComplex
import all WeilConjectures.CategoryTheory.RingedCompletionUnit
import all WeilConjectures.CategoryTheory.RingedDerivedRestriction
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import all WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationIsIso
import all WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationComm
import all WeilConjectures.Algebra.Homology.HomComplexComponents
import all WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationNaturality
import all WeilConjectures.CategoryTheory.RingedStrictTowerHomotopyLimit
import all WeilConjectures.CategoryTheory.RingedSiteGrothendieckAbelian
import all WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all Mathlib.CategoryTheory.Triangulated.Functor
import all Mathlib.Algebra.Homology.Functor
import all Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import all Mathlib.CategoryTheory.Functor.Derived.RightDerived
import all Mathlib.CategoryTheory.Whiskering
import all Mathlib.CategoryTheory.Functor.OfSequence
import all Mathlib.CategoryTheory.Limits.Shapes.Countable
import all Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import all WeilConjectures.Algebra.Homology.KInjectiveProductsTermwise
import all Mathlib.Algebra.Homology.HomologicalComplexLimits
import all Mathlib.Algebra.Homology.DerivedCategory.KInjective
import all WeilConjectures.Algebra.Homology.HomotopyCategory.Products
import all WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Products
import all WeilConjectures.Algebra.Homology.TowerEvaluationKInjective
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
import all Mathlib.CategoryTheory.Adjunction.Evaluation
import all WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import all Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
import all Mathlib.Algebra.BigOperators.Ring.Finset
import all WeilConjectures.Algebra.Homology.RingedInternalHomExactRestrictionSupplement
import all Mathlib.Algebra.Homology.Double
import all Mathlib.CategoryTheory.Endomorphism
import all WeilConjectures.AlgebraicGeometry.RingedLocalizationRestrictionSupplement
import all WeilConjectures.CategoryTheory.RingedCechCompletionUnitIdempotence
import all WeilConjectures.Algebra.Homology.BoundedAboveFlatSheafKFlatSupplement
import all WeilConjectures.Algebra.Homology.KFlatRHomCurrying
import all WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import all WeilConjectures.Algebra.Homology.KFlatSupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Homology.BifunctorShift
import all Mathlib.Algebra.Homology.QuasiIso
import all Mathlib.CategoryTheory.Sites.Equivalence
import all Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import all Mathlib.CategoryTheory.Limits.EssentiallySmall
import all Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import all WeilConjectures.Algebra.Homology.KInjectiveHomComplexSupplement
import all WeilConjectures.Algebra.Homology.HomTensorDegreewise
import all WeilConjectures.Algebra.Homology.HomTensorDifferential
import all WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMap
import all WeilConjectures.Algebra.Homology.HomTensorNaturality
import all WeilConjectures.CategoryTheory.RingedCechTensorIdempotence
import all Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import all Mathlib.Tactic.Basic
import all WeilConjectures.CategoryTheory.RingedLocalizationFactorTensorAugmentation
import all WeilConjectures.FromJoel.Algebra.Homology.Bifunctor
import all WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import all Mathlib.Algebra.Homology.HomologySequenceLemmas
import all Mathlib.Algebra.Homology.HomologicalComplexAbelian
import all Mathlib.Algebra.Homology.HomotopyCategory.SingleFunctors
import all WeilConjectures.Algebra.Category.ModuleCat.Presheaf.SheafificationTensor
import all Mathlib.RingTheory.Localization.BaseChange
import all WeilConjectures.AlgebraicGeometry.RingedLocalizationModelsSupplement
import all WeilConjectures.Algebra.Homology.KFlatComparison
import all WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import all WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import all WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import all WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import WeilConjectures.AlgebraicGeometry.RingedPullbackAugmentedModels
import Mathlib.CategoryTheory.Adjunction.Additive

/-! # Pullback of a global augmented localization model on one chart

Source: Stacks Project, algebraization.tex, Tags 0996 and 099E;
sites-modules.tex, Tag 03EL; sites-cohomology.tex, Tags 06YY and 0G7E.
(blueprint: lem-weil-pbc-cech-model-pullback-on-chart).
-/

@[expose] public section
set_option autoImplicit false
universe u wR wS
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory

/-- A global finite localization model is preserved by ringed module pullback on a
flat-term K-flat representative, with its actual augmentation.

Source: Stacks Project, algebraization.tex, Tags 0996 and 099E;
sites-modules.tex, Tag 03EL; sites-cohomology.tex, Tags 06YY and 0G7E.
(blueprint: lem-weil-pbc-cech-model-pullback-on-chart).

Proof:
1. The scalar equation identifies multiplication by b_i on the pulled-back rank-one
module with multiplication by c_i. Localization is the filtered colimit of rank-one
modules under that multiplication. The left adjoint F preserves this colimit, so its
unit-normalized comparison gives F(R[1/b_i]) isomorphic to S[1/c_i].
2. Ringed module pullback preserves tensor products. Apply the localization comparison
to each two-term factor [R → R[1/b_i]], then tensor the factor comparisons. Preservation
of coproducts gives the comparison on total complexes. Naturality and additivity preserve
the two summands of the differential and their signs. The resulting chain isomorphism
F(C_b) ≅ C_c carries the image augmentation to the actual augmentation through v[0].
For the empty list it is just the single-complex comparison and v[0].
3. C_b is bounded with flat terms: its terms are finite sums of flat localizations.
It is therefore K-flat. The ordinary pullback has a universal derived functor, whose
natural comparison with ordinary pullback is invertible on C_b and P because both are
K-flat with flat terms. Applying this derived functor to e, and composing the two
comparison isomorphisms, gives Q(F C_b) ≅ Q(F P).
4. Naturality of the derived-to-ordinary comparison at both augmentation arrows,
and the equation for e, identify the two image augmentations. Compose the inverse
of the chain comparison of step 2 with this derived isomorphism. Its augmentation
identity is exactly the displayed equation. Changing v by a ring-module unit
rescales the comparison by the same unit, so the assertion does not require a
specified normalization of the chosen left-adjoint adjunction. -/
theorem cech_model_pullback_on_chart
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (R : Sheaf J CommRingCat.{u}) (S : Sheaf K CommRingCat.{u})
    [HasDerivedCategory.{wR} (ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))]
    [HasDerivedCategory.{wS} (ringedSiteModules.{u}
      ((sheafCompose K (forget₂ CommRingCat RingCat)).obj S))]
    (h : RingedToposMorphism
      ((sheafCompose K (forget₂ CommRingCat RingCat)).obj S)
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (F : ringedSiteModules.{u}
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) ⥤
      ringedSiteModules.{u} ((sheafCompose K (forget₂ CommRingCat RingCat)).obj S))
    [F.PreservesZeroMorphisms] (hF : F ⊣ h.modules)
    (v : F.obj (SheafOfModules.unit
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ≅
      SheafOfModules.unit ((sheafCompose K (forget₂ CommRingCat RingCat)).obj S))
    (r : ℕ) (b : Fin r → (R.obj ⋙ forget CommRingCat).sections)
    (c : Fin r → (S.obj ⋙ forget CommRingCat).sections)
    (hscalar : ∀ i : Fin r, F.map (ringedKoszulScalar R (b i)) ≫ v.hom =
      v.hom ≫ ringedKoszulScalar S (c i))
    (P : ringedSiteComplex R) (ε : P ⟶ ringedSiteRingComplex R)
    (hP : P.IsKFlatIndependentCoefficients)
    (hflat : ∀ n : ℤ, SheafOfModules.IsFlat (P.X n))
    (e : DerivedCategory.Q.obj (ringedExtendedCech R r b).1 ≅ DerivedCategory.Q.obj P)
    (he : e.hom ≫ DerivedCategory.Q.map ε =
      DerivedCategory.Q.map (ringedExtendedCech R r b).2) :
    ∃ d : DerivedCategory.Q.obj (ringedExtendedCech S r c).1 ≅
        DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj P),
      d.hom ≫ DerivedCategory.Q.map
        ((F.mapHomologicalComplex (.up ℤ)).map ε ≫
          (HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).hom.app
            (SheafOfModules.unit
              ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ≫
          (HomologicalComplex.single _ (.up ℤ) 0).map v.hom) =
        DerivedCategory.Q.map (ringedExtendedCech S r c).2 := by
  let : F.Additive := hF.left_adjoint_additive
  let : F.IsLeftAdjoint := hF.isLeftAdjoint
  have hloc := fun i ↦ scalar_localization_pullback R S F v (b i) (c i) (hscalar i)
  have hfactor : ∀ i : Fin r,
      ∃ l : (F.mapHomologicalComplex (.up ℤ)).obj (ringedLocalizationTwoTerm R (b i)) ≅
          ringedLocalizationTwoTerm S (c i),
        l.hom ≫ ringedLocalizationTwoTermAugmentation S (c i) =
          (F.mapHomologicalComplex (.up ℤ)).map
              (ringedLocalizationTwoTermAugmentation R (b i)) ≫
            (HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).hom.app
              (SheafOfModules.unit
                ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ≫
            (HomologicalComplex.single _ (.up ℤ) 0).map v.hom := by
    intro i
    obtain ⟨loc, hloc⟩ := hloc i
    let a : Arrow.mk (F.map (ringedSectionLocalizationUnit R (b i))) ≅
        Arrow.mk (ringedSectionLocalizationUnit S (c i)) :=
      Arrow.isoMk v loc hloc.symm
    let e := factorArrow R S F (b i) (c i) a
    refine ⟨Arrow.leftFunc.mapIso e, ?_⟩
    exact e.hom.w
  obtain ⟨l, hl⟩ := cech_pullback_complex R S h F hF v r b c hscalar hfactor
  have hC := (CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat _).2
    (cech_kflat R r b)
  have hfC := cech_terms_flat R r b
  obtain ⟨d, hd⟩ := ringed_pullback_augmented_models R S h F hF
    (ringedExtendedCech R r b).1 P (ringedSiteRingComplex R)
    (ringedExtendedCech R r b).2 ε hC hfC hP hflat e he
  refine ⟨(DerivedCategory.Q.mapIso l).symm ≪≫ d, ?_⟩
  have hh : l.inv ≫
      (F.mapHomologicalComplex (.up ℤ)).map (ringedExtendedCech R r b).2 ≫
        (HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).hom.app
          (SheafOfModules.unit
            ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ≫
        (HomologicalComplex.single _ (.up ℤ) 0).map v.hom =
      (ringedExtendedCech S r c).2 := by
    rw [← hl, Iso.inv_hom_id_assoc]
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_inv,
    Functor.map_comp, Category.assoc]
  rw [← Category.assoc d.hom
    (DerivedCategory.Q.map ((F.mapHomologicalComplex (.up ℤ)).map ε)), hd]
  simpa only [Functor.map_comp, Category.assoc] using congrArg DerivedCategory.Q.map hh

end CategoryTheory
