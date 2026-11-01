/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.RingTheory.Localization.Away.Basic
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
public import Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.Algebra.Homology.HomComplex
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationIsIso
public import WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationComm
public import WeilConjectures.Algebra.Homology.HomComplexComponents
public import WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationNaturality
public import WeilConjectures.ProEtaleCoefficients.RingedStrictTowerHomotopyLimit
public import WeilConjectures.CategoryTheory.Ringed.RingedInternalHomExactRestrictionSupplement
public import Mathlib.Algebra.Homology.Double
public import Mathlib.CategoryTheory.Endomorphism
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.Algebra.Homology.Functor
public import WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
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
import WeilConjectures.CategoryTheory.ScalarLocalizationPullback
import all WeilConjectures.CategoryTheory.CechPullbackComplex
import all WeilConjectures.ProperBaseChange.RingedLocalizationFactorRestriction
import all WeilConjectures.ProperBaseChange.RingedCechCompletionUnitIdempotence
import WeilConjectures.CategoryTheory.RingedPullbackAugmentedModels
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
