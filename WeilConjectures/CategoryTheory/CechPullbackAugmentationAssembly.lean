/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.CechPullbackTensorCoherence
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
public import WeilConjectures.CategoryTheory.CechPullbackAugmentedTensorStep
public import WeilConjectures.CategoryTheory.CechPullbackNormalizedCoherence
public import WeilConjectures.CategoryTheory.RingedKoszulSystem

/-!
# Assembly of the Cech pullback comparison

Source: Stacks Project, algebraization.tex, Tags 0996 and 099E;
sites-modules.tex, Tag 03EL.
(blueprint: lem-weil-pbc-cech-pullback-augmentation-assembly).

The statement records the remaining ordinary-complex construction: tensor
coherence for the canonical tensor products `SheafOfModules.monoidalCategory`
(those of `ringedExtendedCech`) is iterated through the two-term localization
factors and the augmentation is checked by induction on the number of factors.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/--
Given a tensor comparison for `F` and the canonical tensor products, the augmented two-term
factor comparisons assemble into the augmented comparison of the extended Cech complexes.

Proof. Write `w = F.map unitA.inv ≫ v.hom ≫ unitB.hom`; `unitA`, `unitB` are automorphisms
of the units, i.e. unit global sections acting centrally, so `w = v ≫ c` for a central unit `c`,
and the tensor comparison multiplied by `c` is natural and satisfies the unit equation for `v`.
Induct on `r`. For `r = 0` both complexes are the ring complex in degree `0`, and `v[0]` is the
comparison. For `r + 1`, the complex is the totalized tensor of the first two-term factor with
the complex of the remaining sections; `F` is additive and a left adjoint, so it commutes with
the finite sums of the totalization and the signed differentials, and the tensor comparison
in each bidegree, the factor comparison of `hfactor` and the induction hypothesis give the chain
isomorphism. The augmentation is the tensor of the two augmentations followed by the left unitor
of the unit; by naturality of the tensor comparison it reduces to the unit equation at
`𝟙 ⊗ 𝟙`, and the augmentation equations of `hfactor` and of the induction give the equation
through `v`.
(blueprint: lem-weil-pbc-cech-pullback-augmentation-assembly)
-/
theorem cech_pullback_augmentation_assembly
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (R : Sheaf J CommRingCat.{u}) (S : Sheaf K CommRingCat.{u})
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
    (hfactor : ∀ i : Fin r,
      ∃ l : (F.mapHomologicalComplex (.up ℤ)).obj (ringedLocalizationTwoTerm R (b i)) ≅
          ringedLocalizationTwoTerm S (c i),
        l.hom ≫ ringedLocalizationTwoTermAugmentation S (c i) =
          (F.mapHomologicalComplex (.up ℤ)).map
              (ringedLocalizationTwoTermAugmentation R (b i)) ≫
            (HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).hom.app
              (SheafOfModules.unit
                ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ≫
            (HomologicalComplex.single _ (.up ℤ) 0).map v.hom)
    (coh : @TensorCoherence _ _ _ _
      (SheafOfModules.monoidalCategory R) (SheafOfModules.monoidalCategory S) F
      (SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
      (SheafOfModules.unit ((sheafCompose K (forget₂ CommRingCat RingCat)).obj S)) v) :
    ∃ l : ((F.mapHomologicalComplex (.up ℤ)).obj (ringedExtendedCech R r b).1) ≅
        (ringedExtendedCech S r c).1,
      l.hom ≫ (ringedExtendedCech S r c).2 =
        (F.mapHomologicalComplex (.up ℤ)).map (ringedExtendedCech R r b).2 ≫
          (HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).hom.app
            (SheafOfModules.unit
              ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ≫
          (HomologicalComplex.single _ (.up ℤ) 0).map v.hom := by
  obtain ⟨t, ht, hu⟩ := cech_pullback_normalized_coherence R S h F hF v coh
  induction r with
  | zero =>
    let l := (HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).app
      (SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ≪≫
      (HomologicalComplex.single _ (.up ℤ) 0).mapIso v
    refine ⟨l, ?_⟩
    change l.hom ≫ 𝟙 _ = _
    simp [l, ringedExtendedCech]
  | succ r ih =>
    obtain ⟨ly, hy⟩ := ih (fun i ↦ b i.succ) (fun i ↦ c i.succ)
      (fun i ↦ hscalar i.succ) (fun i ↦ hfactor i.succ)
    exact cech_pullback_augmented_tensor_step R S h F hF v t ht hu r b c
      (hfactor 0) ly hy

end CategoryTheory
