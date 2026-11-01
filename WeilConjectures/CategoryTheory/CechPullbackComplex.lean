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
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
import all WeilConjectures.CategoryTheory.Ringed.RingedLocalizationModelsSupplement
import all WeilConjectures.ProperBaseChange.RingedCechKoszulDualKFlat
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.ObjectProperty.FiniteProducts
import WeilConjectures.Algebra.Homology.KFlatComparison
import WeilConjectures.CategoryTheory.CechPullbackAugmentationAssembly

/-! # The ordinary augmented Cech pullback comparison

Source: Stacks Project, algebraization.tex, Tags 0996 and 099E;
sites-modules.tex, Tag 03EL; sites-cohomology.tex, Tags 06YY and 0G7E.
(blueprint: lem-weil-pbc-cech-pullback-complex).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory

private theorem cech_terms_flat
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J CommRingCat.{u}) (r : ℕ)
    (b : Fin r → (O.obj ⋙ forget CommRingCat).sections) :
    ∀ n : ℤ, SheafOfModules.IsFlat ((ringedExtendedCech O r b).1.X n) := by
  classical
  let A := ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)
  let : IsGrothendieckAbelian.{u} A := SheafOfModules.isGrothendieckAbelian _
  let := SheafOfModules.monoidalCategory O
  let := SheafOfModules.symmetricCategory O
  let := (SheafOfModules.tensorClosed O).1.some
  let := (SheafOfModules.tensorClosed O).2.1.some
  have factor (s : (O.obj ⋙ forget CommRingCat).sections) (n : ℤ) :
      ObjectProperty.flat ((ringedLocalizationTwoTerm O s).X n) := by
    change ObjectProperty.flat (ringedLocalizationTwoTermX O s n)
    by_cases hn : n = 0
    · subst n
      rw [ringedLocalizationTwoTermX_zero]
      exact ObjectProperty.prop_unit ObjectProperty.flat
    · by_cases hn' : n = 1
      · subst n
        rw [ringedLocalizationTwoTermX_one]
        exact (SheafOfModules.isFlat_iff_flat _).1 (localization_isFlat O s)
      · simp only [ringedLocalizationTwoTermX, if_neg hn, if_neg hn']
        exact ObjectProperty.flat_of_isZero (isZero_zero _)
  have hall : ∀ (r : ℕ) (b : Fin r → (O.obj ⋙ forget CommRingCat).sections) (n : ℤ),
      ObjectProperty.flat ((ringedExtendedCech O r b).1.X n) := by
    intro r
    induction r with
    | zero =>
      intro b n
      by_cases hn : n = 0
      · subst n
        exact ObjectProperty.prop_of_iso ObjectProperty.flat
          (HomologicalComplex.singleObjXSelf (.up ℤ) 0 _).symm
          (ObjectProperty.prop_unit ObjectProperty.flat)
      · exact ObjectProperty.flat_of_isZero
          (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 _ n hn)
    | succ r ih =>
      intro b n
      let P := (ringedExtendedCech O r (fun i ↦ b i.succ)).1
      let T := (((MonoidalCategory.curriedTensor A).mapBifunctorHomologicalComplex
        (.up ℤ) (.up ℤ)).obj (ringedLocalizationTwoTerm O (b 0))).obj P
      have hz (p q : ℤ) (h₀ : p ≠ 0) (h₁ : p ≠ 1) : IsZero ((T.X p).X q) := by
        apply ((MonoidalCategory.curriedTensor A).flip.obj (P.X q)).map_isZero
        change IsZero (ringedLocalizationTwoTermX O (b 0) p)
        simp only [ringedLocalizationTwoTermX, if_neg h₀, if_neg h₁]
        exact isZero_zero _
      change ObjectProperty.flat ((T.total (.up ℤ)).X n)
      apply ObjectProperty.prop_of_iso ObjectProperty.flat (totalTwoXIso T hz n).symm
      apply ObjectProperty.prop_of_iso ObjectProperty.flat (biprod.isoProd _ _).symm
      exact ObjectProperty.prop_prod ObjectProperty.flat _ _
        (ObjectProperty.prop_tensor (factor (b 0) 0) (ih _ n))
        (ObjectProperty.prop_tensor (factor (b 0) 1) (ih _ (n - 1)))
  intro n
  exact (hall r b n).tensorRight

/-- Pullback of a finite augmented localization complex is the localization complex
of the scalar-image list, given its augmented two-term factor comparisons.

Source: Stacks Project, Modules on Sites, Tag 03EL; Cohomology on Sites, Tags 0G7E
and 06YY; algebraization.tex, Tags 0996 and 099E.
(blueprint: lem-weil-pbc-cech-pullback-complex).

Proof:
1. Take the supplied augmented two-term factor comparisons. Their degree-zero
comparison is the specified v, and their augmentation equations are part of hfactor.
2. Choose the canonical tensor-unit comparison v0 on the actual geometric module
pullback, and transfer it to F by uniqueness of left adjoints. Put a = v0.inv followed
by v.hom, an automorphism of the target tensor unit. Its central action on any module M
is lambda_M.inv followed by (a tensor id_M) followed by lambda_M.hom. This gives an
invertible natural transformation, hence also an automorphism of every complex.
Postcompose the factor comparisons with its inverse to normalize them to v0.
3. Module pullback preserves tensor products. Transfer its tensor comparison through
uniqueness of left adjoints from the actual inverse-image-and-extension functor to F.
On complexes, F preserves the countable coproducts in totalization, and additivity
preserves the signed differentials. Apply the tensor comparison inductively to the
ordered two-term factors. Use the rank-one tensor unitors at each augmentation.
The canonical tensor-unit coherence makes the resulting target comparison v0[0].
Postcompose the comparison with the central action of a on the whole target Cech
complex. Naturality at the augmentation changes v0[0] to precisely v[0].
The empty list uses that single-complex comparison directly.
4. Each two-term factor has flat terms: the ring module is flat and the localization
module is flat by sectionwise localization flatness and exact sheafification. A finite
tensor of these bounded complexes has, in every degree, a finite sum of tensor
products of their terms. Tensor products and finite sums preserve flatness. The
complex is bounded above, so bounded-above flat implies K-flat. This proof includes
zero sections, nilpotents and the empty generating list. -/
theorem cech_pullback_complex
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
            (HomologicalComplex.single _ (.up ℤ) 0).map v.hom) :
    ∃ l : ((F.mapHomologicalComplex (.up ℤ)).obj (ringedExtendedCech R r b).1) ≅
        (ringedExtendedCech S r c).1,
      l.hom ≫ (ringedExtendedCech S r c).2 =
        (F.mapHomologicalComplex (.up ℤ)).map (ringedExtendedCech R r b).2 ≫
          (HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).hom.app
            (SheafOfModules.unit
              ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ≫
          (HomologicalComplex.single _ (.up ℤ) 0).map v.hom := by
  obtain ⟨coh⟩ := cech_pullback_tensor_coherence R S h F hF v
  exact cech_pullback_augmentation_assembly R S h F hF v r b c hscalar hfactor coh

end CategoryTheory
