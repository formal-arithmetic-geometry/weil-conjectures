/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.ExactScalarPeriodicResolution
public import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.CategoryTheory.Monoidal.Preadditive
import Mathlib.Algebra.Homology.SingleHomology
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
/-! # Alternating rank-one resolutions -/
@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u v
open CategoryTheory CategoryTheory.Limits ZeroObject
namespace CochainComplex
variable {A : Type u} [Category.{v} A] [HasZeroMorphisms A] [HasZeroObject A]

private def alternatingD {M : A} (f g : End M) (i : ℤ) :
    scalarPeriodicX M i ⟶ scalarPeriodicX M (i + 1) :=
  if hi : i < 0 then
    eqToHom (if_pos (le_of_lt hi)) ≫ (if i % 2 = 0 then f else g) ≫
      eqToHom (if_pos (Int.add_one_le_iff.mpr hi)).symm
  else 0

private theorem alternatingD_comp {M : A} (f g : End M)
    (hfg : f ≫ g = 0) (hgf : g ≫ f = 0) (i : ℤ) :
    alternatingD f g i ≫ alternatingD f g (i + 1) = 0 := by
  classical
  by_cases hi : i < 0
  · by_cases hj : i + 1 < 0
    · simp only [alternatingD, dif_pos hi, dif_pos hj, Category.assoc,
        eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
      by_cases he : i % 2 = 0
      · have he' : ¬ (i + 1) % 2 = 0 := by omega
        simp only [if_pos he, if_neg he']
        rw [← Category.assoc f g, hfg, zero_comp, comp_zero]
      · have he' : (i + 1) % 2 = 0 := by omega
        simp only [if_neg he, if_pos he']
        rw [← Category.assoc g f, hgf, zero_comp, comp_zero]
    · simp [alternatingD, hj]
  · simp [alternatingD, hi]

private def alternating {M : A} (f g : End M) (hfg : f ≫ g = 0) (hgf : g ≫ f = 0) :
    CochainComplex A ℤ :=
  CochainComplex.of (scalarPeriodicX M) (alternatingD f g) (alternatingD_comp f g hfg hgf)

private def alternatingXIso {M : A} (f g : End M) (hfg : f ≫ g = 0) (hgf : g ≫ f = 0)
    (i : ℤ) (hi : i ≤ 0) : (alternating f g hfg hgf).X i ≅ M :=
  eqToIso (if_pos hi)

variable [HasCokernels A]

private theorem alternatingAugmentation_condition {M : A} (f g : End M)
    (hfg : f ≫ g = 0) (hgf : g ≫ f = 0)
    (i : ℤ) (hi : (ComplexShape.up ℤ).Rel i 0) :
    (alternating f g hfg hgf).d i 0 ≫
      (alternatingXIso f g hfg hgf 0 le_rfl).hom ≫ cokernel.π g = 0 := by
  have hi' : i + 1 = 0 := hi
  have hi0 : i = -1 := by omega
  subst i
  simp [alternating, CochainComplex.of.d, alternatingD, alternatingXIso]

private def alternatingAugmentation {M : A} (f g : End M)
    (hfg : f ≫ g = 0) (hgf : g ≫ f = 0) :
    alternating f g hfg hgf ⟶
      (HomologicalComplex.single A (ComplexShape.up ℤ) 0).obj (cokernel g) :=
  HomologicalComplex.mkHomToSingle
    ((alternatingXIso f g hfg hgf 0 le_rfl).hom ≫ cokernel.π g)
    (alternatingAugmentation_condition f g hfg hgf)
private theorem alternating_exactAt
    {B : Type*} [Category* B] [Abelian B] {M : B}
    (f g : End M) (hfg : f ≫ g = 0) (hgf : g ≫ f = 0)
    (hef : (ShortComplex.mk f g hfg).Exact)
    (heg : (ShortComplex.mk g f hgf).Exact) (i : ℤ) (hi : i ≠ 0) :
    (alternating f g hfg hgf).ExactAt i := by
  by_cases hn : i < 0
  · rw [HomologicalComplex.exactAt_iff' _ (i - 1) i (i + 1) (by simp) (by simp)]
    by_cases he : i % 2 = 0
    · have hm : ¬ (i - 1) % 2 = 0 := by omega
      let e : (alternating f g hfg hgf).sc' (i - 1) i (i + 1) ≅
          ShortComplex.mk g f hgf :=
        ShortComplex.isoMk
          (alternatingXIso f g hfg hgf (i - 1) (by omega))
          (alternatingXIso f g hfg hgf i (by omega))
          (alternatingXIso f g hfg hgf (i + 1) (by omega))
          (by simp [alternating, CochainComplex.of.d, alternatingD,
            alternatingXIso, show i - 1 < 0 by omega, hm])
          (by simp [alternating, CochainComplex.of.d, alternatingD,
            alternatingXIso, hn, he])
      exact (ShortComplex.exact_iff_of_iso e).2 heg
    · have hm : (i - 1) % 2 = 0 := by omega
      let e : (alternating f g hfg hgf).sc' (i - 1) i (i + 1) ≅
          ShortComplex.mk f g hfg :=
        ShortComplex.isoMk
          (alternatingXIso f g hfg hgf (i - 1) (by omega))
          (alternatingXIso f g hfg hgf i (by omega))
          (alternatingXIso f g hfg hgf (i + 1) (by omega))
          (by simp [alternating, CochainComplex.of.d, alternatingD,
            alternatingXIso, show i - 1 < 0 by omega, hm])
          (by simp [alternating, CochainComplex.of.d, alternatingD,
            alternatingXIso, hn, he])
      exact (ShortComplex.exact_iff_of_iso e).2 hef
  · apply HomologicalComplex.ExactAt.of_isZero
    simpa [alternating, scalarPeriodicX, show ¬ i ≤ 0 by omega] using isZero_zero B

set_option backward.isDefEq.respectTransparency false in
private theorem alternating_quasiIso
    {B : Type*} [Category* B] [Abelian B] {M : B}
    (f g : End M) (hfg : f ≫ g = 0) (hgf : g ≫ f = 0)
    (hef : (ShortComplex.mk f g hfg).Exact)
    (heg : (ShortComplex.mk g f hgf).Exact) :
    QuasiIso (alternatingAugmentation f g hfg hgf) := by
  rw [quasiIso_iff]
  intro i
  by_cases hi : i = 0
  · subst i
    rw [quasiIsoAt_iff' _ (-1) 0 1 (by simp) (by simp)]
    rw [ShortComplex.quasiIso_iff_of_zeros' _
      (by simp [alternating, CochainComplex.of.d, alternatingD])
      (by simp) (by simp)]
    constructor
    · let e : ShortComplex.mk
          ((alternating f g hfg hgf).d (-1) 0)
          ((alternatingAugmentation f g hfg hgf).f 0)
          (by rw [← (alternatingAugmentation f g hfg hgf).comm (-1) 0]; simp) ≅
          ShortComplex.mk g (cokernel.π g) (cokernel.condition g) :=
        ShortComplex.isoMk
          (alternatingXIso f g hfg hgf (-1) (by omega))
          (alternatingXIso f g hfg hgf 0 le_rfl)
          (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (cokernel g))
          (by simp [alternating, CochainComplex.of.d, alternatingD, alternatingXIso])
          (by simp [alternatingAugmentation, HomologicalComplex.mkHomToSingle_f])
      exact (ShortComplex.exact_iff_of_iso e).2
        (ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel g))
    · change Epi ((alternatingAugmentation f g hfg hgf).f 0)
      dsimp [alternatingAugmentation]
      rw [HomologicalComplex.mkHomToSingle_f]
      infer_instance
  · exact (quasiIsoAt_iff_exactAt' _ i
      (HomologicalComplex.exactAt_single_obj (.up ℤ) 0 _ i hi)).2
      (alternating_exactAt f g hfg hgf hef heg i hi)

private theorem alternating_map_exactAt
    {B D : Type*} [Category* B] [Abelian B] [Category* D] [Abelian D]
    (F : B ⥤ D) [F.Additive] {M : B}
    (f g : End M) (hfg : f ≫ g = 0) (hgf : g ≫ f = 0)
    (hef : (ShortComplex.mk f g hfg |>.map F).Exact)
    (heg : (ShortComplex.mk g f hgf |>.map F).Exact) (i : ℤ) (hi : i < 0) :
    ((F.mapHomologicalComplex (.up ℤ)).obj (alternating f g hfg hgf)).ExactAt i := by
  let P := (F.mapHomologicalComplex (.up ℤ)).obj (alternating f g hfg hgf)
  rw [HomologicalComplex.exactAt_iff' _ (i - 1) i (i + 1) (by simp) (by simp)]
  by_cases he : i % 2 = 0
  · have hm : ¬ (i - 1) % 2 = 0 := by omega
    let e : P.sc' (i - 1) i (i + 1) ≅ (ShortComplex.mk g f hgf).map F :=
      ShortComplex.isoMk
        (F.mapIso (alternatingXIso f g hfg hgf (i - 1) (by omega)))
        (F.mapIso (alternatingXIso f g hfg hgf i (by omega)))
        (F.mapIso (alternatingXIso f g hfg hgf (i + 1) (by omega)))
        (by simp [P, alternating, CochainComplex.of.d, alternatingD,
          alternatingXIso, show i - 1 < 0 by omega, hm])
        (by simp [P, alternating, CochainComplex.of.d, alternatingD,
          alternatingXIso, hi, he])
    exact (ShortComplex.exact_iff_of_iso e).2 heg
  · have hm : (i - 1) % 2 = 0 := by omega
    let e : P.sc' (i - 1) i (i + 1) ≅ (ShortComplex.mk f g hfg).map F :=
      ShortComplex.isoMk
        (F.mapIso (alternatingXIso f g hfg hgf (i - 1) (by omega)))
        (F.mapIso (alternatingXIso f g hfg hgf i (by omega)))
        (F.mapIso (alternatingXIso f g hfg hgf (i + 1) (by omega)))
        (by simp [P, alternating, CochainComplex.of.d, alternatingD,
          alternatingXIso, show i - 1 < 0 by omega, hm])
        (by simp [P, alternating, CochainComplex.of.d, alternatingD,
          alternatingXIso, hi, he])
    exact (ShortComplex.exact_iff_of_iso e).2 hef

private theorem alternating_map_d_zero
    {B D : Type*} [Category* B] [Abelian B] [Category* D] [Abelian D]
    (F : B ⥤ D) [F.Additive] {M : B}
    (f g : End M) (hfg : f ≫ g = 0) (hgf : g ≫ f = 0)
    (hf : F.map f = 0) (hg : F.map g = 0) (i j : ℤ) :
    F.map ((alternating f g hfg hgf).d i j) = 0 := by
  by_cases hij : i + 1 = j
  · subst j
    simp only [alternating, CochainComplex.of_d, alternatingD]
    split_ifs <;> simp only [Functor.map_comp, hf, hg, zero_comp, comp_zero, Functor.map_zero]
  · rw [HomologicalComplex.shape _ _ _ hij]
    exact F.map_zero _ _

private def alternating_map_homology_iso
    {B D : Type*} [Category* B] [Abelian B] [Category* D] [Abelian D]
    (F : B ⥤ D) [F.Additive] {M : B}
    (f g : End M) (hfg : f ≫ g = 0) (hgf : g ≫ f = 0)
    (hf : F.map f = 0) (hg : F.map g = 0) (i : ℤ) (hi : i ≤ 0) :
    ((F.mapHomologicalComplex (.up ℤ)).obj (alternating f g hfg hgf)).homology i ≅
      F.obj M := by
  let P := (F.mapHomologicalComplex (.up ℤ)).obj (alternating f g hfg hgf)
  have h₁ : (P.sc i).f = 0 := alternating_map_d_zero F f g hfg hgf hf hg _ _
  have h₂ : (P.sc i).g = 0 := alternating_map_d_zero F f g hfg hgf hf hg _ _
  exact (ShortComplex.LeftHomologyData.ofZeros (P.sc i) h₁ h₂).homologyIso ≪≫
    F.mapIso (alternatingXIso f g hfg hgf i hi)

end CochainComplex

namespace SheafOfModules
universe r
variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{r})

private theorem alternating_unit_kFlat
    (f g : End (unit ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)))
    (hfg : f ≫ g = 0) (hgf : g ≫ f = 0)
    (hef : (ShortComplex.mk f g hfg).Exact)
    (heg : (ShortComplex.mk g f hgf).Exact) :
    CochainComplex.IsKFlatResolutionIndependentCoefficients
      (CochainComplex.alternatingAugmentation f g hfg hgf) := by
  let P := CochainComplex.alternating f g hfg hgf
  have hq : QuasiIso (CochainComplex.alternatingAugmentation f g hfg hgf) :=
    CochainComplex.alternating_quasiIso f g hfg hgf hef heg
  have hflat : ∀ i : ℤ, IsFlatOnSite (J := J) (R := R) (P.X i) := by
    let := isMonoidal_W_independentCoefficients R
    let := monoidalCategory R
    let := tensorPreadditive R
    intro i
    apply (exactFunctor _ _).prop_of_iso (siteSheafTensorRightIso R (P.X i)).symm
    dsimp [P, CochainComplex.alternating, CochainComplex.scalarPeriodicX]
    split_ifs
    · exact (ObjectProperty.prop_unit ObjectProperty.flat).2
    · have hz : IsZero (MonoidalCategory.tensorRight
          (0 : SheafOfModules.{r}
            ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R))) := by
        rw [Functor.isZero_iff]
        intro M
        exact (MonoidalCategory.tensorLeft M).map_isZero (isZero_zero _)
      have := Functor.preservesLimitsOfSize_of_isZero _ hz
      have := Functor.preservesColimitsOfSize_of_isZero _ hz
      change PreservesFiniteLimits _ ∧ PreservesFiniteColimits _
      exact ⟨inferInstance, inferInstance⟩
  have hb : P.IsStrictlyLE 0 := by
    rw [CochainComplex.isStrictlyLE_iff]
    intro i hi
    simpa [P, CochainComplex.alternating, CochainComplex.scalarPeriodicX,
      show ¬ i ≤ 0 by omega] using isZero_zero (SheafOfModules.{r}
        ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R))
  have := hb
  exact ⟨hq, isKFlatIndependentCoefficients_of_boundedAbove_flatOnSite R P 0 hflat⟩


/-- A rank-one alternating exact complex has a K-flat augmentation, and annihilating
both differentials makes its tensor cohomology equal to its rank-one terms.
Source: Stacks Project, Tag 06YU, periodic free quotient resolutions; blueprint order
1429, the counterexample's periodic-resolution calculation.
(blueprint: lem-weil-pbc-alternating-unit-resolution).

Proof: put the coefficient unit in each nonpositive degree and zero above, alternating
f and g, with g entering degree zero. The two assumed exact short complexes prove
exactness in every negative degree. The cokernel augmentation computes degree-zero
homology and is therefore a quasi-isomorphism. All terms are flat and the complex is
bounded above, so the augmentation is a K-flat resolution. After tensoring, if both
endomorphisms vanish, every differential vanishes. The homology is then the term in
that degree, which is the tensor of the coefficient unit with the supplied module.
The statement includes degree zero and the zero module.
-/
theorem alternatingUnit_resolution
    (f g : End (unit ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)))
    (hfg : f ≫ g = 0) (hgf : g ≫ f = 0)
    (hef : (ShortComplex.mk f g hfg).Exact)
    (heg : (ShortComplex.mk g f hgf).Exact) :
    letI := isMonoidal_W_independentCoefficients R
    letI := monoidalCategory R
    letI := tensorPreadditive R
    ∃ (P : CochainComplex (SheafOfModules.{r}
        ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) ℤ)
      (p : P ⟶ (CochainComplex.singleFunctor _ 0).obj (cokernel g)),
      CochainComplex.IsKFlatResolutionIndependentCoefficients p ∧
      ∀ (M : SheafOfModules.{r}
          ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R))
        (i : ℤ), i ≤ 0 → (MonoidalCategory.tensorRight M).map f = 0 →
        (MonoidalCategory.tensorRight M).map g = 0 →
        Nonempty ((HomologicalComplex.homologyFunctor _ (.up ℤ) i).obj
          (((MonoidalCategory.tensorRight M).mapHomologicalComplex (.up ℤ)).obj P) ≅
            (MonoidalCategory.tensorRight M).obj (unit _)) := by
  let := isMonoidal_W_independentCoefficients R
  let := monoidalCategory R
  let := tensorPreadditive R
  refine ⟨CochainComplex.alternating f g hfg hgf,
    CochainComplex.alternatingAugmentation f g hfg hgf,
    alternating_unit_kFlat R f g hfg hgf hef heg, ?_⟩
  intro M i hi hf hg
  exact ⟨CochainComplex.alternating_map_homology_iso
    (MonoidalCategory.tensorRight M) f g hfg hgf hf hg i hi⟩

end SheafOfModules
