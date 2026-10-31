/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.PerfectReductionCoefficientUnits
import WeilConjectures.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction
import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
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
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u v r wR wA
open CategoryTheory CategoryTheory.Limits Opposite
open SheafOfModules SheafOfModules.RegularQuotientCone SheafOfModules.TotalTensorSigns
open scoped ChangeOfRings
namespace CategoryTheory.PerfectReductionRoos

section Coordinates
variable {A B : Type*} [Category* A] [Abelian A] [HasCountableProducts A]
  [Category* B] [Abelian B] [HasCountableProducts B]

private theorem product_degree_ext (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (n : ℤ)
    {T : A} {f g : T ⟶ (roosP X).X n}
    (h : ∀ j : ℕ, f ≫ (Pi.π (fun k : ℕ ↦ X.asFunctor.obj (op k)) j).f n =
      g ≫ (Pi.π (fun k : ℕ ↦ X.asFunctor.obj (op k)) j).f n) : f = g := by
  apply (isLimitOfPreserves (HomologicalComplex.eval A (.up ℤ) n)
    (limit.isLimit (Discrete.functor (fun k : ℕ ↦ X.asFunctor.obj (op k))))).hom_ext
  intro j
  exact h j.as

private theorem comparison_fst_coordinate (F : A ⥤ B) [F.Additive]
    (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (n : ℤ) (j : ℕ) :
    (roosAdditiveComparison F X).f (n + 1) ≫
      (roosχ ((roosTowerAction F).obj X) n).hom ≫ biprod.fst ≫
      (Pi.π (fun k : ℕ ↦ ((roosTowerAction F).obj X).asFunctor.obj (op k)) j).f n =
    F.map ((roosχ X n).hom ≫ biprod.fst ≫
      (Pi.π (fun k : ℕ ↦ X.asFunctor.obj (op k)) j).f n) := by
  rw [reassoc_of% roosAdditiveComparison_coordinates]
  simp only [biprod.map_fst_assoc, Functor.biprodComparison_fst_assoc]
  have h := congrArg (fun f ↦ f.f n)
    (piComparison_comp_π (F.mapHomologicalComplex (.up ℤ))
      (fun k : ℕ ↦ X.asFunctor.obj (op k)) j)
  change (roosProductComparison F X).f n ≫ _ = F.map _ at h
  erw [h]
  simp only [Functor.map_comp]

private theorem comparison_snd_coordinate (F : A ⥤ B) [F.Additive]
    (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (n : ℤ) (j : ℕ) :
    (roosAdditiveComparison F X).f (n + 1) ≫
      (roosχ ((roosTowerAction F).obj X) n).hom ≫ biprod.snd ≫
      (Pi.π (fun k : ℕ ↦ ((roosTowerAction F).obj X).asFunctor.obj (op k)) j).f (n + 1) =
    F.map ((roosχ X n).hom ≫ biprod.snd ≫
      (Pi.π (fun k : ℕ ↦ X.asFunctor.obj (op k)) j).f (n + 1)) := by
  rw [reassoc_of% roosAdditiveComparison_coordinates]
  simp only [biprod.map_snd_assoc, Functor.biprodComparison_snd_assoc]
  have h := congrArg (fun f ↦ f.f (n + 1))
    (piComparison_comp_π (F.mapHomologicalComplex (.up ℤ))
      (fun k : ℕ ↦ X.asFunctor.obj (op k)) j)
  change (roosProductComparison F X).f (n + 1) ≫ _ = F.map _ at h
  erw [h]
  simp only [Functor.map_comp]

private theorem map_fst_coordinate {X Y : CochainComplex (ℕᵒᵖ ⥤ A) ℤ}
    (f : X ⟶ Y) (n : ℤ) (j : ℕ) :
    (roosF.map f).f (n + 1) ≫ (roosχ Y n).hom ≫ biprod.fst ≫
      (Pi.π (fun k : ℕ ↦ Y.asFunctor.obj (op k)) j).f n =
    (roosχ X n).hom ≫ biprod.fst ≫
      (Pi.π (fun k : ℕ ↦ X.asFunctor.obj (op k)) j).f n ≫ (f.f n).app (op j) := by
  rw [reassoc_of% roosF_map_χ]
  simp only [biprod.map_fst_assoc]
  have h := congrArg (fun f ↦ f.f n)
    (Pi.map_π (fun k : ℕ ↦
      (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map f).app (op k)) j)
  simp only [HomologicalComplex.comp_f] at h
  erw [h]
  rfl

private theorem map_snd_coordinate {X Y : CochainComplex (ℕᵒᵖ ⥤ A) ℤ}
    (f : X ⟶ Y) (n : ℤ) (j : ℕ) :
    (roosF.map f).f (n + 1) ≫ (roosχ Y n).hom ≫ biprod.snd ≫
      (Pi.π (fun k : ℕ ↦ Y.asFunctor.obj (op k)) j).f (n + 1) =
    (roosχ X n).hom ≫ biprod.snd ≫
      (Pi.π (fun k : ℕ ↦ X.asFunctor.obj (op k)) j).f (n + 1) ≫
        (f.f (n + 1)).app (op j) := by
  rw [reassoc_of% roosF_map_χ]
  simp only [biprod.map_snd_assoc]
  have h := congrArg (fun f ↦ f.f (n + 1))
    (Pi.map_π (fun k : ℕ ↦
      (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map f).app (op k)) j)
  simp only [HomologicalComplex.comp_f] at h
  erw [h]
  rfl

end Coordinates

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasSheafify J AddCommGrpCat.{r}]
  [HasSheafify J CommRingCat.{r}]
  (R : Sheaf J CommRingCat.{r})
  (t : (unit (derivedChangeRingIndependentCoefficients J R)).sections)

-- The cone has only the target single-complex summand in degree zero.
omit [HasSheafify J CommRingCat.{r}] in
private theorem zeroInclusion_isIso (m : ℕ) : IsIso (koszulZeroInclusion R t m) := by
  classical
  let f := principalKoszulScalarComplex R t m
  let S := (CochainComplex.singleFunctor (RegularQuotientCone.Modules R) 0).obj
    (unit (derivedChangeRingIndependentCoefficients J R))
  let e := HomologicalComplex.singleObjXSelf (.up ℤ) 0
    (unit (derivedChangeRingIndependentCoefficients J R))
  let g := (CochainComplex.mappingCone.snd f).v 0 0 (by omega) ≫ e.hom
  have hz : IsZero (S.X 1) := HomologicalComplex.isZero_single_obj_X
    (.up ℤ) 0 _ 1 (by omega)
  refine ⟨⟨g, ?_, ?_⟩⟩
  · change e.inv ≫ (CochainComplex.mappingCone.inr f).f 0 ≫
        (CochainComplex.mappingCone.snd f).v 0 0 (by omega) ≫ e.hom = 𝟙 _
    simp only [CochainComplex.mappingCone.inr_f_snd_v_assoc, Iso.inv_hom_id]
  · apply CochainComplex.mappingCone.ext_from f 1 0 (by omega)
    · exact hz.eq_of_src _ _
    · change (CochainComplex.mappingCone.inr f).f 0 ≫
        ((CochainComplex.mappingCone.snd f).v 0 0 (by omega) ≫ e.hom) ≫
          e.inv ≫ (CochainComplex.mappingCone.inr f).f 0 = _
      simp only [Category.assoc, CochainComplex.mappingCone.inr_f_snd_v_assoc,
        Iso.hom_inv_id_assoc]
      change (CochainComplex.mappingCone.inr f).f 0 =
        (CochainComplex.mappingCone.inr f).f 0 ≫ 𝟙 ((CochainComplex.mappingCone f).X 0)
      rw [Category.comp_id]

variable [HasDerivedCategory.{wR} (RegularQuotientCone.Modules R)]
  [∀ m, HasDerivedCategory.{wA} (RegularQuotientCone.Modules (powerRing R t m))]

private theorem coefficientUnit_degree_naturality
    (d : ∀ m, DerivedChangeOfRingsCochainModel (powerProjection R t m))
    (c : CoefficientUnits R t d) (m : ℕ)
    (Z W : CochainComplex (RegularQuotientCone.Modules R) ℤ) (i j : ℤ)
    (f : Z.X i ⟶ W.X j) :
    f ≫ ((c.ρ m).app W).f j =
      ((c.ρ m).app Z).f i ≫ (restriction (powerProjection R t m)).map ((d m).E.map f) := by
  classical
  obtain ⟨_hlim, _hcol, ho⟩ := sheafRingCoefficientOrdinaryAdjunction (powerProjection R t m)
  obtain ⟨adj, ha⟩ := ho (d m).E (d m).obj_eq (d m).map_eq
  have he (P : CochainComplex (RegularQuotientCone.Modules R) ℤ) (n : ℤ) :
      ((c.ρ m).app P).f n = adj.unit.app (P.X n) := by
    let e := (restriction (powerProjection R t m)).map (eqToHom ((d m).obj_eq (P.X n)))
    apply (cancel_mono e).mp
    ext U x
    change (eqToHom ((d m).obj_eq (P.X n))).val.app U
        ((((c.ρ m).app P).f n).val.app U x) =
      (eqToHom ((d m).obj_eq (P.X n))).val.app U
        ((adj.unit.app (P.X n)).val.app U x)
    have h := ha (P.X n) (changeOfRings (powerProjection R t m) (P.X n)) (𝟙 _) U x
    simp only [Category.comp_id, Adjunction.homEquiv_unit] at h
    exact (c.ρ_sections m P n U x).trans h.symm
  rw [he W j, he Z i]
  exact adj.unit.naturality f

variable [HasDerivedCategory.{wR} (ℕᵒᵖ ⥤ RegularQuotientCone.Modules R)]
  [∀ m, HasDerivedCategory.{wA} (ℕᵒᵖ ⥤ RegularQuotientCone.Modules (powerRing R t m))]
  [HasCountableProducts (RegularQuotientCone.Modules R)]
  [∀ m, HasCountableProducts (RegularQuotientCone.Modules (powerRing R t m))]
structure KoszulSquareData
    (d : ∀ m, DerivedChangeOfRingsCochainModel (powerProjection R t m))
    (c : CoefficientUnits R t d)
    (δ : ∀ m P, ((total R).obj (principalKoszul R t m)).obj (roosF.obj P) ≅
      roosF.obj (tensorTower R (principalKoszul R t m) P))
    (α : ∀ m, (total R).obj (principalKoszul R t m) ⟶
      (d m).E.mapHomologicalComplex (.up ℤ) ⋙
        (restriction (powerProjection R t m)).mapHomologicalComplex (.up ℤ)) where
  augmentation_square : ∀ m P,
    (α m).app (roosF.obj P) ≫
      ((restriction (powerProjection R t m)).mapHomologicalComplex (.up ℤ)).map
        (roosAdditiveComparison (d m).E P) ≫
      roosAdditiveComparison (restriction (powerProjection R t m))
        ((roosTowerAction (d m).E).obj P) =
    (δ m P).hom ≫ roosF.map
      (koszulTowerComplexMap R (Functor.whiskerLeft P.asFunctor (α m)))

-- Keep the original signature, including regularity and derived-tower instances;
-- this strict coordinate calculation takes place entirely before localization.
set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in
/-- strict augmentation square data; source Bhatt--Scholze Lemma 3.5.5.

Proof: Expand both composites using the two additive Roos coordinate formulas and the two
supplied δ identities. On nonzero Koszul degree the α component is zero, and on degree
zero both paths are the normalized coefficient unit. Coordinate extensionality for the
Roos mapping cone proves the square.
(blueprint: lem-sp-perfect-reduction-koszul-comparison-square-data). -/
theorem nonempty_koszulSquareData
    (ht : Mono (globalSectionMultiplication R t))
    (d : ∀ m, DerivedChangeOfRingsCochainModel (powerProjection R t m))
    (c : CoefficientUnits R t d)
    (δ : ∀ m P, ((total R).obj (principalKoszul R t m)).obj (roosF.obj P) ≅
      roosF.obj (tensorTower R (principalKoszul R t m) P))
    (α : ∀ m, (total R).obj (principalKoszul R t m) ⟶
      (d m).E.mapHomologicalComplex (.up ℤ) ⋙
        (restriction (powerProjection R t m)).mapHomologicalComplex (.up ℤ))
    (hδ_shifted : ∀ m P i p n (h : p + (i + 1) = n + 1) j,
      ι R (principalKoszul R t m) (roosF.obj P) p (i + 1) (n + 1) h ≫
        (δ m P).hom.f (n + 1) ≫
        (roosχ (tensorTower R (principalKoszul R t m) P) n).hom ≫ biprod.fst ≫
        (Pi.π (fun k : ℕ ↦ (tensorTower R (principalKoszul R t m) P).asFunctor.obj
          (op k)) j).f n =
      p.negOnePow • ((tensor R).obj ((principalKoszul R t m).X p)).map
        ((roosχ P i).hom ≫ biprod.fst ≫
          (Pi.π (fun k : ℕ ↦ P.asFunctor.obj (op k)) j).f i) ≫
        ι R (principalKoszul R t m) (P.asFunctor.obj (op j)) p i n (by omega))
    (hδ_unshifted : ∀ m P i p n (h : p + (i + 1) = n + 1) j,
      ι R (principalKoszul R t m) (roosF.obj P) p (i + 1) (n + 1) h ≫
        (δ m P).hom.f (n + 1) ≫
        (roosχ (tensorTower R (principalKoszul R t m) P) n).hom ≫ biprod.snd ≫
        (Pi.π (fun k : ℕ ↦ (tensorTower R (principalKoszul R t m) P).asFunctor.obj
          (op k)) j).f (n + 1) =
      ((tensor R).obj ((principalKoszul R t m).X p)).map
        ((roosχ P i).hom ≫ biprod.snd ≫
          (Pi.π (fun k : ℕ ↦ P.asFunctor.obj (op k)) j).f (i + 1)) ≫
        ι R (principalKoszul R t m) (P.asFunctor.obj (op j)) p (i + 1) (n + 1) h)
    (hα_zero : ∀ m Z i p n (h : p + i = n), p ≠ 0 →
      ι R (principalKoszul R t m) Z p i n h ≫ ((α m).app Z).f n = 0)
    (hα_unit : ∀ m Z n,
      ((tensor R).map (koszulZeroInclusion R t m)).app (Z.X n) ≫
        ι R (principalKoszul R t m) Z 0 n n (zero_add n) ≫ ((α m).app Z).f n =
          ((SheafOfModules.monoidalCategory R).leftUnitor (Z.X n)).hom ≫
            ((c.ρ m).app Z).f n) :
    Nonempty (KoszulSquareData R t d c δ α) := by
  refine ⟨{ augmentation_square := ?_ }⟩
  intro m P
  -- Normalize alpha on degree-zero summands, including maps between different degrees.
  have hα_natural (Z W : CochainComplex (RegularQuotientCone.Modules R) ℤ)
      (i j : ℤ) (f : Z.X i ⟶ W.X j) :
      ((tensor R).obj ((principalKoszul R t m).X 0)).map f ≫
          ι R (principalKoszul R t m) W 0 j j (zero_add j) ≫ ((α m).app W).f j =
        ι R (principalKoszul R t m) Z 0 i i (zero_add i) ≫ ((α m).app Z).f i ≫
          (restriction (powerProjection R t m)).map ((d m).E.map f) := by
    let := SheafOfModules.monoidalCategory R
    have := zeroInclusion_isIso R t m
    apply (cancel_epi (((tensor R).map (koszulZeroInclusion R t m)).app (Z.X i))).1
    rw [← Category.assoc, ← NatTrans.naturality, Category.assoc, hα_unit]
    change MonoidalCategory.whiskerLeft _ f ≫ _ = _
    erw [MonoidalCategory.leftUnitor_naturality_assoc,
      coefficientUnit_degree_naturality R t d c m Z W i j f]
    simpa only [Category.assoc] using
      (congrArg (fun a ↦ a ≫ (restriction (powerProjection R t m)).map ((d m).E.map f))
        (hα_unit m Z i)).symm
  -- The two Roos coordinates are jointly detected by their product projections.
  ext k : 1
  obtain ⟨n, rfl⟩ := (Equiv.addRight (1 : ℤ)).surjective k
  change ((α m).app (roosF.obj P) ≫
      ((restriction (powerProjection R t m)).mapHomologicalComplex (.up ℤ)).map
        (roosAdditiveComparison (d m).E P) ≫
      roosAdditiveComparison (restriction (powerProjection R t m))
        ((roosTowerAction (d m).E).obj P)).f (n + 1) =
    ((δ m P).hom ≫ roosF.map
      (koszulTowerComplexMap R (Functor.whiskerLeft P.asFunctor (α m)))).f (n + 1)
  apply (cancel_mono (roosχ
    ((roosTowerAction (restriction (powerProjection R t m))).obj
      ((roosTowerAction (d m).E).obj P)) n).hom).1
  simp only [HomologicalComplex.comp_f, Category.assoc]
  apply biprod.hom_ext
  · apply product_degree_ext
    intro j
    simp only [Category.assoc]
    erw [comparison_fst_coordinate, map_fst_coordinate]
    simp only [Functor.mapHomologicalComplex_map_f]
    erw [← Functor.map_comp, comparison_fst_coordinate]
    apply HomologicalComplex.mapBifunctor.hom_ext
    intro p q hpq
    obtain ⟨i, rfl⟩ := (Equiv.addRight (1 : ℤ)).surjective q
    change p + (i + 1) = n + 1 at hpq
    change ι R (principalKoszul R t m) (roosF.obj P) p (i + 1) (n + 1) hpq ≫ _ = _
    erw [reassoc_of% hδ_shifted m P i p n hpq j]
    change _ = _ ≫ ((α m).app (P.asFunctor.obj (op j))).f n
    by_cases hp : p = 0
    · subst p
      have hi : i = n := by omega
      subst i
      simp only [Int.negOnePow_zero, one_smul, Category.assoc]
      exact (hα_natural (roosF.obj P) (P.asFunctor.obj (op j)) (n + 1) n
          ((roosχ P n).hom ≫ biprod.fst ≫
            (Pi.π (fun k : ℕ ↦ P.asFunctor.obj (op k)) j).f n)).symm
    · simp only [Linear.units_smul_comp, Category.assoc]
      rw [reassoc_of% hα_zero m (roosF.obj P) (i + 1) p (n + 1) hpq hp]
      rw [hα_zero m (P.asFunctor.obj (op j)) i p n (by omega) hp]
      simp
  · apply product_degree_ext
    intro j
    simp only [Category.assoc]
    erw [comparison_snd_coordinate, map_snd_coordinate]
    simp only [Functor.mapHomologicalComplex_map_f]
    erw [← Functor.map_comp, comparison_snd_coordinate]
    apply HomologicalComplex.mapBifunctor.hom_ext
    intro p q hpq
    obtain ⟨i, rfl⟩ := (Equiv.addRight (1 : ℤ)).surjective q
    change p + (i + 1) = n + 1 at hpq
    change ι R (principalKoszul R t m) (roosF.obj P) p (i + 1) (n + 1) hpq ≫ _ = _
    erw [reassoc_of% hδ_unshifted m P i p n hpq j]
    change _ = ((tensor R).obj ((principalKoszul R t m).X p)).map
      ((roosχ P i).hom ≫ biprod.snd ≫
        (Pi.π (fun k : ℕ ↦ P.asFunctor.obj (op k)) j).f (i + 1)) ≫
      ι R (principalKoszul R t m) (P.asFunctor.obj (op j)) p (i + 1) (n + 1) hpq ≫
        ((α m).app (P.asFunctor.obj (op j))).f (n + 1)
    by_cases hp : p = 0
    · subst p
      have hi : i = n := by omega
      subst i
      exact (hα_natural (roosF.obj P) (P.asFunctor.obj (op j)) (n + 1) (n + 1)
        ((roosχ P n).hom ≫ biprod.snd ≫
          (Pi.π (fun k : ℕ ↦ P.asFunctor.obj (op k)) j).f (n + 1))).symm
    · rw [reassoc_of% hα_zero m (roosF.obj P) (i + 1) p (n + 1) hpq hp]
      rw [hα_zero m (P.asFunctor.obj (op j)) (i + 1) p (n + 1) hpq hp]
      simp
end CategoryTheory.PerfectReductionRoos
