/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteOpenCoverRowSections
import WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.Exact
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts

/-! # The relative-image row evaluated on sections

Source: Stacks Project, Tag 03AZ, the relative row calculation.
(blueprint: new-finite-cover-row-comparison)
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale

variable {X Y : Scheme.{u}} (B : Type (u + 1)) [CommRing B]

/-- Evaluate a sheaf-valued functor at a coefficient sheaf and an etale test object.
Source: Stacks Project, Tag 03AZ.
(blueprint: new-finite-cover-row-comparison) -/
def finiteCoverRowEvaluation (T : Y.Etale)
    (M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)) :
    (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B) ⥤
      Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} B)) ⥤ ModuleCat.{u + 1} B :=
  (evaluation _ _).obj M ⋙ sheafToPresheaf Y.smallEtaleTopology _ ⋙
    (evaluation _ _).obj (op T)

instance finiteCoverRowEvaluation_additive (T : Y.Etale)
    (M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)) :
    (finiteCoverRowEvaluation B T M).Additive := by
  dsimp [finiteCoverRowEvaluation]
  infer_instance

variable (f : X ⟶ Y) {m : ℕ} (U : Fin m → X.Opens)
    (J : CochainComplex
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B) ⥤
        Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)) ℕ)
    (data : finiteOpenCoverOrderedData B f m U J)

/-- The degreewise comparison is the finite-biproduct comparison followed by the
localization comparison on each open intersection.
Source: Stacks Project, Tag 03AZ.
(blueprint: new-finite-cover-row-comparison) -/
def finiteCoverRowSectionsIso (T : Y.Etale)
    (M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)) (p q : ℕ) :
    (finiteCoverRowEvaluation B T M).obj
        ((finiteOpenCoverOrderedColumn B f U J data.hB p).X q) ≅
      finiteCoverSectionTerm B f T ((J.X q).obj M) U p := by
  letI := data.hB p q
  exact (Functor.mapBiproduct (finiteCoverRowEvaluation B T M)
    (fun a : Fin (p + 1) ↪o Fin m ↦
      J.X q ⋙ finiteCoverOpenImage B f (finiteCoverIntersection U a))) ≪≫
      biproduct.mapIso (fun a : Fin (p + 1) ↪o Fin m ↦
        finiteCoverImageSectionsIso B f (finiteCoverIntersection U a) ((J.X q).obj M) T)

/-- The comparison carries every coordinate projection to its named section comparison.
Source: Stacks Project, Tag 03AZ, finite products.
(blueprint: new-finite-cover-row-comparison) -/
@[reassoc]
theorem finiteCoverRowSectionsIso_hom_π (T : Y.Etale)
    (M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)) (p q : ℕ)
    (a : Fin (p + 1) ↪o Fin m) :
    (finiteCoverRowSectionsIso B f U J data T M p q).hom ≫
        biproduct.π (fun a : Fin (p + 1) ↪o Fin m ↦
          (finiteCoverSectionPresheaf B f T ((J.X q).obj M)).obj
            (op (⨅ k, U (a k)))) a =
      (finiteCoverRowEvaluation B T M).map
        (show (finiteOpenCoverOrderedColumn B f U J data.hB p).X q ⟶
            J.X q ⋙ finiteCoverOpenImage B f (finiteCoverIntersection U a) from by
            letI := data.hB p q
            exact biproduct.π (fun a : Fin (p + 1) ↪o Fin m ↦
              J.X q ⋙ finiteCoverOpenImage B f (finiteCoverIntersection U a)) a) ≫
        (finiteCoverImageSectionsIso B f (finiteCoverIntersection U a)
          ((J.X q).obj M) T).hom := by
  letI := data.hB p q
  simp [finiteCoverRowSectionsIso, finiteCoverSectionPresheaf,
    finiteCoverIntersection, Category.assoc]

/-- Horizontal maps become the alternating section restrictions.
Source: Stacks Project, Tag 03AZ. Project onto a final increasing tuple, use the
biproduct projection formulas, distribute evaluation over the finite signed sum,
and apply the proved section formula for the adjunction-unit restriction.
(blueprint: new-finite-cover-row-comparison) -/
theorem finiteCoverRowSectionsIso_d (T : Y.Etale)
    (M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)) (p q : ℕ) :
    (finiteCoverRowEvaluation B T M).map
        (finiteOpenCoverOrderedHorizontal B f U J data.hB p q) ≫
        (finiteCoverRowSectionsIso B f U J data T M (p + 1) q).hom =
      (finiteCoverRowSectionsIso B f U J data T M p q).hom ≫
        finiteCoverSectionDifferential B f T ((J.X q).obj M) U p := by
  letI := data.hB p q
  letI := data.hB (p + 1) q
  let ev := finiteCoverRowEvaluation B T M
  apply biproduct.hom_ext
  intro a
  rw [Category.assoc, finiteCoverRowSectionsIso_hom_π]
  rw [← Category.assoc, ← ev.map_comp]
  simp only [finiteOpenCoverOrderedHorizontal, biproduct.lift_π]
  simp only [Functor.map_sum, Functor.map_zsmul, Functor.map_comp,
    Preadditive.sum_comp, Preadditive.zsmul_comp, Category.assoc,
    finiteCoverSectionDifferential, finiteOrderedCechCoface,
    Preadditive.comp_sum, Preadditive.comp_zsmul, biproduct.lift_π]
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  let b := j.succAboveOrderEmb.trans a
  let h : finiteCoverIntersection U a ≤ finiteCoverIntersection U b :=
    le_iInf fun k ↦ iInf_le (fun l ↦ U (a l)) (j.succAbove k)
  let π := biproduct.π (fun b : Fin (p + 1) ↪o Fin m ↦
    J.X q ⋙ finiteCoverOpenImage B f (finiteCoverIntersection U b)) b
  have hr : ev.map (Functor.whiskerLeft (J.X q) (finiteCoverImageRestriction B f h)) ≫
      (finiteCoverImageSectionsIso B f (finiteCoverIntersection U a)
        ((J.X q).obj M) T).hom =
    (finiteCoverImageSectionsIso B f (finiteCoverIntersection U b)
      ((J.X q).obj M) T).hom ≫
      (finiteCoverSectionPresheaf B f T ((J.X q).obj M)).map (homOfLE h).op :=
    finiteCoverImageSectionsIso_restriction B f h ((J.X q).obj M) T
  calc
    _ = ev.map π ≫ ((finiteCoverImageSectionsIso B f (finiteCoverIntersection U b)
        ((J.X q).obj M) T).hom ≫
        (finiteCoverSectionPresheaf B f T ((J.X q).obj M)).map (homOfLE h).op) :=
      congrArg (fun t ↦ ev.map π ≫ t) hr
    _ = _ := by
      simpa only [Category.assoc] using
        (congrArg (fun t ↦ t ≫
          (finiteCoverSectionPresheaf B f T ((J.X q).obj M)).map (homOfLE h).op)
          (finiteCoverRowSectionsIso_hom_π B f U J data T M p q b)).symm

/-- The same comparison identifies the augmented term with restriction from the top.
Source: Stacks Project, Tag 03AN. Project onto a singleton intersection and use the
restriction comparison for its inclusion into the top open.
(blueprint: new-finite-cover-row-comparison) -/
theorem finiteCoverRowSectionsIso_augmentation (T : Y.Etale)
    (M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)) (q : ℕ) :
    (finiteCoverRowEvaluation B T M).map
        (finiteOpenCoverRowMap B f U J data.hB data.hId data.hComp q) ≫
        (finiteCoverRowSectionsIso B f U J data T M 0 q).hom =
      (finiteCoverImageSectionsIso B f ⊤ ((J.X q).obj M) T).hom ≫
        finiteCoverSectionAugmentation B f T ((J.X q).obj M) U := by
  letI := data.hB 0 q
  let ev := finiteCoverRowEvaluation B T M
  apply biproduct.hom_ext
  intro a
  rw [Category.assoc, finiteCoverRowSectionsIso_hom_π,
    ← Category.assoc, ← ev.map_comp]
  simp only [finiteOpenCoverRowMap, biproduct.lift_π,
    finiteCoverSectionAugmentation, Category.assoc]
  exact finiteCoverImageSectionsIso_restriction B f le_top ((J.X q).obj M) T

/-- Exactness of module sheaves follows from exactness on every test object.
Source: Stacks Project, Tag 03AZ. The presheaf sequence is exact pointwise;
exact sheafification takes it back to the given sheaf sequence.
(blueprint: new-finite-cover-row-comparison) -/
theorem finiteCoverSheafExact_of_sections
    (S : ShortComplex (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} B)))
    (h : ∀ T : Y.Etale, (S.map (sheafToPresheaf Y.smallEtaleTopology _ ⋙
      (evaluation _ _).obj (op T))).Exact) : S.Exact := by
  let P := S.map (sheafToPresheaf Y.smallEtaleTopology (ModuleCat.{u + 1} B))
  have hP : P.Exact := by
    rw [ShortComplex.exact_iff_evaluation]
    intro T
    exact h T.unop
  have hP' := hP.map (presheafToSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} B))
  exact ShortComplex.exact_of_iso
    (ShortComplex.mapNatIso S (sheafificationNatIso Y.smallEtaleTopology _)).symm hP'

/-- The augmentation short complex in a fixed vertical degree.
Source: Stacks Project, Tag 03AZ.
(blueprint: new-finite-cover-row-comparison) -/
abbrev finiteCoverAugmentedRow (q : ℕ) : ShortComplex
    (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B) ⥤
      Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} B)) :=
  ShortComplex.mk
    ((finiteOpenCoverRowAugmentation B f m U J data.hB data.hId data.hComp
      data.hComm data.hSq data.hAug).f q)
    (((finiteOpenCoverResolutionDoubleComplex B f m U J data.hB data.hComm data.hSq).d
      0 1).f q)
    (by rw [← HomologicalComplex.comp_f, data.hEps, HomologicalComplex.zero_f])

/-- The positive short complex in a fixed vertical degree.
Source: Stacks Project, Tag 03AZ.
(blueprint: new-finite-cover-row-comparison) -/
abbrev finiteCoverPositiveRow (p q : ℕ) : ShortComplex
    (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B) ⥤
      Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} B)) :=
  ShortComplex.mk
    (((finiteOpenCoverResolutionDoubleComplex B f m U J data.hB data.hComm data.hSq).d
      p (p + 1)).f q)
    (((finiteOpenCoverResolutionDoubleComplex B f m U J data.hB data.hComm data.hSq).d
      (p + 1) (p + 2)).f q)
    (by rw [← HomologicalComplex.comp_f, HomologicalComplex.d_comp_d,
      HomologicalComplex.zero_f])

/-- The beginning of the named row is exactly the augmented section complex.
Source: Stacks Project, Tags 03AN and 03AZ. The two component squares are the
proved augmentation and horizontal compatibility identities.
(blueprint: new-finite-cover-row-comparison) -/
def finiteCoverAugmentedRowSectionsIso (T : Y.Etale)
    (M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)) (q : ℕ) :
    (finiteCoverAugmentedRow B f U J data q).map (finiteCoverRowEvaluation B T M) ≅
      ShortComplex.mk
        (finiteCoverSectionAugmentation B f T ((J.X q).obj M) U)
        (finiteCoverSectionDifferential B f T ((J.X q).obj M) U 0)
        (finiteCoverSectionAugmentation_d B f T ((J.X q).obj M) U) :=
  ShortComplex.isoMk (finiteCoverImageSectionsIso B f ⊤ ((J.X q).obj M) T)
    (finiteCoverRowSectionsIso B f U J data T M 0 q)
    (finiteCoverRowSectionsIso B f U J data T M 1 q)
    (finiteCoverRowSectionsIso_augmentation B f U J data T M q).symm
    (by simpa [finiteOpenCoverResolutionDoubleComplex,
      finiteOpenCoverOrderedHorizontalHom] using
        (finiteCoverRowSectionsIso_d B f U J data T M 0 q).symm)

/-- Each positive short complex of the named row is the section Cech complex.
Source: Stacks Project, Tag 03AZ. Use the three degreewise comparisons and the
proved horizontal compatibility twice.
(blueprint: new-finite-cover-row-comparison) -/
def finiteCoverPositiveRowSectionsIso (T : Y.Etale)
    (M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)) (p q : ℕ) :
    (finiteCoverPositiveRow B f U J data p q).map (finiteCoverRowEvaluation B T M) ≅
      ShortComplex.mk
        (finiteCoverSectionDifferential B f T ((J.X q).obj M) U p)
        (finiteCoverSectionDifferential B f T ((J.X q).obj M) U (p + 1))
        (finiteCoverSectionDifferential_squared B f T ((J.X q).obj M) U p) :=
  ShortComplex.isoMk (finiteCoverRowSectionsIso B f U J data T M p q)
    (finiteCoverRowSectionsIso B f U J data T M (p + 1) q)
    (finiteCoverRowSectionsIso B f U J data T M (p + 2) q)
    (by simpa [finiteOpenCoverResolutionDoubleComplex,
      finiteOpenCoverOrderedHorizontalHom] using
        (finiteCoverRowSectionsIso_d B f U J data T M p q).symm)
    (by simpa [finiteOpenCoverResolutionDoubleComplex,
      finiteOpenCoverOrderedHorizontalHom] using
        (finiteCoverRowSectionsIso_d B f U J data T M (p + 1) q).symm)

end AlgebraicGeometry.Etale
