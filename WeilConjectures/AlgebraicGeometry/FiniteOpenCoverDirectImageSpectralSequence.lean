/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMap
public import WeilConjectures.CategoryTheory.Abelian.RightDerived.Comp
public import WeilConjectures.CategoryTheory.Sites.GeometricMorphism
public import Mathlib.AlgebraicTopology.SimplicialObject.Basic
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.CategoryTheory.FiberedCategory.Grothendieck
public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Adjunction.CompositionIso
public import WeilConjectures.CategoryTheory.SiteContinuousPushforwardSheaf
public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
public import WeilConjectures.CategoryTheory.Grothendieck.GrothendieckTopos
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import WeilConjectures.Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import WeilConjectures.CategoryTheory.RightDerivedSingleUnitHomologyComparison
public import WeilConjectures.CategoryTheory.DoubleComplexTotal
public import WeilConjectures.CategoryTheory.CanonicalFiltration
public import WeilConjectures.Algebra.Homology.FirstQuadrantAugmentation
public import WeilConjectures.CategoryTheory.KInjectiveBridge
public import WeilConjectures.AlgebraicGeometry.Sites.KInjectiveComparisonPrinciple
public import WeilConjectures.FromJoel.Algebra.Homology.Embedding.ExtendMap
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
public import WeilConjectures.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
public import WeilConjectures.Mathlib.Algebra.Homology.SpectralSequence.Basic
public import WeilConjectures.Mathlib.Algebra.Homology.TotalComplex
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.Order.Fin.Basic

public import WeilConjectures.Algebra.Homology.ExactCouple.DoubleComplex
public import WeilConjectures.Algebra.Homology.TotalComplexRowResolution
public import WeilConjectures.Algebra.Homology.TermwiseBiproductHomology
public import WeilConjectures.AlgebraicGeometry.FiniteOpenCoverPositiveRows
public import WeilConjectures.AlgebraicGeometry.FiniteOpenCoverRestrictionComposition
public import WeilConjectures.AlgebraicGeometry.FiniteOpenCoverRowDescent
public import WeilConjectures.CategoryTheory.CompRightDerivedNatural
public import WeilConjectures.CategoryTheory.FiniteOrderedCechSquare
public import WeilConjectures.CategoryTheory.FunctorialResolutionRightDerived
public import WeilConjectures.CategoryTheory.SpectralSequence.Vanishing
public import WeilConjectures.CategoryTheory.TotalSiteAugmentationData.TotalSiteInjectiveAugmentationExactness
public import WeilConjectures.DeligneLaumon.DoubleComplexSpectralSequenceFromOne
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence

/-! # Ordered finite-open-cover spectral sequence for etale direct images

Source: Stacks Project, sites-cohomology.tex, Tag 03AZ, relative ordered variant;
homology.tex, Tags 0130 and 0132
(blueprint: lem-per-finite-open-cover-direct-image-spectral-sequence).

The spectral sequence and its finite abutment filtration live in the functor category
of module sheaves. The first-page comparison with the actual higher direct images is
normalized by the canonical comparison on restricted injective resolutions. Thus the
first differential is the alternating sum of the canonical restrictions.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

variable {X Y : Scheme.{u}} (B : Type (u + 1)) [CommRing B]

/-- Restriction to an open followed by direct image to Y, before deriving.
Source: Stacks 03AZ, relative ordered variant
(blueprint: lem-per-finite-open-cover-direct-image-spectral-sequence). -/
def finiteCoverOpenImage (f : X ⟶ Y) (U : X.Opens) :
    Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B) ⥤
      Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} B) :=
  upperStar (ModuleCat.{u + 1} B) U.ι ⋙ lowerStar (ModuleCat.{u + 1} B) (U.ι ≫ f)

/-- The actual higher direct image of the restricted sheaf, as a functor in M.
Source: Stacks 03AZ, relative variant, and derived.tex, Tag 013K
(blueprint: lem-per-finite-open-cover-direct-image-spectral-sequence). -/
def finiteCoverHigherImage (f : X ⟶ Y) (U : X.Opens) (q : ℕ) :
    Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B) ⥤
      Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} B) :=
  upperStar (ModuleCat.{u + 1} B) U.ι ⋙
    (lowerStar (ModuleCat.{u + 1} B) (U.ι ≫ f)).rightDerived q

/-- Canonical restriction from the image over U to that over V contained in U.
It is the inverse/direct-image adjunction unit, followed by the canonical composition
isomorphisms; on sections this is ordinary restriction, with its B-action.
Source: Stacks 03AZ and 00XZ
(blueprint: lem-per-finite-open-cover-direct-image-spectral-sequence). -/
def finiteCoverImageRestriction (f : X ⟶ Y) {U V : X.Opens} (h : V ≤ U) :
    finiteCoverOpenImage B f U ⟶ finiteCoverOpenImage B f V :=
  Functor.whiskerLeft (upperStar (ModuleCat.{u + 1} B) U.ι)
      (Functor.whiskerRight (upperStarLowerStarAdjunction (ModuleCat.{u + 1} B)
        (X.homOfLE h)).unit (lowerStar (ModuleCat.{u + 1} B) (U.ι ≫ f))) ≫
    Functor.whiskerLeft (upperStar (ModuleCat.{u + 1} B) U.ι ⋙
      upperStar (ModuleCat.{u + 1} B) (X.homOfLE h))
      (lowerStarComp (ModuleCat.{u + 1} B) (X.homOfLE h) (U.ι ≫ f)
        (V.ι ≫ f) (by simp)).hom ≫
    Functor.whiskerRight (upperStarComp (ModuleCat.{u + 1} B) (X.homOfLE h) U.ι
      V.ι (by simp)).inv (lowerStar (ModuleCat.{u + 1} B) (V.ι ≫ f))

/-- Intersection indexed by a strictly increasing tuple of cover indices.
Source: Stacks 03AZ, relative ordered variant
(blueprint: lem-per-finite-open-cover-direct-image-spectral-sequence). -/
def finiteCoverIntersection {m p : ℕ} (U : Fin m → X.Opens)
    (a : Fin (p + 1) ↪o Fin m) : X.Opens :=
  ⨅ k : Fin (p + 1), U (a k)

/-- The first-page direct sum of the actual higher direct images.
The index type is finite, and empty when p is at least m.
Source: Stacks 03AZ, relative ordered variant
(blueprint: lem-per-finite-open-cover-direct-image-spectral-sequence). -/
def finiteCoverPageOne (f : X ⟶ Y) {m : ℕ} (U : Fin m → X.Opens) (p q : ℕ) :
    Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B) ⥤
      Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} B) :=
  biproduct (fun a : Fin (p + 1) ↪o Fin m ↦
    finiteCoverHigherImage B f (finiteCoverIntersection U a) q)

/-- Projection to one ordered summand of the first-page direct sum.
Source: Stacks 03AZ, relative ordered variant
(blueprint: lem-per-finite-open-cover-direct-image-spectral-sequence). -/
def finiteCoverPageOneProjection (f : X ⟶ Y) {m : ℕ} (U : Fin m → X.Opens)
    (p q : ℕ) (a : Fin (p + 1) ↪o Fin m) :
    finiteCoverPageOne B f U p q ⟶
      finiteCoverHigherImage B f (finiteCoverIntersection U a) q :=
  biproduct.π (fun b : Fin (p + 1) ↪o Fin m ↦
    finiteCoverHigherImage B f (finiteCoverIntersection U b) q) a

/-- Higher restriction transported by specified restricted-resolution comparisons.
Source: Stacks 03AZ, relative ordered variant, and derived.tex, Tag 013P
(blueprint: lem-per-finite-open-cover-direct-image-spectral-sequence). -/
def finiteCoverHigherRestriction (f : X ⟶ Y) {U V : X.Opens} (h : V ≤ U) (q : ℕ)
    (cU : (finiteCoverOpenImage B f U).rightDerived q ≅ finiteCoverHigherImage B f U q)
    (cV : (finiteCoverOpenImage B f V).rightDerived q ≅ finiteCoverHigherImage B f V q) :
    finiteCoverHigherImage B f U q ⟶ finiteCoverHigherImage B f V q :=
  cU.inv ≫ NatTrans.rightDerived (finiteCoverImageRestriction B f h) q ≫ cV.hom

/-- The direct-image complex `q ↦ J^q ⋙ finiteCoverOpenImage B f V` on an open `V`, with
vertical differential induced by that of `J`.
Source: Stacks 03AZ, relative ordered variant, step 3
(blueprint: lem-per-finite-open-cover-direct-image-spectral-sequence). -/
def finiteOpenCoverColumn
    (f : X ⟶ Y) (V : X.Opens)
    (J : CochainComplex
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B) ⥤
        Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)) ℕ) :
    CochainComplex
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B) ⥤
        Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} B)) ℕ :=
  { X := fun q => J.X q ⋙ finiteCoverOpenImage B f V
    d := fun q r => Functor.whiskerRight (J.d q r) (finiteCoverOpenImage B f V)
    shape := by
      intro i j hij
      rw [J.shape i j hij]
      exact Functor.whiskerRight_zero _
    d_comp_d' := by
      intro q r s hqr hrs
      rw [← Functor.whiskerRight_comp, J.d_comp_d q r s]
      exact Functor.whiskerRight_zero _ }

/-- The restriction chain map from the column on `W` to the column on `V ≤ W`, termwise the
canonical restriction `finiteCoverImageRestriction`.
Source: Stacks 03AZ, relative ordered variant, step 3
(blueprint: lem-per-finite-open-cover-direct-image-spectral-sequence). -/
def finiteOpenCoverColumnMap
    (f : X ⟶ Y) {V W : X.Opens} (h : V ≤ W)
    (J : CochainComplex
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B) ⥤
        Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)) ℕ) :
    finiteOpenCoverColumn B f W J ⟶ finiteOpenCoverColumn B f V J :=
  { f := fun q =>
      Functor.whiskerLeft (J.X q) (finiteCoverImageRestriction B f h)
    comm' := by
      intro i j hij
      dsimp [finiteOpenCoverColumn]
      apply NatTrans.ext
      funext M
      exact ((finiteCoverImageRestriction B f h).naturality ((J.d i j).app M)).symm }

/-- The open-dependent coefficient presheaf `V ↦ J ⋙ finiteCoverOpenImage B f V`, with the
restriction chain maps; `hId` and `hComp` are its functoriality equations.
Source: Stacks 03AZ, relative ordered variant, step 3
(blueprint: lem-per-finite-open-cover-direct-image-spectral-sequence). -/
def finiteOpenCoverCoefficient
    (f : X ⟶ Y)
    (J : CochainComplex
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B) ⥤
        Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)) ℕ)
    (hId : ∀ V : X.Opens,
      finiteOpenCoverColumnMap B f (V := V) (W := V) le_rfl J = 𝟙 _)
    (hComp : ∀ (V W Z : X.Opens) (hVW : V ≤ W) (hWZ : W ≤ Z),
      finiteOpenCoverColumnMap B f (V := V) (W := Z) (hVW.trans hWZ) J =
        finiteOpenCoverColumnMap B f (V := W) (W := Z) hWZ J ≫
          finiteOpenCoverColumnMap B f (V := V) (W := W) hVW J) :
    X.Opensᵒᵖ ⥤ CochainComplex
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B) ⥤
        Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} B)) ℕ where
  obj V := finiteOpenCoverColumn B f V.unop J
  map g := finiteOpenCoverColumnMap B f (leOfHom g.unop) J
  map_id V := hId V.unop
  map_comp g h := hComp _ _ _ (leOfHom h.unop) (leOfHom g.unop)

/-- Column `p` of the ordered Cech/injective-resolution double complex:
`D^{p,q} = ⊕_{a : Fin (p+1) ↪o Fin m} (f_{U_a})_*(J^q|_{U_a})`, zero when `p ≥ m`.
Source: Stacks 03AZ, relative ordered variant, step 3
(blueprint: lem-per-finite-open-cover-direct-image-spectral-sequence). -/
def finiteOpenCoverOrderedColumn
    (f : X ⟶ Y) {m : ℕ} (U : Fin m → X.Opens)
    (J : CochainComplex
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B) ⥤
        Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)) ℕ)
    (hB : ∀ p q : ℕ, HasBiproduct
      (fun a : Fin (p + 1) ↪o Fin m ↦
        J.X q ⋙ finiteCoverOpenImage B f (finiteCoverIntersection U a)))
    (p : ℕ) : CochainComplex
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B) ⥤
        Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} B)) ℕ :=
  { X := fun q => by
      letI := hB p q
      exact biproduct (fun a : Fin (p + 1) ↪o Fin m ↦
        J.X q ⋙ finiteCoverOpenImage B f (finiteCoverIntersection U a))
    d := fun q r => by
      letI := hB p q
      letI := hB p r
      exact biproduct.map (fun a : Fin (p + 1) ↪o Fin m ↦
        Functor.whiskerRight (J.d q r)
          (finiteCoverOpenImage B f (finiteCoverIntersection U a)))
    shape := by
      intro i j hij
      letI := hB p i
      letI := hB p j
      rw [J.shape i j hij]
      apply biproduct.hom_ext
      intro a
      simp
    d_comp_d' := by
      intro q r s hqr hrs
      letI := hB p q
      letI := hB p r
      letI := hB p s
      apply biproduct.hom_ext
      intro a
      simp only [Category.assoc, biproduct.map_π_assoc, biproduct.map_π,
        ← Functor.whiskerRight_comp, J.d_comp_d, Functor.whiskerRight_zero,
        comp_zero, zero_comp] }

/-- The horizontal Cech map in vertical degree `q`: the alternating sum over the deleted
index `j` of the canonical restrictions from `U_{a ∘ δ_j}` to `U_a`.
Source: Stacks 03AZ, relative ordered variant, step 3
(blueprint: lem-per-finite-open-cover-direct-image-spectral-sequence). -/
def finiteOpenCoverOrderedHorizontal
    (f : X ⟶ Y) {m : ℕ} (U : Fin m → X.Opens)
    (J : CochainComplex
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B) ⥤
        Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)) ℕ)
    (hB : ∀ p q : ℕ, HasBiproduct
      (fun a : Fin (p + 1) ↪o Fin m ↦
        J.X q ⋙ finiteCoverOpenImage B f (finiteCoverIntersection U a)))
    (p q : ℕ) :
    (finiteOpenCoverOrderedColumn B f U J hB p).X q ⟶
      (finiteOpenCoverOrderedColumn B f U J hB (p + 1)).X q := by
  letI := hB p q
  letI := hB (p + 1) q
  exact biproduct.lift (fun a : Fin (p + 2) ↪o Fin m ↦
    ∑ j : Fin (p + 2), (-1 : ℤ) ^ (j : ℕ) •
      (biproduct.π (fun b : Fin (p + 1) ↪o Fin m ↦
        J.X q ⋙ finiteCoverOpenImage B f (finiteCoverIntersection U b))
        (j.succAboveOrderEmb.trans a) ≫
        Functor.whiskerLeft (J.X q)
          (finiteCoverImageRestriction B f
            (le_iInf fun k ↦ iInf_le (fun l ↦ U (a l)) (j.succAbove k)))))

/-- The horizontal Cech maps as a chain map between consecutive columns.
Source: Stacks 03AZ, relative ordered variant, step 3
(blueprint: lem-per-finite-open-cover-direct-image-spectral-sequence). -/
def finiteOpenCoverOrderedHorizontalHom
    (f : X ⟶ Y) {m : ℕ} (U : Fin m → X.Opens)
    (J : CochainComplex
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B) ⥤
        Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)) ℕ)
    (hB : ∀ p q : ℕ, HasBiproduct
      (fun a : Fin (p + 1) ↪o Fin m ↦
        J.X q ⋙ finiteCoverOpenImage B f (finiteCoverIntersection U a)))
    (hComm : ∀ (p q r : ℕ) (hqr : (ComplexShape.up ℕ).Rel q r),
      finiteOpenCoverOrderedHorizontal B f U J hB p q ≫
          ((finiteOpenCoverOrderedColumn B f U J hB (p + 1)).d q r) =
        ((finiteOpenCoverOrderedColumn B f U J hB p).d q r) ≫
          finiteOpenCoverOrderedHorizontal B f U J hB p r)
    (p : ℕ) :
    finiteOpenCoverOrderedColumn B f U J hB p ⟶
      finiteOpenCoverOrderedColumn B f U J hB (p + 1) :=
  { f := fun q => finiteOpenCoverOrderedHorizontal B f U J hB p q
    comm' := fun q r hqr ↦ hComm p q r hqr }

/-- The named ordered Cech/injective-resolution double complex of step 3, with the
ordered columns and the alternating horizontal maps.
Source: Stacks 03AZ, relative ordered variant, step 3
(blueprint: lem-per-finite-open-cover-direct-image-spectral-sequence). -/
noncomputable def finiteOpenCoverResolutionDoubleComplex
    (f : X ⟶ Y) (m : ℕ) (U : Fin m → X.Opens)
    (J : CochainComplex
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B) ⥤
        Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)) ℕ)
    (hB : ∀ p q : ℕ, HasBiproduct
      (fun a : Fin (p + 1) ↪o Fin m ↦
        J.X q ⋙ finiteCoverOpenImage B f (finiteCoverIntersection U a)))
    (hComm : ∀ (p q r : ℕ) (hqr : (ComplexShape.up ℕ).Rel q r),
      finiteOpenCoverOrderedHorizontal B f U J hB p q ≫
          ((finiteOpenCoverOrderedColumn B f U J hB (p + 1)).d q r) =
        ((finiteOpenCoverOrderedColumn B f U J hB p).d q r) ≫
          finiteOpenCoverOrderedHorizontal B f U J hB p r)
    (hSq : ∀ p : ℕ,
      finiteOpenCoverOrderedHorizontalHom B f U J hB hComm p ≫
          finiteOpenCoverOrderedHorizontalHom B f U J hB hComm (p + 1) = 0) :
    HomologicalComplex₂
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B) ⥤
        Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} B))
      (ComplexShape.up ℕ) (ComplexShape.up ℕ) :=
  HomologicalComplex.mk
    (fun p ↦ finiteOpenCoverOrderedColumn B f U J hB p)
    (fun p q ↦ if h : p + 1 = q then
      finiteOpenCoverOrderedHorizontalHom B f U J hB hComm p ≫
        eqToHom (congrArg (fun n ↦ finiteOpenCoverOrderedColumn B f U J hB n) h)
      else 0)
    (by
      intro p q hpq
      rw [ComplexShape.up_Rel] at hpq
      split_ifs <;> simp_all [ComplexShape.up_Rel])
    (by
      intro p q r hpq hqr
      rw [ComplexShape.up_Rel] at hpq hqr
      simp only [dif_pos hpq, dif_pos hqr, Category.assoc]
      subst q
      subst r
      simpa using hSq p)

/-- The source complex `f_* J`, as the coefficient at the terminal open.
Source: Stacks 03AZ, relative ordered variant, step 6
(blueprint: lem-per-finite-open-cover-direct-image-spectral-sequence). -/
def finiteOpenCoverSource
    (f : X ⟶ Y)
    (J : CochainComplex
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B) ⥤
        Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)) ℕ)
    (hId : ∀ V : X.Opens,
      finiteOpenCoverColumnMap B f (V := V) (W := V) le_rfl J = 𝟙 _)
    (hComp : ∀ (V W Z : X.Opens) (hVW : V ≤ W) (hWZ : W ≤ Z),
      finiteOpenCoverColumnMap B f (V := V) (W := Z) (hVW.trans hWZ) J =
        finiteOpenCoverColumnMap B f (V := W) (W := Z) hWZ J ≫
          finiteOpenCoverColumnMap B f (V := V) (W := W) hVW J) :
    CochainComplex
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B) ⥤
        Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} B)) ℕ :=
  (finiteOpenCoverCoefficient B f J hId hComp).obj (Opposite.op ⊤)

/-- The row augmentation in degree `q`: restriction from `X` to each `U_i`.
Source: Stacks 03AZ, relative ordered variant, step 6
(blueprint: lem-per-finite-open-cover-direct-image-spectral-sequence). -/
def finiteOpenCoverRowMap
    (f : X ⟶ Y) {m : ℕ} (U : Fin m → X.Opens)
    (J : CochainComplex
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B) ⥤
        Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)) ℕ)
    (hB : ∀ p q : ℕ, HasBiproduct
      (fun a : Fin (p + 1) ↪o Fin m ↦
        J.X q ⋙ finiteCoverOpenImage B f (finiteCoverIntersection U a)))
    (hId : ∀ V : X.Opens,
      finiteOpenCoverColumnMap B f (V := V) (W := V) le_rfl J = 𝟙 _)
    (hComp : ∀ (V W Z : X.Opens) (hVW : V ≤ W) (hWZ : W ≤ Z),
      finiteOpenCoverColumnMap B f (V := V) (W := Z) (hVW.trans hWZ) J =
        finiteOpenCoverColumnMap B f (V := W) (W := Z) hWZ J ≫
          finiteOpenCoverColumnMap B f (V := V) (W := W) hVW J)
    (q : ℕ) :
    (finiteOpenCoverSource B f J hId hComp).X q ⟶
      (finiteOpenCoverOrderedColumn B f U J hB 0).X q := by
  letI := hB 0 q
  exact biproduct.lift (fun a : Fin 1 ↪o Fin m ↦
    Functor.whiskerLeft (J.X q)
      (finiteCoverImageRestriction B f (le_top : finiteCoverIntersection U a ≤ ⊤)))

/-- The row augmentation `f_* J ⟶ D^{0,•}` as a chain map.
Source: Stacks 03AZ, relative ordered variant, step 6
(blueprint: lem-per-finite-open-cover-direct-image-spectral-sequence). -/
def finiteOpenCoverRowAugmentation
    (f : X ⟶ Y) (m : ℕ) (U : Fin m → X.Opens)
    (J : CochainComplex
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B) ⥤
        Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)) ℕ)
    (hB : ∀ p q : ℕ, HasBiproduct
      (fun a : Fin (p + 1) ↪o Fin m ↦
        J.X q ⋙ finiteCoverOpenImage B f (finiteCoverIntersection U a)))
    (hId : ∀ V : X.Opens,
      finiteOpenCoverColumnMap B f (V := V) (W := V) le_rfl J = 𝟙 _)
    (hComp : ∀ (V W Z : X.Opens) (hVW : V ≤ W) (hWZ : W ≤ Z),
      finiteOpenCoverColumnMap B f (V := V) (W := Z) (hVW.trans hWZ) J =
        finiteOpenCoverColumnMap B f (V := W) (W := Z) hWZ J ≫
          finiteOpenCoverColumnMap B f (V := V) (W := W) hVW J)
    (hComm : ∀ (p q r : ℕ) (hqr : (ComplexShape.up ℕ).Rel q r),
      finiteOpenCoverOrderedHorizontal B f U J hB p q ≫
          ((finiteOpenCoverOrderedColumn B f U J hB (p + 1)).d q r) =
        ((finiteOpenCoverOrderedColumn B f U J hB p).d q r) ≫
          finiteOpenCoverOrderedHorizontal B f U J hB p r)
    (hSq : ∀ p : ℕ,
      finiteOpenCoverOrderedHorizontalHom B f U J hB hComm p ≫
          finiteOpenCoverOrderedHorizontalHom B f U J hB hComm (p + 1) = 0)
    (hAug : ∀ q r : ℕ, (ComplexShape.up ℕ).Rel q r →
      finiteOpenCoverRowMap B f U J hB hId hComp q ≫
          ((finiteOpenCoverOrderedColumn B f U J hB 0).d q r) =
        (finiteOpenCoverSource B f J hId hComp).d q r ≫
          finiteOpenCoverRowMap B f U J hB hId hComp r) :
    finiteOpenCoverSource B f J hId hComp ⟶
      (finiteOpenCoverResolutionDoubleComplex B f m U J hB hComm hSq).X 0 :=
  { f := fun q => finiteOpenCoverRowMap B f U J hB hId hComp q
    comm' := fun q r hqr ↦ hAug q r hqr }

/-- Coherence data for the ordered Cech/injective-resolution construction: finite biproducts,
functoriality of the restrictions, the double-complex equations and the row augmentation
equations. All fields are propositions.
Source: Stacks 03AZ, relative ordered variant, steps 3 and 6
(blueprint: lem-per-finite-open-cover-direct-image-spectral-sequence). -/
structure finiteOpenCoverOrderedData
    (f : X ⟶ Y) (m : ℕ) (U : Fin m → X.Opens)
    (J : CochainComplex
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B) ⥤
        Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)) ℕ) where
  hB : ∀ p q : ℕ, HasBiproduct
    (fun a : Fin (p + 1) ↪o Fin m ↦
      J.X q ⋙ finiteCoverOpenImage B f (finiteCoverIntersection U a))
  hId : ∀ V : X.Opens,
    finiteOpenCoverColumnMap B f (V := V) (W := V) le_rfl J = 𝟙 _
  hComp : ∀ (V W Z : X.Opens) (hVW : V ≤ W) (hWZ : W ≤ Z),
    finiteOpenCoverColumnMap B f (V := V) (W := Z) (hVW.trans hWZ) J =
      finiteOpenCoverColumnMap B f (V := W) (W := Z) hWZ J ≫
        finiteOpenCoverColumnMap B f (V := V) (W := W) hVW J
  hComm : ∀ (p q r : ℕ) (hqr : (ComplexShape.up ℕ).Rel q r),
    finiteOpenCoverOrderedHorizontal B f U J hB p q ≫
        ((finiteOpenCoverOrderedColumn B f U J hB (p + 1)).d q r) =
      ((finiteOpenCoverOrderedColumn B f U J hB p).d q r) ≫
        finiteOpenCoverOrderedHorizontal B f U J hB p r
  hSq : ∀ p : ℕ,
    finiteOpenCoverOrderedHorizontalHom B f U J hB hComm p ≫
        finiteOpenCoverOrderedHorizontalHom B f U J hB hComm (p + 1) = 0
  hAug : ∀ q r : ℕ, (ComplexShape.up ℕ).Rel q r →
    finiteOpenCoverRowMap B f U J hB hId hComp q ≫
        ((finiteOpenCoverOrderedColumn B f U J hB 0).d q r) =
      (finiteOpenCoverSource B f J hId hComp).d q r ≫
        finiteOpenCoverRowMap B f U J hB hId hComp r
  hEps : finiteOpenCoverRowAugmentation B f m U J hB hId hComp hComm hSq hAug ≫
      (finiteOpenCoverResolutionDoubleComplex B f m U J hB hComm hSq).d 0 1 = 0

set_option maxHeartbeats 1200000 in
-- The normalized first-page differential has several dependent functor-category composites.
end AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Etale

private theorem finiteOpenCoverOrderedHorizontal_comm
    (f : X ⟶ Y) {m : ℕ} (U : Fin m → X.Opens)
    (J : CochainComplex
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B) ⥤
        Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)) ℕ)
    (hB : ∀ p q : ℕ, HasBiproduct
      (fun a : Fin (p + 1) ↪o Fin m ↦
        J.X q ⋙ finiteCoverOpenImage B f (finiteCoverIntersection U a)))
    (p q r : ℕ) :
    finiteOpenCoverOrderedHorizontal B f U J hB p q ≫
        ((finiteOpenCoverOrderedColumn B f U J hB (p + 1)).d q r) =
      ((finiteOpenCoverOrderedColumn B f U J hB p).d q r) ≫
        finiteOpenCoverOrderedHorizontal B f U J hB p r := by
  letI := hB p q
  letI := hB p r
  letI := hB (p + 1) q
  letI := hB (p + 1) r
  apply biproduct.hom_ext
  intro a
  simp only [finiteOpenCoverOrderedHorizontal, finiteOpenCoverOrderedColumn,
    Category.assoc, biproduct.map_π, biproduct.lift_π_assoc, biproduct.lift_π,
    Preadditive.sum_comp, Preadditive.comp_sum, Preadditive.zsmul_comp,
    Preadditive.comp_zsmul, biproduct.map_π_assoc]
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  congr 1
  exact (finiteOpenCoverColumnMap B f
    (le_iInf fun k ↦ iInf_le (fun l ↦ U (a l)) (j.succAbove k)) J).comm q r

private def finiteCoverDerivedComparison (f : X ⟶ Y) (V : X.Opens) (q : ℕ) :
    (finiteCoverOpenImage B f V).rightDerived q ≅ finiteCoverHigherImage B f V q :=
  Functor.compRightDerivedIso _ _ (fun I _ ↦ by
    have := injective_upperStar_obj_of_etale B V.ι I
    exact Functor.rightAcyclic_of_injective
      ((upperStar (ModuleCat.{u + 1} B) V.ι).obj I)) q

private def finiteCoverTopImageIso (f : X ⟶ Y) :
    lowerStar (ModuleCat.{u + 1} B) f ≅ finiteCoverOpenImage B f (⊤ : X.Opens) := by
  let A := ModuleCat.{u + 1} B
  let j := (⊤ : X.Opens).ι
  letI : IsIso j := by
    change IsIso X.topIso.hom
    infer_instance
  exact (Functor.leftUnitor (lowerStar A f)).symm ≪≫
    Functor.isoWhiskerRight (asIso (upperStarLowerStarAdjunction A j).unit)
      (lowerStar A f) ≪≫
    Functor.associator (upperStar A j) (lowerStar A j) (lowerStar A f) ≪≫
    Functor.isoWhiskerLeft (upperStar A j) (lowerStarComp A j f)

private theorem finiteOpenCoverOrderedHorizontal_squared (p q : ℕ) :
    finiteOpenCoverOrderedHorizontal B f U J hB p q ≫
      finiteOpenCoverOrderedHorizontal B f U J hB (p + 1) q = 0 := by
  let F := finiteOpenCoverCoefficient B f J hId hComp ⋙
    HomologicalComplex.eval _ (ComplexShape.up ℕ) q
  let hF (r : ℕ) : HasBiproduct
      (fun a : Fin (r + 1) ↪o Fin m ↦ F.obj (Opposite.op (⨅ k, U (a k)))) := hB r q
  have he (r : ℕ) : finiteOpenCoverOrderedHorizontal B f U J hB r q =
      ∑ j : Fin (r + 2), (-1 : ℤ) ^ (j : ℕ) • finiteOrderedCechCoface F U hF r j := by
    letI := hB r q
    letI := hB (r + 1) q
    apply biproduct.hom_ext
    intro a
    simp only [finiteOpenCoverOrderedHorizontal, finiteOrderedCechCoface,
      Preadditive.sum_comp, Preadditive.zsmul_comp, biproduct.lift_π]
    change _ = ∑ j : Fin (r + 2), (-1 : ℤ) ^ (j : ℕ) •
      (biproduct.lift (fun a ↦ biproduct.π
        (fun b : Fin (r + 1) ↪o Fin m ↦ F.obj (Opposite.op (⨅ k, U (b k))))
        (j.succAboveOrderEmb.trans a) ≫
        F.map (homOfLE (le_iInf fun k ↦
          iInf_le (fun l ↦ U (a l)) (j.succAbove k))).op)) ≫
        biproduct.π (fun a : Fin (r + 2) ↪o Fin m ↦
          F.obj (Opposite.op (⨅ k, U (a k)))) a
    simp only [biproduct.lift_π]
    rfl
  rw [he p, he (p + 1)]
  exact finiteOrderedCechDifferential_squared F U hF p

private theorem finiteOpenCoverRowMap_comm (q r : ℕ) :
    finiteOpenCoverRowMap B f U J hB hId hComp q ≫
        (finiteOpenCoverOrderedColumn B f U J hB 0).d q r =
      (finiteOpenCoverSource B f J hId hComp).d q r ≫
        finiteOpenCoverRowMap B f U J hB hId hComp r := by
  letI := hB 0 q
  letI := hB 0 r
  apply biproduct.hom_ext
  intro a
  simp only [finiteOpenCoverRowMap, finiteOpenCoverOrderedColumn,
    Category.assoc, biproduct.lift_π, biproduct.map_π, biproduct.lift_π_assoc]
  exact (finiteOpenCoverColumnMap B f
    (le_top : finiteCoverIntersection U a ≤ ⊤) J).comm q r

private theorem finiteOpenCoverRowMap_horizontal (q : ℕ) :
    finiteOpenCoverRowMap B f U J hB hId hComp q ≫
      finiteOpenCoverOrderedHorizontal B f U J hB 0 q = 0 := by
  letI := hB 0 q
  letI := hB 1 q
  apply biproduct.hom_ext
  intro a
  simp only [finiteOpenCoverRowMap, finiteOpenCoverOrderedHorizontal,
    Category.assoc, biproduct.lift_π, Preadditive.comp_sum,
    Preadditive.comp_zsmul, biproduct.lift_π_assoc, zero_comp]
  have h (j : Fin 2) :
      Functor.whiskerLeft (J.X q)
        (finiteCoverImageRestriction B f
          (le_top : finiteCoverIntersection U (j.succAboveOrderEmb.trans a) ≤ ⊤)) ≫
        Functor.whiskerLeft (J.X q)
          (finiteCoverImageRestriction B f
            (le_iInf fun k ↦ iInf_le (fun l ↦ U (a l)) (j.succAbove k))) =
      Functor.whiskerLeft (J.X q)
        (finiteCoverImageRestriction B f (le_top : finiteCoverIntersection U a ≤ ⊤)) := by
    exact (congrArg (fun k ↦ k.f q) (hComp (finiteCoverIntersection U a)
      (finiteCoverIntersection U (j.succAboveOrderEmb.trans a)) ⊤
      (le_iInf fun k ↦ iInf_le (fun l ↦ U (a l)) (j.succAbove k)) le_top)).symm
  simp only [h, Fin.sum_univ_two]
  simp

private theorem finiteOpenCoverOrderedDataOfRestrictions (f : X ⟶ Y) {m : ℕ}
    (U : Fin m → X.Opens)
    (J : CochainComplex
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B) ⥤
        Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)) ℕ)
    (hRid : ∀ V : X.Opens, finiteCoverImageRestriction B f
      (U := V) (V := V) le_rfl = 𝟙 _)
    (hRcomp : ∀ (V W Z : X.Opens) (hVW : V ≤ W) (hWZ : W ≤ Z),
      finiteCoverImageRestriction B f (hVW.trans hWZ) =
        finiteCoverImageRestriction B f hWZ ≫ finiteCoverImageRestriction B f hVW) :
    finiteOpenCoverOrderedData B f m U J := by
  let hB (p q : ℕ) : HasBiproduct
      (fun a : Fin (p + 1) ↪o Fin m ↦
        J.X q ⋙ finiteCoverOpenImage B f (finiteCoverIntersection U a)) :=
    HasBiproduct.of_hasProduct _
  have hId (V : X.Opens) :
      finiteOpenCoverColumnMap B f (V := V) (W := V) le_rfl J = 𝟙 _ := by
    ext q : 1
    change Functor.whiskerLeft (J.X q) _ = 𝟙 _
    rw [hRid]
    rfl
  have hComp (V W Z : X.Opens) (hVW : V ≤ W) (hWZ : W ≤ Z) :
      finiteOpenCoverColumnMap B f (V := V) (W := Z) (hVW.trans hWZ) J =
        finiteOpenCoverColumnMap B f (V := W) (W := Z) hWZ J ≫
          finiteOpenCoverColumnMap B f (V := V) (W := W) hVW J := by
    ext q : 1
    change Functor.whiskerLeft (J.X q) _ =
      Functor.whiskerLeft (J.X q) _ ≫ Functor.whiskerLeft (J.X q) _
    rw [hRcomp, Functor.whiskerLeft_comp]
  have hComm (p q r : ℕ) (_ : (ComplexShape.up ℕ).Rel q r) :
      finiteOpenCoverOrderedHorizontal B f U J hB p q ≫
          (finiteOpenCoverOrderedColumn B f U J hB (p + 1)).d q r =
        (finiteOpenCoverOrderedColumn B f U J hB p).d q r ≫
          finiteOpenCoverOrderedHorizontal B f U J hB p r :=
    finiteOpenCoverOrderedHorizontal_comm B f U J hB p q r
  have hSq (p : ℕ) :
      finiteOpenCoverOrderedHorizontalHom B f U J hB hComm p ≫
        finiteOpenCoverOrderedHorizontalHom B f U J hB hComm (p + 1) = 0 := by
    ext q : 1
    exact finiteOpenCoverOrderedHorizontal_squared B f U J hB hId hComp p q
  have hAug (q r : ℕ) (_ : (ComplexShape.up ℕ).Rel q r) :
      finiteOpenCoverRowMap B f U J hB hId hComp q ≫
          (finiteOpenCoverOrderedColumn B f U J hB 0).d q r =
        (finiteOpenCoverSource B f J hId hComp).d q r ≫
          finiteOpenCoverRowMap B f U J hB hId hComp r :=
    finiteOpenCoverRowMap_comm B f U J hB hId hComp q r
  have hEps : finiteOpenCoverRowAugmentation B f m U J hB hId hComp hComm hSq hAug ≫
      (finiteOpenCoverResolutionDoubleComplex B f m U J hB hComm hSq).d 0 1 = 0 := by
    ext q : 1
    change finiteOpenCoverRowMap B f U J hB hId hComp q ≫
      ((finiteOpenCoverResolutionDoubleComplex B f m U J hB hComm hSq).d 0 1).f q = 0
    have hd : (finiteOpenCoverResolutionDoubleComplex B f m U J hB hComm hSq).d 0 1 =
        finiteOpenCoverOrderedHorizontalHom B f U J hB hComm 0 :=
      by simp [finiteOpenCoverResolutionDoubleComplex]
    rw [hd]
    exact finiteOpenCoverRowMap_horizontal B f U J hB hId hComp q
  exact ⟨hB, hId, hComp, hComm, hSq, hAug, hEps⟩

private theorem finiteCoverIsoProjectionTransport
    {C : Type*} [Category C] {K A D R S P Q M : C}
    (k : K ⟶ A) (u : A ⟶ D) (ea : A ≅ R) (ed : D ≅ S)
    (ca : R ≅ P) (cd : S ≅ Q) (r : R ⟶ S) (ep : K ⟶ M) (π : M ⟶ P)
    (hu : u ≫ ed.hom = ea.hom ≫ r) (hπ : ep ≫ π = k ≫ ea.hom ≫ ca.hom) :
    k ≫ u ≫ ed.hom ≫ cd.hom = ep ≫ π ≫ (ca.inv ≫ r ≫ cd.hom) := by
  calc
    _ = k ≫ ea.hom ≫ r ≫ cd.hom := by rw [reassoc_of% hu]
    _ = (k ≫ ea.hom ≫ ca.hom) ≫ ca.inv ≫ r ≫ cd.hom := by
      simp only [Category.assoc, Iso.hom_inv_id_assoc]
    _ = _ := by rw [← hπ]; simp only [Category.assoc]

private abbrev finiteCoverColumnBiproducts {m : ℕ} (U : Fin m → X.Opens)
    (hB : ∀ p q : ℕ, HasBiproduct
      (fun a : Fin (p + 1) ↪o Fin m ↦
        J.X q ⋙
          finiteCoverOpenImage B f (finiteCoverIntersection U a))) (p : ℕ) :
    ∀ q : ℕ, HasBiproduct (fun a : Fin (p + 1) ↪o Fin m ↦
      (finiteOpenCoverColumn B f (finiteCoverIntersection U a)
        J).X q) := fun q ↦ hB p q

private def finiteCoverColumnProjection {m : ℕ} (U : Fin m → X.Opens)
    (hB : ∀ p q : ℕ, HasBiproduct
      (fun a : Fin (p + 1) ↪o Fin m ↦
        J.X q ⋙ finiteCoverOpenImage B f (finiteCoverIntersection U a))) (p : ℕ)
    (a : Fin (p + 1) ↪o Fin m) :
    finiteOpenCoverOrderedColumn B f U J hB p ⟶
      finiteOpenCoverColumn B f (finiteCoverIntersection U a) J :=
  HomologicalComplex.termwiseBiproductπ
    (fun a : Fin (p + 1) ↪o Fin m ↦
      finiteOpenCoverColumn B f (finiteCoverIntersection U a) J)
    (finiteCoverColumnBiproducts B f J U hB p) a

private def finiteCoverColumnPageIso {m : ℕ} (U : Fin m → X.Opens)
    (hB : ∀ p q : ℕ, HasBiproduct
      (fun a : Fin (p + 1) ↪o Fin m ↦
        J.X q ⋙
          finiteCoverOpenImage B f (finiteCoverIntersection U a))) (p q : ℕ) :
    (finiteOpenCoverOrderedColumn B f U J hB p).homology q ≅
      finiteCoverPageOne B f U p q := by
  letI := Fintype.ofFinite (Fin (p + 1) ↪o Fin m)
  let A := fun a : Fin (p + 1) ↪o Fin m ↦
    finiteOpenCoverColumn B f (finiteCoverIntersection U a) J
  letI : HasBiproduct (fun a ↦ (A a).homology q) := HasBiproduct.of_hasProduct _
  exact HomologicalComplex.termwiseBiproductHomologyIso A
    (finiteCoverColumnBiproducts B f J U hB p) q ≪≫
    biproduct.mapIso (fun a ↦ e
      (finiteCoverIntersection U a) q ≪≫
        finiteCoverDerivedComparison B f (finiteCoverIntersection U a) q)

private theorem finiteCoverColumnPageIso_hom_π {m : ℕ}
    (U : Fin m → X.Opens)
    (hB : ∀ p q : ℕ, HasBiproduct
      (fun a : Fin (p + 1) ↪o Fin m ↦
        J.X q ⋙
          finiteCoverOpenImage B f (finiteCoverIntersection U a))) (p q : ℕ)
    (a : Fin (p + 1) ↪o Fin m) :
    (finiteCoverColumnPageIso B f J e U hB p q).hom ≫
      finiteCoverPageOneProjection B f U p q a =
      HomologicalComplex.homologyMap
        (finiteCoverColumnProjection B f J U hB p a) q ≫
        (e (finiteCoverIntersection U a) q).hom ≫
          (finiteCoverDerivedComparison B f (finiteCoverIntersection U a) q).hom := by
  letI := Fintype.ofFinite (Fin (p + 1) ↪o Fin m)
  simp only [finiteCoverColumnPageIso, Iso.trans_hom, finiteCoverPageOneProjection,
    Category.assoc, biproduct.mapIso_hom, biproduct.map_π, finiteCoverColumnProjection,
    HomologicalComplex.termwiseBiproductHomologyIso_hom_π_assoc]

private theorem finiteCoverOrderedHorizontalHom_comp_π {m : ℕ}
    (U : Fin m → X.Opens) (data : finiteOpenCoverOrderedData B f m U
      J) (p : ℕ) (a : Fin (p + 2) ↪o Fin m) :
    finiteOpenCoverOrderedHorizontalHom B f U J
        data.hB data.hComm p ≫
      finiteCoverColumnProjection B f J U data.hB (p + 1) a =
      ∑ j : Fin (p + 2), (-1 : ℤ) ^ (j : ℕ) •
        (finiteCoverColumnProjection B f J U data.hB p (j.succAboveOrderEmb.trans a) ≫
          finiteOpenCoverColumnMap B f
            (le_iInf fun k ↦ iInf_le (fun l ↦ U (a l)) (j.succAbove k))
            J) := by
  ext q : 1
  letI := data.hB p q
  letI := data.hB (p + 1) q
  change _ = (HomologicalComplex.Hom.fAddMonoidHom q) _
  rw [map_sum]
  simp only [map_zsmul, HomologicalComplex.Hom.fAddMonoidHom_apply,
    HomologicalComplex.comp_f,
    HomologicalComplex.eval_map, finiteOpenCoverOrderedHorizontalHom,
    finiteOpenCoverOrderedHorizontal, finiteCoverColumnProjection,
    HomologicalComplex.termwiseBiproductπ,
    finiteOpenCoverColumnMap]
  dsimp only [finiteOpenCoverColumn]
  simp only [biproduct.lift_π]

private theorem finiteCoverOrderedHorizontal_homology_π {m : ℕ}
    (U : Fin m → X.Opens) (data : finiteOpenCoverOrderedData B f m U J)
    (p q : ℕ) (a : Fin (p + 2) ↪o Fin m) :
    HomologicalComplex.homologyMap
        (finiteOpenCoverOrderedHorizontalHom B f U J data.hB data.hComm p) q ≫
      HomologicalComplex.homologyMap
        (finiteCoverColumnProjection B f J U data.hB (p + 1) a) q =
    ∑ j : Fin (p + 2), (-1 : ℤ) ^ (j : ℕ) •
      (HomologicalComplex.homologyMap
        (finiteCoverColumnProjection B f J U data.hB p (j.succAboveOrderEmb.trans a)) q ≫
      HomologicalComplex.homologyMap
        (finiteOpenCoverColumnMap B f
          (le_iInf fun k ↦ iInf_le (fun l ↦ U (a l)) (j.succAbove k)) J) q) := by
  rw [← HomologicalComplex.homologyMap_comp,
    finiteCoverOrderedHorizontalHom_comp_π B f J U data p a]
  change (HomologicalComplex.homologyFunctor _ _ q).map _ = _
  simp only [Functor.map_sum, Functor.map_zsmul, Functor.map_comp]
  rfl

private theorem finiteCoverColumnPageIso_face
    (he : ∀ (V W : X.Opens) (h : W ≤ V) (q : ℕ),
      HomologicalComplex.homologyMap (finiteOpenCoverColumnMap B f h J) q ≫
        (e W q).hom = (e V q).hom ≫
          NatTrans.rightDerived (finiteCoverImageRestriction B f h) q) {m : ℕ} (U : Fin m → X.Opens)
    (data : finiteOpenCoverOrderedData B f m U J)
    (p q : ℕ) (a : Fin (p + 2) ↪o Fin m) (j : Fin (p + 2)) :
    HomologicalComplex.homologyMap
        (finiteCoverColumnProjection B f J U data.hB p (j.succAboveOrderEmb.trans a)) q ≫
      HomologicalComplex.homologyMap
        (finiteOpenCoverColumnMap B f
          (le_iInf fun k ↦ iInf_le (fun l ↦ U (a l)) (j.succAbove k)) J) q ≫
      (e (finiteCoverIntersection U a) q).hom ≫
      (finiteCoverDerivedComparison B f (finiteCoverIntersection U a) q).hom =
    (finiteCoverColumnPageIso B f J e U data.hB p q).hom ≫
      finiteCoverPageOneProjection B f U p q (j.succAboveOrderEmb.trans a) ≫
      finiteCoverHigherRestriction B f
        (le_iInf fun k ↦ iInf_le (fun l ↦ U (a l)) (j.succAbove k)) q
        (finiteCoverDerivedComparison B f
          (finiteCoverIntersection U (j.succAboveOrderEmb.trans a)) q)
        (finiteCoverDerivedComparison B f (finiteCoverIntersection U a) q) := by
  let b := j.succAboveOrderEmb.trans a
  let h : finiteCoverIntersection U a ≤ finiteCoverIntersection U b :=
    le_iInf fun k ↦ iInf_le (fun l ↦ U (a l)) (j.succAbove k)
  exact finiteCoverIsoProjectionTransport
    (HomologicalComplex.homologyMap (finiteCoverColumnProjection B f J U data.hB p b) q)
    (HomologicalComplex.homologyMap (finiteOpenCoverColumnMap B f h J) q)
    (e (finiteCoverIntersection U b) q) (e (finiteCoverIntersection U a) q)
    (finiteCoverDerivedComparison B f (finiteCoverIntersection U b) q)
    (finiteCoverDerivedComparison B f (finiteCoverIntersection U a) q)
    (NatTrans.rightDerived (finiteCoverImageRestriction B f h) q)
    (finiteCoverColumnPageIso B f J e U data.hB p q).hom
    (finiteCoverPageOneProjection B f U p q b)
    (he (finiteCoverIntersection U b) (finiteCoverIntersection U a) h q)
    (finiteCoverColumnPageIso_hom_π B f J e U data.hB p q b)

private theorem finiteCoverColumnPageIso_horizontal
    (he : ∀ (V W : X.Opens) (h : W ≤ V) (q : ℕ),
      HomologicalComplex.homologyMap (finiteOpenCoverColumnMap B f h J) q ≫
        (e W q).hom = (e V q).hom ≫
          NatTrans.rightDerived (finiteCoverImageRestriction B f h) q) {m : ℕ}
    (U : Fin m → X.Opens)
    (data : finiteOpenCoverOrderedData B f m U J)
    (p q : ℕ) (a : Fin (p + 2) ↪o Fin m) :
    HomologicalComplex.homologyMap
        (finiteOpenCoverOrderedHorizontalHom B f U J
          data.hB data.hComm p) q ≫
        (finiteCoverColumnPageIso B f J e U data.hB (p + 1) q).hom ≫
        finiteCoverPageOneProjection B f U (p + 1) q a =
      (finiteCoverColumnPageIso B f J e U data.hB p q).hom ≫
      ∑ j : Fin (p + 2), (-1 : ℤ) ^ (j : ℕ) •
        (finiteCoverPageOneProjection B f U p q (j.succAboveOrderEmb.trans a) ≫
          finiteCoverHigherRestriction B f
            (le_iInf fun k ↦ iInf_le (fun l ↦ U (a l)) (j.succAbove k)) q
            (finiteCoverDerivedComparison B f
              (finiteCoverIntersection U (j.succAboveOrderEmb.trans a)) q)
            (finiteCoverDerivedComparison B f (finiteCoverIntersection U a) q)) := by
  rw [finiteCoverColumnPageIso_hom_π B f J e U data.hB (p + 1) q a,
    ← Category.assoc, ← Category.assoc,
    finiteCoverOrderedHorizontal_homology_π B f J U data p q a]
  simp only [Preadditive.sum_comp, Preadditive.zsmul_comp,
    Preadditive.comp_sum, Preadditive.comp_zsmul, Category.assoc]
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  exact finiteCoverColumnPageIso_face B f J e he U data p q a j

private abbrev finiteCoverInjectiveComplex : CochainComplex
    (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B) ⥤
      Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)) ℕ :=
  (𝟭 (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B))).nonnegativeInjectiveComplex

private def finiteCoverColumnImageIso (f : X ⟶ Y) (V : X.Opens) :
    finiteOpenCoverColumn B f V (finiteCoverInjectiveComplex B) ≅
      Functor.nonnegativeInjectiveImageComplex
        (𝟭 (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B))) (finiteCoverOpenImage B f V) :=
  HomologicalComplex.Hom.isoOfComponents (fun _ ↦ Iso.refl _) (by
    intro i j hij
    exact (Category.id_comp _).trans (Category.comp_id _).symm)

private theorem finiteCoverColumnImageIso_naturality (f : X ⟶ Y)
    {V W : X.Opens} (h : W ≤ V) :
    finiteOpenCoverColumnMap B f h (finiteCoverInjectiveComplex B) ≫
        (finiteCoverColumnImageIso B f W).hom =
      (finiteCoverColumnImageIso B f V).hom ≫
        Functor.nonnegativeInjectiveImageMap
          (𝟭 (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)))
          (finiteCoverImageRestriction B f h) := by
  ext n : 1
  change Functor.whiskerLeft ((finiteCoverInjectiveComplex B).X n)
      (finiteCoverImageRestriction B f h) ≫ 𝟙 _ =
    𝟙 _ ≫ Functor.whiskerLeft ((finiteCoverInjectiveComplex B).X n)
      (finiteCoverImageRestriction B f h)
  exact (Category.comp_id _).trans (Category.id_comp _).symm

private def finiteCoverColumnHomologyIso (f : X ⟶ Y) (V : X.Opens) (q : ℕ) :
    (finiteOpenCoverColumn B f V (finiteCoverInjectiveComplex B)).homology q ≅
      (finiteCoverOpenImage B f V).rightDerived q :=
  HomologicalComplex.homologyMapIso (finiteCoverColumnImageIso B f V) q ≪≫
    Functor.nonnegativeInjectiveImageHomologyIso
      (𝟭 (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B))) (finiteCoverOpenImage B f V) q ≪≫
        Functor.leftUnitor _

private theorem finiteCoverColumnHomologyIso_naturality (f : X ⟶ Y)
    {V W : X.Opens} (h : W ≤ V) (q : ℕ) :
    HomologicalComplex.homologyMap
        (finiteOpenCoverColumnMap B f h (finiteCoverInjectiveComplex B)) q ≫
        (finiteCoverColumnHomologyIso B f W q).hom =
      (finiteCoverColumnHomologyIso B f V q).hom ≫
        NatTrans.rightDerived (finiteCoverImageRestriction B f h) q := by
  simp only [finiteCoverColumnHomologyIso, Iso.trans_hom,
    HomologicalComplex.homologyMapIso_hom, Category.assoc]
  rw [← reassoc_of% (HomologicalComplex.homologyMap_comp _ _ q),
    finiteCoverColumnImageIso_naturality, HomologicalComplex.homologyMap_comp,
    Category.assoc]
  simpa only [Iso.trans_hom, Category.assoc] using congrArg (fun z ↦
    HomologicalComplex.homologyMap (finiteCoverColumnImageIso B f V).hom q ≫ z)
      (Functor.identity_nonnegativeInjectiveImageHomologyIso_naturality
        (finiteCoverImageRestriction B f h) q)

private def finiteCoverPageOneIso (f : X ⟶ Y) {m : ℕ} (U : Fin m → X.Opens)
    (data : finiteOpenCoverOrderedData B f m U (finiteCoverInjectiveComplex B))
    (p q : ℕ) :
    ((finiteOpenCoverResolutionDoubleComplex B f m U (finiteCoverInjectiveComplex B)
      data.hB data.hComm data.hSq).firstSpectralSequenceFromOne.page 1).X (p, q) ≅
        finiteCoverPageOne B f U p q :=
  (finiteOpenCoverResolutionDoubleComplex B f m U (finiteCoverInjectiveComplex B)
      data.hB data.hComm data.hSq).firstSpectralSequenceFromOnePageOneIso p q ≪≫
    finiteCoverColumnPageIso B f (finiteCoverInjectiveComplex B)
      (finiteCoverColumnHomologyIso B f) U data.hB p q

private theorem finiteCoverFirstPageTransport
    {C : Type*} [Category C] [Abelian C]
    (K : HomologicalComplex₂ C (ComplexShape.up ℕ) (ComplexShape.up ℕ))
    (p q : ℕ) {P Q : C} (ep : (K.X p).homology q ≅ P)
    (en : (K.X (p + 1)).homology q ≅ Q) :
    (K.firstSpectralSequenceFromOnePageOneIso p q ≪≫ ep).inv ≫
        (K.firstSpectralSequenceFromOne.page 1).d (p, q) (p + 1, q) ≫
        (K.firstSpectralSequenceFromOnePageOneIso (p + 1) q ≪≫ en).hom =
      ep.inv ≫ HomologicalComplex.homologyMap (K.d p (p + 1)) q ≫ en.hom := by
  simp only [Iso.trans_hom, Iso.trans_inv, Category.assoc]
  rw [HomologicalComplex₂.firstSpectralSequenceFromOnePageOneIso_d_assoc]

private theorem finiteCoverPageOneIso_d (f : X ⟶ Y) {m : ℕ} (U : Fin m → X.Opens)
    (data : finiteOpenCoverOrderedData B f m U (finiteCoverInjectiveComplex B))
    (p q : ℕ) (a : Fin (p + 2) ↪o Fin m) :
    (finiteCoverPageOneIso B f U data p q).inv ≫
      ((finiteOpenCoverResolutionDoubleComplex B f m U (finiteCoverInjectiveComplex B)
        data.hB data.hComm data.hSq).firstSpectralSequenceFromOne.page 1).d
          (p, q) (p + 1, q) ≫
      (finiteCoverPageOneIso B f U data (p + 1) q).hom ≫
        finiteCoverPageOneProjection B f U (p + 1) q a =
      ∑ j : Fin (p + 2), (-1 : ℤ) ^ (j : ℕ) •
        (finiteCoverPageOneProjection B f U p q (j.succAboveOrderEmb.trans a) ≫
          finiteCoverHigherRestriction B f
            (le_iInf fun k ↦ iInf_le (fun l ↦ U (a l)) (j.succAbove k)) q
            (finiteCoverDerivedComparison B f
              (finiteCoverIntersection U (j.succAboveOrderEmb.trans a)) q)
            (finiteCoverDerivedComparison B f (finiteCoverIntersection U a) q)) := by
  let D := finiteOpenCoverResolutionDoubleComplex B f m U (finiteCoverInjectiveComplex B)
    data.hB data.hComm data.hSq
  have hd : D.d p (p + 1) = finiteOpenCoverOrderedHorizontalHom B f U
      (finiteCoverInjectiveComplex B) data.hB data.hComm p := by
    simp [D, finiteOpenCoverResolutionDoubleComplex]
  dsimp only [finiteCoverPageOneIso]
  calc
    _ = (finiteCoverColumnPageIso B f (finiteCoverInjectiveComplex B)
          (finiteCoverColumnHomologyIso B f) U data.hB p q).inv ≫
        HomologicalComplex.homologyMap (D.d p (p + 1)) q ≫
        (finiteCoverColumnPageIso B f (finiteCoverInjectiveComplex B)
          (finiteCoverColumnHomologyIso B f) U data.hB (p + 1) q).hom ≫
        finiteCoverPageOneProjection B f U (p + 1) q a := by
      simpa only [Category.assoc] using congrArg
        (fun z ↦ z ≫ finiteCoverPageOneProjection B f U (p + 1) q a)
        (finiteCoverFirstPageTransport D p q
          (finiteCoverColumnPageIso B f (finiteCoverInjectiveComplex B)
          (finiteCoverColumnHomologyIso B f) U data.hB p q)
          (finiteCoverColumnPageIso B f (finiteCoverInjectiveComplex B)
          (finiteCoverColumnHomologyIso B f) U data.hB (p + 1) q))
    _ = _ := by
      rw [← cancel_epi (finiteCoverColumnPageIso B f (finiteCoverInjectiveComplex B)
          (finiteCoverColumnHomologyIso B f) U data.hB p q).hom]
      simp only [Category.assoc, Iso.hom_inv_id_assoc]
      rw [hd]
      exact finiteCoverColumnPageIso_horizontal B f (finiteCoverInjectiveComplex B)
        (finiteCoverColumnHomologyIso B f)
        (fun V W h q ↦ finiteCoverColumnHomologyIso_naturality B f h q) U data p q a

private def finiteCoverSourceHomologyIso (f : X ⟶ Y)
    (hId : ∀ V : X.Opens, finiteOpenCoverColumnMap B f (V := V) (W := V)
      le_rfl (finiteCoverInjectiveComplex B) = 𝟙 _)
    (hComp : ∀ (V W Z : X.Opens) (hVW : V ≤ W) (hWZ : W ≤ Z),
      finiteOpenCoverColumnMap B f (V := V) (W := Z) (hVW.trans hWZ)
          (finiteCoverInjectiveComplex B) =
        finiteOpenCoverColumnMap B f (V := W) (W := Z) hWZ
          (finiteCoverInjectiveComplex B) ≫
        finiteOpenCoverColumnMap B f (V := V) (W := W) hVW
          (finiteCoverInjectiveComplex B)) (n : ℕ) :
    (finiteOpenCoverSource B f (finiteCoverInjectiveComplex B) hId hComp).homology n ≅
      (lowerStar (ModuleCat.{u + 1} B) f).rightDerived n := by
  let e := finiteCoverTopImageIso B f
  let e' : (finiteCoverOpenImage B f (⊤ : X.Opens)).rightDerived n ≅
      (lowerStar (ModuleCat.{u + 1} B) f).rightDerived n :=
    { hom := NatTrans.rightDerived e.inv n
      inv := NatTrans.rightDerived e.hom n
      hom_inv_id := by rw [← NatTrans.rightDerived_comp, e.inv_hom_id,
        NatTrans.rightDerived_id]
      inv_hom_id := by rw [← NatTrans.rightDerived_comp, e.hom_inv_id,
        NatTrans.rightDerived_id] }
  exact finiteCoverColumnHomologyIso B f ⊤ n ≪≫ e'

end AlgebraicGeometry.Etale
