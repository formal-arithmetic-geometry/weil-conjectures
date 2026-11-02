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

/-- The canonical comparison computed on the restriction of an injective resolution.
The restriction is exact and preserves injectives; no choice of a comparison map occurs.
Source: Stacks 03AZ and 04JC
(blueprint: lem-per-finite-open-cover-direct-image-spectral-sequence). -/
def finiteCoverDerivedComparisonApp (f : X ⟶ Y) (U : X.Opens) (q : ℕ)
    (M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)) :
    ((finiteCoverOpenImage B f U).rightDerived q).obj M ≅
      (finiteCoverHigherImage B f U q).obj M :=
  Functor.compRightDerivedObjIso _ _ (fun I _ ↦ by
    have := injective_upperStar_obj_of_etale B U.ι I
    exact Functor.rightAcyclic_of_injective
      ((upperStar (ModuleCat.{u + 1} B) U.ι).obj I)) q M

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

/-- The total augmentation `f_* J ⟶ Tot D`, by inclusion in bidegree `(0, q)`.
Source: Stacks 03AZ, relative ordered variant, and homology.tex Tag 0133, step 6
(blueprint: lem-per-finite-open-cover-direct-image-spectral-sequence). -/
noncomputable def finiteOpenCoverTotalAugmentation
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
          finiteOpenCoverRowMap B f U J hB hId hComp r)
    (hε : finiteOpenCoverRowAugmentation B f m U J hB hId hComp hComm hSq hAug ≫
        (finiteOpenCoverResolutionDoubleComplex B f m U J hB hComm hSq).d 0 1 = 0) :
    finiteOpenCoverSource B f J hId hComp ⟶
      (finiteOpenCoverResolutionDoubleComplex B f m U J hB hComm hSq).total
        (ComplexShape.up ℕ) :=
  HomologicalComplex₂.toTotalOfAugmentation
    (finiteOpenCoverResolutionDoubleComplex B f m U J hB hComm hSq)
    (finiteOpenCoverRowAugmentation B f m U J hB hId hComp hComm hSq hAug) hε

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

/-- The step-6 row argument for the named ordered double complex.
(blueprint: new-finite-open-cover-total-augmentation) -/
theorem finite_open_cover_augmentation_quasiIso
    (f : X ⟶ Y) (m : ℕ) (hm : 1 ≤ m) (U : Fin m → X.Opens) (hU : iSup U = ⊤)
    (J : CochainComplex
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B) ⥤
        Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)) ℕ)
    (data : finiteOpenCoverOrderedData B f m U J)
    (h₀ : ∀ q, Mono ((finiteOpenCoverRowAugmentation B f m U J data.hB data.hId
      data.hComp data.hComm data.hSq data.hAug).f q))
    (h₁ : ∀ q, (ShortComplex.mk
      ((finiteOpenCoverRowAugmentation B f m U J data.hB data.hId data.hComp
        data.hComm data.hSq data.hAug).f q)
      (((finiteOpenCoverResolutionDoubleComplex B f m U J data.hB data.hComm data.hSq).d 0 1).f q)
      (by rw [← HomologicalComplex.comp_f, data.hEps, HomologicalComplex.zero_f])).Exact)
    (hrow : ∀ (p q : ℕ), (ShortComplex.mk
      (((finiteOpenCoverResolutionDoubleComplex B f m U J data.hB data.hComm data.hSq).d p (p + 1)).f q)
      (((finiteOpenCoverResolutionDoubleComplex B f m U J data.hB data.hComm data.hSq).d (p + 1) (p + 2)).f q)
      (by rw [← HomologicalComplex.comp_f, HomologicalComplex.d_comp_d,
        HomologicalComplex.zero_f])).Exact) :
    QuasiIso (finiteOpenCoverTotalAugmentation B f m U J data.hB data.hId data.hComp
      data.hComm data.hSq data.hAug data.hEps) := by
  apply (finiteOpenCoverResolutionDoubleComplex B f m U J data.hB data.hComm
    data.hSq).quasiIso_toTotalOfAugmentation
  · exact h₀
  · exact h₁
  · exact hrow

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

/-- Core page data for the named ordered Cech double complex.
The proof chooses an injective resolution, constructs the open-dependent coefficient and
ordered biproduct rows, and applies the first-quadrant spectral-sequence comparison; the
vertical comparison is the canonical restricted-resolution map and the horizontal map is
the alternating deletion sum.
(blueprint: new-finite-open-cover-page-data) -/
theorem finite_open_cover_page_core
    (f : X ⟶ Y) (m : ℕ) (hm : 1 ≤ m) (U : Fin m → X.Opens) (hU : iSup U = ⊤) :
    ∃ (J : CochainComplex
        (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B) ⥤
          Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)) ℕ)
      (data : finiteOpenCoverOrderedData B f m U J)
      (c : ∀ (p q : ℕ) (a : Fin (p + 1) ↪o Fin m),
        (finiteCoverOpenImage B f (finiteCoverIntersection U a)).rightDerived q ≅
          finiteCoverHigherImage B f (finiteCoverIntersection U a) q)
      (E : CohomologicalSpectralSequenceNat
        (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B) ⥤
          Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} B)) 1)
      (e₁ : ∀ p q : ℕ, (E.page 1).X (p, q) ≅ finiteCoverPageOne B f U p q),
      (∀ n : ℕ, Nonempty ((finiteOpenCoverSource B f J data.hId data.hComp).homology n ≅
        (lowerStar (ModuleCat.{u + 1} B) f).rightDerived n)) ∧
      (∀ q, Mono ((finiteOpenCoverRowAugmentation B f m U J data.hB data.hId
        data.hComp data.hComm data.hSq data.hAug).f q)) ∧
      (∀ q, (ShortComplex.mk
        ((finiteOpenCoverRowAugmentation B f m U J data.hB data.hId data.hComp
          data.hComm data.hSq data.hAug).f q)
        (((finiteOpenCoverResolutionDoubleComplex B f m U J data.hB data.hComm data.hSq).d 0 1).f q)
        (by rw [← HomologicalComplex.comp_f, data.hEps, HomologicalComplex.zero_f])).Exact) ∧
      (∀ (p q : ℕ), (ShortComplex.mk
        (((finiteOpenCoverResolutionDoubleComplex B f m U J data.hB data.hComm data.hSq).d
        p (p + 1)).f q)
        (((finiteOpenCoverResolutionDoubleComplex B f m U J data.hB data.hComm data.hSq).d
        (p + 1) (p + 2)).f q)
        (by rw [← HomologicalComplex.comp_f, HomologicalComplex.d_comp_d,
          HomologicalComplex.zero_f])).Exact) ∧
      CategoryTheory.SimplicialSlice.augmentationPagesFromTwo E =
          HomologicalComplex₂.firstSpectralSequence
            (finiteOpenCoverResolutionDoubleComplex B f m U J data.hB data.hComm data.hSq) ∧
      (∀ (p q : ℕ) (a : Fin (p + 1) ↪o Fin m)
        (M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)),
        (c p q a).hom.app M =
          (finiteCoverDerivedComparisonApp B f (finiteCoverIntersection U a) q M).hom) ∧
      (∀ (p q : ℕ) (a : Fin (p + 2) ↪o Fin m),
        (e₁ p q).inv ≫ (E.page 1).d (p, q) (p + 1, q) ≫ (e₁ (p + 1) q).hom ≫
          finiteCoverPageOneProjection B f U (p + 1) q a =
        ∑ j : Fin (p + 2), (-1 : ℤ) ^ (j : ℕ) •
          (finiteCoverPageOneProjection B f U p q (j.succAboveOrderEmb.trans a) ≫
            finiteCoverHigherRestriction B f
              (U := finiteCoverIntersection U (j.succAboveOrderEmb.trans a))
              (V := finiteCoverIntersection U a)
              (le_iInf fun k ↦ iInf_le (fun l ↦ U (a l)) (j.succAbove k)) q
              (c p q (j.succAboveOrderEmb.trans a)) (c (p + 1) q a))) := by
  let J := finiteCoverInjectiveComplex (X := X) B
  let data := finiteOpenCoverOrderedDataOfRestrictions B f U J
    (finiteCoverImageRestriction_id B f) (finiteCoverImageRestriction_comp B f)
  let c := fun p q (a : Fin (p + 1) ↪o Fin m) ↦
    finiteCoverDerivedComparison B f (finiteCoverIntersection U a) q
  let D := finiteOpenCoverResolutionDoubleComplex B f m U J data.hB data.hComm data.hSq
  let E := D.firstSpectralSequenceFromOne
  let e₁ := finiteCoverPageOneIso B f U data
  have hI (q : ℕ) (M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)) :
      Injective ((J.X q).obj M) := by
    change Injective
      (((𝟭 (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B))).nonnegativeInjectiveSyzygy
        q).injectiveExtension.obj M)
    infer_instance
  obtain ⟨h₀, h₁⟩ := finite_open_cover_row_descent B f m hm U hU J data
  have hrow := finite_open_cover_positive_rows_exact B f m hm U hU J hI data
  refine ⟨J, data, c, E, e₁, ?_, h₀, h₁, hrow, ?_, ?_, ?_⟩
  · intro n
    exact ⟨finiteCoverSourceHomologyIso B f data.hId data.hComp n⟩
  · rfl
  · intro p q a M
    rfl
  · exact finiteCoverPageOneIso_d B f U data

private lemma isZero_biproduct_of_isEmpty {C : Type*} [Category C] [Preadditive C]
    {ι : Type*} {F : ι → C} [HasBiproduct F] [IsEmpty ι] : IsZero (⨁ F) := by
  rw [IsZero.iff_id_eq_zero]
  apply biproduct.hom_ext'
  intro i
  exact isEmptyElim i

private lemma finiteCoverPageOne_isZero
    (f : X ⟶ Y) {m : ℕ} (U : Fin m → X.Opens) (p q : ℕ) (hmp : m ≤ p) :
    IsZero (finiteCoverPageOne B f U p q) := by
  letI : IsEmpty (Fin (p + 1) ↪o Fin m) := by
    constructor
    intro a
    have hc := Fintype.card_le_of_injective (a : Fin (p + 1) → Fin m) a.injective
    simp only [Fintype.card_fin] at hc
    omega
  exact isZero_biproduct_of_isEmpty

/-- Finite-column support for the named page data.
The proof uses the absence of increasing tuples of length p+1 for p≥m and the
first-quadrant page recursion, after transporting along e₁ and hE to the named complex.
(blueprint: new-finite-open-cover-page-support) -/
theorem finite_open_cover_page_support
    (f : X ⟶ Y) (m : ℕ) (U : Fin m → X.Opens)
    (J : CochainComplex
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B) ⥤
        Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)) ℕ)
    (data : finiteOpenCoverOrderedData B f m U J)
    (E : CohomologicalSpectralSequenceNat
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B) ⥤
        Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} B)) 1)
    (e₁ : ∀ p q : ℕ, (E.page 1).X (p, q) ≅ finiteCoverPageOne B f U p q)
    (hE : CategoryTheory.SimplicialSlice.augmentationPagesFromTwo E =
      HomologicalComplex₂.firstSpectralSequence
        (finiteOpenCoverResolutionDoubleComplex B f m U J data.hB data.hComm data.hSq)) :
    (∀ (p q : ℕ) (r : ℤ) (hr : 1 ≤ r), m ≤ p →
      IsZero ((E.page r hr).X (p, q))) ∧
    (∀ (p q : ℕ) (r : ℤ) (hr : 1 ≤ r), max (p : ℤ) ((q : ℤ) + 1) < r →
      Nonempty ((E.page r hr).X (p, q) ≅
        (CategoryTheory.SimplicialSlice.augmentationPagesFromTwo E).pageInfinity
          (p, q))) := by
  let D := finiteOpenCoverResolutionDoubleComplex B f m U J data.hB data.hComm data.hSq
  have hDcol (p q : ℕ) (hmp : m ≤ p) : IsZero (D.X p |>.X q) := by
    dsimp [D, finiteOpenCoverResolutionDoubleComplex, finiteOpenCoverOrderedColumn]
    letI := data.hB p q
    letI : IsEmpty (Fin (p + 1) ↪o Fin m) := by
      constructor
      intro a
      have hc := Fintype.card_le_of_injective (a : Fin (p + 1) → Fin m) a.injective
      simp only [Fintype.card_fin] at hc
      omega
    exact isZero_biproduct_of_isEmpty
  have hDpage2 (p q : ℕ) (hmp : m ≤ p) :
      IsZero ((D.firstSpectralSequence.page 2).X (p, q)) := by
    let H := (((HomologicalComplex.homologyFunctor
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B) ⥤
        Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} B)) (ComplexShape.up ℕ) q).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj D)
    have hH : IsZero (H.X p) := by
      dsimp [H]
      exact (HomologicalComplex.ExactAt.of_isZero (hDcol p q hmp)).isZero_homology
    have hHH : IsZero (H.homology p) := (H.sc p).isZero_homology_of_isZero_X₂ hH
    convert hHH.of_iso (D.firstSpectralSequencePageTwoIso p q) using 1
  constructor
  · intro p q r hr hmp
    by_cases h1 : r = 1
    · subst r
      simpa using (finiteCoverPageOne_isZero B f U p q hmp).of_iso (e₁ p q)
    · have hr2 : 2 ≤ r := by omega
      change IsZero (((CategoryTheory.SimplicialSlice.augmentationPagesFromTwo E).page r hr2).X
        (p, q))
      rw [hE]
      exact SpectralSequence.isZero_page_of_isZero_page_two
        (hDpage2 p q hmp) r hr2
  · intro p q r hr hbound
    have hr2 : 2 ≤ r := by omega
    change Nonempty (((CategoryTheory.SimplicialSlice.augmentationPagesFromTwo E).page r hr2).X
        (p, q) ≅ (CategoryTheory.SimplicialSlice.augmentationPagesFromTwo E).pageInfinity (p, q))
    rw [hE]
    change Nonempty ((D.firstSpectralSequence.page r _).X (p, q) ≅
      D.firstSpectralSequence.pageInfinity (p, q))
    change Nonempty (((D.extendNat.columnFiltration.exactCouple.firstQuadrantSpectralSequence
      D.extendNat_columnFiltration_isFirstQuadrant).page r hr2).X (p, q) ≅
      (D.extendNat.columnFiltration.exactCouple.firstQuadrantSpectralSequence
        D.extendNat_columnFiltration_isFirstQuadrant).pageInfinity (p, q))
    rw [ExactCouple.firstQuadrantSpectralSequence_page_X
      D.extendNat.columnFiltration.exactCouple
      D.extendNat_columnFiltration_isFirstQuadrant r hr2]
    rw [SpectralSequence.pageInfinity]
    simp only [Prod.fst, Prod.snd]
    norm_num
    rw [ExactCouple.firstQuadrantSpectralSequence_page_X
      D.extendNat.columnFiltration.exactCouple
      D.extendNat_columnFiltration_isFirstQuadrant (↑(p + q + 2) : ℤ) (by omega)]
    have hrnonneg : 0 ≤ r - 1 := by omega
    let N₀ := max p (q + 1)
    have hN' : ((N₀ : ℕ) : ℤ) ≤ r - 1 := by
      dsimp [N₀]
      omega
    have hN : N₀ ≤ (r - 1).toNat := by
      have hN'' : ((N₀ : ℕ) : ℤ) ≤ ((r - 1).toNat : ℤ) := by
        rw [Int.toNat_of_nonneg hrnonneg]
        exact hN'
      exact_mod_cast hN''
    have hNinf : N₀ ≤ p + q + 1 := by
      dsimp [N₀]
      omega
    obtain ⟨eᵣ⟩ := D.extendNat.columnFiltration.exactCouple.nonempty_derivedIter_E_iso_of_isFirstQuadrant
      D.extendNat_columnFiltration_isFirstQuadrant p (p + q) N₀
      (by dsimp [N₀]; omega) (by dsimp [N₀]; omega) (r - 1).toNat hN
    have heq : ((↑(p + q + 2) : ℤ) - 1).toNat = p + q + 1 := by
      have heq' : ((((↑(p + q + 2) : ℤ) - 1).toNat : ℤ)) = p + q + 1 := by
        rw [Int.toNat_of_nonneg (by omega)]
        omega
      exact_mod_cast heq'
    obtain ⟨einf⟩ := D.extendNat.columnFiltration.exactCouple.nonempty_derivedIter_E_iso_of_isFirstQuadrant
      D.extendNat_columnFiltration_isFirstQuadrant p (p + q) N₀
      (by dsimp [N₀]; omega) (by dsimp [N₀]; omega)
      ((↑(p + q + 2) : ℤ) - 1).toNat (by
        have hsum : ((↑p + ↑q + 2 : ℤ).toNat) = p + q + 2 := by
          have hsum' : ((((↑p + ↑q + 2 : ℤ).toNat : ℤ))) = p + q + 2 := by
            rw [Int.toNat_of_nonneg (by omega)]
          exact_mod_cast hsum'
        simpa [hsum] using hNinf)
    apply Nonempty.intro
    simpa [Prod.fst, Prod.snd] using (eᵣ ≪≫ einf.symm)

/-- Transport homology across the total augmentation of the named complex: a
quasi-isomorphism `f_* J ⟶ Tot D` and `H^n(f_* J) ≅ R^n f_*` give `H^n(Tot D) ≅ R^n f_*`.
Source: homology.tex Tag 0133, step 6
(blueprint: lem-per-finite-open-cover-direct-image-spectral-sequence). -/
theorem finite_open_cover_total_augmentation
    (f : X ⟶ Y) (m : ℕ) (hm : 1 ≤ m) (U : Fin m → X.Opens) (hU : iSup U = ⊤)
    (J : CochainComplex
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B) ⥤
        Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)) ℕ)
    (data : finiteOpenCoverOrderedData B f m U J)
    (hAug : QuasiIso (finiteOpenCoverTotalAugmentation B f m U J data.hB data.hId
      data.hComp data.hComm data.hSq data.hAug data.hEps))
    (hSource : ∀ n : ℕ, Nonempty ((finiteOpenCoverSource B f J data.hId data.hComp).homology n ≅
      (lowerStar (ModuleCat.{u + 1} B) f).rightDerived n)) :
    ∀ n : ℕ, Nonempty ((((finiteOpenCoverResolutionDoubleComplex B f m U J data.hB
      data.hComm data.hSq).total (ComplexShape.up ℕ)).homology n) ≅
      (lowerStar (ModuleCat.{u + 1} B) f).rightDerived n) := by
  intro n
  letI := hAug
  exact ⟨(isoOfQuasiIsoAt
      (finiteOpenCoverTotalAugmentation B f m U J data.hB data.hId data.hComp
        data.hComm data.hSq data.hAug data.hEps) n).symm ≪≫ (hSource n).some⟩

private theorem finite_open_cover_abutment_of_total
    (f : X ⟶ Y)
    (m : ℕ) (U : Fin m → X.Opens)
    (D : HomologicalComplex₂
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B) ⥤
        Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} B))
      (ComplexShape.up ℕ) (ComplexShape.up ℕ))
    (E : CohomologicalSpectralSequenceNat
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B) ⥤
        Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} B)) 1)
    (hE : CategoryTheory.SimplicialSlice.augmentationPagesFromTwo E =
      HomologicalComplex₂.firstSpectralSequence
        D)
    (hTot : ∀ n : ℕ, Nonempty (((D.total
      (ComplexShape.up ℕ)).homology n) ≅
      (lowerStar (ModuleCat.{u + 1} B) f).rightDerived n)) :
    (CategoryTheory.SimplicialSlice.augmentationPagesFromTwo E).AbutsTo
      (fun n : ℕ ↦ (lowerStar (ModuleCat.{u + 1} B) f).rightDerived n) := by
  rw [hE]
  exact (HomologicalComplex₂.firstSpectralSequence_abutsTo D).of_nonempty_iso hTot

/-- The functorial ordered finite-open-cover direct-image spectral sequence, with its
canonical first page, alternating differential, vanishing range and finite convergence.
Source: Stacks 03AZ (relative ordered variant), 03FB, 03FC, 01FJ, 01FM and
homology.tex, Tags 0130, 0132 and 0133
(blueprint: lem-per-finite-open-cover-direct-image-spectral-sequence).

Proof:
1. Choose a nonnegative injective resolution M -> J in the Grothendieck category
   of B-module etale sheaves, with coefficients in the universe of the site skeleton.
2. Restriction to each intersection is exact and preserves injectives by etale
   extension by zero. It therefore gives an injective resolution of the restriction.
3. Form D^(p,q) = direct-sum_I (f_I)_*(J^q|_I), using increasing (p+1)-tuples.
   Horizontal maps are alternating restrictions, and vertical maps come from J.
   Double omissions cancel, giving a double complex with total differential
   d_h + (-1)^p d_v, naturally on the target etale site and in B-modules.
4. Exact module sheafification makes the underlying module presheaf of J^q
   injective, by the exact-left-adjoint criterion. No forgetting of B is used.
5. At V etale over Y, the pulled-back opens cover X x_Y V. Injective presheaf
   Cech cocycle lifting and the all-tuple/ordered comparison give row exactness
   in positive degrees. In degree zero use sheaf gluing. All products are finite.
6. Kernels are sectionwise, so these are exact augmented sheaf rows. The column
   augmentation f_*J -> Tot D is a quasi-isomorphism, with sign +1 in column zero.
   Hence total cohomology is R^n f_*M.
7. The column spectral sequence has the displayed E1. Finite sums commute with
   cohomology. The restricted-resolution comparison is exactly the specified
   comparison, and identifies d1 with alternating canonical restrictions.
8. The double-complex spectral sequence gives stabilization and the finite image
   filtration, with associated quotients E_infinity. Columns outside 0 <= p < m
   vanish; the subsequent-page recursion preserves this vanishing.
9. Lift M -> N to injective resolutions. Two lifts are homotopic; their column
   maps agree on E1. The total homotopy in column p is (-1)^p times the restricted
   homotopy; its horizontal terms cancel. It preserves the column filtration.
   Comparisons between resolutions and composition of lifts give functoriality
   of pages, identifications, abutment and filtration in M.
-/
theorem finite_open_cover_direct_image_spectral_sequence
    (f : X ⟶ Y) (m : ℕ) (hm : 1 ≤ m) (U : Fin m → X.Opens) (hU : iSup U = ⊤) :
    ∃ (c : ∀ (p q : ℕ) (a : Fin (p + 1) ↪o Fin m),
        (finiteCoverOpenImage B f (finiteCoverIntersection U a)).rightDerived q ≅
          finiteCoverHigherImage B f (finiteCoverIntersection U a) q)
      (E : CohomologicalSpectralSequenceNat
        (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B) ⥤
          Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} B)) 1)
      (e₁ : ∀ p q : ℕ, (E.page 1).X (p, q) ≅ finiteCoverPageOne B f U p q),
      (∀ (p q : ℕ) (a : Fin (p + 1) ↪o Fin m)
        (M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)),
        (c p q a).hom.app M =
          (finiteCoverDerivedComparisonApp B f (finiteCoverIntersection U a) q M).hom) ∧
      (∀ (p q : ℕ) (a : Fin (p + 2) ↪o Fin m),
        (e₁ p q).inv ≫ (E.page 1).d (p, q) (p + 1, q) ≫ (e₁ (p + 1) q).hom ≫
          finiteCoverPageOneProjection B f U (p + 1) q a =
        ∑ j : Fin (p + 2), (-1 : ℤ) ^ (j : ℕ) •
          (finiteCoverPageOneProjection B f U p q (j.succAboveOrderEmb.trans a) ≫
            finiteCoverHigherRestriction B f
              (U := finiteCoverIntersection U (j.succAboveOrderEmb.trans a))
              (V := finiteCoverIntersection U a)
              (le_iInf fun k ↦ iInf_le (fun l ↦ U (a l)) (j.succAbove k)) q
              (c p q (j.succAboveOrderEmb.trans a)) (c (p + 1) q a))) ∧
      (∀ (p q : ℕ) (r : ℤ) (hr : 1 ≤ r), m ≤ p →
        IsZero ((E.page r hr).X (p, q))) ∧
      (∀ (p q : ℕ) (r : ℤ) (hr : 1 ≤ r), max (p : ℤ) ((q : ℤ) + 1) < r →
        Nonempty ((E.page r hr).X (p, q) ≅
          (CategoryTheory.SimplicialSlice.augmentationPagesFromTwo E).pageInfinity (p, q))) ∧
      (CategoryTheory.SimplicialSlice.augmentationPagesFromTwo E).AbutsTo
        (fun n : ℕ ↦ (lowerStar (ModuleCat.{u + 1} B) f).rightDerived n) := by
  obtain ⟨J, data, c, E, e₁, hSource, h₀, h₁, hrow, hE, hc, hd⟩ :=
    finite_open_cover_page_core B f m hm U hU
  obtain ⟨hz, hs⟩ := finite_open_cover_page_support B f m U J data E e₁ hE
  have hQ := finite_open_cover_augmentation_quasiIso B f m hm U hU J data h₀ h₁ hrow
  have hTot := finite_open_cover_total_augmentation B f m hm U hU J data hQ hSource
  have hab := finite_open_cover_abutment_of_total B f m U
    (finiteOpenCoverResolutionDoubleComplex B f m U J data.hB data.hComm data.hSq) E hE hTot
  exact ⟨c, E, e₁, hc, hd, hz, hs, hab⟩

end AlgebraicGeometry.Etale
