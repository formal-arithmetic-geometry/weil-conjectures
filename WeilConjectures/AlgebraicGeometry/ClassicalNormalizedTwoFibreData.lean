/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.NormalizedClassicalWeilRealization
public import WeilConjectures.AlgebraicGeometry.RationalCoefficientCategoryComparison
public import WeilConjectures.AlgebraicGeometry.LisseRationalRealization
public import WeilConjectures.AlgebraicGeometry.AdicNormalizedFibreExactness
public import WeilConjectures.AlgebraicGeometry.PerAdicNormalizedFibreComparisons
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import WeilConjectures.AlgebraicGeometry.FieldCohomologyScalarExtension
public import WeilConjectures.AlgebraicGeometry.ConstructiblePullbackTExact
public import WeilConjectures.AlgebraicGeometry.FiniteCoefficientPoint
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.AlgebraicGeometry.ProEtaleSiteComparisonSupplement

import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import WeilConjectures.AlgebraicGeometry.SfConstructibleHeart
import WeilConjectures.AlgebraicGeometry.LocalizedTStructure
import WeilConjectures.AlgebraicGeometry.ContinuousRationalDerivedRealization
import WeilConjectures.AlgebraicGeometry.IntegralStratifiedPerfectCharacterization
import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.AlgebraicGeometry.InverseImageStalkGerm
import WeilConjectures.AlgebraicGeometry.Sites.EtaleSheavesGsetsPoint
import WeilConjectures.SecSmoothPurity.ProEtaleFiniteConstantSections
import WeilConjectures.AlgebraicGeometry.PointProEtaleSectionsExactOfUniverses
import WeilConjectures.AlgebraicGeometry.LisseCompletedSystemComparison
import WeilConjectures.AlgebraicGeometry.DirectImagesConstructible

/-! # The two normalized fibres of a classical lisse adic system

Source: Bhatt--Scholze, Proposition 6.8.4(1),(4), Proposition 6.8.14(2),
Remark 6.8.15; blueprint real-mixed-by-curves, proof paragraph 1
(blueprint: def-zl-classical-two-fibre-data).

## Main definitions and statements

* `Stage`, `AtStage`: normalized finite-stage heart, derived and stalk-limit comparisons.
* `commonVectorScalar`: actual finite-to-common scalar map.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option genSizeOfSpec false
set_option genCtorIdx false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
attribute [-instance] AlgebraicGeometry.Scheme.pbcRationalHasShift
open scoped TensorProduct
namespace WeilConjectures.ClassicalTwoFibre
open AlgebraicGeometry.Scheme.ContinuousRational
open AlgebraicGeometry.Scheme.AdicFibreComparison

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] [hl : Fact (l ≠ D.p)]
  (Ω : Type u) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
  (Y₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
  [IsSeparated Y₀.hom]

/-- The geometric fibre, in the existing separated finite-type base interface.
Source: blueprint base convention; BS 6.8.14(2)
(blueprint: def-zl-classical-two-fibre-data). -/
def geometricBase : FiniteTypeBase D.k where
  scheme := (D.geometricFiber Y₀).left
  «over» := (zlRealizationBase D l hl.out Y₀).over
  finiteType := (zlRealizationBase D l hl.out Y₀).finiteType
  quasiCompact := (zlRealizationBase D l hl.out Y₀).quasiCompact
  separated := by
    change IsSeparated (pullback.snd Y₀.hom
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))))
    infer_instance

/-- Invertibility is inherited from the finite-field datum, without an extra hypothesis.
Source: blueprint coefficient convention
(blueprint: def-zl-classical-two-fibre-data). -/
instance primeUnit : Fact (IsUnit (l : D.k)) := ⟨finiteFieldDatumPrimeUnit D l hl.out⟩

/-- The same inherited residue-field units at the geometric point.
Source: BS 6.8.15 (blueprint: def-zl-classical-two-fibre-data). -/
instance pointInvertible (x : Spec (.of D.k)) :
    Invertible (l : (Spec (.of D.k)).residueField x) :=
  LisseRealization.baseInvertible D l hl.out (LisseRealization.point D l hl.out) x

omit l hl in
/-- The geometric fibre has finite dimension, inherited from its structure morphism.
Source: finite-type dimension bound; BS 6.8.14(2)
(blueprint: def-zl-classical-two-fibre-data). -/
instance dimension : Fact (∃ n : ℕ, topologicalKrullDim (D.geometricFiber Y₀).left ≤ n) := by
  let f : (D.geometricFiber Y₀).left ⟶ Spec (.of D.k) := (D.geometricFiber Y₀).hom
  have : LocallyOfFiniteType f := by
    change LocallyOfFiniteType (pullback.snd Y₀.hom
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))))
    infer_instance
  have : QuasiCompact f := by
    change QuasiCompact (pullback.snd Y₀.hom
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))))
    infer_instance
  exact ⟨exists_topologicalKrullDim_le f⟩

/-- The same inherited stalk units, in the PBC API's convention.
Source: BS 6.8.14(2) (blueprint: def-zl-classical-two-fibre-data). -/
instance stalkUnits : Fact (∀ x : (D.geometricFiber Y₀).left,
    IsUnit (l : (D.geometricFiber Y₀).left.presheaf.stalk x)) :=
  finiteTypeBasePrimeUnit l (geometricBase D l Y₀)

variable (E : Padic.FiniteCoefficientFields l Ω)

/-- The canonical small derived fibre before its harmless carrier lift.
Source: BS 6.8.14(2) (blueprint: def-zl-classical-two-fibre-data). -/
def sfSmall (x : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left) :=
  rationalDerivedPullback l (pbcFiniteField.{u} l Ω E) x ⋙
    constructiblePointRationalRealization D l hl.out (pbcFiniteField.{u} l Ω E)

/-- The scalar comparison is the recorded pullback/point tensor comparison on D(E).
Source: BS 6.8.14(2), 6.8.15
(blueprint: def-zl-classical-two-fibre-data). -/
def finiteDerivedScalar (L : Padic.FiniteCoefficientFields l Ω) (h : E ≤ L)
    (x : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left)
    (K : sfRationalConstructibleCategory l (pbcFiniteField.{u} l Ω E)
      (D.geometricFiber Y₀).left) :=
  (constructiblePointRationalRealization D l hl.out (pbcFiniteField.{u} l Ω L)).mapIso
    ((rationalPullbackScalarComparison l (pbcFiniteField.{u} l Ω E)
      (pbcFiniteField.{u} l Ω L) (pbcFiniteFieldInclusion l Ω h) x).symm.app K) ≪≫
    (DerivedCategory.pointFiniteDimensional (pbcFiniteField.{u} l Ω L)).ι.mapIso
      ((pointRationalFibreScalarIso D l hl.out (pbcFiniteField.{u} l Ω E)
        (pbcFiniteField.{u} l Ω L) (pbcFiniteFieldInclusion l Ω h)).app
          ((rationalDerivedPullback l (pbcFiniteField.{u} l Ω E) x).obj K)) ≪≫
    ((DerivedCategory.pointFiniteDimensional (pbcFiniteField.{u} l Ω L)).liftCompιIso
      ((DerivedCategory.pointFiniteDimensional (pbcFiniteField.{u} l Ω E)).ι ⋙
        DerivedCategory.fieldDerivedScalarExtension
          (pbcFiniteFieldInclusion l Ω h).toRingHom)
      (fun T ↦ DerivedCategory.fieldDerivedScalarExtension_preserves
        (pbcFiniteFieldInclusion l Ω h).toRingHom T.obj T.property)).app
          ((pointRationalFibre D l hl.out (pbcFiniteField.{u} l Ω E)).obj
            ((rationalDerivedPullback l (pbcFiniteField.{u} l Ω E) x).obj K))

/-- The actual sf point fibre, retaining its small derived category and carrier lift.
Source: definition of Fib_s; BS 6.8.14(2)
(blueprint: def-zl-classical-two-fibre-data). -/
def sfDerived (x : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left) :=
  rationalDerivedPullback l (pbcFiniteField.{u} l Ω E) x ⋙
    pointRationalFibre D l hl.out (pbcFiniteField.{u} l Ω E) ⋙
      (DerivedCategory.pointFiniteDimensional (pbcFiniteField.{u} l Ω E)).ι ⋙
        (ModuleCat.uliftFunctor.{u + 1, u} (pbcFiniteField.{u} l Ω E)).mapDerivedCategory

/-- Degree-zero vector space of the same point fibre.
Source: BS 6.8.14(2), normalized lisse point comparison
(blueprint: def-zl-classical-two-fibre-data). -/
def sfVector (x : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left) :=
  rationalDerivedPullback l (pbcFiniteField.{u} l Ω E) x ⋙
    LisseRealization.fibre D l hl.out (pbcFiniteField.{u} l Ω E)

/-- The same canonical scalar map on degree-zero vector spaces; the tensor/lift
comparison sends up(b tensor m) to b tensor up(m).
Source: BS 6.8.14(2) (blueprint: def-zl-classical-two-fibre-data). -/
def finiteVectorScalar (L : Padic.FiniteCoefficientFields l Ω) (h : E ≤ L)
    (x : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left)
    (K : sfRationalConstructibleCategory l (pbcFiniteField.{u} l Ω E)
      (D.geometricFiber Y₀).left) :=
  (ModuleCat.uliftFunctor.{u + 1, u} (pbcFiniteField.{u} l Ω L)).mapIso
    ((DerivedCategory.homologyFunctor _ 0).mapIso (finiteDerivedScalar D l Ω Y₀ E L h x K) ≪≫
      (DerivedCategory.fieldDerivedHomologyIso
        (pbcFiniteFieldInclusion l Ω h).toRingHom 0).app
          ((sfSmall D l Ω Y₀ E x).obj K)) ≪≫
    ((pointFibreTensorLift_existsUnique l (pbcFiniteField.{u} l Ω E)
      (pbcFiniteField.{u} l Ω L) (pbcFiniteFieldInclusion l Ω h)).exists.choose).app
        ((DerivedCategory.homologyFunctor _ 0).obj ((sfSmall D l Ω Y₀ E x).obj K))

/-- Heart identification and the comparison of the two derived realizations.
Source: BS 6.8.14(2), the identity on common integral representatives
(blueprint: def-zl-classical-two-fibre-data). -/
structure Stage (a : LisseRealization.Family D l hl.out) (R : ContinuousRational.Family.{u} l)
    (C : FdCoefficientComparison l Ω (D.geometricFiber Y₀).left) where
  heart : ∀ K : sfRationalConstructibleCategory l (pbcFiniteField.{u} l Ω E)
      (D.geometricFiber Y₀).left,
    sfRationalHeartProperty l (pbcFiniteField.{u} l Ω E) (D.geometricFiber Y₀).left K ↔
      (localizedT l (pbcFiniteField.{u} l Ω E)
        (base l (geometricBase D l Y₀))).heart ((C.stage E).rational.functor.obj K)
  realization : (C.stage E).rational.functor ⋙
      (R.realization (pbcFiniteField.{u} l Ω E) (base l (geometricBase D l Y₀))).J ≅
    (a.realization (pbcFiniteField.{u} l Ω E) (zlRealizationBase D l hl.out Y₀)).J

/-- Restrict the recorded coefficient comparison to the lisse sf heart.
Source: BS 6.8.14(2) (blueprint: def-zl-classical-two-fibre-data). -/
def Stage.heartFunctor {a : LisseRealization.Family D l hl.out}
    {R : ContinuousRational.Family.{u} l}
    {C : FdCoefficientComparison l Ω (D.geometricFiber Y₀).left}
    (S : Stage D l Ω Y₀ E a R C) :=
  ObjectProperty.lift
    (localizedT l (pbcFiniteField.{u} l Ω E) (base l (geometricBase D l Y₀))).heart
    ((rationalLisseHeartProperty l (pbcFiniteField.{u} l Ω E)
      (D.geometricFiber Y₀).left).ι ⋙ (C.stage E).rational.functor)
    (fun K ↦ (S.heart K.obj).mp K.property.1)

/-- The specified normalized PBC fibre after the actual heart comparison.
Source: BS 6.8.4 and 6.8.14(2)
(blueprint: def-zl-classical-two-fibre-data). -/
def Stage.pbcVector {a : LisseRealization.Family D l hl.out}
    {R : ContinuousRational.Family.{u} l}
    {C : FdCoefficientComparison l Ω (D.geometricFiber Y₀).left}
    (S : Stage D l Ω Y₀ E a R C) (ω : Fibres (k := D.k) l R)
    (x : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left) :=
  S.heartFunctor D l Ω Y₀ E ⋙
    ((ω (pbcFiniteField.{u} l Ω E) (geometricBase D l Y₀)).point D.k x).functor

/-- The PBC derived realization with the specified normalized lattice model.
Source: BS 6.8.14(2) (blueprint: def-zl-classical-two-fibre-data). -/
def Stage.model {a : LisseRealization.Family D l hl.out}
    {R : ContinuousRational.Family.{u} l}
    {C : FdCoefficientComparison l Ω (D.geometricFiber Y₀).left}
    (S : Stage D l Ω Y₀ E a R C)
    (K : (rationalLisseHeartProperty l (pbcFiniteField.{u} l Ω E)
      (D.geometricFiber Y₀).left).FullSubcategory)
    (N : NormalizedFibre.Lattice l (pbcFiniteField.{u} l Ω E) (D.geometricFiber Y₀).left)
    (φ : (a.realization (pbcFiniteField.{u} l Ω E) (zlRealizationBase D l hl.out Y₀)).J.obj
      K.obj ≅ (DerivedCategory.singleFunctor _ 0).obj (N.rational l _)) :=
  S.realization.app K.obj ≪≫ φ

/-- The two fibre isomorphisms, with one shared inverse-limit normalization.
The left derived fibre is explicitly concentrated in degree zero. The right functor
is the recorded normalized PBC fibre, not a freely chosen vector-space functor.
Source: BS 6.8.4(1),(4), 6.8.14(2), Remark 6.8.15
(blueprint: def-zl-classical-two-fibre-data). -/
structure AtStage (a : LisseRealization.Family D l hl.out) (R : ContinuousRational.Family.{u} l)
    (C : FdCoefficientComparison l Ω (D.geometricFiber Y₀).left)
    (ω : Fibres (k := D.k) l R) extends Stage D l Ω Y₀ E a R C where
  fibres : ∀ x : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left,
    (rationalLisseHeartProperty l (pbcFiniteField.{u} l Ω E)
      (D.geometricFiber Y₀).left).ι ⋙ sfVector D l Ω Y₀ E x ≅
        toStage.pbcVector D l Ω Y₀ E ω x
  left_normalization : ∀
      (K : (rationalLisseHeartProperty l (pbcFiniteField.{u} l Ω E)
        (D.geometricFiber Y₀).left).FullSubcategory)
      (x : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left),
    HEq ((fibres x).hom.app K ≫
      ((ω (pbcFiniteField.{u} l Ω E) (geometricBase D l Y₀)).point D.k x).intrinsic.hom.app
        ((toStage.heartFunctor D l Ω Y₀ E).obj K) ≫
      (NormalizedFibre.ambient l (pbcFiniteField.{u} l Ω E) D.k x).map
        ((DerivedCategory.homologyFunctor
          (LisseRealization.Modules D l hl.out (pbcFiniteField.{u} l Ω E)
            (zlRealizationBase D l hl.out Y₀)) 0).map
            (toStage.realization.hom.app K.obj)))
      ((a.point (pbcFiniteField.{u} l Ω E)).comparison.hom.app
        ⟨(rationalDerivedPullback l (pbcFiniteField.{u} l Ω E) x).obj K.obj,
          (a.along (pbcFiniteField.{u} l Ω E)
            (X := LisseRealization.point D l hl.out)
            (Y := zlRealizationBase D l hl.out Y₀) x).preserves K.obj K.property⟩ ≫
        (LisseRealization.sections D l hl.out (pbcFiniteField.{u} l Ω E)).map
          ((a.along (pbcFiniteField.{u} l Ω E)
            (X := LisseRealization.point D l hl.out)
            (Y := zlRealizationBase D l hl.out Y₀) x).comparison K.obj K.property).hom)
  degree_zero : ∀ (K : (rationalLisseHeartProperty l (pbcFiniteField.{u} l Ω E)
      (D.geometricFiber Y₀).left).FullSubcategory)
      (x : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left),
    (sfDerived D l Ω Y₀ E x).obj K.obj ≅
      (DerivedCategory.singleFunctor _ 0).obj ((sfVector D l Ω Y₀ E x).obj K.obj)
  limit : ∀ (K : (rationalLisseHeartProperty l (pbcFiniteField.{u} l Ω E)
      (D.geometricFiber Y₀).left).FullSubcategory)
      (N : NormalizedFibre.Lattice l (pbcFiniteField.{u} l Ω E) (D.geometricFiber Y₀).left)
      (_φ : (a.realization (pbcFiniteField.{u} l Ω E) (zlRealizationBase D l hl.out Y₀)).J.obj
        K.obj ≅ (DerivedCategory.singleFunctor _ 0).obj (N.rational l _))
      (x : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left),
    (toStage.pbcVector D l Ω Y₀ E ω x).obj K ≅ N.rationalFiber l _ D.k x
  normalization : ∀
      (K : (rationalLisseHeartProperty l (pbcFiniteField.{u} l Ω E)
        (D.geometricFiber Y₀).left).FullSubcategory)
      (N : NormalizedFibre.Lattice l (pbcFiniteField.{u} l Ω E) (D.geometricFiber Y₀).left)
      (φ : (a.realization (pbcFiniteField.{u} l Ω E) (zlRealizationBase D l hl.out Y₀)).J.obj
        K.obj ≅ (DerivedCategory.singleFunctor _ 0).obj (N.rational l _))
      (B : NormalizedFibre.Chart l (base l (geometricBase D l Y₀)))
      (hB : B.Adapted l _ (R.realization _ (base l (geometricBase D l Y₀)))
        ((toStage.heartFunctor D l Ω Y₀ E).obj K))
      (M : NormalizedFibre.Lattice l (pbcFiniteField.{u} l Ω E) B.scheme)
      (hs : M.system = N.system ⋙ Etale.upperStar
        (ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l (pbcFiniteField.{u} l Ω E)))
          B.map)
      (η : (modulePull B.map (NormalizedFibre.coefficient l _ B.map)).obj
        (N.rational l _) ≅ M.rational l _)
      (_hη : IsPulledLattice l _ B.map N M hs η)
      (t : Spec (.of D.k) ⟶ B.scheme)
      (P : PullLimit l _ B.map N M D.k t
        (pullTowerIso l _ B.map N M (eqToIso hs) D.k t)),
    (limit K N φ (t ≫ B.map)).hom =
      ((ω (pbcFiniteField.{u} l Ω E) (geometricBase D l Y₀)).normalization B
        ((toStage.heartFunctor D l Ω Y₀ E).obj K) hB M
        ((modulePull B.map (NormalizedFibre.coefficient l _ B.map)).mapIso
          (modelH0 l (toStage.model D l Ω Y₀ E K N φ)) ≪≫ η) D.k t).hom ≫
        (ModuleCat.extendScalars (Padic.coefficientExtensionIntegers l
          (pbcFiniteField.{u} l Ω E)).subtype).map P.iso.hom
  representatives : ∀
      (K H : (rationalLisseHeartProperty l (pbcFiniteField.{u} l Ω E)
        (D.geometricFiber Y₀).left).FullSubcategory)
      (N M : NormalizedFibre.Lattice l (pbcFiniteField.{u} l Ω E) (D.geometricFiber Y₀).left)
      (φ : (a.realization (pbcFiniteField.{u} l Ω E) (zlRealizationBase D l hl.out Y₀)).J.obj
        K.obj ≅ (DerivedCategory.singleFunctor _ 0).obj (N.rational l _))
      (ψ : (a.realization (pbcFiniteField.{u} l Ω E) (zlRealizationBase D l hl.out Y₀)).J.obj
        H.obj ≅ (DerivedCategory.singleFunctor _ 0).obj (M.rational l _))
      (v : N.system ⟶ M.system) (b : ℕ),
    ∃ (u : N.integral ⟶ M.integral) (f : K ⟶ H),
      NormalizedFibre.Represents l _ N M u v ∧
        ((a.realization (pbcFiniteField.{u} l Ω E) (zlRealizationBase D l hl.out Y₀)).sheaf
        D l hl.out _).map f.hom ≫ (modelH0 l ψ).hom = (modelH0 l φ).hom ≫
          (((Padic.coefficientExtensionUniformizer l (pbcFiniteField.{u} l Ω E) :
            pbcFiniteField.{u} l Ω E) ^ b)⁻¹ •
              (pbcExtend (integralRationalCoefficientMap l _ (D.geometricFiber Y₀).left)).map u)
  fractions : ∀
      (K H : (rationalLisseHeartProperty l (pbcFiniteField.{u} l Ω E)
        (D.geometricFiber Y₀).left).FullSubcategory)
      (N M : NormalizedFibre.Lattice l (pbcFiniteField.{u} l Ω E) (D.geometricFiber Y₀).left)
      (φ : (a.realization (pbcFiniteField.{u} l Ω E) (zlRealizationBase D l hl.out Y₀)).J.obj
        K.obj ≅ (DerivedCategory.singleFunctor _ 0).obj (N.rational l _))
      (ψ : (a.realization (pbcFiniteField.{u} l Ω E) (zlRealizationBase D l hl.out Y₀)).J.obj
        H.obj ≅ (DerivedCategory.singleFunctor _ 0).obj (M.rational l _))
      (f : K ⟶ H) (u : N.integral ⟶ M.integral) (v : N.system ⟶ M.system)
      (_hu : NormalizedFibre.Represents l _ N M u v) (b : ℕ)
      (_hf : ((a.realization (pbcFiniteField.{u} l Ω E) (zlRealizationBase D l hl.out Y₀)).sheaf
        D l hl.out _).map f.hom ≫ (modelH0 l ψ).hom = (modelH0 l φ).hom ≫
          (((Padic.coefficientExtensionUniformizer l (pbcFiniteField.{u} l Ω E) :
            pbcFiniteField.{u} l Ω E) ^ b)⁻¹ •
              (pbcExtend (integralRationalCoefficientMap l _ (D.geometricFiber Y₀).left)).map u))
      (x : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left),
    ((toStage.pbcVector D l Ω Y₀ E ω x).map f ≫ (limit H M ψ x).hom =
      (limit K N φ x).hom ≫
        (((Padic.coefficientExtensionUniformizer l (pbcFiniteField.{u} l Ω E) :
          pbcFiniteField.{u} l Ω E) ^ b)⁻¹ • NormalizedFibre.rationalLimitMap l _ N M v D.k x)) ∧
    ((sfVector D l Ω Y₀ E x).map f.hom ≫
        (fibres x).hom.app H ≫ (limit H M ψ x).hom =
      (fibres x).hom.app K ≫ (limit K N φ x).hom ≫
        (((Padic.coefficientExtensionUniformizer l (pbcFiniteField.{u} l Ω E) :
          pbcFiniteField.{u} l Ω E) ^ b)⁻¹ • NormalizedFibre.rationalLimitMap l _ N M v D.k x))
  finite_free : ∀ (N : NormalizedFibre.Lattice l (pbcFiniteField.{u} l Ω E)
      (D.geometricFiber Y₀).left) (x : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left),
    Module.Finite (Padic.coefficientExtensionIntegers l (pbcFiniteField.{u} l Ω E))
      (N.fiber l _ D.k x) ∧
    Module.Free (Padic.coefficientExtensionIntegers l (pbcFiniteField.{u} l Ω E))
      (N.fiber l _ D.k x)

/-- The actual common-stage point fibre in degree zero, in the same carrier universe.
Source: BS 6.8.14(2) (blueprint: def-zl-classical-two-fibre-data). -/
def commonVector (x : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left) :=
  commonStageDerivedPullback l Ω x ⋙
    constructiblePointCommonStageRealization D l hl.out Ω ⋙
      DerivedCategory.homologyFunctor (ModuleCat.{u} Ω) 0 ⋙ ModuleCat.uliftFunctor.{u + 1, u} Ω

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
omit D l Ω Y₀ in
/-- The canonical carrier transport for scalar tensor, with actual linear-equivalence data.
It sends up(b tensor m) to b tensor up(m).
Source: tensor universal property (blueprint: def-zl-classical-two-fibre-data). -/
def tensorLift {A B : Type u} [Field A] [Field B] (f : A →+* B) (M : ModuleCat.{u} A) :
    (ModuleCat.uliftFunctor.{u + 1, u} B).obj ((ModuleCat.extendScalars f).obj M) ≅
      (ModuleCat.extendScalars f).obj ((ModuleCat.uliftFunctor.{u + 1, u} A).obj M) :=
  letI := f.toAlgebra
  (ULift.moduleEquiv ≪≫ₗ
    TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl B B)
      ULift.moduleEquiv.symm).toModuleIso

/-- The finite-to-common point comparison uses the actual pair-object identity and
canonical tensor tower, followed by degree-zero cohomology and the carrier lift.
Source: BS 6.8.14(2) (blueprint: def-zl-classical-two-fibre-data). -/
def commonVectorScalar (x : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left)
    (K : sfRationalConstructibleCategory l (pbcFiniteField.{u} l Ω E)
      (D.geometricFiber Y₀).left) :=
  (ModuleCat.uliftFunctor.{u + 1, u} Ω).mapIso
    ((DerivedCategory.homologyFunctor (ModuleCat.{u} Ω) 0).mapIso
      ((constructiblePointCommonStageRealization D l hl.out Ω).mapIso
        (eqToIso ((commonStageDerivedPullback_existsUnique l Ω x).exists.choose_spec.1
          ((GeneralAlgebraicallyClosedCoefficients.inclusion E).obj K))) ≪≫
        (constructiblePointCommonStageScalarComponent D l hl.out Ω E
          ((rationalDerivedPullback l (pbcFiniteField.{u} l Ω E) x).obj K)).symm) ≪≫
      (DerivedCategory.fieldDerivedHomologyIso (stageEmbedding l Ω E) 0).app
        ((sfSmall D l Ω Y₀ E x).obj K)) ≪≫
    tensorLift (stageEmbedding l Ω E)
        ((DerivedCategory.homologyFunctor _ 0).obj ((sfSmall D l Ω Y₀ E x).obj K))

/-- The sf common-stage lisse heart, as the intersection of the two existing predicates.
Source: blueprint common-stage convention
(blueprint: def-zl-classical-two-fibre-data). -/
def commonLisse : ObjectProperty
    (generalAlgebraicallyClosedConstructibleCategory l Ω (D.geometricFiber Y₀).left) :=
  fun K ↦ sfCommonStageHeartProperty l (D.geometricFiber Y₀).left Ω K ∧
    IsCommonStageLisse l Ω (D.geometricFiber Y₀).left K


end WeilConjectures.ClassicalTwoFibre
