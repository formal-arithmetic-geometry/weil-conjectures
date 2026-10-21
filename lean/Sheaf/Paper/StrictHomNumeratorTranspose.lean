/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q80
-/
module

public import Sheaf.Paper.DerivedInternalHomFilteredColimitData
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import Sheaf.Algebra.Homology.KInjectiveHomComplex
import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMap
import Mathlib.Algebra.Homology.DerivedCategory.KInjective

/-! # Transpose of the strict normalized Hom numerator

Source: Stacks Project, sites-cohomology.tex, Tag 08J9, and the strict numerator
calculation in the node (blueprint: lem-sfb-hom-strict-numerator-transpose).
The records below package chain maps and their full representative normalizations;
they do not replace the recorded tensor, Hom, or resolution constructions.
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v r w w2
open CategoryTheory CategoryTheory.Limits Opposite
namespace WeilConjectures.SfbHomFilteredColimit

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max u v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v r}]
  (R : Sheaf J CommRingCat.{max u v r})

/-- The simultaneous precomposition and resolved postcomposition on the fixed Hom.
Source: Stacks 0A95, 08J9 (blueprint: lem-sfb-hom-strict-numerator-transpose). -/
noncomputable def numeratorHomMap
    {P P' L L' : CochainComplex (Modules.{u, v, r} J R) ℤ}
    (b : P' ⟶ P) (c : L ⟶ L') :
    (homFixed.{u, v, r} J R P).obj L ⟶ (homFixed.{u, v, r} J R P').obj L' :=
  ((homComplexFunctor (R := R)).map b.op).app
      ((coefficientHomResolution.{r, u, v} J R).obj L) ≫
    ((homComplexFunctor (R := R)).obj (op P')).map
      ((coefficientHomResolution.{r, u, v} J R).map c)

/-- Total-tensor map with its two source and target objects explicit.
Source: Stacks 06YN (blueprint: lem-sfb-hom-strict-numerator-transpose). -/
noncomputable def numeratorTotalMap
    {X Y P Q : CochainComplex (Modules.{u, v, r} J R) ℤ}
    (f : X ⟶ Y) (g : P ⟶ Q) :
    (coefficientTotalTensor.{r, u, v} J R).obj (X, P) ⟶
      (coefficientTotalTensor.{r, u, v} J R).obj (Y, Q) :=
  (coefficientTotalTensor.{r, u, v} J R).map (X := (X, P)) (Y := (Y, Q)) (f, g)

/-- Coefficient-tensor map with the same fixed degree-zero presentation.
Source: Stacks 06YN (blueprint: lem-sfb-hom-strict-numerator-transpose). -/
noncomputable def numeratorTensorMap
    {T T' : Modules.{u, v, r} J R}
    {X Y : CochainComplex (Modules.{u, v, r} J R) ℤ}
    (f : T ⟶ T') (g : X ⟶ Y) :
    (tensor.{u, v, r} J R).obj (T, X) ⟶ (tensor.{u, v, r} J R).obj (T', Y) :=
  (tensor.{u, v, r} J R).map (X := (T, X)) (Y := (T', Y)) (f, g)

attribute [local irreducible] homComplexFunctor SheafOfModules.monoidalCategory
  PresheafOfModules.sheafification PresheafOfModules.sheafificationAdjunction

variable [HasDerivedCategory.{w} (Modules.{u, v, r} J R)]

/-- Witness maps for the strict numerator, including a comparison with arbitrary first
factor. The comparison is fixed by naturality and its restriction to K-flat first factors
in `StrictNumeratorLaws`, rather than chosen independently of the normalized model.
Source: Stacks 08J9 (blueprint: lem-sfb-hom-strict-numerator-transpose). -/
structure StrictNumeratorData
    (S : CoefficientClosedStructure (derivedInternalHomOfUniverses.{u, v, r, w} J R))
    (P L : CochainComplex (Modules.{u, v, r} J R) ℤ) where
  /-- One-sided total tensor comparison, with unrestricted first complex. -/
  tensorIso : ∀ X : CochainComplex (Modules.{u, v, r} J R) ℤ,
    DerivedCategory.Q.obj ((coefficientTotalTensor.{r, u, v} J R).obj (X, P)) ≅
      S.tensor.obj (DerivedCategory.Q.obj X, DerivedCategory.Q.obj P)
  /-- Evaluation into the very same fixed resolution of L. -/
  evaluation : (coefficientTotalTensor.{r, u, v} J R).obj
    ((homFixed.{u, v, r} J R P).obj L, P) ⟶
      (coefficientHomResolution.{r, u, v} J R).obj L
  /-- Scalar evaluation, before applying any resolution of its target. -/
  scalarEvaluation : ∀ T : Modules.{u, v, r} J R,
    (coefficientTotalTensor.{r, u, v} J R).obj
      ((tensor.{u, v, r} J R).obj (T, (homFixed.{u, v, r} J R P).obj L), P) ⟶
        (tensor.{u, v, r} J R).obj (T, (coefficientHomResolution.{r, u, v} J R).obj L)
  /-- The chain uncurrying of the actual normalized comparison. -/
  uncurry : ∀ T : Modules.{u, v, r} J R,
    (coefficientTotalTensor.{r, u, v} J R).obj
      ((tensor.{u, v, r} J R).obj (T, (homFixed.{u, v, r} J R P).obj L), P) ⟶
        (coefficientHomResolution.{r, u, v} J R).obj
          ((tensor.{u, v, r} J R).obj (T, (coefficientHomResolution.{r, u, v} J R).obj L))

/-- Exact chain and derived normalization of the witness maps. All section formulas
use actual product-Hom projections and the two sheafification units, through the recorded
`homValue`, `tensorGenerator` and `coefficientTensorGenerator`.
Source: Stacks 08J9 (blueprint: lem-sfb-hom-strict-numerator-transpose). -/
def StrictNumeratorLaws
    (S : CoefficientClosedStructure (derivedInternalHomOfUniverses.{u, v, r, w} J R))
    (M : CoefficientTensorModels.{r, u, v, w} J R S)
    (P L : CochainComplex (Modules.{u, v, r} J R) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients (R := R) P)
    (d : StrictNumeratorData.{u, v, r, w} J R S P L) : Prop :=
  -- tensor_natural
  (∀ (X Y : CochainComplex (Modules.{u, v, r} J R) ℤ) (f : X ⟶ Y),
    DerivedCategory.Q.map (numeratorTotalMap.{u, v, r} J R f (𝟙 P)) ≫
        (d.tensorIso Y).hom =
      (d.tensorIso X).hom ≫ S.tensor.map
        (X := (DerivedCategory.Q.obj X, DerivedCategory.Q.obj P))
        (Y := (DerivedCategory.Q.obj Y, DerivedCategory.Q.obj P))
        (DerivedCategory.Q.map f, 𝟙 _)) ∧
  -- tensor_normalized
  (∀ (X : CochainComplex (Modules.{u, v, r} J R) ℤ)
    (hX : CochainComplex.IsKFlatIndependentCoefficients (R := R) X),
    d.tensorIso X = CoefficientTensorModels.iso.{r, u, v, w} J R S M X P hX hP) ∧
  -- evaluation_formula
  (∀ (n p k : ℤ) (h : n + p = k) (h' : p + n = k) (U : Cᵒᵖ)
    (f : (((homFixed.{u, v, r} J R P).obj L).X n).val.obj U)
    (x : (P.X p).val.obj U),
    (d.evaluation.f k).val.app U
        (coefficientTensorGenerator.{r, u, v} J R _ P n p k h U f x) =
      homValue.{u, v, r} J R P ((coefficientHomResolution.{r, u, v} J R).obj L)
        n p k h' U f x) ∧
  -- scalar_formula
  (∀ (T : Modules.{u, v, r} J R) (n p k : ℤ)
    (h : n + p = k) (h' : p + n = k) (U : Cᵒᵖ) (t : T.val.obj U)
    (f : (((homFixed.{u, v, r} J R P).obj L).X n).val.obj U)
    (x : (P.X p).val.obj U),
    ((d.scalarEvaluation T).f k).val.app U
        (coefficientTensorGenerator.{r, u, v} J R _ P n p k h U
          (tensorGenerator.{u, v, r} J R T _ n U t f) x) =
      tensorGenerator.{u, v, r} J R T _ k U t
        (homValue.{u, v, r} J R P ((coefficientHomResolution.{r, u, v} J R).obj L)
          n p k h' U f x)) ∧
  -- uncurry_formula
  (∀ (T : Modules.{u, v, r} J R) (n p k : ℤ)
    (h : n + p = k) (h' : p + n = k) (U : Cᵒᵖ)
    (a : (((tensor.{u, v, r} J R).obj
      (T, (homFixed.{u, v, r} J R P).obj L)).X n).val.obj U)
    (x : (P.X p).val.obj U),
    ((d.uncurry T).f k).val.app U
        (coefficientTensorGenerator.{r, u, v} J R _ P n p k h U a x) =
      homValue.{u, v, r} J R P
        ((coefficientHomResolution.{r, u, v} J R).obj
          ((tensor.{u, v, r} J R).obj
            (T, (coefficientHomResolution.{r, u, v} J R).obj L))) n p k h' U
        ((((comparison.{u, v, r} J R P L).app T).f n).val.app U a) x) ∧
  -- uncurry_eq
  (∀ T : Modules.{u, v, r} J R,
    d.uncurry T = d.scalarEvaluation T ≫ (resolutionUnit.{u, v, r} J R).app _) ∧
  -- evaluation_derived
  ((d.tensorIso ((homFixed.{u, v, r} J R P).obj L)).hom ≫
      S.tensor.map
        (X := (DerivedCategory.Q.obj ((homFixed.{u, v, r} J R P).obj L),
          DerivedCategory.Q.obj P))
        (Y := ((derivedInternalHomOfUniverses.{u, v, r, w} J R).obj
          (op (DerivedCategory.Q.obj P), DerivedCategory.Q.obj L), DerivedCategory.Q.obj P))
        ((coefficientHomResolutionIso.{r, u, v, w} J R P L).inv, 𝟙 _) ≫
      S.evaluation (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj L) =
    DerivedCategory.Q.map d.evaluation ≫
      coefficientHomResolutionInverse.{r, u, v, w} J R L) ∧
  -- transpose_derived
  (∀ T : Modules.{u, v, r} J R,
    (d.tensorIso ((tensor.{u, v, r} J R).obj
        (T, (homFixed.{u, v, r} J R P).obj L))).hom ≫
      (S.transpose _ (DerivedCategory.Q.obj P)
        (DerivedCategory.Q.obj ((tensor.{u, v, r} J R).obj
          (T, (coefficientHomResolution.{r, u, v} J R).obj L)))).symm
        (DerivedCategory.Q.map ((comparison.{u, v, r} J R P L).app T) ≫
          (coefficientHomResolutionIso.{r, u, v, w} J R P
            ((tensor.{u, v, r} J R).obj
              (T, (coefficientHomResolution.{r, u, v} J R).obj L))).inv) =
      DerivedCategory.Q.map (d.scalarEvaluation T))

/-- The representative naturality squares, with their stated variances. The final
clause makes inversion of representative quasi-isomorphisms legitimate even for non-flat T.
Source: Stacks 08J9, 0A95, 0A96, 070I
(blueprint: lem-sfb-hom-strict-numerator-transpose). -/
def StrictNumeratorNaturality
    (S : CoefficientClosedStructure (derivedInternalHomOfUniverses.{u, v, r, w} J R))
    (P L P' L' : CochainComplex (Modules.{u, v, r} J R) ℤ)
    (d : StrictNumeratorData.{u, v, r, w} J R S P L)
    (d' : StrictNumeratorData.{u, v, r, w} J R S P' L')
    (b : P' ⟶ P) (c : L ⟶ L') : Prop :=
  -- tensor_square
  (∀ X : CochainComplex (Modules.{u, v, r} J R) ℤ,
    DerivedCategory.Q.map (numeratorTotalMap.{u, v, r} J R (𝟙 X) b) ≫ (d.tensorIso X).hom =
      (d'.tensorIso X).hom ≫ S.tensor.map
        (X := (DerivedCategory.Q.obj X, DerivedCategory.Q.obj P'))
        (Y := (DerivedCategory.Q.obj X, DerivedCategory.Q.obj P))
        (𝟙 _, DerivedCategory.Q.map b)) ∧
  -- evaluation_square
  (numeratorTotalMap.{u, v, r} J R (numeratorHomMap.{u, v, r} J R b c) (𝟙 P') ≫
      d'.evaluation =
    numeratorTotalMap.{u, v, r} J R (𝟙 _) b ≫ d.evaluation ≫
      (coefficientHomResolution.{r, u, v} J R).map c) ∧
  -- scalar_square
  (∀ (T T' : Modules.{u, v, r} J R) (a : T ⟶ T'),
    numeratorTotalMap.{u, v, r} J R
        (numeratorTensorMap.{u, v, r} J R a (numeratorHomMap.{u, v, r} J R b c)) (𝟙 P') ≫
        d'.scalarEvaluation T' =
      numeratorTotalMap.{u, v, r} J R (𝟙 _) b ≫ d.scalarEvaluation T ≫
        numeratorTensorMap.{u, v, r} J R a ((coefficientHomResolution.{r, u, v} J R).map c)) ∧
  -- comparison_square
  (∀ (T T' : Modules.{u, v, r} J R) (a : T ⟶ T'),
    numeratorTensorMap.{u, v, r} J R a (numeratorHomMap.{u, v, r} J R b c) ≫
        (comparison.{u, v, r} J R P' L').app T' =
      (comparison.{u, v, r} J R P L).app T ≫
        numeratorHomMap.{u, v, r} J R b
          (numeratorTensorMap.{u, v, r} J R a ((coefficientHomResolution.{r, u, v} J R).map c))) ∧
  -- uncurry_square
  (∀ (T T' : Modules.{u, v, r} J R) (a : T ⟶ T'),
    numeratorTotalMap.{u, v, r} J R
        (numeratorTensorMap.{u, v, r} J R a (numeratorHomMap.{u, v, r} J R b c)) (𝟙 P') ≫
        d'.uncurry T' =
      numeratorTotalMap.{u, v, r} J R (𝟙 _) b ≫ d.uncurry T ≫
        (coefficientHomResolution.{r, u, v} J R).map
          (numeratorTensorMap.{u, v, r} J R a ((coefficientHomResolution.{r, u, v} J R).map c))) ∧
  -- invertible_changes
  (QuasiIso b → QuasiIso c →
    QuasiIso (numeratorHomMap.{u, v, r} J R b c) ∧
    QuasiIso ((coefficientHomResolution.{r, u, v} J R).map c) ∧
    ∀ T : Modules.{u, v, r} J R,
      QuasiIso (numeratorTensorMap.{u, v, r} J R (𝟙 T) (numeratorHomMap.{u, v, r} J R b c)) ∧
      QuasiIso (numeratorTensorMap.{u, v, r} J R (𝟙 T)
        ((coefficientHomResolution.{r, u, v} J R).map c)) ∧
      QuasiIso (numeratorTotalMap.{u, v, r} J R
        (numeratorTensorMap.{u, v, r} J R (𝟙 T) (numeratorHomMap.{u, v, r} J R b c)) (𝟙 P')) ∧
      QuasiIso (numeratorTotalMap.{u, v, r} J R
        (𝟙 ((tensor.{u, v, r} J R).obj (T, (homFixed.{u, v, r} J R P).obj L))) b))

/-- The source A = T tensor Hom(P,I(L)), with its already recorded tensor.
Source: Stacks 08J9 (blueprint: lem-sfb-hom-strict-numerator-transpose). -/
noncomputable abbrev numeratorSource
    (P L : CochainComplex (Modules.{u, v, r} J R) ℤ) (T : Modules.{u, v, r} J R) :=
  (tensor.{u, v, r} J R).obj (T, (homFixed.{u, v, r} J R P).obj L)

/-- The output N = T tensor I(L), before its fixed augmentation.
Source: Stacks 08J9 (blueprint: lem-sfb-hom-strict-numerator-transpose). -/
noncomputable abbrev numeratorTarget
    (L : CochainComplex (Modules.{u, v, r} J R) ℤ) (T : Modules.{u, v, r} J R) :=
  (tensor.{u, v, r} J R).obj (T, (coefficientHomResolution.{r, u, v} J R).obj L)

/-- Actual scalar restriction along a coefficient-ring morphism on this site.
Source: Stacks 03DA (blueprint: lem-sfb-hom-strict-numerator-transpose). -/
noncomputable abbrev numeratorRestriction {R' : Sheaf J CommRingCat.{max u v r}}
    (φ : R ⟶ R') : Modules.{u, v, r} J R' ⥤ Modules.{u, v, r} J R :=
  SheafOfModules.restrictScalars.{max u v r}
    ((sheafCompose J (forget₂ CommRingCat.{max u v r} RingCat.{max u v r})).map φ)

/-- Scalar restriction on actual cochain complexes.
Source: Stacks 03DA (blueprint: lem-sfb-hom-strict-numerator-transpose). -/
noncomputable abbrev numeratorRestrictionComplex {R' : Sheaf J CommRingCat.{max u v r}}
    (φ : R ⟶ R') :=
  (numeratorRestriction.{u, v, r} J R φ).mapHomologicalComplex (ComplexShape.up ℤ)

section Coefficients

variable (R' : Sheaf J CommRingCat.{max u v r}) (φ : R ⟶ R')
  (P L : CochainComplex (Modules.{u, v, r} J R) ℤ)
  (P' L' : CochainComplex (Modules.{u, v, r} J R') ℤ)
  (T : Modules.{u, v, r} J R) (T' : Modules.{u, v, r} J R')

/-- Supplied coefficient comparisons, expressed as linear arrows into scalar restriction.
No arbitrary scalar extension is asserted to commute with Hom products. The compatibility
conditions below say exactly that these supplied arrows preserve the tensors, evaluations
and fixed augmentations.
Source: node proof step 7, Stacks 08J9
(blueprint: lem-sfb-hom-strict-numerator-transpose). -/
structure StrictNumeratorCoefficientMaps where
  /-- Map of coefficient modules. -/
  moduleMap : T ⟶ (numeratorRestriction.{u, v, r} J R φ).obj T'
  /-- Map of the first complex, semilinear over φ. -/
  inputMap : P ⟶ (numeratorRestrictionComplex.{u, v, r} J R φ).obj P'
  /-- Supplied map of the fixed resolved outputs. -/
  resolutionMap : (coefficientHomResolution.{r, u, v} J R).obj L ⟶
    (numeratorRestrictionComplex.{u, v, r} J R φ).obj
      ((coefficientHomResolution.{r, u, v} J R').obj L')
  /-- Supplied Hom representative comparison. -/
  homMap : (homFixed.{u, v, r} J R P).obj L ⟶
    (numeratorRestrictionComplex.{u, v, r} J R φ).obj ((homFixed.{u, v, r} J R' P').obj L')
  /-- The induced map on A. -/
  sourceMap : numeratorSource.{u, v, r} J R P L T ⟶
    (numeratorRestrictionComplex.{u, v, r} J R φ).obj (numeratorSource.{u, v, r} J R' P' L' T')
  /-- The induced map on N. -/
  targetMap : numeratorTarget.{u, v, r} J R L T ⟶
    (numeratorRestrictionComplex.{u, v, r} J R φ).obj (numeratorTarget.{u, v, r} J R' L' T')
  /-- The induced map on the total tensor A tensor P. -/
  totalMap : (coefficientTotalTensor.{r, u, v} J R).obj (numeratorSource.{u, v, r} J R P L T, P) ⟶
    (numeratorRestrictionComplex.{u, v, r} J R φ).obj
      ((coefficientTotalTensor.{r, u, v} J R').obj (numeratorSource.{u, v, r} J R' P' L' T', P'))
  /-- The induced map on the evaluation source B tensor P. -/
  evaluationSourceMap : (coefficientTotalTensor.{r, u, v} J R).obj
      ((homFixed.{u, v, r} J R P).obj L, P) ⟶
    (numeratorRestrictionComplex.{u, v, r} J R φ).obj
      ((coefficientTotalTensor.{r, u, v} J R').obj ((homFixed.{u, v, r} J R' P').obj L', P'))
  /-- The supplied comparison of the fixed replacements of N. -/
  augmentedMap : (coefficientHomResolution.{r, u, v} J R).obj (numeratorTarget.{u, v, r} J R L T) ⟶
    (numeratorRestrictionComplex.{u, v, r} J R φ).obj
      ((coefficientHomResolution.{r, u, v} J R').obj (numeratorTarget.{u, v, r} J R' L' T'))

/-- Evaluation-preserving coefficient maps, tested using the actual slice projections
and sheafified tensor generators. This is the precise compatibility assumed in proof step 7.
Source: node proof step 7, Stacks 08J9
(blueprint: lem-sfb-hom-strict-numerator-transpose). -/
def StrictNumeratorCoefficientCompatible
    (a : StrictNumeratorCoefficientMaps.{u, v, r} J R R' φ P L P' L' T T') : Prop :=
  -- hom_evaluation
  (∀ (n p k : ℤ) (h : p + n = k) (U : Cᵒᵖ)
    (f : (((homFixed.{u, v, r} J R P).obj L).X n).val.obj U)
    (x : (P.X p).val.obj U),
    homValue.{u, v, r} J R' P' ((coefficientHomResolution.{r, u, v} J R').obj L')
        n p k h U ((a.homMap.f n).val.app U f) ((a.inputMap.f p).val.app U x) =
      (a.resolutionMap.f k).val.app U
        (homValue.{u, v, r} J R P ((coefficientHomResolution.{r, u, v} J R).obj L)
          n p k h U f x)) ∧
  -- source_tensor
  (∀ (n : ℤ) (U : Cᵒᵖ) (t : T.val.obj U)
    (f : (((homFixed.{u, v, r} J R P).obj L).X n).val.obj U),
    (a.sourceMap.f n).val.app U (tensorGenerator.{u, v, r} J R T _ n U t f) =
      tensorGenerator.{u, v, r} J R' T' _ n U (a.moduleMap.val.app U t)
        ((a.homMap.f n).val.app U f)) ∧
  -- target_tensor
  (∀ (n : ℤ) (U : Cᵒᵖ) (t : T.val.obj U)
    (j : (((coefficientHomResolution.{r, u, v} J R).obj L).X n).val.obj U),
    (a.targetMap.f n).val.app U (tensorGenerator.{u, v, r} J R T _ n U t j) =
      tensorGenerator.{u, v, r} J R' T' _ n U (a.moduleMap.val.app U t)
        ((a.resolutionMap.f n).val.app U j)) ∧
  -- total_tensor
  (∀ (n p k : ℤ) (h : n + p = k) (U : Cᵒᵖ)
    (z : ((numeratorSource.{u, v, r} J R P L T).X n).val.obj U)
    (x : (P.X p).val.obj U),
    (a.totalMap.f k).val.app U (coefficientTensorGenerator.{r, u, v} J R _ P n p k h U z x) =
      coefficientTensorGenerator.{r, u, v} J R' _ P' n p k h U
        ((a.sourceMap.f n).val.app U z) ((a.inputMap.f p).val.app U x)) ∧
  -- evaluation_tensor
  (∀ (n p k : ℤ) (h : n + p = k) (U : Cᵒᵖ)
    (f : (((homFixed.{u, v, r} J R P).obj L).X n).val.obj U)
    (x : (P.X p).val.obj U),
    (a.evaluationSourceMap.f k).val.app U
        (coefficientTensorGenerator.{r, u, v} J R _ P n p k h U f x) =
      coefficientTensorGenerator.{r, u, v} J R' _ P' n p k h U
        ((a.homMap.f n).val.app U f) ((a.inputMap.f p).val.app U x)) ∧
  -- augmentation
  ((resolutionUnit.{u, v, r} J R).app _ ≫ a.augmentedMap =
    a.targetMap ≫ (numeratorRestrictionComplex.{u, v, r} J R φ).map
      ((resolutionUnit.{u, v, r} J R').app _))

end Coefficients


/-- The squares asserted for supplied compatible coefficient comparisons. Localizing
these exact equalities gives the coefficient squares for the derived transposes, since
`transpose_derived` identifies them with the localizations of scalar evaluation.
The normalized comparison a_T enters through its chain uncurrying (`uncurry_eq`); no square
for a_T itself as a map into Hom(P,I(N)) is asserted, since evaluation only at the image of
the supplied map of P does not determine a supplied arrow between Hom representatives.
Source: node proof step 7, Stacks 08J9
(blueprint: lem-sfb-hom-strict-numerator-transpose). -/
def StrictNumeratorCoefficientSquares
    (S : CoefficientClosedStructure (derivedInternalHomOfUniverses.{u, v, r, w} J R))
    (R' : Sheaf J CommRingCat.{max u v r})
    [HasDerivedCategory.{w2} (Modules.{u, v, r} J R')]
    (S' : CoefficientClosedStructure (derivedInternalHomOfUniverses.{u, v, r, w2} J R'))
    (P L : CochainComplex (Modules.{u, v, r} J R) ℤ)
    (P' L' : CochainComplex (Modules.{u, v, r} J R') ℤ)
    (d : StrictNumeratorData.{u, v, r, w} J R S P L)
    (d' : StrictNumeratorData.{u, v, r, w2} J R' S' P' L')
    (T : Modules.{u, v, r} J R) (T' : Modules.{u, v, r} J R') (φ : R ⟶ R')
    (a : StrictNumeratorCoefficientMaps.{u, v, r} J R R' φ P L P' L' T T') : Prop :=
  -- evaluation
  (d.evaluation ≫ a.resolutionMap =
    a.evaluationSourceMap ≫ (numeratorRestrictionComplex.{u, v, r} J R φ).map d'.evaluation) ∧
  -- scalar
  (d.scalarEvaluation T ≫ a.targetMap =
    a.totalMap ≫ (numeratorRestrictionComplex.{u, v, r} J R φ).map (d'.scalarEvaluation T')) ∧
  -- uncurry
  (d.uncurry T ≫ a.augmentedMap =
    a.totalMap ≫ (numeratorRestrictionComplex.{u, v, r} J R φ).map (d'.uncurry T'))

/-- The strict normalized numerator has scalar evaluation as its derived tensor-Hom
transpose, for arbitrary coefficient modules and arbitrary unbounded target complexes.
Source: Stacks Project, sites-cohomology.tex, Tag 08J9, with the node's strict-model
refinement (blueprint: lem-sfb-hom-strict-numerator-transpose).

Proof:
1. Put J = I(L), B = Hom(P,J), N = T tensor J and E = I(N). The fixed augmentations
are quasi-isomorphisms to K-injectives. The one-K-flat chain transpose, applied to the
identity of B, represents evaluation by ev_J followed by the inverse augmentation of L.
The tensor comparison extends the normalized comparison on K-flats using a K-flat
resolution of the unrestricted first factor; it is natural and uniquely determined there.
2. On each slice and (n,p) total summand send (t tensor f) tensor x to t tensor f(x).
Balancedness, restrictions, sheafification and the total coproduct give the map h.
Its differential is t tensor ((d_B f)(x) + (-1)^n f(d_P x)) = t tensor d_J(f(x)).
No permutation of f and x occurs, hence there is no extra interchange sign.
3. The fixed comparison is normalized on actual Hom-product projections and actual
sheafification units: a_T(t tensor f)(x) = eta_N(t tensor f(x)). The tensor,
sheafification, product and coproduct universal properties identify its chain uncurrying
with h followed by eta_N, as an equality of chain maps.
4. Apply lem-sfb-hom-kflat-chain-transpose to the unrestricted complex A and the
K-injective E. Its transpose is Q(h followed by eta_N). The fixed inverse localized
augmentation prescribed by def-coef-hom-representative-evaluation cancels Q(eta_N),
so that the transpose into QN is Q(h). Neither A nor T is assumed flat.
5. Module maps, precomposition in P and resolved postcomposition in L give identical
section formulas on the two sides of the asserted naturality squares. The same universal
properties give the chain equalities. Naturality of the fixed augmentation gives the
squares for a and its uncurrying; localization and the normalized tensor comparison give
the derived squares.
6. Quasi-isomorphisms in L give quasi-isomorphisms between its fixed K-injectives.
Quasi-isomorphisms in P give quasi-isomorphisms of B by lem-pur-rhom-well-defined.
The Hom complexes B are K-injective by lem-pur-hom-kflat-into-kinjective. These changes
are homotopy equivalences by lem-weil-pbc-kinjective-hom-derived, and tensoring with
T[0] preserves their homotopies even when T is non-flat. One-K-flat tensor comparison
also inverts changes of P with unrestricted A. Thus the same squares commute after
inverting the representative changes.
7. Supplied coefficient maps preserve evaluation precisely when alpha_B(f)(alpha_P(x))
= alpha_J(f(x)). Both routes for h then send the actual double tensor generator to
alpha_T(t) tensor alpha_J(f(x)). Tensor/sheafification universal properties give the
coefficient square; augmentation compatibility gives those for a and its uncurrying.
Localize and use step 4 for the transpose square. Identity and successive compatible
maps obey the same equations. No assertion of scalar extension through infinite products,
boundedness, finite generation or continuity is used. -/
theorem strict_numerator_transpose
    (S : CoefficientClosedStructure (derivedInternalHomOfUniverses.{u, v, r, w} J R))
    (M : CoefficientTensorModels.{r, u, v, w} J R S)
    (P L : CochainComplex (Modules.{u, v, r} J R) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients (R := R) P)
    (hflat : ∀ n : ℤ,
      SheafOfModules.IsFlatOnSite.{u, v, max u v r, max u v r} (J := J) (R := R) (P.X n)) :
    ∃ d : StrictNumeratorData.{u, v, r, w} J R S P L,
      StrictNumeratorLaws.{u, v, r, w} J R S M P L hP d ∧
      (∀ (P' L' : CochainComplex (Modules.{u, v, r} J R) ℤ)
        (hP' : CochainComplex.IsKFlatIndependentCoefficients (R := R) P')
        (_hflat' : ∀ n : ℤ,
          SheafOfModules.IsFlatOnSite.{u, v, max u v r, max u v r} (J := J) (R := R) (P'.X n))
        (d' : StrictNumeratorData.{u, v, r, w} J R S P' L'),
        StrictNumeratorLaws.{u, v, r, w} J R S M P' L' hP' d' →
        ∀ (b : P' ⟶ P) (c : L ⟶ L'),
          StrictNumeratorNaturality.{u, v, r, w} J R S P L P' L' d d' b c) ∧
      (∀ (R' : Sheaf J CommRingCat.{max u v r})
        [HasDerivedCategory.{w2} (Modules.{u, v, r} J R')]
        (S' : CoefficientClosedStructure (derivedInternalHomOfUniverses.{u, v, r, w2} J R'))
        (M' : CoefficientTensorModels.{r, u, v, w2} J R' S')
        (P' L' : CochainComplex (Modules.{u, v, r} J R') ℤ)
        (hP' : CochainComplex.IsKFlatIndependentCoefficients (R := R') P')
        (_hflat' : ∀ n : ℤ,
          SheafOfModules.IsFlatOnSite.{u, v, max u v r, max u v r} (J := J) (R := R') (P'.X n))
        (d' : StrictNumeratorData.{u, v, r, w2} J R' S' P' L'),
        StrictNumeratorLaws.{u, v, r, w2} J R' S' M' P' L' hP' d' →
        ∀ (T : Modules.{u, v, r} J R) (T' : Modules.{u, v, r} J R') (φ : R ⟶ R')
          (a : StrictNumeratorCoefficientMaps.{u, v, r} J R R' φ P L P' L' T T'),
          StrictNumeratorCoefficientCompatible.{u, v, r} J R R' φ P L P' L' T T' a →
          StrictNumeratorCoefficientSquares.{u, v, r, w, w2}
            J R S R' S' P L P' L' d d' T T' φ a) := by
  sorry

end WeilConjectures.SfbHomFilteredColimit
