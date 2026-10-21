/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NB
-/
module

public import Sheaf.SixFunctors.IntegralOpenReductionComparison
public import Sheaf.TraceFormula.CompactSupportSystemEvaluationDiagram
public import WeilConjectures.Compactification.RefinementCategory
public import Mathlib.CategoryTheory.Functor.OfSequence
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import Sheaf.SecSmoothPurity.IntrinsicCompactSupportRestriction
import Sheaf.AlgebraicGeometry.ProEtaleFixedScalarRestrictionDirectImage
import Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed
import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
import Sheaf.Paper.CompletedIntegralConstantMapOfUniverses

/-!
# The proper-image and compact-support quotient towers

Source: Bhatt--Scholze, Definition 6.7.6 and Lemma 6.7.7; Stacks Tags 0GL1 and 0E8I;
blueprint main-20261015, `def-weil-integral-rational-qbar-compact-support`
(blueprint: lem-sf-compact-support-proper-image-tower).

Index n denotes exponent n+1. All coefficient categories are the recorded module-sheaf
categories on the small pro-etale site, with independent site and coefficient universes.
The presentation data below retain the section-normalized open restriction comparison
and the K-injective-normalized direct-image comparison; they are supplied in the conclusion.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective

universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures.CompactSupportProperImageTower

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Presentation of the canonical finite direct images and their coefficient comparisons.
The underived comparison is identity on sections; the derived comparison is its normalized
resolution comparison, without assuming that restriction preserves K-injectives.
Source: Stacks 0D6E; node proof Steps 2--3
(blueprint: lem-sf-compact-support-proper-image-tower). -/
class DirectData {V Y : Scheme.{t}} (p : V ⟶ Y) where
  [additive : ∀ n : ℕ, (compactSupportLevelDirectImage l E p n).Additive]
  [kInjective : ∀ n : ℕ, Abelian.HasKInjectiveResolutions (normalizedDVRModules l E V n)]
  ordinary : ∀ n : ℕ,
    normalizedDVRModuleRes l E V (Nat.le_succ n) ⋙ compactSupportLevelDirectImage l E p (n+1) ≅
      compactSupportLevelDirectImage l E p n ⋙ normalizedDVRModuleRes l E Y (Nat.le_succ n)
  sections : ∀ (n : ℕ) (M : normalizedDVRModules l E V n) (W : Y.ProEtᵒᵖ),
    HEq (fun x ↦ ((ordinary n).hom.app M).val.app W x)
      (fun x : M.val.obj ((proEtaleBaseChange p).op.obj W) ↦ x)
  comparison : ∀ n : ℕ,
    normalizedDVRRes l E V (Nat.le_succ n) ⋙
        (compactSupportLevelDirectImage l E p (n+1)).rightDerivedFunctor ≅
      (compactSupportLevelDirectImage l E p n).rightDerivedFunctor ⋙
        normalizedDVRRes l E Y (Nat.le_succ n)
  normalization : ∀ n : ℕ,
    CompactSupportDerivedSquareNormalization
      (compactSupportLevelDirectImage l E p n) (compactSupportLevelDirectImage l E p (n+1))
      (normalizedDVRModuleRes l E V (Nat.le_succ n))
      (normalizedDVRModuleRes l E Y (Nat.le_succ n)) (ordinary n) (comparison n)

attribute [instance] DirectData.additive DirectData.kInjective

variable {X V Y : Scheme.{t}} (j : X ⟶ V) [IsOpenImmersion j] (p : V ⟶ Y)

/-- The canonical finite open/scalar-restriction identification, given on ordinary module
sheaves and normalized by the same section on every extension summand.
Source: Stacks 0E8I; node proof Step 1
(blueprint: lem-sf-compact-support-proper-image-tower). -/
structure OpenData (o : IntegralOpenReduction.Operations l E j) where
  ordinary : ∀ n : ℕ,
    normalizedDVRModuleRes l E X (Nat.le_succ n) ⋙
        IntegralOpenReduction.finiteExtension l E j o (n+1) ≅
      IntegralOpenReduction.finiteExtension l E j o n ⋙
        normalizedDVRModuleRes l E V (Nat.le_succ n)
  sections : ∀ (n : ℕ) (M : normalizedDVRModules l E X n) (W : V.ProEt)
      (a : W ⟶ IntegralOpenReduction.openObject j),
    HEq (fun x : ((normalizedDVRModuleRes l E X (Nat.le_succ n)).obj M).val.obj
        (op ((IntegralOpenReduction.sliceSite j).obj (Over.mk a))) ↦
      ((ordinary n).hom.app M).val.app (op W)
        (IntegralOpenReduction.finiteExtensionSection l E j o (n+1)
          ((normalizedDVRModuleRes l E X (Nat.le_succ n)).obj M) W a x))
      (fun x : M.val.obj (op ((IntegralOpenReduction.sliceSite j).obj (Over.mk a))) ↦
        IntegralOpenReduction.finiteExtensionSection l E j o n M W a x)

variable (o : IntegralOpenReduction.Operations l E j)

/-- The localized canonical open/scalar comparison.
Source: Stacks 015F and 0E8I; node proof Step 1
(blueprint: lem-sf-compact-support-proper-image-tower). -/
def openRestriction (e : OpenData l E j o) (n : ℕ) :
    normalizedDVRRes l E X (Nat.le_succ n) ⋙ compactSupportCanonicalJLevel l E j o (n+1) ≅
      compactSupportCanonicalJLevel l E j o n ⋙ normalizedDVRRes l E V (Nat.le_succ n) :=
by
  letI := normalizedDVRModuleRes_limits l E X (Nat.le_succ n)
  letI := normalizedDVRModuleRes_colimits l E X (Nat.le_succ n)
  letI := normalizedDVRModuleRes_limits l E V (Nat.le_succ n)
  letI := normalizedDVRModuleRes_colimits l E V (Nat.le_succ n)
  exact Functor.mapDerivedCategorySquareIso (e.ordinary n)

/-- The quotient map is the transpose of the actual smaller-level scalar-extension unit.
Thus it is id tensor quotient on K-flat representatives.
Source: Stacks 06YY; node proof Steps 1--2
(blueprint: lem-sf-compact-support-proper-image-tower). -/
def reductionMap (W : Scheme.{t}) (K : DerivedCategory (scalarReductionSource l E W))
    (n : ℕ) :
    (coefficientFiniteDerivedExtension l E W (n+1)).obj K ⟶
      (normalizedDVRRes l E W (Nat.le_succ n)).obj
        ((coefficientFiniteDerivedExtension l E W n).obj K) :=
  ((coefficientFiniteAdjunction l E W (n+1)).homEquiv _ _).symm
    ((coefficientFiniteAdjunction l E W n).unit.app K ≫
      (compactSupportSystemRestrictionComp l E W (Nat.le_succ n)).inv.app
        ((coefficientFiniteDerivedExtension l E W n).obj K))

/-- The evaluated canonical strict open-reduction comparison alpha_n.
Source: Stacks 0GL1 and 0E8I; node proof Step 1
(blueprint: lem-sf-compact-support-proper-image-tower). -/
def alpha (SV : CoefficientDerivedSystemCalculus l E V)
    (SX : CoefficientDerivedSystemCalculus l E X)
    (tensor : IntegralOpenReduction.TensorComparison l E j o)
    (r : IntegralOpenReduction.Comparison l E j o SV SX tensor)
    (K : (IntegralOpenReduction.complete l E X).FullSubcategory) (n : ℕ) :
    (coefficientFiniteDerivedExtension l E V n).obj
        ((IntegralOpenReduction.shriek l E j o).obj K.obj) ≅
      (compactSupportCanonicalJLevel l E j o n).obj
        ((coefficientFiniteDerivedExtension l E X n).obj K.obj) :=
  ((SV.reductionEvaluation n).app ((IntegralOpenReduction.shriek l E j o).obj K.obj)).symm ≪≫
    (coefficientSequenceDerivedEvaluation l E V n).mapIso (r.r.app K) ≪≫
    (compactSupportCanonicalJEvaluation l E j o n).app (SX.reduction.obj K.obj) ≪≫
    (compactSupportCanonicalJLevel l E j o n).mapIso ((SX.reductionEvaluation n).app K.obj)

variable [d : DirectData l E p]

/-- The proper-image reduction level N_n, restricted to the completed coefficients of Y.
Source: Bhatt--Scholze 6.7.6; node statement
(blueprint: lem-sf-compact-support-proper-image-tower). -/
def properLevel (K : DerivedCategory (scalarReductionSource l E X)) (n : ℕ) :=
  (coefficientFiniteDerivedRestriction l E Y n).obj
    ((compactSupportLevelDirectImage l E p n).rightDerivedFunctor.obj
      ((coefficientFiniteDerivedExtension l E V n).obj
        ((IntegralOpenReduction.shriek l E j o).obj K)))

/-- The compact-support level M_n uses exactly the finite composite Rp_* j_!.
Source: Bhatt--Scholze 6.7.6; node statement
(blueprint: lem-sf-compact-support-proper-image-tower). -/
def supportLevel (K : DerivedCategory (scalarReductionSource l E X)) (n : ℕ) :=
  (coefficientFiniteDerivedRestriction l E Y n).obj
    ((compactSupportLevelDirectImage l E p n).rightDerivedFunctor.obj
      ((compactSupportCanonicalJLevel l E j o n).obj
        ((coefficientFiniteDerivedExtension l E X n).obj K)))

/-- The proper transition is Res_(n+1) of Rp_*(d_n) followed by C_n.
The final comparison is the actual composition of coefficient restrictions.
Source: node proof Step 2 (blueprint: lem-sf-compact-support-proper-image-tower). -/
def properTransition (K : DerivedCategory (scalarReductionSource l E X)) (n : ℕ) :
    properLevel l E j p o K (n+1) ⟶ properLevel l E j p o K n :=
  (coefficientFiniteDerivedRestriction l E Y (n+1)).map
    ((compactSupportLevelDirectImage l E p (n+1)).rightDerivedFunctor.map
      (reductionMap l E V ((IntegralOpenReduction.shriek l E j o).obj K) n) ≫
      (d.comparison n).hom.app
        ((coefficientFiniteDerivedExtension l E V n).obj
          ((IntegralOpenReduction.shriek l E j o).obj K))) ≫
    (compactSupportSystemRestrictionComp l E Y (Nat.le_succ n)).hom.app
      ((compactSupportLevelDirectImage l E p n).rightDerivedFunctor.obj
        ((coefficientFiniteDerivedExtension l E V n).obj
          ((IntegralOpenReduction.shriek l E j o).obj K)))

/-- The compact-support transition applies j_! and Rp_* to quotient reduction, then
uses the canonical open restriction identification and the same C_n.
Source: node proof Step 2 (blueprint: lem-sf-compact-support-proper-image-tower). -/
def supportTransition (e : OpenData l E j o)
    (K : DerivedCategory (scalarReductionSource l E X)) (n : ℕ) :
    supportLevel l E j p o K (n+1) ⟶ supportLevel l E j p o K n :=
  (coefficientFiniteDerivedRestriction l E Y (n+1)).map
    ((compactSupportLevelDirectImage l E p (n+1)).rightDerivedFunctor.map
      ((compactSupportCanonicalJLevel l E j o (n+1)).map (reductionMap l E X K n) ≫
        (openRestriction l E j o e n).hom.app
          ((coefficientFiniteDerivedExtension l E X n).obj K)) ≫
      (d.comparison n).hom.app
        ((compactSupportCanonicalJLevel l E j o n).obj
          ((coefficientFiniteDerivedExtension l E X n).obj K))) ≫
    (compactSupportSystemRestrictionComp l E Y (Nat.le_succ n)).hom.app
      ((compactSupportLevelDirectImage l E p n).rightDerivedFunctor.obj
        ((compactSupportCanonicalJLevel l E j o n).obj
          ((coefficientFiniteDerivedExtension l E X n).obj K)))

/-- The specified component beta_n = Res_n Rp_*(alpha_n), including its inverse.
Source: node statement and proof Step 4
(blueprint: lem-sf-compact-support-proper-image-tower). -/
def beta (SV : CoefficientDerivedSystemCalculus l E V)
    (SX : CoefficientDerivedSystemCalculus l E X)
    (tensor : IntegralOpenReduction.TensorComparison l E j o)
    (r : IntegralOpenReduction.Comparison l E j o SV SX tensor)
    (K : (IntegralOpenReduction.complete l E X).FullSubcategory) (n : ℕ) :
    properLevel l E j p o K.obj n ≅ supportLevel l E j p o K.obj n :=
  (coefficientFiniteDerivedRestriction l E Y n).mapIso
    ((compactSupportLevelDirectImage l E p n).rightDerivedFunctor.mapIso
      (alpha l E j o SV SX tensor r K n))

/-- The proper-image tower as an ordinary inverse system in D(R_Y).
Source: Stacks 0030; node proof Step 4
(blueprint: lem-sf-compact-support-proper-image-tower). -/
def properTower (K : DerivedCategory (scalarReductionSource l E X)) :
    ℕᵒᵖ ⥤ DerivedCategory (scalarReductionSource l E Y) :=
  Functor.ofOpSequence (properTransition l E j p o K)

/-- The compact-support tower with its specified quotient transitions.
Source: Stacks 0030; node proof Step 4
(blueprint: lem-sf-compact-support-proper-image-tower). -/
def supportTower (e : OpenData l E j o) (K : DerivedCategory (scalarReductionSource l E X)) :
    ℕᵒᵖ ⥤ DerivedCategory (scalarReductionSource l E Y) :=
  Functor.ofOpSequence (supportTransition l E j p o e K)

/-- The canonical components give an isomorphism of the two specified inverse systems.
Source: Bhatt--Scholze 6.7.6--6.7.7; Stacks 0GL1, 0E8I and 0030;
blueprint main-20261015, integral compact-support formula
(blueprint: lem-sf-compact-support-proper-image-tower).
Proof:
1. Evaluate the strict open-reduction comparison on a complete K. Its strict quotient
square says S(alpha_n) d_n = e_n j_!(k_n) alpha_(n+1); both open identifications
are the identity on the underlying open sections (the open-reduction and compact-support
restriction-of-scalars lemmas).
2. Write D_n = Rp_*. The proper transition before restriction is C_n D_(n+1)(d_n).
The support transition is C_n D_(n+1)(e_n) D_(n+1)(j_!(k_n)), exactly the composite
specified by the compact-support restriction-of-scalars lemma.
3. Naturality of the normalized direct-image comparison at alpha_n and functoriality
of D_(n+1), followed by the square in Step 1, give
S(D_n(alpha_n)) C_n D_(n+1)(d_n) = t^M_n D_(n+1)(alpha_(n+1)).
This uses the ordinary unbounded direct images, with no constructibility or Tor bound.
4. Restrict to R_Y. Composing scalar restrictions is identity on underlying sections,
so the equation becomes t^N_n beta_n = beta_(n+1) t^M_n in Lean composition order.
Each beta_n is invertible. The equations construct a natural transformation of the
ofOpSequence functors; the component inverses also commute with the transitions,
so this transformation is an isomorphism. All m>=n equations follow by composition. -/
theorem compactSupportProperImageTower
    (K₀ : Type t) [Field K₀]
    [X.Over (Spec (.of K₀))] [Y.Over (Spec (.of K₀))]
    [LocallyOfFiniteType (X ↘ Spec (.of K₀))] [QuasiCompact (X ↘ Spec (.of K₀))]
    [LocallyOfFiniteType (Y ↘ Spec (.of K₀))] [QuasiCompact (Y ↘ Spec (.of K₀))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of K₀))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (_hl : IsUnit (l : K₀)) (c : Compactification f) [QuasiCompact c.i] :
    ∃ (o : IntegralOpenReduction.Operations l E c.i)
      (SV : CoefficientDerivedSystemCalculus l E c.Z)
      (SX : CoefficientDerivedSystemCalculus l E X)
      (tensor : IntegralOpenReduction.TensorComparison l E c.i o)
      (r : IntegralOpenReduction.Comparison l E c.i o SV SX tensor)
      (d : DirectData l E c.g) (e : OpenData l E c.i o),
      ∀ K : (IntegralOpenReduction.complete l E X).FullSubcategory,
        (∀ n : ℕ,
          properTransition l E c.i c.g o (d := d) K.obj n ≫
              (beta l E c.i c.g o (d := d) SV SX tensor r K n).hom =
            (beta l E c.i c.g o (d := d) SV SX tensor r K (n+1)).hom ≫
              supportTransition l E c.i c.g o (d := d) e K.obj n) ∧
        ∃ b : properTower l E c.i c.g o (d := d) K.obj ≅
            supportTower l E c.i c.g o (d := d) e K.obj,
          ∀ n : ℕ, b.hom.app (op n) =
            (beta l E c.i c.g o (d := d) SV SX tensor r K n).hom := by
  sorry

end WeilConjectures.CompactSupportProperImageTower
