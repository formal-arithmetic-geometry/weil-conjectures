/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Sites.SectionsWithSupport
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback
public import WeilConjectures.AlgebraicGeometry.CoefOpenTensorEvaluationData
public import WeilConjectures.AlgebraicGeometry.CoefSupportPointSectionsData
public import WeilConjectures.AlgebraicGeometry.CompactSupportReductionTower
public import WeilConjectures.AlgebraicGeometry.CoefDerivedSystemEvaluationCalculus
public import WeilConjectures.SixFunctors.CoefTowerTraceRectification
public import WeilConjectures.Algebra.Homology.OrdinaryModuleDerivedInternalHom
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralCoefficientGerm
import all WeilConjectures.AlgebraicGeometry.CompactSupportReductionTower
import WeilConjectures.AlgebraicGeometry.CompactSupportNativeSystemTransition
import WeilConjectures.AlgebraicGeometry.CoefSupportPointSectionsModelExistence
import WeilConjectures.AlgebraicGeometry.CoefNativeOpenTensorModelsExistence

/-! # Compact-support reduction and the normalized open tensor model

Source: blueprint main-20261015, sec-smooth-purity/sk-lem-sp-tower,
prop-coef-integral-dualizing.proof.md, paragraph 2; Stacks 0941, 0E8I, 0GL1, 07A4
(blueprint: lem-coef-support-open-tensor-model).

All categories are ordinary unbounded derived categories. Index n denotes exponent n+1.
The tower is the specified reduction/open/proper/restriction composite, before limits.
-/

@[expose] public noncomputable section
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option autoImplicit false
set_option relaxedAutoImplicit false
attribute [local irreducible] CategoryTheory.Functor.leftAdjoint
  CategoryTheory.Functor.mapDerivedCategory CategoryTheory.Functor.rightDerivedFunctor
  HasDerivedCategory.standard
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures.SemilinearSections
namespace WeilConjectures.CoefSupportOpenTensor




attribute [-instance] SemilinearSections.hasDerived SemilinearSections.moduleAbelian
  SemilinearSections.abelianSheafify SemilinearSections.locallyBijective
  SemilinearSections.sequenceSmall SemilinearSections.sliceSmall

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The separately derived native compact-support operation on quotient systems.
Source: blueprint paragraph 2; Stacks 0941
(blueprint: lem-coef-support-open-tensor-model). -/
def operation {X Y : Scheme.{u}} {a : X ⟶ Y} (c : Compactification a) :=
  ProEtale.VaryingRing.J (compactSupportSystemLevel l E) (compactSupportSystemQuotient l E) c.i ⋙
    ProEtale.VaryingRing.P (compactSupportSystemLevel l E) (compactSupportSystemQuotient l E) c.g

/-- The named strict tower, bound to the specified lifting composite rather than
selected from its finite evaluations. Its input model is S.reductionModel.
Source: blueprint paragraph 2; node proof steps 1--3
(blueprint: lem-coef-support-open-tensor-model). -/
def tower {X Y : Scheme.{u}} {a : X ⟶ Y} (c : Compactification a)
    (S : CoefficientDerivedSystemCalculus.{u, u} l E X) :=
  S.reduction ⋙ operation l E c ⋙ coefficientSequenceDerivedRestriction.{u, u} l E Y

/-- The first whole-derived realization in the native ringed-site presentation.
Here the specified strict compact-support functor is its actual lifting composite,
so the comparison is the identity of that composite before any finite evaluation.
Source: blueprint paragraph 2; node proof step 2
(blueprint: lem-coef-support-open-tensor-model). -/
def realization {X Y : Scheme.{u}} {a : X ⟶ Y} (c : Compactification a)
    (S : CoefficientDerivedSystemCalculus.{u, u} l E X) :
    S.reduction ⋙ operation l E c ⋙ coefficientSequenceDerivedRestriction.{u, u} l E Y ≅
      tower l E c S :=
  Iso.refl _

/-- Canonical finite evaluation: restriction/evaluation, native compact support,
then the simultaneous reduction computation. These are functor isomorphisms.
Source: Stacks 0941; node proof step 3
(blueprint: lem-coef-support-open-tensor-model). -/
def evaluation {X Y : Scheme.{u}} {a : X ⟶ Y} (c : Compactification a)
    (S : CoefficientDerivedSystemCalculus.{u, u} l E X) (n : ℕ) :
    tower l E c S ⋙ pbcTowerEvaluation Y (completedIntegralCommRingSheafUnrestricted l E Y) n ≅
      compactSupportRestrictedLevel l E c n :=
  Functor.isoWhiskerLeft (S.reduction ⋙ operation l E c)
      (coefficientRestrictedEvaluationIso.{u, u} l E Y n) ≪≫
    Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft S.reduction (compactSupportSystemEvaluation l E c n) ≪≫
        Functor.isoWhiskerRight (S.reductionEvaluation n)
          (sfIntrinsicCompactSupport c (Padic.coefficientExtensionRing l E (n + 1))))
      (scalarReductionDerivedRestriction l E Y n)


/-- The whole-derived ringed point-square comparison applied to compact support.
The comparison is fixed by SectionsModel.comparison_unit, not chosen from its values.
Source: Stacks 0D6E; node proof step 4
(blueprint: lem-coef-support-open-tensor-model). -/
def pointComparison {X Y : Scheme.{u}} {a : X ⟶ Y} (c : Compactification a)
    (S : CoefficientDerivedSystemCalculus.{u, u} l E X)
    (sections : SectionsModel l E Y) :
    S.reduction ⋙ operation l E c ⋙ quotientSections l E Y ≅
      tower l E c S ⋙ integralSections l E Y :=
  Functor.isoWhiskerLeft (S.reduction ⋙ operation l E c) sections.comparison

/-- Finite R-linear point evaluation of the actual quotient-system realization.
Source: Stacks 0941, 0D6E; node proof step 4
(blueprint: lem-coef-support-open-tensor-model). -/
def pointEvaluation {X Y : Scheme.{u}} {a : X ⟶ Y} (c : Compactification a)
    (S : CoefficientDerivedSystemCalculus.{u, u} l E X)
    (sections : SectionsModel l E Y) (n : ℕ) :
    S.reduction ⋙ operation l E c ⋙ quotientSections l E Y ⋙ coefTraceEvaluation l E n ≅
      compactSupportRestrictedLevel l E c n ⋙ levelSections l E Y :=
  Functor.isoWhiskerRight (pointComparison l E c S sections) (coefTraceEvaluation l E n) ≪≫
    Functor.isoWhiskerLeft (tower l E c S) (sections.evaluation n) ≪≫
    Functor.isoWhiskerRight (evaluation l E c S n) (levelSections l E Y)

private theorem pastePointTransitions
    {C : Type*} [Category C]
    {Qm Qn Im In Em En Vm Vn : C}
    (tQ : Qm ⟶ Qn) (am : Qm ⟶ Im) (an : Qn ⟶ In) (tI : Im ⟶ In)
    (bm : Im ⟶ Em) (bn : In ⟶ En) (tE : Em ⟶ En)
    (em : Em ⟶ Vm) (en : En ⟶ Vn) (tV : Vm ⟶ Vn)
    (ha : am ≫ tI = tQ ≫ an) (hb : tI ≫ bn = bm ≫ tE)
    (he : tE ≫ en = em ≫ tV) :
    tQ ≫ an ≫ bn ≫ en = am ≫ bm ≫ em ≫ tV := by
  rw [← reassoc_of% ha, reassoc_of% hb, he]

/-- The strict compact-support reduction realization and normalized open tensor model.
All structural witnesses are conclusions, and the strict tower is the named composite.
No finiteness, boundedness, normalization or Tor condition is imposed on K, U or L.

Source: blueprint main-20261015, prop-coef-integral-dualizing.proof.md, paragraph 2;
Stacks 0941, 0D6E, 0E8I, 0GL1 and 07A4
(blueprint: lem-coef-support-open-tensor-model).

Proof, following the six steps of the node:
1. Resolve K by a flat-term K-flat P. Constant inverse image and coefficient pullback
preserve this class. The derived-pullback comparison identifies M with the strict
system P tensor A_n, with chain maps id tensor q. The reduction calculus supplies
this identification naturally, with its actual quotient transitions.
2. Apply exact native open extension, separately derive proper image, and restrict
along the completed coefficient projections. This is exactly tower, by definition;
its identification is on the full derived system category, before evaluation.
3. Native compact-support evaluation, followed by S.reductionEvaluation, gives
Res_n F_n K_n. The native transition theorem gives compactSupportRestrictedTransition
for every comparable pair, including the equal-level case, naturally in K.
4. The point-sections/scalar-restriction square commutes on actual sections and actions.
Derived direct-image composition, with exact scalar restriction, identifies its two
factorizations. Constant-tower evaluation preserves simultaneous K-injectives, so its
finite values are R Gamma(Y,F_n K_n) and its arrows are sections of step 3. No limit.
5. Apply the normalized open tensor theorem on the quotient sequence site. Its inverse
is the open-unit transpose under the canonical restriction/tensor isomorphism. The
ordinary version is the sheafified pure-tensor map u tensor l to u tensor l restricted
to X, by its unit equation and the pure-tensor normalization of restriction. Assemble
these module maps on each total summand; naturality gives compatibility with the
signed differential d_C tensor 1 + (-1)^a 1 tensor d_P. For arbitrary C and flat-term
K-flat P, a K-flat refinement of C and tensor descent give the one-flat-factor models.
Their refinement equations make the localized chain map precisely gamma.
6. The same maps are module morphisms on the entire sequence site, so they commute
with every quotient-semilinear restriction, including nonflat quotients. Exact vertical
evaluation preserves these chain formulas, units and tensor comparisons; hence it
carries gamma to the identical canonical finite open comparison. Tensor descent makes
all representative choices yield the same natural transformation. -/
theorem supportOpenTensorModel
    (k : Type u) [Field k] (X Y : Scheme.{u})
    [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    (a : X ⟶ Y) [a.IsOver (Spec (.of k))]
    [IsSeparated a] [LocallyOfFiniteType a] [QuasiCompact a]
    (_hl : IsUnit (l : k)) (c : Compactification a) :
    ∃ (SX : CoefficientDerivedSystemCalculus.{u, u} l E X)
      (SZ : CoefficientDerivedSystemCalculus.{u, u} l E c.Z)
      (sections : SectionsModel l E Y)
      (O : SystemOpenModel l E c.i SX.toCoefficientDerivedSystemTensors
        SZ.toCoefficientDerivedSystemTensors)
      (On : ∀ n : ℕ, FiniteOpenModel l E c.i SX.toCoefficientDerivedSystemTensors
        SZ.toCoefficientDerivedSystemTensors n),
      (∀ (K : DerivedCategory (scalarReductionSource.{u, u} l E X))
        (m n : ℕ) (h : n ≤ m),
        (pbcTowerTransition Y (completedIntegralCommRingSheafUnrestricted l E Y) m n h).app
            ((tower l E c SX).obj K) ≫ (evaluation l E c SX n).hom.app K =
          (evaluation l E c SX m).hom.app K ≫
            compactSupportRestrictedTransition l E c m n h K) ∧
      GammaEvaluation l E c.i SX SZ O On ∧
      (∀ (K : DerivedCategory (scalarReductionSource.{u, u} l E X))
        (m n : ℕ) (h : n ≤ m),
        (coefTraceTransition l E h).app
            ((SX.reduction ⋙ operation l E c ⋙ quotientSections l E Y).obj K) ≫
            (pointEvaluation l E c SX sections n).hom.app K =
          (pointEvaluation l E c SX sections m).hom.app K ≫
            (levelSections l E Y).map (compactSupportRestrictedTransition l E c m n h K)) := by
  obtain ⟨SX, _⟩ := coefficientDerivedSystemEvaluationCalculus.{u, u} l E X
  obtain ⟨SZ, _⟩ := coefficientDerivedSystemEvaluationCalculus.{u, u} l E c.Z
  obtain ⟨sections⟩ := sectionsModel_exists l E Y
  obtain ⟨O, On, hO⟩ := nativeOpenTensorModels_exists l E c.i SX SZ
  have ht : ∀ (K : DerivedCategory (scalarReductionSource.{u, u} l E X))
      (m n : ℕ) (h : n ≤ m),
      (pbcTowerTransition Y (completedIntegralCommRingSheafUnrestricted l E Y) m n h).app
          ((tower l E c SX).obj K) ≫ (evaluation l E c SX n).hom.app K =
        (evaluation l E c SX m).hom.app K ≫
          compactSupportRestrictedTransition l E c m n h K := by
    intro K m n h
    let F (n : ℕ) := sfIntrinsicCompactSupport c
      (Padic.coefficientExtensionRing l E (n + 1))
    let R (W : Scheme.{u}) (n : ℕ) := scalarReductionDerivedRestriction l E W n
    let r (W : Scheme.{u}) := (proEtaleCoefficientRestrictScalars W
      (compactSupportLevelQuotient l E m n h)).mapDerivedCategory
    let M := SX.reduction.obj K
    let N := (operation l E c).obj M
    let d := (compactSupportCoefficientTransition l E X h).app M
    let dn := (compactSupportCoefficientTransition l E Y h).app N
    let ε (n : ℕ) := (compactSupportSystemEvaluation l E c n).hom.app M
    let ρ (n : ℕ) := (SX.reductionEvaluation n).hom.app K
    have hg := compactSupportNativeSystemTransition l E c h M
    have hd := compactSupportReductionTransition l E X SX.toCoefficientDerivedSystemReduction h K
    change dn ≫ (r Y).map (ε n) = ε m ≫ (F m).map d ≫
      (sfCompactSupportRestriction c (compactSupportLevelQuotient l E m n h)).hom.app
        ((coefficientSequenceDerivedEvaluation l E X n).obj M) at hg
    change d ≫ (r X).map (ρ n) = ρ m ≫ compactSupportReductionMap l E X m n h K at hd
    have H := compactSupportFiniteSquare (F m) (F n) (r X) (r Y)
      (sfCompactSupportRestriction c (compactSupportLevelQuotient l E m n h)).hom
      d (ρ m) (ρ n) (compactSupportReductionMap l E X m n h K) dn (ε m) (ε n) hg hd
    dsimp only [evaluation, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
      Iso.trans_hom, NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
    simp only [compactSupportRestrictedTransition, Functor.map_comp, Category.assoc]
    change (pbcTowerTransition Y (completedIntegralCommRingSheafUnrestricted l E Y) m n h).app
        ((coefficientSequenceDerivedRestriction.{u, u} l E Y).obj N) ≫
      (coefficientRestrictedEvaluationIso l E Y n).hom.app N ≫
      (R Y n).map (ε n) ≫ (R Y n).map ((F n).map (ρ n)) =
      (coefficientRestrictedEvaluationIso l E Y m).hom.app N ≫
      (R Y m).map (ε m) ≫ (R Y m).map ((F m).map (ρ m)) ≫
      (R Y m).map ((F m).map (compactSupportReductionMap l E X m n h K)) ≫
      (R Y m).map ((sfCompactSupportRestriction c (compactSupportLevelQuotient l E m n h)).hom.app
        ((scalarReductionDerivedExtension l E X n).obj K)) ≫
      (compactSupportRestrictionComp l E Y m n h).hom.app
        ((F n).obj ((scalarReductionDerivedExtension l E X n).obj K))
    exact compactSupportCompletedSquare (r Y) (R Y m) (R Y n)
      (compactSupportRestrictionComp l E Y m n h).hom dn (ε m) (ε n)
      ((F m).map (ρ m)) ((F n).map (ρ n))
      ((F m).map (compactSupportReductionMap l E X m n h K))
      ((sfCompactSupportRestriction c (compactSupportLevelQuotient l E m n h)).hom.app
        ((scalarReductionDerivedExtension l E X n).obj K))
      ((pbcTowerTransition Y (completedIntegralCommRingSheafUnrestricted l E Y) m n h).app
        ((coefficientSequenceDerivedRestriction.{u, u} l E Y).obj N))
      ((coefficientRestrictedEvaluationIso l E Y m).hom.app N)
      ((coefficientRestrictedEvaluationIso l E Y n).hom.app N)
      (compactSupportCoefficientTransition_restricted l E Y h N) H
  refine ⟨SX, SZ, sections, O, On, ht, hO, ?_⟩
  intro K m n h
  have hn := (coefTraceTransition l E h).naturality
    ((pointComparison l E c SX sections).hom.app K)
  have hs := sections.transitions ((tower l E c SX).obj K) m n h
  dsimp only [pointEvaluation, Iso.trans_hom, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app]
  have hf := congrArg (levelSections l E Y).map (ht K m n h)
  simp only [Functor.map_comp] at hf
  simpa only [Category.assoc] using
    pastePointTransitions _ _ _ _ _ _ _ _ _ _ hn hs hf

end WeilConjectures.CoefSupportOpenTensor
