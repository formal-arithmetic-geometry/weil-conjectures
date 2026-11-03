/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CompactSupportComposition.CondensedCompactSupportWitnessFamilies
public import WeilConjectures.AlgebraicGeometry.SepFinType
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.ProfiniteFiniteConstantLocalModel
public import WeilConjectures.CategoryTheory.ProEtaleCoefficients.LocalizingAdmissibleCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SmoothPurity.AdmissibleCondensedCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedModuleDerivedPushpull
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.DetSfCompBaseChangeDefs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerStarComp
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperStarCoherence
public import WeilConjectures.Compactification.Triangle
public import WeilConjectures.CategoryTheory.Adjunction.ExchangeMate
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperLowerShriek
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Proper.ProEtaleProperOpenInterchange
import WeilConjectures.Compactification.NagataCompactification
import WeilConjectures.Compactification.Refinement
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compactification.CompactificationLocalizing
import WeilConjectures.AlgebraicGeometry.Open.OpenImmersionLocalizing
import WeilConjectures.AlgebraicGeometry.Finite.FiniteDirectImageComposition
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compactification.CompactificationCoherenceCocycle
import WeilConjectures.Compactification.CommonDenseRefinement
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compactification.CompactificationRefinementLocalizing
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Proper.ProperImageLocalizingProper
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SmoothPurity.AdmissibleCondensedCoefficients
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedModuleDerivedPushpull
import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.ProfiniteFiniteConstantLocalModel
import WeilConjectures.CategoryTheory.ProEtaleCoefficients.LocalizingAdmissibleCoefficients
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedAmbientExchange
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteProperBaseChange
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralProperBaseChange
import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.PadicIntegersInvertEll
import WeilConjectures.SixFunctors.Integral.IntegralModelsGenerators
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedAmbientExchangeTriangulated
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProperBaseChange.Compatibility
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedCoefficientIsoExchange
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Proper.ProperBaseChangeAdmissibleGenerators
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteCoefficientProperFormulaTools
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Monoidal.Mon
import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars
import WeilConjectures.AlgebraicGeometry.QuotientChange.ScalarGeometricExchangeRectangle
import WeilConjectures.Algebra.Homology.ScalarPullback.KFlatScalarComparisonNormalization
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
import WeilConjectures.AlgebraicGeometry.QuotientChange.InternalScalarRestrictionMateNormalization
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficientsMate
import WeilConjectures.AlgebraicGeometry.IntegralQuotient.IntegralQuotientExchangeComparison
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.PushIntegralDerivedIso
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.AmbientQcqsExchangeCanonicalShifts
import WeilConjectures.Mathlib.CategoryTheory.Triangulated.LocalizingIsoLocus
import WeilConjectures.Compactification.BaseChange
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compact.CompactSupportRefinementBaseChange
import Mathlib.CategoryTheory.Adjunction.Mates
import WeilConjectures.CategoryTheory.RingedDerivedComparisons.RingedDerivedMonoidalComparisons
public import WeilConjectures.AlgebraicGeometry.CondensedPullIsoBalancedComparison

/-! # Coherent composition and arbitrary base change for condensed compact supports

Source: blueprint latest, sec-six-functors-basics/sk-thm-sf-comp-composition,
clauses (1)--(2), canonicity, associativity, and base change
(blueprint: sk-thm-sf-comp-composition).

All comparison components live in the ordinary unbounded module-object derived category.
Their source is the full localizing closure. Preservation clauses give their full targets
and their restrictions to bounded constructible finite-Tor objects. Normalization equations
specify the actual proper/open maps, including for base maps not over the ground field.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.CondensedRing
namespace CompactSupportComposition

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

set_option maxHeartbeats 2000000 in
-- The twelve laws instantiate many derived-functor comparison types.
/-- The twelve comparison laws on six independently supplied witnesses.
This is the exact conjunction in `Coherent`, before packaging its witnesses as fields.
Source: blueprint composition/base change, all normalizations and coherence equations
(blueprint: def-sfb-compact-support-comparison-laws). -/
def ComparisonLawsFor (k : Type u) [Field k]
    (preserves : PreservationFamily Λ k)
    (comparison : RefinementComparisonFamily Λ k)
    (comp : CompositionComparisonFamily Λ k)
    (openIso : OpenExchangeFamily Λ k)
    (pullback_preserves : PullbackPreservationFamily Λ k)
    (exchange : ExchangeFamily Λ k) : Prop :=
  -- refinement
  (∀ {X Y : SepFinType k} (f : X ⟶ Y)
      (c d : Compactification f.hom.left)
      (r : Compactification.DenseBoundaryCompactification f.hom.left)
      [QuasiCompact f.hom.left]
      (hc : r.obj ⟶ detSfBoundaryCompactification c)
      (hd : r.obj ⟶ detSfBoundaryCompactification d)
      (K : (localizingClosureProEtale Λ X.obj.left).FullSubcategory),
    (comparison f c d).hom.app K ≫ compactificationRefinementComponent Λ hd K.obj =
      compactificationRefinementComponent Λ hc K.obj) ∧
  -- comparison_id
  (∀ {X Y : SepFinType k} (f : X ⟶ Y) (c : Compactification f.hom.left),
    comparison f c c = Iso.refl _) ∧
  -- comparison_cocycle
  (∀ {X Y : SepFinType k} (f : X ⟶ Y)
      (c d e : Compactification f.hom.left),
    comparison f c d ≪≫ comparison f d e = comparison f c e) ∧
  -- comp_normalized
  (∀ {X Y Z : SepFinType k} (f : X ⟶ Y) (g : Y ⟶ Z)
      (T : Compactification.Triangle f.hom.left g.hom.left)
      [QuasiCompact (T.cf.g ≫ T.cg.i)]
      (K : (localizingClosureProEtale Λ X.obj.left).FullSubcategory),
    ∃ m, compositionInterchangeIsNormalized Λ T.cf.g T.cg.i
        (detSfBoundaryCompactification (middle T))
        (D((T.cf.i)_!open⟦Λ⟧).obj K.obj) m ∧
      (comp f g T.cf T.cg T.cfg).hom.app K =
        R((T.cg.g)_*⟦Λ⟧).map
          (m ≫ R((T.p)_*⟦Λ⟧).map
            ((openFactor Λ T.cf.i T.q T.cfg.i T.i_q).hom.app K.obj)) ≫
          (rightDerivedLowerStarComp Λ T.p T.cg.g).hom.app
            (D((T.cfg.i)_!open⟦Λ⟧).obj K.obj) ≫
          (Functor.rightDerivedFunctorNatIso
            (eqToIso (congrArg (lowerStar Λ) T.p_g))).hom.app
              (D((T.cfg.i)_!open⟦Λ⟧).obj K.obj)) ∧
  -- comp_independent
  (∀ {X Y Z : SepFinType k} (f : X ⟶ Y) (g : Y ⟶ Z)
      (c c' : Compactification f.hom.left) (d d' : Compactification g.hom.left)
      (e e' : Compactification (f.hom.left ≫ g.hom.left))
      (K : (localizingClosureProEtale Λ X.obj.left).FullSubcategory),
    (comp f g c d e).hom.app K ≫ (comparison (f ≫ g) e e').hom.app K =
      (rightDerivedLowerShriekOfCompactification Λ d).map ((comparison f c c').hom.app K) ≫
        (comparison g d d').hom.app
          ⟨_, (preserves f c').1 K.obj K.property⟩ ≫ (comp f g c' d' e').hom.app K) ∧
  -- unit_left
  (∀ {X Y : SepFinType k} (f : X ⟶ Y) (c : Compactification f.hom.left)
      (K : (localizingClosureProEtale Λ X.obj.left).FullSubcategory),
    (comp (𝟙 X) f (Compactification.ofIsProper (𝟙 X.obj.left)) c
      (c.copy (Category.id_comp f.hom.left))).hom.app K =
      (rightDerivedLowerShriekOfCompactification Λ c).map ((identity Λ X.obj.left).hom.app K.obj)) ∧
  -- unit_right
  (∀ {X Y : SepFinType k} (f : X ⟶ Y) (c : Compactification f.hom.left)
      (K : (localizingClosureProEtale Λ X.obj.left).FullSubcategory),
    (comp f (𝟙 Y) c (Compactification.ofIsProper (𝟙 Y.obj.left))
      (c.copy (Category.comp_id f.hom.left))).hom.app K =
      (identity Λ Y.obj.left).hom.app ((rightDerivedLowerShriekOfCompactification Λ c).obj K.obj)) ∧
  -- assoc
  (∀ {X Y Z W : SepFinType k} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W)
      (c : Compactification f.hom.left) (d : Compactification g.hom.left)
      (e : Compactification h.hom.left)
      (cd : Compactification (f.hom.left ≫ g.hom.left))
      (de : Compactification (g.hom.left ≫ h.hom.left))
      (cde : Compactification ((f.hom.left ≫ g.hom.left) ≫ h.hom.left))
      (K : (localizingClosureProEtale Λ X.obj.left).FullSubcategory),
    (rightDerivedLowerShriekOfCompactification Λ e).map ((comp f g c d cd).hom.app K) ≫
        (comp (f ≫ g) h cd e cde).hom.app K =
      (comp g h d e de).hom.app ⟨_, (preserves f c).1 K.obj K.property⟩ ≫
        (comp f (g ≫ h) c de (cde.copy (Category.assoc _ _ _).symm)).hom.app K) ∧
  -- open_normalized
  (∀ {X Y X' Y' : SepFinType k} {f : X ⟶ Y} {f' : X' ⟶ Y'}
      {a : X'.obj.left ⟶ X.obj.left} {v : Y'.obj.left ⟶ Y.obj.left}
      (sq : IsPullback a f'.hom.left f.hom.left v) (c : Compactification f.hom.left),
    (openIso sq c).inv = openExchange Λ sq c) ∧
  -- exchange_normalized
  (∀ {X Y X' Y' : SepFinType k} {f : X ⟶ Y} {f' : X' ⟶ Y'}
      {a : X'.obj.left ⟶ X.obj.left} {v : Y'.obj.left ⟶ Y.obj.left}
      (sq : IsPullback a f'.hom.left f.hom.left v)
      (c : Compactification f.hom.left) (d : Compactification f'.hom.left)
      (K : (localizingClosureProEtale Λ X.obj.left).FullSubcategory),
    (exchange sq c d).hom.app K =
      (condensedAmbientExchange Λ (square (c.isPullback_g_ofIsPullback sq).flip)).app
          (D((c.i)_!open⟦Λ⟧).obj K.obj) ≫
        R(((c.ofIsPullback sq).g)_*⟦Λ⟧).map ((openIso sq c).hom.app K.obj) ≫
        (comparison f' (c.ofIsPullback sq) d).hom.app
          ⟨_, (pullback_preserves X' X a).1 K.obj K.property⟩) ∧
  -- exchange_independent
  (∀ {X Y X' Y' : SepFinType k} {f : X ⟶ Y} {f' : X' ⟶ Y'}
      {a : X'.obj.left ⟶ X.obj.left} {v : Y'.obj.left ⟶ Y.obj.left}
      (sq : IsPullback a f'.hom.left f.hom.left v)
      (c c' : Compactification f.hom.left) (d d' : Compactification f'.hom.left)
      (K : (localizingClosureProEtale Λ X.obj.left).FullSubcategory),
    (moduleObjectDerivedPullback Λ v).map ((comparison f c c').hom.app K) ≫
        (exchange sq c' d').hom.app K =
      (exchange sq c d).hom.app K ≫ (comparison f' d d').hom.app
        ⟨_, (pullback_preserves X' X a).1 K.obj K.property⟩) ∧
  -- comp_exchange
  (∀ {X Y Z X' Y' Z' : SepFinType k}
      (f : X ⟶ Y) (g : Y ⟶ Z) (f' : X' ⟶ Y') (g' : Y' ⟶ Z')
      (a : X'.obj.left ⟶ X.obj.left) (b : Y'.obj.left ⟶ Y.obj.left)
      (v : Z'.obj.left ⟶ Z.obj.left)
      (sf : IsPullback a f'.hom.left f.hom.left b)
      (sg : IsPullback b g'.hom.left g.hom.left v)
      (c : Compactification f.hom.left) (d : Compactification g.hom.left)
      (e : Compactification (f.hom.left ≫ g.hom.left))
      (c' : Compactification f'.hom.left) (d' : Compactification g'.hom.left)
      (e' : Compactification (f'.hom.left ≫ g'.hom.left))
      (K : (localizingClosureProEtale Λ X.obj.left).FullSubcategory),
    (moduleObjectDerivedPullback Λ v).map ((comp f g c d e).hom.app K) ≫
        (exchange (X := X) (Y := Z) (X' := X') (Y' := Z')
          (f := f ≫ g) (f' := f' ≫ g') (a := a) (v := v) (sf.paste_vert sg) e e').hom.app K =
      (exchange (f := g) (f' := g') (a := b) (v := v) sg d d').hom.app
          ⟨_, (preserves f c).1 K.obj K.property⟩ ≫
        (rightDerivedLowerShriekOfCompactification Λ d').map
          ((exchange (f := f) (f' := f') (a := a) (v := b) sf c c').hom.app K) ≫
        (comp f' g' c' d' e').hom.app
          ⟨_, (pullback_preserves X' X a).1 K.obj K.property⟩)


set_option maxHeartbeats 2000000 in
-- The simultaneous coherence predicate elaborates many nested derived-functor comparisons.

/-- Turn a Cartesian square into the published square with its canonical pullback identification.
Source: blueprint composition/base change, Cartesian squares
(blueprint: sk-thm-sf-comp-composition). -/
def square {A B C D : Scheme.{u}} {a : A ⟶ B} {b : A ⟶ C}
    {f : B ⟶ D} {v : C ⟶ D} (h : IsPullback a b f v) : ChosenCartesianSquare a b f v :=
  ⟨h.toCommSq, h.isoPullback, h.isoPullback_hom_fst, h.isoPullback_hom_snd⟩

/-- The open compositor is the canonical uniqueness-of-left-adjoint comparison.
Source: blueprint composition, consecutive open factors
(blueprint: sk-thm-sf-comp-composition). -/
def openComp {X Y Z : Scheme.{u}} (i : X ⟶ Y) (j : Y ⟶ Z)
    [IsOpenImmersion i] [IsOpenImmersion j] :
    D((i)_!open⟦Λ⟧) ⋙ D((j)_!open⟦Λ⟧) ≅ D((i ≫ j)_!open⟦Λ⟧) :=
  Adjunction.leftAdjointUniq
    ((derivedOpenImmersionLowerShriekUpperStarAdjunction Λ i).comp
      (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ j))
    ((derivedOpenImmersionLowerShriekUpperStarAdjunction Λ (i ≫ j)).ofNatIsoRight
      (Functor.mapDerivedCategoryNatIso (upperStarComp Λ i j) ≪≫
        Functor.mapDerivedCategoryCompIso _ _))

/-- The canonical open compositor transported along an equality of scheme morphisms.
Source: blueprint composition, identification of the composite open factor
(blueprint: sk-thm-sf-comp-composition). -/
@[irreducible] def openFactor {X Y Z : Scheme.{u}} (i : X ⟶ Y) (j : Y ⟶ Z) (h : X ⟶ Z)
    [IsOpenImmersion i] [IsOpenImmersion j] [IsOpenImmersion h] (e : i ≫ j = h) :
    D((i)_!open⟦Λ⟧) ⋙ D((j)_!open⟦Λ⟧) ≅ D((h)_!open⟦Λ⟧) :=
  openComp Λ i j ≪≫ eqToIso (by subst h; rfl)

/-- The intermediate compactification in a compactification triangle.
Source: blueprint composition, proper/open interchange
(blueprint: sk-thm-sf-comp-composition). -/
def middle {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    (T : Compactification.Triangle f g) : Compactification (T.cf.g ≫ T.cg.i) where
  Z := T.cfg.Z
  i := T.q
  g := T.p
  comm := T.isPullback.w
  isProper := inferInstance
  isOpenImmersion := inferInstance

/-- The canonical open inverse-exchange map for an arbitrary Cartesian base square.
Source: blueprint base change, open-adjunction transpose of the identity on the open
(blueprint: sk-thm-sf-comp-composition). -/
@[irreducible] def openExchange {X X' Y Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {a : X' ⟶ X} {v : Y' ⟶ Y} (sq : IsPullback a f' f v)
    (c : Compactification f) :
    moduleObjectDerivedPullback Λ a ⋙ D(((c.ofIsPullback sq).i)_!open⟦Λ⟧) ⟶
      D((c.i)_!open⟦Λ⟧) ⋙
        moduleObjectDerivedPullback Λ (pullback.fst c.g v) :=
  Adjunction.exchangeLeft
    ((derivedOpenImmersionLowerShriekUpperStarAdjunction Λ c.i).ofNatIsoRight
      (leftDerivedUpperStarIsoMapDerivedCategory Λ c.i).symm)
    ((derivedOpenImmersionLowerShriekUpperStarAdjunction Λ (c.ofIsPullback sq).i).ofNatIsoRight
      (leftDerivedUpperStarIsoMapDerivedCategory Λ (c.ofIsPullback sq).i).symm)
    (condensedAmbientPullbackComparison Λ (square (c.isPullback_i_ofIsPullback sq))).symm

/-- The canonical identity comparison for the identity compactification.
Source: blueprint composition, identity normalization
(blueprint: sk-thm-sf-comp-composition). -/
@[irreducible] def identity (X : Scheme.{u}) :
    rightDerivedLowerShriekOfCompactification Λ (Compactification.ofIsProper (𝟙 X)) ≅ 𝟭 _ :=
  Functor.isoWhiskerRight (derivedOpenImmersionLowerShriekId Λ X) _ ≪≫
    Functor.leftUnitor _ ≪≫
      conjugateIsoEquiv (derivedUpperStarLowerStarAdjunction Λ (𝟙 X))
        (Adjunction.id) (leftDerivedUpperStarId Λ X).symm

/-- Existence of coherent comparisons, with the full targets expressed by preservation.
The witnesses and conditions are preservation, canonical refinement normalization, composition,
proper/open normalization, compactification independence, units, associativity, arbitrary
base change, its normalization and independence, and the composition/exchange equation.
Source: blueprint latest, sk-thm-sf-comp-composition, clauses (1)--(2) and proof
(blueprint: sk-thm-sf-comp-composition). -/
def Coherent (k : Type u) [Field k] : Prop :=
  ∃ (preserves : PreservationFamily Λ k),
  ∃ (comparison : RefinementComparisonFamily Λ k),
  ∃ (comp : CompositionComparisonFamily Λ k),
  ∃ (openIso : OpenExchangeFamily Λ k),
  ∃ (pullback_preserves : PullbackPreservationFamily Λ k),
  ∃ (exchange : ExchangeFamily Λ k),
  ComparisonLawsFor Λ k preserves comparison comp openIso pullback_preserves exchange

/-- Composition and arbitrary scheme base change for condensed compact supports, with the
canonical refinement and proper/open normalizations and all coherence equations.
Source: blueprint latest, sk-thm-sf-comp-composition, clauses (1)--(2)
(blueprint: sk-thm-sf-comp-composition).

Proof plan, following the seven DAG steps:
1. Choose compactifications using thm-nagata-compactification and
lem-sfb-over-compactification-composite-cartesian. The theorems
det-sf-comp-coherence-single and det-proper-image-localizing-open preserve Dctf and Loc.
2. Interchange the middle proper and open factors using the unique identity-on-the-open
map (det-sf-comp-composition-interchange, lem-zl-condensed-open-proper-pasting). Apply the
last proper image and the canonical compositors (lem-weil-derived-direct-image-composition).
3. Compare all compactification models by common dense refinements. Mixed horizontal and
vertical mate-pasting commute with refinement; the compactification cocycle cancels the
intermediate comparisons (det-nagata-refinement-common-dense,
det-sf-comp-coherence-refinement, det-sf-comp-coherence-cocycle,
lem-zl-condensed-open-proper-pasting). This gives simultaneous independence.
4. Expand both threefold bracketings. Disjoint moves commute; overlapping moves are the
mixed-pasting equations or the proper/open compositor associativity laws. Identity models
give both unit equations. These are equations of actual ambient arrows on every Loc object.
5. Arbitrary scheme pullback preserves Dctf and sums. Proper exchange is invertible on Dctf
by lem-zl-condensed-arbitrary-proper-generators and lem-weil-pbc-proper-base-change, and on
Loc by det-proper-image-localizing-proper, lem-sfb-ambient-qcqs-exchange-canonical-shifts and
det-sf-determination-localizing. Pullback preservation is lem-zl-condensed-arbitrary-pullback.
No vertical map is required to respect the ground field.
6. Pull back each compactification literally, allowing nondense models. Compose proper
exchange with the inverse of the open-adjunction mate and the normalized compactification
comparison (lemma-nagata-compactification-base-change). The theorem
lem-sfb-compact-support-refinement-base-change and the cocycle prove choice independence.
7. Expand composition/exchange into these proper and open mates. Mate-pasting, the mixed
cube equation and open composition give the displayed equation, with canonical associators
(lem-zl-condensed-open-proper-pasting, lem-weil-pbc-mate-pasting,
lem-sfb-ringed-derived-monoidal-comparisons).
Fullness and the preservation clauses restrict every comparison and equation to Dctf. -/
theorem coherent_exists (ℓ p : ℕ) [Fact ℓ.Prime] [Fact p.Prime]
    (hpℓ : p ≠ ℓ) (k : Type u) [Field k] [CharP k p]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (hΛ : IsLocalizingAdmissibleCoefficient ℓ Λ) :
    Coherent Λ k := by
  sorry

end CompactSupportComposition
end AlgebraicGeometry.ProEtale.CondensedRing
