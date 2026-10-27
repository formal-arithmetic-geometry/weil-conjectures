/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q124
-/
module

public import Sheaf.Paper.BoundedSiteAdjunctionTranspose
public import Sheaf.Paper.CompactSupportSiteCoherence
public import Sheaf.Paper.CohomologicalSmoothnessFiniteComparison
public import Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients
public import Sheaf.Paper.ExchangeProjectionSuppliedDomains
public import Sheaf.Paper.CompactSupportExchangeTransport
public import Sheaf.AlgebraicGeometry.CompactSupportFiniteTorsion
public import Sheaf.AlgebraicGeometry.FixedComparisonDirectImageMate
public import Mathlib.CategoryTheory.Adjunction.Mates
import Sheaf.Paper.PurityFiniteSettingComparisonHypotheses

/-! # Bounded site comparison of compact-support exchange transposes

Source: current blueprint, lem-pur-co-smooth-etale-locality, proof Steps 1 and 4;
thm-pur-composition-coherence, proof Steps 1--2; Stacks Project, Tag 0B65
(blueprint: lem-pur-bounded-site-exchange-transposes).

The right-adjoint comparison is the site-unit map rho. The exceptional arrows are
transposes of inverse exchange followed by the counit. No invertibility of these
exceptional arrows, or exceptional adjunction on unbounded pro-etale inputs, is used.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale

/-- The canonical isomorphism rho, obtained by applying H and comparison to the
site-adjunction unit. Its data are fixed by that unit.
Source: Stacks Tag 0B65, bounded site-adjunction normalization
(blueprint: lem-pur-bounded-site-exchange-transposes). -/
def boundedExchangeRhoIso (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}}
    (H : Etale.DerivedCategoryModule A Y ⥤ Etale.DerivedCategoryModule A X)
    (K : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    D(comparisonUpperStar (ModuleCat.{u + 1} A) X).obj (H.obj K.obj) ≅
      D(comparisonUpperStar (ModuleCat.{u + 1} A) X).obj
        (H.obj (R(comparisonLowerStar (ModuleCat.{u + 1} A) Y).obj
          (D(comparisonUpperStar (ModuleCat.{u + 1} A) Y).obj K.obj))) :=
  letI := isIso_derivedComparisonAdjunction_unit_app
    (ModuleCat.{u + 1} A) Y K.obj K.property
  D(comparisonUpperStar (ModuleCat.{u + 1} A) X).mapIso
    (H.mapIso (asIso ((derivedComparisonAdjunction (ModuleCat.{u + 1} A) Y).unit.app K.obj)))

/-- The retained origin of w^* G_f^p C_Y K: kappa_w followed by w^*(rho).
Source: the node's proof Steps 2--4, retaining the source identification
(blueprint: lem-pur-bounded-site-exchange-transposes). -/
def boundedExchangeSourceIso (A : Type (u + 1)) [CommRing A] [Finite A]
    {X X' Y : Scheme.{u}} (w : X' ⟶ X)
    (H : Etale.DerivedCategoryModule A Y ⥤ Etale.DerivedCategoryModule A X)
    (K : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (hHK : _root_.DerivedCategory.TStructure.t.plus (H.obj K.obj)) :=
  (leftDerivedUpperStarComparisonIso w A).app ⟨H.obj K.obj, hHK⟩ ≪≫
    (upperStar (ModuleCat.{u + 1} A) w).leftDerivedFunctor.mapIso
      (boundedExchangeRhoIso A H K)

/-- The specified pro-etale transpose using the displayed etale origin, then
changing that origin by kappa_w followed by w^*(rho). The function is exactly the
forward map of boundedSiteHomEquiv; it does not choose an ambient adjunction.
Source: Stacks Tag 0B65 and node proof Steps 3--4
(blueprint: lem-pur-bounded-site-exchange-transposes). -/
def boundedExchangeProTranspose (A : Type (u + 1)) [CommRing A] [Finite A]
    {X X' Y Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {w : X' ⟶ X} {v : Y' ⟶ Y} (sq : IsPullback w f' f v)
    (c : Compactification f)
    (H : Etale.DerivedCategoryModule A Y ⥤ Etale.DerivedCategoryModule A X)
    (H' : Etale.DerivedCategoryModule A Y' ⥤ Etale.DerivedCategoryModule A X')
    (adj' : Etale.rightDerivedLowerShriekOfCompactification
      (ModuleCat.{u + 1} A) (c.ofIsPullback sq) ⊣ H')
    (K : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (hHK : _root_.DerivedCategory.TStructure.t.plus (H.obj K.obj))
    (q : (rightDerivedLowerShriekOfCompactification
        (ModuleCat.{u + 1} A) (c.ofIsPullback sq)).obj
        ((upperStar (ModuleCat.{u + 1} A) w).leftDerivedFunctor.obj
          (D(comparisonUpperStar (ModuleCat.{u + 1} A) X).obj
            (H.obj (R(comparisonLowerStar (ModuleCat.{u + 1} A) Y).obj
              (D(comparisonUpperStar (ModuleCat.{u + 1} A) Y).obj K.obj))))) ⟶
      (upperStar (ModuleCat.{u + 1} A) v).leftDerivedFunctor.obj
        (D(comparisonUpperStar (ModuleCat.{u + 1} A) Y).obj K.obj)) :=
  (boundedExchangeSourceIso A w H K hHK).inv ≫
    boundedSiteTranspose A (c.ofIsPullback sq) H' adj'
      (D+(Etale.upperStar (ModuleCat.{u + 1} A) w).obj
        ⟨H.obj K.obj, hHK⟩)
      ((upperStar (ModuleCat.{u + 1} A) v).leftDerivedFunctor.obj
        (D(comparisonUpperStar (ModuleCat.{u + 1} A) Y).obj K.obj))
      ((rightDerivedLowerShriekOfCompactification
        (ModuleCat.{u + 1} A) (c.ofIsPullback sq)).map
          (boundedExchangeSourceIso A w H K hHK).hom ≫ q)

/-- The chosen etale exchange in the ordinary derived category. The two displayed
compatibilities insert exactly the inclusion of the bounded-below compact supports.
Source: def-cbc-exchange-map and bounded/unbounded compact-support compatibility
(blueprint: lem-pur-bounded-site-exchange-transposes). -/
def boundedExchangeEtaleMap (A : Type (u + 1)) [CommRing A] [Finite A]
    {X X' Y Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {w : X' ⟶ X} {v : Y' ⟶ Y} (sq : IsPullback w f' f v)
    (c : Compactification f)
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :=
  (Etale.upperStar (ModuleCat.{u + 1} A) v).mapDerivedCategory.map
      ((Etale.rightDerivedLowerShriekOfCompactificationPlusCompatibility
        (ModuleCat.{u + 1} A) c).inv.app L) ≫
    DerivedCategory.Plus.ι.map
      ((Etale.rightDerivedLowerShriekOfCompactificationPlusBaseChangeMap A sq c).app L) ≫
    (Etale.rightDerivedLowerShriekOfCompactificationPlusCompatibility
      (ModuleCat.{u + 1} A) (c.ofIsPullback sq)).hom.app
        (D+(Etale.upperStar (ModuleCat.{u + 1} A) w).obj L)

/-- The actual exchanges are isomorphisms, and their inverse-exchange/counit
transposes have the required comparison square. The two equations imposed on qe
and qp uniquely prescribe them as inverse exchange followed by the relevant counit.
Thus the last equation compares the actual d_e and d_p, not arbitrary endpoint maps.
The last target factor is G_f'^p(kappa_v); the source factor is
kappa_w followed by w^*(rho). At the coefficient unit these are the dualizing arrows.

Source: current blueprint, lem-pur-co-smooth-etale-locality proof Steps 1 and 4;
Stacks Tag 0B65 (blueprint: lem-pur-bounded-site-exchange-transposes).

Proof, following the seven DAG steps:
1. finite_setting_comparison_hypotheses supplies a nonnegative bound for c.Z,
including the empty case. compactSupport_exchange_transport gives the square of the
actual exchanges with the proper-mate/open B. compactSupportFiniteTorsion makes the
etale exchange invertible; the square gives the pro-etale result on every origin.
Invert this square, reversing the comparison factors.
2. boundedSiteAdjunctionTranspose identifies epsilon_p F_p(rho) B with C(epsilon_e).
The two normalization equations below consequently define precisely q_e and q_p.
3. Naturality of E_p in rho moves F_f'^p(w^*rho) across inverse exchange. Substitute
the inverse square of Step 1 and the counit equation of Step 2. Insert kappa_w at
the source and kappa_v inverse at the target. The result is C(q_e).
4. Apply boundedSiteAdjunctionTranspose for f' to that compatible pair. Source
naturality of the bounded-origin Hom bijection gives the displayed equality.
5. At K=A_Y, inverse image of the constant unit identifies v^*A_Y with A_Y'.
compactSupport_exchange_transport identifies the transported exchange in the
co-smoothness definition with this same exchange at its retained origin.
6. For forward mates use mateEquiv, its unit/square/counit formula, the normalized
counits above and fixedComparisonDirectImageMatePlus for ordinary direct images.
7. mateEquiv_vcomp, mateEquiv_hcomp, conjugate compatibility and the identity law,
with compactSupportSiteCoherence, preserve identity, both Cartesian pastings,
proper refinement and further open restriction. The diagram statement below retains
all these operations and their bounded intermediate origins explicitly. -/
theorem boundedSiteExchangeTransposes
    (P : WeilConjectures.PurityFiniteSetting.{u})
    {X X' Y Y' : Scheme.{u}}
    (aX : X ⟶ Spec (.of P.field.k)) (aY : Y ⟶ Spec (.of P.field.k))
    (aX' : X' ⟶ Spec (.of P.field.k)) (aY' : Y' ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aX] [QuasiCompact aX] [LocallyOfFiniteType aY] [QuasiCompact aY]
    [LocallyOfFiniteType aX'] [QuasiCompact aX']
    [LocallyOfFiniteType aY'] [QuasiCompact aY']
    (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (f' : X' ⟶ Y') [IsSeparated f'] [LocallyOfFiniteType f'] [QuasiCompact f']
    (w : X' ⟶ X) (v : Y' ⟶ Y) (sq : IsPullback w f' f v)
    (hf : f ≫ aY = aX) (_hf' : f' ≫ aY' = aX')
    (_hv : v ≫ aY = aY') (_hw : w ≫ aX = aX') (c : Compactification f) :
    ∃ (d : ℕ) (hd : topologicalKrullDim c.Z ≤ (d : WithBot ℕ∞)),
    ∀ (H : Etale.DerivedCategoryModule P.Coefficient Y ⥤
        Etale.DerivedCategoryModule P.Coefficient X)
      (H' : Etale.DerivedCategoryModule P.Coefficient Y' ⥤
        Etale.DerivedCategoryModule P.Coefficient X')
      (adj : Etale.rightDerivedLowerShriekOfCompactification
        (ModuleCat.{u + 1} P.Coefficient) c ⊣ H)
      (adj' : Etale.rightDerivedLowerShriekOfCompactification
        (ModuleCat.{u + 1} P.Coefficient) (c.ofIsPullback sq) ⊣ H')
      (K : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology
        (ModuleCat.{u + 1} P.Coefficient)))
      (hHK : _root_.DerivedCategory.TStructure.t.plus (H.obj K.obj))
      (_hH'K : _root_.DerivedCategory.TStructure.t.plus
        (H'.obj ((D+(Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) v).obj K).obj))),
    IsIso ((Etale.rightDerivedLowerShriekOfCompactificationPlusBaseChangeMap
      P.Coefficient sq c).app ⟨H.obj K.obj, hHK⟩) ∧
    IsIso ((rightDerivedLowerShriekOfCompactificationBaseChangeMap
      (ModuleCat.{u + 1} P.Coefficient) sq c).app
        (D(comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) X).obj
          (H.obj (R(comparisonLowerStar (ModuleCat.{u + 1} P.Coefficient) Y).obj
              (D(comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) Y).obj K.obj))))) ∧
    ∀ (qe : (Etale.rightDerivedLowerShriekOfCompactification
        (ModuleCat.{u + 1} P.Coefficient) (c.ofIsPullback sq)).obj
        ((D+(Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) w).obj
          ⟨H.obj K.obj, hHK⟩).obj) ⟶
        (D+(Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) v).obj K).obj)
      (qp : (rightDerivedLowerShriekOfCompactification
        (ModuleCat.{u + 1} P.Coefficient) (c.ofIsPullback sq)).obj
        ((upperStar (ModuleCat.{u + 1} P.Coefficient) w).leftDerivedFunctor.obj
          (D(comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) X).obj
            (H.obj (R(comparisonLowerStar (ModuleCat.{u + 1} P.Coefficient) Y).obj
                (D(comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) Y).obj K.obj))))) ⟶
        (upperStar (ModuleCat.{u + 1} P.Coefficient) v).leftDerivedFunctor.obj
          (D(comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) Y).obj K.obj)),
      boundedExchangeEtaleMap P.Coefficient sq c ⟨H.obj K.obj, hHK⟩ ≫ qe =
        (Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) v).mapDerivedCategory.map
          (adj.counit.app K.obj) →
      (rightDerivedLowerShriekOfCompactificationBaseChangeMap
        (ModuleCat.{u + 1} P.Coefficient) sq c).app
          (D(comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) X).obj
            (H.obj (R(comparisonLowerStar (ModuleCat.{u + 1} P.Coefficient) Y).obj
                (D(comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) Y).obj K.obj)))) ≫ qp =
        (upperStar (ModuleCat.{u + 1} P.Coefficient) v).leftDerivedFunctor.map
          (boundedSiteCounit P aX aY f hf c d hd H adj
            ((siteComparisonDerivedPullbackPlus Y P.Coefficient).obj K)) →
      D(comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) X').map
          ((adj'.homEquiv _ _ ) qe) ≫
        boundedSiteRho P.Coefficient H'
          ((D+(Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) v).obj K).obj) ≫
        D(comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) X').map
          (H'.map (R(comparisonLowerStar (ModuleCat.{u + 1} P.Coefficient) Y').map
              ((leftDerivedUpperStarComparisonIso v P.Coefficient).hom.app K))) =
      (boundedExchangeSourceIso P.Coefficient w H K hHK).hom ≫
        boundedExchangeProTranspose P.Coefficient sq c H H' adj' K hHK qp := by
  sorry


/-- Finite diagrams of the specified comparisons, now including arbitrary Cartesian
exchange and inverse exchange. The inherited diagrams supply proper refinement,
compact-support composition and open restriction. Concatenation and the two
whiskerings retain both kinds of pasting. Boundary changes insert only compatible
canonical endpoint identifications; they do not assume a generator square commutes.
Every etale intermediate is an object of D+, including all inverse exchanges.
Source: node proof Steps 6--7 (blueprint: lem-pur-bounded-site-exchange-transposes). -/
inductive BoundedExchangeDiagram (P : WeilConjectures.PurityFiniteSetting.{u}) :
    {T : Scheme.{u}} → CompactSupportSiteBoundary P.Coefficient T →
      CompactSupportSiteBoundary P.Coefficient T → Type (u + 2)
  | inherited {T : Scheme.{u}} {b₀ b₁ : CompactSupportSiteBoundary P.Coefficient T}
      (D : CompactSupportSiteDiagram P b₀ b₁) : BoundedExchangeDiagram P b₀ b₁
  | exchange {X X' Y Y' : Over (Spec (.of P.field.k))}
      [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
      [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
      [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
      [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom]
      {f : X ⟶ Y} {f' : X' ⟶ Y'} {w : X' ⟶ X} {v : Y' ⟶ Y}
      [IsSeparated f.left] [LocallyOfFiniteType f.left] [QuasiCompact f.left]
      (sq : IsPullback w.left f'.left f.left v.left) (c : Compactification f.left)
      (L : DerivedCategory.Plus (Sheaf X.left.smallEtaleTopology
        (ModuleCat.{u + 1} P.Coefficient))) :
      BoundedExchangeDiagram P (coherenceRestrictionSource P.Coefficient v.left c L)
        (coherenceRestrictionTarget P.Coefficient sq c L)
  | inverseExchange {X X' Y Y' : Over (Spec (.of P.field.k))}
      [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
      [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
      [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
      [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom]
      {f : X ⟶ Y} {f' : X' ⟶ Y'} {w : X' ⟶ X} {v : Y' ⟶ Y}
      [IsSeparated f.left] [LocallyOfFiniteType f.left] [QuasiCompact f.left]
      (sq : IsPullback w.left f'.left f.left v.left) (c : Compactification f.left)
      (L : DerivedCategory.Plus (Sheaf X.left.smallEtaleTopology
        (ModuleCat.{u + 1} P.Coefficient))) :
      BoundedExchangeDiagram P (coherenceRestrictionTarget P.Coefficient sq c L)
        (coherenceRestrictionSource P.Coefficient v.left c L)
  | comp {T : Scheme.{u}} {b₀ b₁ b₂ : CompactSupportSiteBoundary P.Coefficient T}
      (D : BoundedExchangeDiagram P b₀ b₁) (E : BoundedExchangeDiagram P b₁ b₂) :
      BoundedExchangeDiagram P b₀ b₂
  | push {X Y : Over (Spec (.of P.field.k))}
      [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
      [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
      {f : X ⟶ Y} [IsSeparated f.left] [LocallyOfFiniteType f.left] [QuasiCompact f.left]
      (c : Compactification f.left) {b₀ b₁ : CompactSupportSiteBoundary P.Coefficient X.left}
      (D : BoundedExchangeDiagram P b₀ b₁) :
      BoundedExchangeDiagram P (coherencePushBoundary P.Coefficient c b₀)
        (coherencePushBoundary P.Coefficient c b₁)
  | pull {X Y : Over (Spec (.of P.field.k))}
      [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
      [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] (v : X ⟶ Y)
      {b₀ b₁ : CompactSupportSiteBoundary P.Coefficient Y.left}
      (D : BoundedExchangeDiagram P b₀ b₁) :
      BoundedExchangeDiagram P (coherencePullBoundary P.Coefficient v.left b₀)
        (coherencePullBoundary P.Coefficient v.left b₁)
  | change {T : Scheme.{u}}
      {b₀ b₁ c₀ c₁ : CompactSupportSiteBoundary P.Coefficient T}
      (e₀ : b₀.etale ≅ c₀.etale) (e₁ : b₁.etale ≅ c₁.etale)
      (p₀ : b₀.proEtale ≅ c₀.proEtale) (p₁ : b₁.proEtale ≅ c₁.proEtale)
      (h₀ : (coherenceBoundedSiteFunctor P.Coefficient T).map e₀.hom ≫ c₀.comparison.hom =
        b₀.comparison.hom ≫ p₀.hom)
      (h₁ : (coherenceBoundedSiteFunctor P.Coefficient T).map e₁.hom ≫ c₁.comparison.hom =
        b₁.comparison.hom ≫ p₁.hom)
      (D : BoundedExchangeDiagram P b₀ b₁) : BoundedExchangeDiagram P c₀ c₁

/-- The etale assembly of a generated diagram, using the actual exchange or its
unique inverse, and the inherited proper-refinement/composition maps.
Source: node proof Steps 1 and 7 (blueprint: lem-pur-bounded-site-exchange-transposes). -/
def BoundedExchangeDiagram.etaleMap {P : WeilConjectures.PurityFiniteSetting.{u}}
    {T : Scheme.{u}} {b₀ b₁ : CompactSupportSiteBoundary P.Coefficient T}
    (D : BoundedExchangeDiagram P b₀ b₁) : b₀.etale ⟶ b₁.etale :=
  match D with
  | @BoundedExchangeDiagram.inherited .(P) _ _ _ D => D.etaleMap
  | @BoundedExchangeDiagram.exchange .(P) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ sq c L =>
      (Etale.rightDerivedLowerShriekOfCompactificationPlusBaseChangeMap
        P.Coefficient sq c).app L
  | @BoundedExchangeDiagram.inverseExchange .(P) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ sq c L =>
      letI := (Etale.compactSupportFiniteTorsion P.Coefficient sq c).1 L
      inv ((Etale.rightDerivedLowerShriekOfCompactificationPlusBaseChangeMap
        P.Coefficient sq c).app L)
  | @BoundedExchangeDiagram.comp .(P) _ _ _ _ D E => D.etaleMap ≫ E.etaleMap
  | @BoundedExchangeDiagram.push .(P) _ _ _ _ _ _ _ _ _ _ c _ _ D =>
      (coherenceEtaleFunctor P.Coefficient c).map D.etaleMap
  | @BoundedExchangeDiagram.pull .(P) _ _ _ _ _ _ v _ _ D =>
      D+(Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) v.left).map
        D.etaleMap
  | @BoundedExchangeDiagram.change .(P) _ _ _ _ _ e₀ e₁ _ _ _ _ D => e₀.inv ≫ D.etaleMap ≫ e₁.hom

/-- The pro-etale assembly uses the specified ambient exchange, including its
actual inverse, rather than defining exchange by conjugating the etale map.
Source: node proof Steps 1 and 7 (blueprint: lem-pur-bounded-site-exchange-transposes). -/
def BoundedExchangeDiagram.proEtaleMap {P : WeilConjectures.PurityFiniteSetting.{u}}
    {T : Scheme.{u}} {b₀ b₁ : CompactSupportSiteBoundary P.Coefficient T}
    (D : BoundedExchangeDiagram P b₀ b₁) : b₀.proEtale ⟶ b₁.proEtale :=
  match D with
  | @BoundedExchangeDiagram.inherited .(P) _ _ _ D => D.proEtaleMap
  | @BoundedExchangeDiagram.exchange .(P) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ sq c L =>
      (rightDerivedLowerShriekOfCompactificationBaseChangeMap
        (ModuleCat.{u + 1} P.Coefficient) sq c).app
          (D(comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) _).obj L.obj)
  | @BoundedExchangeDiagram.inverseExchange .(P) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ sq c L =>
      letI := isIso_rightDerivedLowerShriekOfCompactificationBaseChangeMap_app
        P.Coefficient sq c _ ⟨L.obj, L.property, ⟨Iso.refl _⟩⟩
      inv ((rightDerivedLowerShriekOfCompactificationBaseChangeMap
        (ModuleCat.{u + 1} P.Coefficient) sq c).app
          (D(comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) _).obj L.obj))
  | @BoundedExchangeDiagram.comp .(P) _ _ _ _ D E => D.proEtaleMap ≫ E.proEtaleMap
  | @BoundedExchangeDiagram.push .(P) _ _ _ _ _ _ _ _ _ _ c _ _ D =>
      (coherenceProEtaleFunctor P.Coefficient c).map D.proEtaleMap
  | @BoundedExchangeDiagram.pull .(P) _ _ _ _ _ _ v _ _ D =>
      (upperStar (ModuleCat.{u + 1} P.Coefficient) v.left).leftDerivedFunctor.map D.proEtaleMap
  | @BoundedExchangeDiagram.change .(P) _ _ _ _ _ _ _ p₀ p₁ _ _ D => p₀.inv ≫ D.proEtaleMap ≫ p₁.hom

/-- Site comparison identifies every generated assembly, and therefore respects
identities, either Cartesian pasting, refinements and further compatible restriction.
The second clause compares assemblies whenever the etale pasting/refinement law
identifies them. No commutativity hypothesis is placed on a generator.
Source: current blueprint, thm-pur-composition-coherence proof Steps 1--2;
Stacks Tag 0B65 (blueprint: lem-pur-bounded-site-exchange-transposes).
Proof: for inherited generators apply compactSupportSiteCoherence. For exchange
apply compactSupport_exchange_transport, and invert its square for inverseExchange.
Naturality of B and of the pullback comparison proves push and pull. Composition
concatenates the squares, identity is the identity square, and change inserts the
specified compatible endpoint isomorphisms. Induction gives the first assertion.
For the second assertion use the first assertion twice and cancel the invertible
boundary. Etale identity, horizontal and vertical pasting are thm-cbc-finite-torsion;
proper refinement and compact-support composition are compactSupportSiteCoherence.
Hence both assemblies and their mates are compared with the very same boundaries. -/
theorem boundedSiteExchangeDiagramComparison
    (P : WeilConjectures.PurityFiniteSetting.{u}) :
    (∀ {T : Scheme.{u}} {b₀ b₁ : CompactSupportSiteBoundary P.Coefficient T}
      (D : BoundedExchangeDiagram P b₀ b₁),
      (coherenceBoundedSiteFunctor P.Coefficient T).map D.etaleMap ≫ b₁.comparison.hom =
        b₀.comparison.hom ≫ D.proEtaleMap) ∧
    (∀ {T : Scheme.{u}} {b₀ b₁ : CompactSupportSiteBoundary P.Coefficient T}
      (D E : BoundedExchangeDiagram P b₀ b₁),
      D.etaleMap = E.etaleMap → D.proEtaleMap = E.proEtaleMap) := by
  sorry

/-- Transposes of every forward or inverse assembly have the same comparison.
Together with mateEquiv's two pasting laws and conjugation laws this is comparison
of the mates under the specified available adjunctions, including their successive
pasting and refinement. All exceptional Hom maps here have bounded etale origins.
Source: current blueprint, thm-pur-composition-coherence proof Step 2;
Stacks Tag 0B65 (blueprint: lem-pur-bounded-site-exchange-transposes).
Proof: the diagram comparison gives B_out C(D_e) = D_p B_in. Insert the specified
source and target identifications, compose with z, and cancel B_out. Apply
boundedSiteAdjunctionTranspose. Naturality gives independence of the origin witness.
The unit is the transpose of the identity, and the counit is the inverse transpose
of the identity, so this also compares unit/square/counit mates. The direct-image
cases use fixedComparisonDirectImageMatePlus_counit. mateEquiv_vcomp and
mateEquiv_hcomp compare either pasted mate; the conjugation rules insert refinement
and boundary changes and conjugateEquiv_id gives identity. No general claim that
mates preserve isomorphisms is made. -/
theorem boundedSiteExchangeDiagramTransposes
    (P : WeilConjectures.PurityFiniteSetting.{u}) {X T : Scheme.{u}}
    (aX : X ⟶ Spec (.of P.field.k)) (aT : T ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aX] [QuasiCompact aX] [LocallyOfFiniteType aT] [QuasiCompact aT]
    (f : X ⟶ T) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (hf : f ≫ aT = aX) (c : Compactification f) (d : ℕ)
    (hd : topologicalKrullDim c.Z ≤ (d : WithBot ℕ∞))
    (H : Etale.DerivedCategoryModule P.Coefficient T ⥤
      Etale.DerivedCategoryModule P.Coefficient X)
    (adj : Etale.rightDerivedLowerShriekOfCompactification
      (ModuleCat.{u + 1} P.Coefficient) c ⊣ H)
    (J : DerivedCategory.Plus (Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} P.Coefficient)))
    (K : DerivedCategory.Plus (Sheaf T.smallEtaleTopology
      (ModuleCat.{u + 1} P.Coefficient)))
    {b₀ b₁ : CompactSupportSiteBoundary P.Coefficient T}
    (D : BoundedExchangeDiagram P b₀ b₁)
    (e : (Etale.rightDerivedLowerShriekOfCompactification
      (ModuleCat.{u + 1} P.Coefficient) c).obj J.obj ≅ b₀.etale.obj)
    (z : b₁.etale.obj ⟶ K.obj) :
    boundedSiteHomEquiv P aX aT f hf c d hd H adj J
      ((siteComparisonDerivedPullbackPlus T P.Coefficient).obj K)
      ((compactSupportSiteComparison P.Coefficient c).hom.app J ≫
        D(comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) T).map e.hom ≫
        b₀.comparison.hom ≫ D.proEtaleMap ≫ b₁.comparison.inv ≫
        D(comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) T).map z) =
    D(comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) X).map
      ((adj.homEquiv J.obj K.obj)
        (e.hom ≫ DerivedCategory.Plus.ι.map D.etaleMap ≫ z)) ≫
      boundedSiteRho P.Coefficient H K.obj := by
  sorry

/-- The existing canonical direct-image mate, included in the ambient pro-etale
category with its specified bounded-below compatibility maps. No new direct-image
comparison is chosen. This is the right-adjoint comparison whose left-adjoint
comparison is kappa, namely fixedComparisonPullbackPlus.
Source: Stacks Tags 099R and 0B65; node proof Step 6
(blueprint: lem-pur-bounded-site-exchange-transposes). -/
def boundedExchangeDirectImageComparison (A : Type (u + 1)) [CommRing A]
    {U V : Scheme.{u}} (g : U ⟶ V)
    (L : DerivedCategory.Plus (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    (coherenceBoundedSiteFunctor A V).obj
        ((Etale.rightDerivedLowerStarPlus (ModuleCat.{u + 1} A) g).obj L) ⟶
      (lowerStar (ModuleCat.{u + 1} A) g).rightDerivedFunctor.obj
        ((coherenceBoundedSiteFunctor A U).obj L) :=
  ((comparisonUpperStar (ModuleCat.{u + 1} A) V).mapDerivedCategoryPlusCompatibility).inv.app
      ((Etale.rightDerivedLowerStarPlus (ModuleCat.{u + 1} A) g).obj L) ≫
    DerivedCategory.Plus.ι.map ((fixedComparisonDirectImageMatePlus A g).app L) ≫
    (lowerStar (ModuleCat.{u + 1} A) g).rightDerivedFunctorPlusCompatibility.hom.app
      ((siteComparisonDerivedPullbackPlus U A).obj L) ≫
    (lowerStar (ModuleCat.{u + 1} A) g).rightDerivedFunctor.map
      ((comparisonUpperStar (ModuleCat.{u + 1} A) U).mapDerivedCategoryPlusCompatibility.hom.app L)

/-- The actual forward etale exchange, mated under w^* adjoint to Rw_* and
v^* adjoint to Rv_* on D+. Its component goes from F_f Rw_* to Rv_* F_f'.
Source: node proof Step 6, Stacks Tag 0B65
(blueprint: lem-pur-bounded-site-exchange-transposes). -/
def boundedExchangeEtaleForwardMate (A : Type (u + 1)) [CommRing A] [Finite A]
    {X X' Y Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {w : X' ⟶ X} {v : Y' ⟶ Y} (sq : IsPullback w f' f v)
    (c : Compactification f) :=
  mateEquiv (Etale.derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} A) w)
    (Etale.derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} A) v)
    (TwoSquare.mk _ _ _ _
      (Etale.rightDerivedLowerShriekOfCompactificationPlusBaseChangeMap A sq c))

/-- The independently constructed pro-etale forward exchange, mated under the
ordinary pullback/direct-image adjunctions. Evaluation below is only at a bounded
etale comparison input. These adjunctions exist on the ordinary derived categories;
no ambient exceptional adjunction is used.
Source: node proof Step 6, Stacks Tag 0B65
(blueprint: lem-pur-bounded-site-exchange-transposes). -/
def boundedExchangeProEtaleForwardMate (A : Type (u + 1)) [CommRing A]
    {X X' Y Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {w : X' ⟶ X} {v : Y' ⟶ Y} (sq : IsPullback w f' f v)
    (c : Compactification f) :=
  mateEquiv (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) w)
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) v)
    (TwoSquare.mk _ _ _ _
      (rightDerivedLowerShriekOfCompactificationBaseChangeMap
        (ModuleCat.{u + 1} A) sq c))

/-- Comparison of the actual forward exchange mates on the two different sites.
The left path is C of the etale mate, then the specified v direct-image comparison,
then Rv_* of B_f'. The right path is B_f, then F_f of the specified w direct-image
comparison, then the actual pro-etale mate. The mate constructions themselves use
w^* adjoint to Rw_* and v^* adjoint to Rv_* separately on the two sites.
All etale objects are in D+, including Rw_* L and F_f' L. There is no hypothesis
identifying two squares, no arbitrary adjunction and no assumed comparison equality.

Source: node proof Steps 6--7, Stacks Tag 0B65
(blueprint: lem-pur-bounded-site-exchange-transposes).
Proof: Step 1 of the node, compactSupport_exchange_transport, identifies the actual
forward exchanges through B and kappa_w, kappa_v. Regard that equation as the
identity of two pasted comparison squares. The mates of the kappa squares are
fixedComparisonDirectImageMatePlus by its counit normalization, after including
D+ into the ordinary categories with exactly the compatibility maps used in
boundedExchangeDirectImageComparison. Apply mateEquiv_vcomp to the two pastings;
their common middle square becomes the forward exchange mate on its own site.
The two resulting boundary paths are exactly the displayed equation. The kappa
maps cancel by their inverse laws, giving this orientation of the equation.
For identity, either Cartesian pasting, proper refinement and further compatible
open restriction, use boundedSiteExchangeDiagramComparison on the corresponding
assemblies, then the same two pasting laws mateEquiv_vcomp and mateEquiv_hcomp.
Conjugation inserts the canonical boundary changes, and the identity mate law
handles identities. The exceptional transposes of these same assemblies are
boundedSiteExchangeDiagramTransposes. Thus every use retains its bounded etale
intermediates and no pro-etale exceptional adjunction is extended. -/
theorem boundedSiteExchangeDiagramMates
    (P : WeilConjectures.PurityFiniteSetting.{u})
    {X X' Y Y' : Over (Spec (.of P.field.k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom]
    {f : X ⟶ Y} {f' : X' ⟶ Y'} {w : X' ⟶ X} {v : Y' ⟶ Y}
    [IsSeparated f.left] [LocallyOfFiniteType f.left] [QuasiCompact f.left]
    (sq : IsPullback w.left f'.left f.left v.left) (c : Compactification f.left)
    (L : DerivedCategory.Plus (Sheaf X'.left.smallEtaleTopology
      (ModuleCat.{u + 1} P.Coefficient))) :
    (coherenceBoundedSiteFunctor P.Coefficient Y.left).map
        ((boundedExchangeEtaleForwardMate P.Coefficient sq c).app L) ≫
      boundedExchangeDirectImageComparison P.Coefficient v.left
        ((coherenceEtaleFunctor P.Coefficient (c.ofIsPullback sq)).obj L) ≫
      (lowerStar (ModuleCat.{u + 1} P.Coefficient) v.left).rightDerivedFunctor.map
        (coherenceBoundaryComponent P.Coefficient (c.ofIsPullback sq) L).hom =
    (coherenceBoundaryComponent P.Coefficient c
        ((Etale.rightDerivedLowerStarPlus
          (ModuleCat.{u + 1} P.Coefficient) w.left).obj L)).hom ≫
      (coherenceProEtaleFunctor P.Coefficient c).map
        (boundedExchangeDirectImageComparison P.Coefficient w.left L) ≫
      (boundedExchangeProEtaleForwardMate P.Coefficient sq c).app
        ((coherenceBoundedSiteFunctor P.Coefficient X'.left).obj L) := by
  sorry

/-- The constant-input specialization is the named dualizing base-change arrow.
The displayed equation fixes the actual inverse-exchange/counit composite, and the
last factor is the canonical v^* A_Y to A_Y' identification. Combined with
boundedSiteExchangeTransposes this identifies exactly finiteComparedBaseChangeClause.
Source: def-pur-co-smoothness, clause 3; node proof Step 5
(blueprint: lem-pur-bounded-site-exchange-transposes).
Proof: the defining mate of rightDerivedUpperShriekBaseChangeMap is the inverse
compact-support exchange. The component formula mateEquiv_counit says its adjunct
is precisely inverse exchange followed by pullback of the counit. The assumed
normalization and invertibility of exchange identify qe with this composite.
Postcompose the adjunct by the image of leftDerivedUpperStarUnitIso, as in the
definition of dualizingComplexBaseChangeMap. The bounded transpose comparison
then carries this named arrow, with its constant-unit identifications, to the
pro-etale counit transpose used by finiteComparedBaseChangeClause. -/
theorem boundedExchangeDualizingNormalization
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X X' Y Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {w : X' ⟶ X} {v : Y' ⟶ Y}
    [HasCompactification f] [HasCompactification f'] [QuasiCompact f']
    (sq : IsPullback w f' f v)
    (qe : (Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A) f').obj
        ((Etale.upperStar (ModuleCat.{u + 1} A) w).leftDerivedFunctor.obj
          (Etale.dualizingComplex (ModuleCat.{u + 1} A) f)) ⟶
      (Etale.upperStar (ModuleCat.{u + 1} A) v).leftDerivedFunctor.obj (𝟙_ _))
    (_hqe : (Etale.rightDerivedLowerShriekBaseChangeMap A sq).app
        (Etale.dualizingComplex (ModuleCat.{u + 1} A) f) ≫ qe =
      (Etale.upperStar (ModuleCat.{u + 1} A) v).leftDerivedFunctor.map
        ((Etale.rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} A) f).counit.app
          (𝟙_ _))) :
    ((Etale.rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} A) f').homEquiv _ _) qe ≫
      (Etale.rightDerivedUpperShriek (ModuleCat.{u + 1} A) f').map
        (Etale.leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} A) v).hom =
      Etale.dualizingComplexBaseChangeMap A sq := by
  sorry

end AlgebraicGeometry.ProEtale
