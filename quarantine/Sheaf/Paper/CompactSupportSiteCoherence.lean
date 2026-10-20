/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q18
-/
module

public import Sheaf.Paper.PurityFiniteSetting
public import Sheaf.Paper.RefinementComparisonIsomorphism
public import Sheaf.Paper.CanonicalOriginCompactSupportComposition
public import Sheaf.Paper.CompactSupportExchangeTransport
import Sheaf.AlgebraicGeometry.CompactSupportFiniteTorsion
import Sheaf.AlgebraicGeometry.CompactifiableCompatibleTower
import Sheaf.AlgebraicGeometry.Etale.DerivedExtensionZeroBaseChange
import Sheaf.AlgebraicGeometry.Etale.OpenImmersionLowerShriekCoherence
import Sheaf.AlgebraicGeometry.EtaleCompactSupportComparisons
import Sheaf.AlgebraicGeometry.ExchangeForgetCoefficients
import Sheaf.AlgebraicGeometry.FiniteConstantCoefficientTransport
import Sheaf.AlgebraicGeometry.FixedComparisonDirectImageMate
import Sheaf.AlgebraicGeometry.ProEtaleDerivedExtensionZeroBaseChange
import Sheaf.AlgebraicGeometry.ProEtaleExtensionZeroComparison
import Sheaf.AlgebraicGeometry.ProperOpenComparisonSiteNormalization
import Sheaf.AlgebraicGeometry.ProperOpenInterchangeCoherence
import Sheaf.AlgebraicGeometry.SfIntrinsicCompactSupport
import Sheaf.AlgebraicGeometry.StrictTowerProperOpenCalculus
import Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence
import Sheaf.CategoryTheory.Adjunction.CoefficientExchange
import Sheaf.Paper.ComparisonPullbackExact
import WeilConjectures.Compactification.BaseChange
import WeilConjectures.Compactification.Refinement
public import WeilConjectures.Compactification.RefinementCategory
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekPlusBaseChange
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.BaseChangeSquare

/-! # Compact-support site coherence

Source: Stacks Project, Tags 0F7C, 0F7D and 0F7F; the agent-formulated normalized
site-coherence calculation in the DAG (blueprint: lem-pur-compact-support-site-coherence).

The diagram generators are the recorded refinement, composition and open-restriction
maps on both sites. A diagram may contain identity edges, composites, and whiskering
by compact support or inverse image, and insertion of compatible boundary isomorphisms.
Its two boundary maps are constructed independently;
commutativity is the theorem, never a field of a generator.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale

/-- Finiteness of the existing positive-level coefficient, without a new coefficient ring.
Source: def-pur-conventions, A = O_E/(varpi_E^n), n positive
(blueprint: lem-pur-compact-support-site-coherence). -/
instance compactSupportCoherenceCoefficientFinite (P : WeilConjectures.PurityFiniteSetting.{u}) :
    Finite P.Coefficient :=
  letI : Finite P.Ring :=
    Padic.finite_coefficientExtensionRing P.coefficients.l P.extension P.level P.level_pos
  Finite.of_equiv P.Ring Equiv.ulift.symm

variable (A : Type (u + 1)) [CommRing A] [Finite A]

/-- The etale compositor evaluated using precisely the three supplied compactifications.
Source: Stacks 0F7J; lem-amb-etale-compact-comparisons
(blueprint: lem-pur-compact-support-site-coherence). -/
def coherenceEtaleCompositor {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    [QuasiCompact f] [QuasiCompact g]
    (c : Compactification f) (d : Compactification g) (e : Compactification (f ≫ g)) :
    Etale.rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} A) c ⋙
        Etale.rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} A) d ≅
      Etale.rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} A) e :=
  letI := c.hasCompactification
  letI := d.hasCompactification
  letI := e.hasCompactification
  Functor.isoWhiskerRight
      (Etale.rightDerivedLowerShriekOfCompactificationPlusIso A c
        (HasCompactification.compactification f))
      (Etale.rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} A) d) ≪≫
    Functor.isoWhiskerLeft (Etale.rightDerivedLowerShriekPlus (ModuleCat.{u + 1} A) f)
      (Etale.rightDerivedLowerShriekOfCompactificationPlusIso A d
        (HasCompactification.compactification g)) ≪≫
    Etale.rightDerivedLowerShriekPlusCompIso A f g ≪≫
    Etale.rightDerivedLowerShriekOfCompactificationPlusIso A
      (HasCompactification.compactification (f ≫ g)) e

/-- The canonical c-to-d comparison, through the specified common refinement. Each leg
is the actual proper-composition/inverse-proper-open construction, not a site conjugate.
Source: prop-compactification-coherence-detailed, common-refinement comparison; node step 6
(blueprint: lem-pur-compact-support-site-coherence). -/
def coherenceCompactificationChange {X Y : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f]
    (c d : Compactification f)
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :=
  (properTransportRefinement A (Compactification.infFst c d) L).symm ≪≫
    properTransportRefinement A (Compactification.infSnd c d) L

/-- The recorded pro-etale alpha, evaluated on the identity etale-origin witness.
Its compactifications are the same c, d, e as in the etale compositor.
Source: thm-sf-comp-composition, normalized compatible-tower construction
(blueprint: lem-pur-compact-support-site-coherence). -/
def coherenceProEtaleCompositor {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    [QuasiCompact f] [QuasiCompact g]
    (c : Compactification f) (d : Compactification g) (e : Compactification (f ≫ g))
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) d).obj
        ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).obj
          ((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.obj L.obj)) ⟶
      (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) e).obj
        ((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.obj L.obj) :=
  letI := c.hasCompactification
  letI := d.hasCompactification
  letI := e.hasCompactification
  let cf := HasCompactification.compactification f
  let dg := HasCompactification.compactification g
  let egf := HasCompactification.compactification (f ≫ g)
  let Fd := rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) d
  let Fdg := rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) dg
  let Bf := (compactExchangeTransportComparison A cf).app L
  (Fd.mapIso (coherenceCompactificationChange A c cf L) ≪≫
    Fd.mapIso Bf.symm ≪≫
    coherenceCompactificationChange A d dg
      ((Etale.rightDerivedLowerShriekPlus (ModuleCat.{u + 1} A) f).obj L) ≪≫
    Fdg.mapIso Bf ≪≫
    (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) Z).ι.mapIso
      ((originComposition A f g).app
        ((comparisonUpperStarPlusEtaleOrigin (ModuleCat.{u + 1} A) X).obj L)) ≪≫
    coherenceCompactificationChange A egf e L).hom

/-- The source boundary of the composition square is B_g followed by F_g^p(B_f).
Only canonical bounded-below inclusions are inserted.
Source: the displayed composition equation of the node, proof step 5
(blueprint: lem-pur-compact-support-site-coherence). -/
def coherenceCompositionSource {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    (c : Compactification f) (d : Compactification g)
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :=
  (compactExchangeTransportComparison A d).app
      ((Etale.rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} A) c).obj L) ≪≫
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) d).mapIso
      ((compactExchangeTransportComparison A c).app L)

/-- A boundary comparison C_T(E) to M. This records the endpoints of the site-coherence
squares, including whiskered endpoints; it does not assert that any square commutes.
Source: node proof step 10, boundaries B_in and B_out of a pasted diagram
(blueprint: lem-pur-compact-support-site-coherence). -/
structure CompactSupportSiteBoundary (T : Scheme.{u}) where
  etale : DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))
  proEtale : _root_.DerivedCategory
    (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A))
  comparison :
    (comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory.obj etale.obj ≅ proEtale

/-- The boundary B_f^c = Rp_*(e_j) beta_p at L, in the ambient target category.
Source: node's defining equation for B, and proof step 2
(blueprint: lem-pur-compact-support-site-coherence). -/
def coherenceCompactificationBoundary {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f)
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    CompactSupportSiteBoundary A Y where
  etale := (Etale.rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} A) c).obj L
  proEtale := (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).obj
    ((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.obj L.obj)
  comparison := (compactExchangeTransportComparison A c).app L

/-- The boundary (F_g^p B_f)(B_g F_f^e) of the composition equation.
Source: node's second displayed coherence equation, proof step 5
(blueprint: lem-pur-compact-support-site-coherence). -/
def coherenceCompositionBoundary {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    (c : Compactification f) (d : Compactification g)
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    CompactSupportSiteBoundary A Z where
  etale := (Etale.rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} A) d).obj
    ((Etale.rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} A) c).obj L)
  proEtale := (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) d).obj
    ((coherenceCompactificationBoundary A c L).proEtale)
  comparison := coherenceCompositionSource A c d L

/-- The source boundary v_p^*(B_f), with the canonical inverse-image comparison a_v.
Source: node's open-restriction equation, proof steps 7--9
(blueprint: lem-pur-compact-support-site-coherence). -/
def coherenceRestrictionSource {X Y Y' : Scheme.{u}} {f : X ⟶ Y}
    (v : Y' ⟶ Y) (c : Compactification f)
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    CompactSupportSiteBoundary A Y' where
  etale := (Etale.upperStar (ModuleCat.{u + 1} A) v).mapDerivedCategoryPlus.obj
    ((coherenceCompactificationBoundary A c L).etale)
  proEtale := (upperStar (ModuleCat.{u + 1} A) v).leftDerivedFunctor.obj
    ((coherenceCompactificationBoundary A c L).proEtale)
  comparison := (compactExchangeTransportSource A v c).app L

/-- The target boundary B_f' followed by F_f'^p(a_u), for the pulled-back compactification.
Source: def-cbc-compact-support-square and the node's open-restriction equation, step 9
(blueprint: lem-pur-compact-support-site-coherence). -/
def coherenceRestrictionTarget {X X' Y Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {u' : X' ⟶ X} {v : Y' ⟶ Y} (sq : IsPullback u' f' f v) (c : Compactification f)
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    CompactSupportSiteBoundary A Y' where
  etale := (Etale.rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} A)
    (c.ofIsPullback sq)).obj
      ((Etale.upperStar (ModuleCat.{u + 1} A) u').mapDerivedCategoryPlus.obj L)
  proEtale := (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A)
    (c.ofIsPullback sq)).obj
      ((upperStar (ModuleCat.{u + 1} A) u').leftDerivedFunctor.obj
        ((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.obj L.obj))
  comparison := (compactExchangeTransportTarget A sq c).app L

/-- Whisker a boundary by the chosen compact-support pair, using its named B comparison.
Source: node proof step 10, horizontal pasting and naturality of B
(blueprint: lem-pur-compact-support-site-coherence). -/
def coherencePushBoundary {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (b : CompactSupportSiteBoundary A X) : CompactSupportSiteBoundary A Y where
  etale := (Etale.rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} A) c).obj
    b.etale
  proEtale := (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).obj b.proEtale
  comparison := (compactExchangeTransportComparison A c).app b.etale ≪≫
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).mapIso b.comparison

/-- Whisker a boundary by inverse image, inserting the canonical comparison a_v.
Source: lem-weil-pbc-comparison-pullback and node proof steps 1 and 10
(blueprint: lem-pur-compact-support-site-coherence). -/
def coherencePullBoundary {X Y : Scheme.{u}} (v : X ⟶ Y)
    (b : CompactSupportSiteBoundary A Y) : CompactSupportSiteBoundary A X where
  etale := (Etale.upperStar (ModuleCat.{u + 1} A) v).mapDerivedCategoryPlus.obj b.etale
  proEtale := (upperStar (ModuleCat.{u + 1} A) v).leftDerivedFunctor.obj b.proEtale
  comparison := (leftDerivedUpperStarComparisonIso v A).app b.etale ≪≫
    (upperStar (ModuleCat.{u + 1} A) v).leftDerivedFunctor.mapIso b.comparison

/-- Formal finite diagrams in the three named compactification comparisons. No constructor
assumes its site-comparison square. Identity, concatenation, and whiskering explicitly
include identity diagrams and horizontal, vertical and mixed pasting. The geometric
vertices of generators are finite-type k-schemes, with no separatedness of their structure
maps. Over morphisms retain compatibility with k. The change constructor inserts compatible
boundary identifications (associators, pullback comparisons, or an etale-origin witness);
its two hypotheses concern only these endpoint isomorphisms, never a generator square.
Source: node's three displayed equations and final sentence; proof steps 4--10
(blueprint: lem-pur-compact-support-site-coherence). -/
inductive CompactSupportSiteDiagram (P : WeilConjectures.PurityFiniteSetting.{u}) :
    {T : Scheme.{u}} → CompactSupportSiteBoundary P.Coefficient T →
      CompactSupportSiteBoundary P.Coefficient T → Type (u + 2)
  | refinement {X Y : Over (Spec (.of P.field.k))}
      [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
      [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
      {f : X ⟶ Y} [IsSeparated f.left] [LocallyOfFiniteType f.left] [QuasiCompact f.left]
      {c d : Compactification f.left} (r : c.Refinement d)
      (L : DerivedCategory.Plus (Sheaf X.left.smallEtaleTopology
        (ModuleCat.{u + 1} P.Coefficient))) :
      CompactSupportSiteDiagram P (coherenceCompactificationBoundary P.Coefficient c L)
        (coherenceCompactificationBoundary P.Coefficient d L)
  | composition {X Y Z : Over (Spec (.of P.field.k))}
      [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
      [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
      [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]
      {f : X ⟶ Y} {g : Y ⟶ Z}
      [IsSeparated f.left] [LocallyOfFiniteType f.left] [QuasiCompact f.left]
      [IsSeparated g.left] [LocallyOfFiniteType g.left] [QuasiCompact g.left]
      (c : Compactification f.left) (d : Compactification g.left)
      (e : Compactification (f.left ≫ g.left))
      (L : DerivedCategory.Plus (Sheaf X.left.smallEtaleTopology
        (ModuleCat.{u + 1} P.Coefficient))) :
      CompactSupportSiteDiagram P (coherenceCompositionBoundary P.Coefficient c d L)
        (coherenceCompactificationBoundary P.Coefficient e L)
  | restriction {X X' Y Y' : Over (Spec (.of P.field.k))}
      [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
      [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
      [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
      [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom]
      {f : X ⟶ Y} {f' : X' ⟶ Y'} {u' : X' ⟶ X} {v : Y' ⟶ Y}
      [IsSeparated f.left] [LocallyOfFiniteType f.left] [QuasiCompact f.left]
      [IsOpenImmersion v.left]
      (sq : IsPullback u'.left f'.left f.left v.left) (c : Compactification f.left)
      (L : DerivedCategory.Plus (Sheaf X.left.smallEtaleTopology
        (ModuleCat.{u + 1} P.Coefficient))) :
      CompactSupportSiteDiagram P (coherenceRestrictionSource P.Coefficient v.left c L)
        (coherenceRestrictionTarget P.Coefficient sq c L)
  | identity {T : Scheme.{u}} (b : CompactSupportSiteBoundary P.Coefficient T) :
      CompactSupportSiteDiagram P b b
  | comp {T : Scheme.{u}} {b₀ b₁ b₂ : CompactSupportSiteBoundary P.Coefficient T}
      (D : CompactSupportSiteDiagram P b₀ b₁) (E : CompactSupportSiteDiagram P b₁ b₂) :
      CompactSupportSiteDiagram P b₀ b₂
  | push {X Y : Over (Spec (.of P.field.k))}
      [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
      [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
      {f : X ⟶ Y} [IsSeparated f.left] [LocallyOfFiniteType f.left] [QuasiCompact f.left]
      (c : Compactification f.left) {b₀ b₁ : CompactSupportSiteBoundary P.Coefficient X.left}
      (D : CompactSupportSiteDiagram P b₀ b₁) :
      CompactSupportSiteDiagram P (coherencePushBoundary P.Coefficient c b₀)
        (coherencePushBoundary P.Coefficient c b₁)
  | pull {X Y : Over (Spec (.of P.field.k))}
      [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
      [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
      (v : X ⟶ Y) [IsOpenImmersion v.left]
      {b₀ b₁ : CompactSupportSiteBoundary P.Coefficient Y.left}
      (D : CompactSupportSiteDiagram P b₀ b₁) :
      CompactSupportSiteDiagram P (coherencePullBoundary P.Coefficient v.left b₀)
        (coherencePullBoundary P.Coefficient v.left b₁)
  | change {T : Scheme.{u}}
      {b₀ b₁ c₀ c₁ : CompactSupportSiteBoundary P.Coefficient T}
      (e₀ : b₀.etale ≅ c₀.etale) (e₁ : b₁.etale ≅ c₁.etale)
      (p₀ : b₀.proEtale ≅ c₀.proEtale) (p₁ : b₁.proEtale ≅ c₁.proEtale)
      (h₀ : (comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) T).mapDerivedCategory.map
          (DerivedCategory.Plus.ι.map e₀.hom) ≫ c₀.comparison.hom =
        b₀.comparison.hom ≫ p₀.hom)
      (h₁ : (comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) T).mapDerivedCategory.map
          (DerivedCategory.Plus.ι.map e₁.hom) ≫ c₁.comparison.hom =
        b₁.comparison.hom ≫ p₁.hom)
      (D : CompactSupportSiteDiagram P b₀ b₁) : CompactSupportSiteDiagram P c₀ c₁

/-- The etale boundary composite, constructed solely with the recorded etale maps.
The refinement uses the inverse of the upstream comparison because its upstream direction
is d to c, whereas the node's rho is c to d.
Source: lem-amb-etale-compact-comparisons, def-cbc-exchange-map, and node proof step 10
(blueprint: lem-pur-compact-support-site-coherence). -/
def CompactSupportSiteDiagram.etaleMap {P : WeilConjectures.PurityFiniteSetting.{u}}
    {T : Scheme.{u}} {b₀ b₁ : CompactSupportSiteBoundary P.Coefficient T}
    (D : CompactSupportSiteDiagram P b₀ b₁) : b₀.etale ⟶ b₁.etale :=
  match D with
  | @CompactSupportSiteDiagram.refinement .(P) _ _ _ _ _ _ _ _ _ _ _ _ r L =>
      (Etale.rightDerivedLowerShriekOfCompactificationPlusRefinementIso P.Coefficient r).inv.app L
  | @CompactSupportSiteDiagram.composition .(P) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ c d e L =>
      (coherenceEtaleCompositor P.Coefficient c d e).hom.app L
  | @CompactSupportSiteDiagram.restriction .(P) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ sq c L =>
      (Etale.rightDerivedLowerShriekOfCompactificationPlusBaseChangeMap P.Coefficient sq c).app L
  | @CompactSupportSiteDiagram.identity .(P) _ b => 𝟙 b.etale
  | @CompactSupportSiteDiagram.comp .(P) _ _ _ _ D E => D.etaleMap ≫ E.etaleMap
  | @CompactSupportSiteDiagram.push .(P) _ _ _ _ _ _ _ _ _ _ c _ _ D =>
      (Etale.rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} P.Coefficient)
        c).map D.etaleMap
  | @CompactSupportSiteDiagram.pull .(P) _ _ _ _ _ _ v _ _ _ D =>
      (Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) v.left).mapDerivedCategoryPlus.map
        D.etaleMap
  | @CompactSupportSiteDiagram.change .(P) _ _ _ _ _ e₀ e₁ _ _ _ _ D =>
      e₀.inv ≫ D.etaleMap ≫ e₁.hom

/-- The pro-etale boundary composite. In particular rho is properTransportRefinement,
alpha is originComposition, and Ex is the ambient proper-mate/open exchange for the
pulled-back compactification. None is defined by conjugating its etale counterpart here.
Source: def-sf-refinement-comparison-isomorphism, thm-sf-comp-composition,
def-cbc-exchange-map and node proof step 10
(blueprint: lem-pur-compact-support-site-coherence). -/
def CompactSupportSiteDiagram.proEtaleMap {P : WeilConjectures.PurityFiniteSetting.{u}}
    {T : Scheme.{u}} {b₀ b₁ : CompactSupportSiteBoundary P.Coefficient T}
    (D : CompactSupportSiteDiagram P b₀ b₁) : b₀.proEtale ⟶ b₁.proEtale :=
  match D with
  | @CompactSupportSiteDiagram.refinement .(P) _ _ _ _ _ _ _ _ _ _ _ _ r L =>
      (properTransportRefinement P.Coefficient r L).hom
  | @CompactSupportSiteDiagram.composition .(P) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ c d e L =>
      coherenceProEtaleCompositor P.Coefficient c d e L
  | @CompactSupportSiteDiagram.restriction .(P) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ sq c L =>
      (rightDerivedLowerShriekOfCompactificationBaseChangeMap
        (ModuleCat.{u + 1} P.Coefficient) sq c).app
          ((comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) _).mapDerivedCategory.obj L.obj)
  | @CompactSupportSiteDiagram.identity .(P) _ b => 𝟙 b.proEtale
  | @CompactSupportSiteDiagram.comp .(P) _ _ _ _ D E => D.proEtaleMap ≫ E.proEtaleMap
  | @CompactSupportSiteDiagram.push .(P) _ _ _ _ _ _ _ _ _ _ c _ _ D =>
      (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} P.Coefficient) c).map
        D.proEtaleMap
  | @CompactSupportSiteDiagram.pull .(P) _ _ _ _ _ _ v _ _ _ D =>
      (upperStar (ModuleCat.{u + 1} P.Coefficient) v.left).leftDerivedFunctor.map D.proEtaleMap
  | @CompactSupportSiteDiagram.change .(P) _ _ _ _ _ _ _ p₀ p₁ _ _ D =>
      p₀.inv ≫ D.proEtaleMap ≫ p₁.hom

/-- Compact-support site coherence on bounded-below etale witnesses, including identities
and arbitrary finite pasting. For a generator the last equation is exactly the corresponding
one of the three displayed equations of the node, with the canonical pullback and inclusion
comparisons made explicit in its boundaries. The final clause transports equal etale routes
to equal pro-etale routes; in particular it includes identity normalization and all pasting.
Source: Stacks Project, Tags 0F7C, 0F7D, 0F7F, and the additional normalized pro-etale
proper/open calculus specified by the node (blueprint: lem-pur-compact-support-site-coherence).

Proof plan, following every step of the DAG proof:
1. Finite-type k-schemes are Noetherian, including all proper compactification ambients.
Every open in the towers is therefore quasi-compact. Exact comparison, open extension and
inverse image preserve bounded-below inputs (lem-sf-comparison-pullback-exact,
lem-weil-pbc-finite-type-over-noetherian, lem-weil-pbc-noetherian-open-subscheme-noetherian).
2. Expand B as the canonical direct-image counit mate followed by Rp_*(e_j). Both factors
are invertible (lem-weil-pbc-comparison-direct-image-canonical-mate and
lem-cbc-proetale-extension-zero-comparison). Mate pasting composes the proper factors;
the open comparison's composition law composes the open factors.
3. Specialize lem-cbc-strict-tower-proper-open-calculus to the constant finite A tower.
Its finite-evaluation normalization gives equation (N) for the actual pro-etale proper/open
map, including non-Cartesian commutative proper/open squares. Use the identity scalar
transport of def-cbc-finite-constant-coefficient-transport. This is not an appeal to
faithfulness of evaluation.
4. For r : c to d, use the inverse proper/open arrow pushed by d.g, after the proper
compositor: precisely properTransportRefinement. Apply (N) to the refinement square,
multiply by its inverse, and apply Rp_*. Naturality and proper-mate composition give
B_d C(rho_e) = rho_p B_c, with rho_e the inverse of the upstream d-to-c comparison.
5. In a compatible composition tower, alpha is the proper/open interchange whiskered
by the exterior proper and open factors. Apply (N) to the middle square and use proper
and open composition. The two boundaries are B_gf C(alpha_e) and alpha_p F_g(B_f) B_g.
6. Pass between compatible towers using a common refining tower. Apply (N) also to the
non-Cartesian intermediate squares and use actual pro-etale horizontal/vertical pasting.
The refinement equation cancels the intermediate comparisons. Thus the recorded canonical
originComposition is the alpha in the displayed equation, for every chosen c, d, e.
7. For an open pullback use c.ofIsPullback sq. The coefficient-exchange-mates theorem,
with the counit normalization of beta and the canonical pullback comparison cube, gives
(P), identifying the specified proper exchanges on the two sites.
8. Transpose the inverses of the open base-change and site/open comparisons under the
open adjunctions. Both resulting unit composites agree by pullback-square coherence;
mate pasting gives (O), the comparison of the specified open exchange factors.
9. Expand Ex as proper exchange followed by Rp'_*(open exchange). Naturality, (P), and
(O) give Ex_p v_p^*(B_f) = B_f' C(Ex_e), with a_v and a_u inserted. The etale exchange is
invertible by thm-cbc-finite-torsion. Both boundaries are invertible, so this equation
makes the actual Ex_p invertible at C_X L, without asserting it on arbitrary inputs.
10. Induct on the diagram. Steps 4, 6 and 9 handle its three generators. Identity and
concatenation use functoriality and substitution t2_p t1_p B = B C(t2_e t1_e).
For push and pull use naturality of B and of the canonical pullback comparison. For change,
conjugate the induction equation by the compatible endpoint isomorphisms. This
proves horizontal as well as vertical and mixed pasting. For two routes with the same
etale map, their squares have identical boundaries; cancel the invertible source B.
The recorded etale identity, refinement-transitivity, composition-associativity and
exchange-pasting laws therefore give the respective pro-etale laws. -/
theorem compactSupportSiteCoherence (P : WeilConjectures.PurityFiniteSetting.{u}) :
    (∀ {X Y : Over (Spec (.of P.field.k))}
      [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
      [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
      (f : X ⟶ Y) [IsSeparated f.left] [LocallyOfFiniteType f.left] [QuasiCompact f.left]
      (c : Compactification f.left)
      (L : DerivedCategory.Plus (Sheaf X.left.smallEtaleTopology
        (ModuleCat.{u + 1} P.Coefficient))),
      IsIso ((compactSupportSiteComparisonPlus P.Coefficient c).hom.app L)) ∧
    (∀ {X X' Y Y' : Over (Spec (.of P.field.k))}
      [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
      [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
      [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
      [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom]
      {f : X ⟶ Y} {f' : X' ⟶ Y'} {u' : X' ⟶ X} {v : Y' ⟶ Y}
      [IsSeparated f.left] [LocallyOfFiniteType f.left] [QuasiCompact f.left]
      [IsOpenImmersion v.left]
      (sq : IsPullback u'.left f'.left f.left v.left) (c : Compactification f.left)
      (L : DerivedCategory.Plus (Sheaf X.left.smallEtaleTopology
        (ModuleCat.{u + 1} P.Coefficient))),
      IsIso ((Etale.rightDerivedLowerShriekOfCompactificationPlusBaseChangeMap
        P.Coefficient sq c).app L) ∧
      IsIso ((rightDerivedLowerShriekOfCompactificationBaseChangeMap
        (ModuleCat.{u + 1} P.Coefficient) sq c).app
          ((comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient)
            X.left).mapDerivedCategory.obj L.obj))) ∧
    (∀ {T : Scheme.{u}} {b₀ b₁ : CompactSupportSiteBoundary P.Coefficient T}
      (D : CompactSupportSiteDiagram P b₀ b₁),
      (comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) T).mapDerivedCategory.map
          (DerivedCategory.Plus.ι.map D.etaleMap) ≫ b₁.comparison.hom =
        b₀.comparison.hom ≫ D.proEtaleMap) ∧
    (∀ {T : Scheme.{u}} {b₀ b₁ : CompactSupportSiteBoundary P.Coefficient T}
      (D E : CompactSupportSiteDiagram P b₀ b₁),
      D.etaleMap = E.etaleMap → D.proEtaleMap = E.proEtaleMap) := by
  sorry

end AlgebraicGeometry.ProEtale
