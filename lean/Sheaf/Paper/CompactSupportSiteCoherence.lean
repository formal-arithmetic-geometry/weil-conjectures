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
public import WeilConjectures.Compactification.RefinementCategory
import Sheaf.AlgebraicGeometry.ComparisonDirectImage
import Sheaf.AlgebraicGeometry.CompactSupportFiniteTorsion
import Sheaf.AlgebraicGeometry.EtaleCompactSupportComparisons
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison

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
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale

-- Keep the Kan-extension constructions abstract in the compactification calculus.
attribute [local irreducible] Etale.upperStar Etale.lowerStar upperStar lowerStar
  comparisonUpperStar

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

attribute [local irreducible] Functor.leftDerivedFunctor Functor.rightDerivedFunctor
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem coherence_exact_hom
    (A : Type (u + 1)) [CommRing A] (T : Scheme.{u})
    (L : DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    (comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategoryPlusCompatibility.hom.app L =
      𝟙 ((comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory.obj L.obj) := rfl

private theorem coherence_exact_inv
    (A : Type (u + 1)) [CommRing A] (T : Scheme.{u})
    (L : DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    (comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategoryPlusCompatibility.inv.app L =
      𝟙 ((comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory.obj L.obj) := rfl

private theorem coherence_identity_tail
    {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D)
    {X : C} {U V : D} (a : U ⟶ V) (b : V ⟶ F.obj X) :
    𝟙 U ≫ a ≫ b ≫ F.map (𝟙 X) = a ≫ b := by
  rw [F.map_id, Category.id_comp, Category.comp_id]

private theorem coherence_identity_tail_of_eq
    {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D)
    {X : C} {U V : D} (q : U ⟶ U) (p : X ⟶ X)
    (a : U ⟶ V) (b : V ⟶ F.obj X) (hq : q = 𝟙 U) (hp : p = 𝟙 X) :
    q ≫ a ≫ b ≫ F.map p = a ≫ b := by
  rw [hq, hp]
  exact coherence_identity_tail F a b

private theorem coherence_identity_ends
    {C D : Type*} [Category* C] [Category* D] (F G : C ⥤ D)
    {X : C} {U V : D} (a : F.obj X ⟶ U) (b : U ⟶ V) (c : V ⟶ G.obj X) :
    F.map (𝟙 X) ≫ a ≫ b ≫ c ≫ G.map (𝟙 X) = a ≫ b ≫ c := by
  rw [F.map_id, G.map_id, Category.id_comp, Category.comp_id]

private theorem coherence_include_square
    {C D : Type*} [Category* C] [Category* D] (J : C ⥤ D)
    {U V P Q : C} {P' Q' : D}
    (x : U ⟶ V) (a : U ⟶ P) (b : V ⟶ Q) (r : P ⟶ Q)
    (pc : J.obj P ≅ P') (pd : J.obj Q ≅ Q') (h : x ≫ b = a ≫ r) :
    J.map x ≫ (J.map b ≫ pd.hom) =
      (J.map a ≫ pc.hom) ≫ (pc.inv ≫ J.map r ≫ pd.hom) := by
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [← J.map_comp_assoc, h, J.map_comp, Category.assoc]

private theorem coherence_identity_ends_of_eq
    {C D : Type*} [Category* C] [Category* D] (F G : C ⥤ D)
    {X : C} {U V : D} (p q : X ⟶ X)
    (a : F.obj X ⟶ U) (b : U ⟶ V) (c : V ⟶ G.obj X)
    (hp : p = 𝟙 X) (hq : q = 𝟙 X) :
    F.map p ≫ a ≫ b ≫ c ≫ G.map q = a ≫ b ≫ c := by
  rw [hp, hq]
  exact coherence_identity_ends F G a b c

private theorem coherence_map_cancel
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    (F : D ⥤ E) {G H : C ⥤ D} (e : G ≅ H) (X : C)
    {Y : E} (t : F.obj (G.obj X) ⟶ Y) :
    F.map (e.hom.app X) ≫ F.map (e.inv.app X) ≫ t = t := by
  rw [← Functor.map_comp_assoc, Iso.hom_inv_id_app, CategoryTheory.Functor.map_id, Category.id_comp]

private theorem coherence_inverse_square
    {C D : Type*} [Category* C] [Category* D]
    (F : C ⥤ D) {U V : C} (e : U ≅ V) {P Q : D}
    (a : F.obj V ≅ P) (b : F.obj U ≅ Q) (t : P ≅ Q)
    (h : F.map e.hom ≫ a.hom = b.hom ≫ t.inv) :
    F.map e.inv ≫ b.hom = a.hom ≫ t.hom := by
  apply (cancel_mono t.inv).mp
  rw [Category.assoc, ← h, ← Category.assoc, ← F.map_comp]
  simp only [Iso.inv_hom_id, F.map_id, Category.id_comp,
    Category.assoc, Iso.hom_inv_id, Category.comp_id]

private theorem coherence_restriction
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X X' Y Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {u' : X' ⟶ X} {v : Y' ⟶ Y}
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (sq : IsPullback u' f' f v) (c : Compactification f)
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    (comparisonUpperStar (ModuleCat.{u + 1} A) Y').mapDerivedCategory.map
        (DerivedCategory.Plus.ι.map
          ((Etale.rightDerivedLowerShriekOfCompactificationPlusBaseChangeMap A sq c).app L)) ≫
      (coherenceRestrictionTarget A sq c L).comparison.hom =
    (coherenceRestrictionSource A v c L).comparison.hom ≫
      (rightDerivedLowerShriekOfCompactificationBaseChangeMap
        (ModuleCat.{u + 1} A) sq c).app
          ((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.obj L.obj) := by
  with_unfolding_all
    have h := NatTrans.congr_app (compactSupport_exchange_transport A sq c).1 L
    simpa only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Functor.comp_map, Functor.comp_obj, ObjectProperty.ι_obj,
      coherenceRestrictionTarget, coherenceRestrictionSource, Iso.app_hom] using h

private theorem coherence_direct_comp
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U V W : Scheme.{u}} (a : U ⟶ V) (b : V ⟶ W) (q : U ⟶ W)
    [IsProper a] [IsProper b] (h : a ≫ b = q)
    (M : DerivedCategory.Plus (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    (comparisonUpperStar (ModuleCat.{u + 1} A) W).mapDerivedCategoryPlus.map
        (((Etale.derivedPlusFormalism (ModuleCat.{u + 1} A)).pfComp' a b q h).inv.app M) ≫
      (fixedComparisonDirectImageMatePlus A q).app M =
    (fixedComparisonDirectImageMatePlus A b).app
        ((Etale.lowerStar (ModuleCat.{u + 1} A) a).rightDerivedFunctorPlus.obj M) ≫
      (lowerStar (ModuleCat.{u + 1} A) b).rightDerivedFunctorPlus.map
        ((fixedComparisonDirectImageMatePlus A a).app M) ≫
      (proEtaleComparisonDirectImageCompIso A a b).hom.app
        ((comparisonUpperStar (ModuleCat.{u + 1} A) U).mapDerivedCategoryPlus.obj M) ≫
      (eqToIso (congrArg
        (fun t ↦ (lowerStar (ModuleCat.{u + 1} A) t).rightDerivedFunctorPlus) h)).hom.app
        ((comparisonUpperStar (ModuleCat.{u + 1} A) U).mapDerivedCategoryPlus.obj M) := by
  subst q
  simpa only [Etale.derivedPlusFormalism_pfComp'_inv, eqToIso_refl,
    Iso.refl_hom, NatTrans.id_app, Category.comp_id, fixedComparisonDirectImageMatePlus,
    etaleComparisonDirectImageCompIso] using comparisonDirectImagePlus_comp A a b M

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem coherence_refinement_plus
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    {f : X ⟶ Y} [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    {c d : Compactification f} (r : c.Refinement d)
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    (comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategoryPlus.map
        ((Etale.rightDerivedLowerShriekOfCompactificationPlusRefinementIso A r).hom.app L) ≫
      (compactSupportSiteComparisonPlus A c).hom.app L =
    (compactSupportSiteComparisonPlus A d).hom.app L ≫
      (properTransportRefinementPlus A r L).inv := by
  have htProper : IsProper r.hom := inferInstance
  rcases c with ⟨Zc, pc, jc, commc, properc, openc⟩
  rcases r with ⟨t, ht, hg⟩
  change Zc ⟶ d.Z at t
  change jc ≫ t = d.i at ht
  change t ≫ d.g = pc at hg
  change IsProper t at htProper
  subst pc
  let : IsProper t := htProper
  let c : Compactification f := ⟨Zc, t ≫ d.g, jc, commc, properc, openc⟩
  let r : c.Refinement d := ⟨t, ht, rfl⟩
  let N₁ := (comparisonUpperStar (ModuleCat.{u + 1} A) c.Z).mapDerivedCategoryPlus
  let N₂ := (comparisonUpperStar (ModuleCat.{u + 1} A) d.Z).mapDerivedCategoryPlus
  let N := (comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategoryPlus
  let R := (Etale.lowerStar (ModuleCat.{u + 1} A) r.hom).rightDerivedFunctorPlus
  let S := (Etale.lowerStar (ModuleCat.{u + 1} A) d.g).rightDerivedFunctorPlus
  let R' := (lowerStar (ModuleCat.{u + 1} A) r.hom).rightDerivedFunctorPlus
  let S' := (lowerStar (ModuleCat.{u + 1} A) d.g).rightDerivedFunctorPlus
  let H' := (lowerStar (ModuleCat.{u + 1} A) c.g).rightDerivedFunctorPlus
  let M := (Etale.openImmersionLowerShriek
    (ModuleCat.{u + 1} A) c.i).mapDerivedCategoryPlus.obj L
  let P := (Etale.openImmersionLowerShriek
    (ModuleCat.{u + 1} A) d.i).mapDerivedCategoryPlus.obj L
  let B₁ := (openImmersionLowerShriek
    (ModuleCat.{u + 1} A) c.i).mapDerivedCategoryPlus.obj
      ((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategoryPlus.obj L)
  let e₁ := (properOpenSiteExtensionIso A c.i).app L
  let e₂ := (properOpenSiteExtensionIso A d.i).app L
  let a : P ⟶ R.obj M := Etale.properOpenComparison A r.hom c.i d.i r.i_hom L
  let D := (Etale.derivedPlusFormalism (ModuleCat.{u + 1} A)).pfComp'
    r.hom d.g c.g r.hom_g
  let cp := proEtaleComparisonDirectImageCompIso A r.hom d.g
  let β₁ := fixedComparisonDirectImageMatePlus A r.hom
  let β₂ := fixedComparisonDirectImageMatePlus A d.g
  let β := fixedComparisonDirectImageMatePlus A c.g
  have hc : N.map (D.inv.app M) ≫ β.app M =
      β₂.app (R.obj M) ≫ S'.map (β₁.app M) ≫ cp.hom.app (N₁.obj M) := by
    simpa only [eqToIso_refl, Iso.refl_hom, NatTrans.id_app, Category.comp_id] using
      coherence_direct_comp A r.hom d.g c.g r.hom_g M
  have hn : N.map (S.map a) ≫ β₂.app (R.obj M) =
      β₂.app P ≫ S'.map (N₂.map a) := β₂.naturality a
  have hp : cp.hom.app (N₁.obj M) ≫
      (lowerStar (ModuleCat.{u + 1} A) (r.hom ≫ d.g)).rightDerivedFunctorPlus.map e₁.hom =
      S'.map (R'.map e₁.hom) ≫ cp.hom.app B₁ :=
    (cp.hom.naturality e₁.hom).symm
  have hd : S'.map e₂.hom ≫ S'.map e₂.inv = 𝟙 _ := by
    rw [← Functor.map_comp, Iso.hom_inv_id, CategoryTheory.Functor.map_id]
  rw [Etale.etaleCompactSupport_refinementComparison_eq]
  simp only [compactSupportSiteComparisonPlus, properTransportRefinementPlus,
    properOpenProEtaleIsoPlus, Iso.trans_hom, Iso.trans_inv, Iso.symm_inv, Iso.symm_hom,
    Iso.app_hom, Iso.app_inv, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Functor.mapIso_inv,
    Functor.mapIso_hom, asIso_hom, eqToIso_refl, Iso.refl_inv, NatTrans.id_app,
    Category.id_comp, Category.comp_id, Category.assoc]
  change N.map (S.map a ≫ D.inv.app M) ≫ β.app M ≫ H'.map e₁.hom =
    β₂.app P ≫ S'.map e₂.hom ≫
      S'.map (e₂.inv ≫ N₂.map a ≫ β₁.app M ≫ R'.map e₁.hom) ≫
        cp.hom.app B₁
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% hd, reassoc_of% hc, reassoc_of% hn]
  rw [hp]

attribute [local irreducible] compactSupportSiteComparisonPlus
  Functor.mapDerivedCategoryPlusCompatibility
  Etale.rightDerivedLowerShriekOfCompactificationPlusCompatibility
  rightDerivedLowerShriekOfCompactificationPlusCompatibility
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

private theorem coherence_comparison_expand
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    (compactExchangeTransportComparison A c).hom.app L =
      (comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategoryPlusCompatibility.inv.app
          ((Etale.lowerStar (ModuleCat.{u + 1} A) c.g).rightDerivedFunctorPlus.obj
            ((Etale.openImmersionLowerShriek
              (ModuleCat.{u + 1} A) c.i).mapDerivedCategoryPlus.obj L)) ≫
      DerivedCategory.Plus.ι.map ((compactSupportSiteComparisonPlus A c).hom.app L) ≫
      (rightDerivedLowerShriekOfCompactificationPlusCompatibility
        (ModuleCat.{u + 1} A) c).hom.app
          ((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategoryPlus.obj L) ≫
      (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).map
        ((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategoryPlusCompatibility.hom.app
          L) := by
  dsimp only [compactExchangeTransportComparison, compactSupportSiteComparison,
    Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv,
    NatTrans.comp_app, Functor.isoWhiskerLeft_inv,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerRight_inv,
    Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.comp_obj, ObjectProperty.ι_obj]
  simp only [Category.id_comp, Category.comp_id, Category.assoc]
  rw [coherence_map_cancel
    (comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory
    (Etale.rightDerivedLowerShriekOfCompactificationPlusCompatibility
      (ModuleCat.{u + 1} A) c) L]


attribute [local implicit_reducible] Functor.mapDerivedCategoryPlus

private theorem coherence_comparison_hom
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    (compactExchangeTransportComparison A c).hom.app L =
      DerivedCategory.Plus.ι.map ((compactSupportSiteComparisonPlus A c).hom.app L) ≫
        (rightDerivedLowerShriekOfCompactificationPlusCompatibility
          (ModuleCat.{u + 1} A) c).hom.app
            ((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategoryPlus.obj L) := by
  let M := (Etale.lowerStar (ModuleCat.{u + 1} A) c.g).rightDerivedFunctorPlus.obj
    ((Etale.openImmersionLowerShriek
      (ModuleCat.{u + 1} A) c.i).mapDerivedCategoryPlus.obj L)
  refine (coherence_comparison_expand A c L).trans ?_
  exact coherence_identity_tail_of_eq
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c)
    ((comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategoryPlusCompatibility.inv.app
      M)
    ((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategoryPlusCompatibility.hom.app
      L)
    (DerivedCategory.Plus.ι.map ((compactSupportSiteComparisonPlus A c).hom.app L))
    ((rightDerivedLowerShriekOfCompactificationPlusCompatibility
      (ModuleCat.{u + 1} A) c).hom.app
        ((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategoryPlus.obj L))
    (coherence_exact_inv A Y M) (coherence_exact_hom A X L)

attribute [local irreducible] compactExchangeTransportComparison properTransportRefinementPlus

private theorem coherence_refinement_hom
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} {c d : Compactification f}
    (r : c.Refinement d)
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    (properTransportRefinement A r L).hom =
      (rightDerivedLowerShriekOfCompactificationPlusCompatibility
        (ModuleCat.{u + 1} A) c).inv.app
          ((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategoryPlus.obj L) ≫
      DerivedCategory.Plus.ι.map (properTransportRefinementPlus A r L).hom ≫
      (rightDerivedLowerShriekOfCompactificationPlusCompatibility
        (ModuleCat.{u + 1} A) d).hom.app
          ((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategoryPlus.obj L) := by
  dsimp only [properTransportRefinement, Iso.app_hom, Iso.app_inv,
    Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
  exact coherence_identity_ends_of_eq
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c)
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) d)
    ((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategoryPlusCompatibility.inv.app L)
    ((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategoryPlusCompatibility.hom.app L)
    ((rightDerivedLowerShriekOfCompactificationPlusCompatibility
      (ModuleCat.{u + 1} A) c).inv.app
        ((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategoryPlus.obj L))
    (DerivedCategory.Plus.ι.map (properTransportRefinementPlus A r L).hom)
    ((rightDerivedLowerShriekOfCompactificationPlusCompatibility
      (ModuleCat.{u + 1} A) d).hom.app
        ((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategoryPlus.obj L))
    (coherence_exact_inv A X L) (coherence_exact_hom A X L)

attribute [local irreducible] properTransportRefinement

private theorem coherence_refinement
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    {f : X ⟶ Y} [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    {c d : Compactification f} (r : c.Refinement d)
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    (comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory.map
        (DerivedCategory.Plus.ι.map
          ((Etale.rightDerivedLowerShriekOfCompactificationPlusRefinementIso A r).inv.app L)) ≫
      ((compactExchangeTransportComparison A d).app L).hom =
    ((compactExchangeTransportComparison A c).app L).hom ≫
      (properTransportRefinement A r L).hom := by
  have h := coherence_refinement_plus A r L
  have hp :
      (comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategoryPlus.map
          ((Etale.rightDerivedLowerShriekOfCompactificationPlusRefinementIso A r).inv.app L) ≫
        (compactSupportSiteComparisonPlus A d).hom.app L =
      (compactSupportSiteComparisonPlus A c).hom.app L ≫
        (properTransportRefinementPlus A r L).hom := by
    exact coherence_inverse_square
      (comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategoryPlus
      ((Etale.rightDerivedLowerShriekOfCompactificationPlusRefinementIso A r).app L)
      ((compactSupportSiteComparisonPlus A c).app L)
      ((compactSupportSiteComparisonPlus A d).app L)
      (properTransportRefinementPlus A r L) h
  dsimp only [Iso.app_hom]
  rw [coherence_comparison_hom, coherence_comparison_hom, coherence_refinement_hom]
  exact coherence_include_square DerivedCategory.Plus.ι
    ((comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategoryPlus.map
      ((Etale.rightDerivedLowerShriekOfCompactificationPlusRefinementIso A r).inv.app L))
    ((compactSupportSiteComparisonPlus A c).hom.app L)
    ((compactSupportSiteComparisonPlus A d).hom.app L)
    (properTransportRefinementPlus A r L).hom
    ((rightDerivedLowerShriekOfCompactificationPlusCompatibility
      (ModuleCat.{u + 1} A) c).app
        ((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategoryPlus.obj L))
    ((rightDerivedLowerShriekOfCompactificationPlusCompatibility
      (ModuleCat.{u + 1} A) d).app
        ((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategoryPlus.obj L)) hp

private theorem coherence_common_conjugation
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {X Y U : C} {PX PY PU : D} (r : X ≅ U) (s : Y ≅ U) (t : X ≅ Y)
    (a : F.obj X ≅ PX) (b : F.obj Y ≅ PY) (e : F.obj U ≅ PU)
    (ur : PU ≅ PX) (us : PU ≅ PY)
    (hr : ur = e.symm ≪≫ F.mapIso r.symm ≪≫ a)
    (hs : us = e.symm ≪≫ F.mapIso s.symm ≪≫ b)
    (ht : t = r ≪≫ s.symm) :
    ur.symm ≪≫ us = a.symm ≪≫ F.mapIso t ≪≫ b := by
  subst ur us t
  apply Iso.ext
  simp only [Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv,
    Functor.mapIso_hom, Functor.mapIso_inv, Functor.map_comp,
    Category.assoc, Iso.hom_inv_id_assoc]

private theorem coherence_change_iso
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    {f : X ⟶ Y} [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c d : Compactification f)
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    coherenceCompactificationChange A c d L =
      ((compactExchangeTransportComparison A c).app L).symm ≪≫
        (comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory.mapIso
          (DerivedCategory.Plus.ι.mapIso
            ((Etale.rightDerivedLowerShriekOfCompactificationPlusIso A c d).app L)) ≪≫
        (compactExchangeTransportComparison A d).app L := by
  have hr {c d : Compactification f} (r : c.Refinement d) :
      properTransportRefinement A r L =
        ((compactExchangeTransportComparison A c).app L).symm ≪≫
          (comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory.mapIso
            (DerivedCategory.Plus.ι.mapIso
              ((Etale.rightDerivedLowerShriekOfCompactificationPlusRefinementIso A r).symm.app L))
          ≪≫ (compactExchangeTransportComparison A d).app L := by
    apply Iso.ext
    apply (cancel_epi ((compactExchangeTransportComparison A c).app L).hom).mp
    simpa only [Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv,
      Functor.mapIso_hom, Category.assoc, Iso.hom_inv_id_assoc,
      Iso.hom_inv_id_app_assoc] using
      (coherence_refinement A r L).symm
  exact coherence_common_conjugation
    (DerivedCategory.Plus.ι ⋙
      (comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory)
    ((Etale.rightDerivedLowerShriekOfCompactificationPlusRefinementIso A
      (Compactification.infFst c d)).app L)
    ((Etale.rightDerivedLowerShriekOfCompactificationPlusRefinementIso A
      (Compactification.infSnd c d)).app L)
    ((Etale.rightDerivedLowerShriekOfCompactificationPlusIso A c d).app L)
    ((compactExchangeTransportComparison A c).app L)
    ((compactExchangeTransportComparison A d).app L)
    ((compactExchangeTransportComparison A (Compactification.inf c d)).app L)
    _ _ (hr (Compactification.infFst c d)) (hr (Compactification.infSnd c d))
    (congrArg (fun i ↦ i.app L)
      (Etale.rightDerivedLowerShriekOfCompactificationPlusIso_eq_refinementIso A
        (Compactification.infFst c d) (Compactification.infSnd c d)))

attribute [local implicit_reducible] Etale.rightDerivedLowerShriekPlus rightDerivedLowerShriek
  originCompactSupport comparisonUpperStarPlusEtaleOrigin
attribute [local irreducible] originCompositionModel

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem coherence_ff_preimage_app
    {C D E : Type*} [Category C] [Category D] [Category E]
    (J : D ⥤ E) (H : J.FullyFaithful) (F G : C ⥤ D)
    (i : F ⋙ J ≅ G ⋙ J) (X : C) :
    J.map (((H.whiskeringRight C).preimageIso i).hom.app X) = i.hom.app X := by
  have h := (H.whiskeringRight C).map_preimage (X := F) (Y := G) i.hom
  exact NatTrans.congr_app h X

private theorem coherence_equiv_preimage_app
    {C D E : Type*} [Category C] [Category D] [Category E] (e : C ≌ D)
    (F G : D ⥤ E) (i : e.functor ⋙ F ≅ e.functor ⋙ G) (X : C) :
    ((e.congrLeft.fullyFaithfulInverse).preimageIso i).hom.app (e.functor.obj X) =
      i.hom.app X := by
  have h := e.congrLeft.fullyFaithfulInverse.map_preimage (X := F) (Y := G) i.hom
  exact NatTrans.congr_app h X

private theorem coherence_functor_preimage_app
    {C D E : Type*} [Category C] [Category D] [Category E]
    (Φ : C ⥤ D) [Φ.IsEquivalence] (F G : D ⥤ E)
    (i : Φ ⋙ F ≅ Φ ⋙ G) (X : C) :
    ((Φ.asEquivalence.congrLeft.fullyFaithfulInverse).preimageIso i).hom.app (Φ.obj X) =
      i.hom.app X := by
  exact coherence_equiv_preimage_app Φ.asEquivalence F G i X

private theorem coherence_origin_construction
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    [QuasiCompact f] [QuasiCompact g] :
    originComposition A f g =
      ((DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) Z).fullyFaithfulι.whiskeringRight
        (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) X).FullSubcategory).preimageIso
        (X := originCompactSupport A f ⋙ originCompactSupport A g)
        (Y := originCompactSupport A (f ≫ g)) (originCompositionAmbient A f g) := rfl

private theorem coherence_origin_ambient_construction
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    [QuasiCompact f] [QuasiCompact g] :
    originCompositionAmbient A f g =
      (comparisonUpperStarPlusEtaleOrigin (ModuleCat.{u + 1} A)
        X).asEquivalence.congrLeft.fullyFaithfulInverse.preimageIso
        (X := (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) X).ι ⋙
          rightDerivedLowerShriek (ModuleCat.{u + 1} A) f ⋙
            rightDerivedLowerShriek (ModuleCat.{u + 1} A) g)
        (Y := (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) X).ι ⋙
          rightDerivedLowerShriek (ModuleCat.{u + 1} A) (f ≫ g))
        (originCompositionModel A f g) := rfl


private theorem coherence_origin_inclusion
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    [QuasiCompact f] [QuasiCompact g]
    (K : (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) X).FullSubcategory) :
    (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) Z).ι.map
        ((originComposition A f g).hom.app K) =
      (originCompositionAmbient A f g).hom.app K := by
  rw [coherence_origin_construction]
  exact coherence_ff_preimage_app
    (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) Z).ι
    (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) Z).fullyFaithfulι
    (originCompactSupport A f ⋙ originCompactSupport A g)
    (originCompactSupport A (f ≫ g)) (originCompositionAmbient A f g) K

private theorem coherence_origin_ambient_model
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    [QuasiCompact f] [QuasiCompact g]
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    (originCompositionAmbient A f g).hom.app
        ((comparisonUpperStarPlusEtaleOrigin (ModuleCat.{u + 1} A) X).obj L) =
      (originCompositionModel A f g).hom.app L := by
  rw [coherence_origin_ambient_construction]
  exact coherence_functor_preimage_app
    (comparisonUpperStarPlusEtaleOrigin (ModuleCat.{u + 1} A) X)
    ((DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) X).ι ⋙
      rightDerivedLowerShriek (ModuleCat.{u + 1} A) f ⋙
        rightDerivedLowerShriek (ModuleCat.{u + 1} A) g)
    ((DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) X).ι ⋙
      rightDerivedLowerShriek (ModuleCat.{u + 1} A) (f ≫ g))
    (originCompositionModel A f g) L

private theorem coherence_origin_model
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    [QuasiCompact f] [QuasiCompact g]
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) Z).ι.map
        ((originComposition A f g).hom.app
          ((comparisonUpperStarPlusEtaleOrigin (ModuleCat.{u + 1} A) X).obj L)) =
      (originCompositionModel A f g).hom.app L := by
  exact (coherence_origin_inclusion A f g _).trans (coherence_origin_ambient_model A f g L)

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] coherenceCompactificationChange compactSupportSiteComparison

private theorem coherence_trans_hom_app
    {C D : Type*} [Category C] [Category D] {F G H : C ⥤ D}
    (a : F ≅ G) (b : G ≅ H) (X : C) :
    (a ≪≫ b).hom.app X = a.hom.app X ≫ b.hom.app X := rfl

private theorem coherence_trans_inv_app
    {C D : Type*} [Category C] [Category D] {F G H : C ⥤ D}
    (a : F ≅ G) (b : G ≅ H) (X : C) :
    (a ≪≫ b).inv.app X = b.inv.app X ≫ a.inv.app X := rfl

private theorem coherence_whisker_right_hom_app
    {C D E : Type*} [Category C] [Category D] [Category E]
    {F G : C ⥤ D} (a : F ≅ G) (H : D ⥤ E) (X : C) :
    (Functor.isoWhiskerRight a H).hom.app X = H.map (a.hom.app X) := rfl

private theorem coherence_whisker_right_inv_app
    {C D E : Type*} [Category C] [Category D] [Category E]
    {F G : C ⥤ D} (a : F ≅ G) (H : D ⥤ E) (X : C) :
    (Functor.isoWhiskerRight a H).inv.app X = H.map (a.inv.app X) := rfl

private theorem coherence_whisker_left_hom_app
    {C D E : Type*} [Category C] [Category D] [Category E]
    (F : C ⥤ D) {G H : D ⥤ E} (a : G ≅ H) (X : C) :
    (Functor.isoWhiskerLeft F a).hom.app X = a.hom.app (F.obj X) := rfl

private theorem coherence_origin_normalized
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    [QuasiCompact f] [QuasiCompact g]
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    (originCompositionModel A f g).hom.app L =
      (rightDerivedLowerShriek (ModuleCat.{u + 1} A) g).map
          ((compactExchangeTransportComparison A
            (HasCompactification.compactification f)).inv.app L) ≫
        (compactExchangeTransportComparison A
          (HasCompactification.compactification g)).inv.app
            ((Etale.rightDerivedLowerShriekPlus (ModuleCat.{u + 1} A) f).obj L) ≫
        (comparisonUpperStar (ModuleCat.{u + 1} A) Z).mapDerivedCategory.map
          (DerivedCategory.Plus.ι.map
            ((Etale.rightDerivedLowerShriekPlusCompIso A f g).hom.app L)) ≫
        (compactExchangeTransportComparison A
          (HasCompactification.compactification (f ≫ g))).hom.app L := by
  delta originCompositionModel compactExchangeTransportComparison
  simp only [coherence_trans_hom_app, coherence_trans_inv_app, Iso.symm_hom,
    Iso.symm_inv, coherence_whisker_right_hom_app, coherence_whisker_right_inv_app,
    coherence_whisker_left_hom_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Etale.rightDerivedLowerShriekPlusCompatibility, Functor.map_comp, Functor.comp_map,
    Category.assoc, Category.id_comp, Category.comp_id]

private theorem coherence_comparison_naturality
    {C D E F G H : Type*} [Category C] [Category D] [Category E]
    [Category F] [Category G] [Category H]
    (K : C ⥤ D) (I : D ⥤ E) (M : E ⥤ H) (J : C ⥤ F)
    (N : F ⥤ G) (P : G ⥤ H) (b : K ⋙ I ⋙ M ≅ J ⋙ N ⋙ P)
    {X Y : C} (a : X ⟶ Y) :
    M.map (I.map (K.map a)) ≫ b.hom.app Y =
      b.hom.app X ≫ P.map (N.map (J.map a)) := by
  exact b.hom.naturality a

private theorem coherence_object_map_cancel
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {X Y : C} (e : X ≅ Y) {Z : D} (t : F.obj X ⟶ Z) :
    F.map e.hom ≫ F.map e.inv ≫ t = t := by
  rw [← F.map_comp_assoc, e.hom_inv_id, F.map_id, Category.id_comp]

private theorem coherence_composition_calc
    {C D : Type*} [Category C] [Category D] (Fd Fg : C ⥤ D)
    {Uc Uf Mc Mf : C} {Tc Tf Tg Tfg Te Mfg Me : D}
    (Bc : Uc ≅ Mc) (Bf : Uf ≅ Mf)
    (b₀ : Tc ≅ Fd.obj Uc) (b₁ : Tf ≅ Fd.obj Uf)
    (bg : Tg ≅ Fg.obj Uf) (bfg : Tfg ≅ Mfg)
    (p : Uc ⟶ Uf) (n : Tc ⟶ Tf) (a : Tf ⟶ Tg) (b : Tg ⟶ Tfg)
    (c : Tfg ⟶ Te) (z : Te ⟶ Me)
    (hn : n ≫ b₁.hom = b₀.hom ≫ Fd.map p) :
    n ≫ a ≫ b ≫ c ≫ z =
      b₀.hom ≫ Fd.map Bc.hom ≫ Fd.map Bc.inv ≫ Fd.map p ≫
        Fd.map Bf.hom ≫ Fd.map Bf.inv ≫ b₁.inv ≫ a ≫ bg.hom ≫
          Fg.map Bf.hom ≫ Fg.map Bf.inv ≫ bg.inv ≫ b ≫ bfg.hom ≫ bfg.inv ≫ c ≫ z := by
  simp only [coherence_object_map_cancel, Iso.hom_inv_id_assoc]
  rw [← reassoc_of% hn]
  simp only [Iso.hom_inv_id_assoc]

private theorem coherence_composition_wire
    {C D : Type*} [Category C] [Category D] (Fd Fg : C ⥤ D)
    {Uc Uf Mc Mf : C} {Tc Tf Tg Tfg Te Mfg Me : D}
    (Bc : Uc ≅ Mc) (Bf : Uf ≅ Mf)
    (b₀ : Tc ≅ Fd.obj Uc) (b₁ : Tf ≅ Fd.obj Uf)
    (bg : Tg ≅ Fg.obj Uf) (bfg : Tfg ≅ Mfg)
    (C₀ : Mc ≅ Mf) (C₁ : Fd.obj Uf ≅ Fg.obj Uf) (C₂ : Mfg ≅ Me)
    (η : Fg.obj Mf ≅ Mfg)
    (p : Uc ⟶ Uf) (n : Tc ⟶ Tf) (a : Tf ⟶ Tg) (b : Tg ⟶ Tfg)
    (c : Tfg ⟶ Te) (z : Te ⟶ Me) (t : Tc ⟶ Te)
    (h₀ : C₀.hom = Bc.inv ≫ p ≫ Bf.hom)
    (h₁ : C₁.hom = b₁.inv ≫ a ≫ bg.hom)
    (h₂ : C₂.hom = bfg.inv ≫ c ≫ z)
    (hη : η.hom = Fg.map Bf.inv ≫ bg.inv ≫ b ≫ bfg.hom)
    (ht : t = n ≫ a ≫ b ≫ c)
    (hn : n ≫ b₁.hom = b₀.hom ≫ Fd.map p) :
    t ≫ z = (b₀ ≪≫ Fd.mapIso Bc).hom ≫
      (Fd.mapIso C₀ ≪≫ Fd.mapIso Bf.symm ≪≫ C₁ ≪≫ Fg.mapIso Bf ≪≫ η ≪≫ C₂).hom := by
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom]
  rw [h₀, h₁, h₂, hη, ht]
  simp only [Functor.map_comp, Category.assoc]
  exact coherence_composition_calc Fd Fg Bc Bf b₀ b₁ bg bfg p n a b c z hn

private theorem coherence_change_hom
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    {f : X ⟶ Y} [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c d : Compactification f)
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    (coherenceCompactificationChange A c d L).hom =
      (compactExchangeTransportComparison A c).inv.app L ≫
        (comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory.map
          (DerivedCategory.Plus.ι.map
            ((Etale.rightDerivedLowerShriekOfCompactificationPlusIso A c d).hom.app L)) ≫
        (compactExchangeTransportComparison A d).hom.app L := by
  have h := congrArg Iso.hom (coherence_change_iso A c d L)
  simpa only [Iso.trans_hom, Iso.symm_hom, Iso.app_inv, Iso.app_hom,
    Functor.mapIso_hom] using h

private theorem coherence_map_iso_app_hom
    {C D E : Type*} [Category C] [Category D] [Category E]
    {F G : C ⥤ D} (J : D ⥤ E) (a : F ≅ G) (X : C) :
    (J.mapIso (a.app X)).hom = J.map (a.hom.app X) := rfl

private theorem coherence_origin_iso_hom
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    [QuasiCompact f] [QuasiCompact g]
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    ((DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) Z).ι.mapIso
      ((originComposition A f g).app
        ((comparisonUpperStarPlusEtaleOrigin (ModuleCat.{u + 1} A) X).obj L))).hom =
      (rightDerivedLowerShriek (ModuleCat.{u + 1} A) g).map
          ((compactExchangeTransportComparison A
            (HasCompactification.compactification f)).inv.app L) ≫
        (compactExchangeTransportComparison A
          (HasCompactification.compactification g)).inv.app
            ((Etale.rightDerivedLowerShriekPlus (ModuleCat.{u + 1} A) f).obj L) ≫
        (comparisonUpperStar (ModuleCat.{u + 1} A) Z).mapDerivedCategory.map
          (DerivedCategory.Plus.ι.map
            ((Etale.rightDerivedLowerShriekPlusCompIso A f g).hom.app L)) ≫
        (compactExchangeTransportComparison A
          (HasCompactification.compactification (f ≫ g))).hom.app L := by
  exact (coherence_map_iso_app_hom
    (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) Z).ι (originComposition A f g)
    ((comparisonUpperStarPlusEtaleOrigin (ModuleCat.{u + 1} A) X).obj L)).trans
    ((coherence_origin_model A f g L).trans (coherence_origin_normalized A f g L))


private theorem coherence_mapped_compositor
    {C D E F G : Type*} [Category C] [Category D] [Category E]
    [Category F] [Category G] {F₀ F₁ : C ⥤ D} {G₀ G₁ : D ⥤ E}
    {H₀ H₁ : C ⥤ E} (a : F₀ ≅ F₁) (b : G₀ ≅ G₁)
    (c : F₁ ⋙ G₁ ≅ H₀) (d : H₀ ≅ H₁) (I : E ⥤ F) (M : F ⥤ G) (X : C) :
    M.map (I.map ((Functor.isoWhiskerRight a G₀ ≪≫
      Functor.isoWhiskerLeft F₁ b ≪≫ c ≪≫ d).hom.app X)) =
      M.map (I.map (G₀.map (a.hom.app X))) ≫
        M.map (I.map (b.hom.app (F₁.obj X))) ≫
          M.map (I.map (c.hom.app X)) ≫ M.map (I.map (d.hom.app X)) := by
  simp only [coherence_trans_hom_app, coherence_whisker_right_hom_app,
    coherence_whisker_left_hom_app, Functor.map_comp]

private theorem coherence_etale_construction
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    [QuasiCompact f] [QuasiCompact g]
    (c : Compactification f) (d : Compactification g) (e : Compactification (f ≫ g)) :
    coherenceEtaleCompositor A c d e =
      Functor.isoWhiskerRight
        (Etale.rightDerivedLowerShriekOfCompactificationPlusIso A c
          (HasCompactification.compactification f))
        (Etale.rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} A) d) ≪≫
      Functor.isoWhiskerLeft (Etale.rightDerivedLowerShriekPlus (ModuleCat.{u + 1} A) f)
        (Etale.rightDerivedLowerShriekOfCompactificationPlusIso A d
          (HasCompactification.compactification g)) ≪≫
      Etale.rightDerivedLowerShriekPlusCompIso A f g ≪≫
      Etale.rightDerivedLowerShriekOfCompactificationPlusIso A
        (HasCompactification.compactification (f ≫ g)) e := rfl

attribute [local irreducible] Etale.rightDerivedLowerShriekPlusCompIso
  Etale.rightDerivedLowerShriekOfCompactificationPlusIso

private theorem coherence_etale_compositor_hom
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    [QuasiCompact f] [QuasiCompact g]
    (c : Compactification f) (d : Compactification g) (e : Compactification (f ≫ g))
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    (comparisonUpperStar (ModuleCat.{u + 1} A) Z).mapDerivedCategory.map
        (DerivedCategory.Plus.ι.map ((coherenceEtaleCompositor A c d e).hom.app L)) =
      (comparisonUpperStar (ModuleCat.{u + 1} A) Z).mapDerivedCategory.map
          (DerivedCategory.Plus.ι.map
            ((Etale.rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} A) d).map
              ((Etale.rightDerivedLowerShriekOfCompactificationPlusIso A c
                (HasCompactification.compactification f)).hom.app L))) ≫
        (comparisonUpperStar (ModuleCat.{u + 1} A) Z).mapDerivedCategory.map
          (DerivedCategory.Plus.ι.map
            ((Etale.rightDerivedLowerShriekOfCompactificationPlusIso A d
              (HasCompactification.compactification g)).hom.app
                ((Etale.rightDerivedLowerShriekPlus (ModuleCat.{u + 1} A) f).obj L))) ≫
        (comparisonUpperStar (ModuleCat.{u + 1} A) Z).mapDerivedCategory.map
          (DerivedCategory.Plus.ι.map
            ((Etale.rightDerivedLowerShriekPlusCompIso A f g).hom.app L)) ≫
        (comparisonUpperStar (ModuleCat.{u + 1} A) Z).mapDerivedCategory.map
          (DerivedCategory.Plus.ι.map
            ((Etale.rightDerivedLowerShriekOfCompactificationPlusIso A
              (HasCompactification.compactification (f ≫ g)) e).hom.app L)) := by
  have h := congrArg
    (fun a ↦ (comparisonUpperStar (ModuleCat.{u + 1} A) Z).mapDerivedCategory.map
      (DerivedCategory.Plus.ι.map (a.hom.app L))) (coherence_etale_construction A c d e)
  exact h.trans (coherence_mapped_compositor
    (F₁ := Etale.rightDerivedLowerShriekPlus (ModuleCat.{u + 1} A) f)
    (G₁ := Etale.rightDerivedLowerShriekPlus (ModuleCat.{u + 1} A) g)
    (Etale.rightDerivedLowerShriekOfCompactificationPlusIso A c
      (HasCompactification.compactification f))
    (Etale.rightDerivedLowerShriekOfCompactificationPlusIso A d
      (HasCompactification.compactification g))
    (Etale.rightDerivedLowerShriekPlusCompIso A f g)
    (Etale.rightDerivedLowerShriekOfCompactificationPlusIso A
      (HasCompactification.compactification (f ≫ g)) e)
    DerivedCategory.Plus.ι
    (comparisonUpperStar (ModuleCat.{u + 1} A) Z).mapDerivedCategory L)

private theorem coherence_composition
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y] [IsNoetherian Z]
    {f : X ⟶ Y} {g : Y ⟶ Z}
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    (c : Compactification f) (d : Compactification g) (e : Compactification (f ≫ g))
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    (comparisonUpperStar (ModuleCat.{u + 1} A) Z).mapDerivedCategory.map
        (DerivedCategory.Plus.ι.map ((coherenceEtaleCompositor A c d e).hom.app L)) ≫
      ((compactExchangeTransportComparison A e).app L).hom =
    (coherenceCompositionSource A c d L).hom ≫
      coherenceProEtaleCompositor A c d e L := by
  let := c.hasCompactification
  let := d.hasCompactification
  let := e.hasCompactification
  let cf := HasCompactification.compactification f
  let dg := HasCompactification.compactification g
  let egf := HasCompactification.compactification (f ≫ g)
  let Fd := rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) d
  let Fg := rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) dg
  let CY := (comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory
  let CZ := (comparisonUpperStar (ModuleCat.{u + 1} A) Z).mapDerivedCategory
  let Lf := (Etale.rightDerivedLowerShriekPlus (ModuleCat.{u + 1} A) f).obj L
  let ec := Etale.rightDerivedLowerShriekOfCompactificationPlusIso A c cf
  let ed := Etale.rightDerivedLowerShriekOfCompactificationPlusIso A d dg
  let ee := Etale.rightDerivedLowerShriekOfCompactificationPlusIso A egf e
  let Bc := (compactExchangeTransportComparison A c).app L
  let Bf := (compactExchangeTransportComparison A cf).app L
  let b₀ := (compactExchangeTransportComparison A d).app
    ((Etale.rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} A) c).obj L)
  let b₁ := (compactExchangeTransportComparison A d).app Lf
  let bg := (compactExchangeTransportComparison A dg).app Lf
  let bfg := (compactExchangeTransportComparison A egf).app L
  let C₀ := coherenceCompactificationChange A c cf L
  let C₁ := coherenceCompactificationChange A d dg Lf
  let C₂ := coherenceCompactificationChange A egf e L
  let η := (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) Z).ι.mapIso
    ((originComposition A f g).app
      ((comparisonUpperStarPlusEtaleOrigin (ModuleCat.{u + 1} A) X).obj L))
  let p := CY.map (DerivedCategory.Plus.ι.map (ec.hom.app L))
  let n := CZ.map (DerivedCategory.Plus.ι.map
    ((Etale.rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} A) d).map
      (ec.hom.app L)))
  let a₁ := CZ.map (DerivedCategory.Plus.ι.map (ed.hom.app Lf))
  let a₂ := CZ.map (DerivedCategory.Plus.ι.map
    ((Etale.rightDerivedLowerShriekPlusCompIso A f g).hom.app L))
  let a₃ := CZ.map (DerivedCategory.Plus.ι.map (ee.hom.app L))
  let z := ((compactExchangeTransportComparison A e).app L).hom
  let t := CZ.map (DerivedCategory.Plus.ι.map ((coherenceEtaleCompositor A c d e).hom.app L))
  dsimp only [coherenceProEtaleCompositor, coherenceCompositionSource]
  refine coherence_composition_wire Fd Fg Bc Bf b₀ b₁ bg bfg C₀ C₁ C₂ η
    p n a₁ a₂ a₃ z t ?_ ?_ ?_ ?_ ?_ ?_
  · exact coherence_change_hom A c cf L
  · exact coherence_change_hom A d dg Lf
  · exact coherence_change_hom A egf e L
  · exact coherence_origin_iso_hom A f g L
  · exact coherence_etale_compositor_hom A c d e L
  · exact coherence_comparison_naturality
      (Etale.rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} A) d)
      DerivedCategory.Plus.ι CZ DerivedCategory.Plus.ι CY Fd
      (compactExchangeTransportComparison A d) (ec.hom.app L)

private theorem coherence_transport_square
    {C D E F G H : Type*} [Category C] [Category D] [Category E]
    [Category F] [Category G] [Category H]
    (K : C ⥤ D) (I : D ⥤ E) (M : E ⥤ H) (J : C ⥤ F)
    (N : F ⥤ G) (P : G ⥤ H) (b : K ⋙ I ⋙ M ≅ J ⋙ N ⋙ P)
    {X Y : C} {U V : G} (e₀ : N.obj (J.obj X) ≅ U) (e₁ : N.obj (J.obj Y) ≅ V)
    (a : X ⟶ Y) (q : U ⟶ V)
    (h : N.map (J.map a) ≫ e₁.hom = e₀.hom ≫ q) :
    M.map (I.map (K.map a)) ≫ (b.app Y ≪≫ P.mapIso e₁).hom =
      (b.app X ≪≫ P.mapIso e₀).hom ≫ P.map q := by
  have hn := coherence_comparison_naturality K I M J N P b a
  simp only [Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, Category.assoc]
  rw [reassoc_of% hn, ← P.map_comp, h, P.map_comp]

private theorem coherence_conjugate_square
    {C D E : Type*} [Category C] [Category D] [Category E]
    (I : C ⥤ D) (M : D ⥤ E)
    {X₀ X₁ Y₀ Y₁ : C} {U₀ U₁ V₀ V₁ : E}
    (b₀ : M.obj (I.obj X₀) ≅ U₀) (b₁ : M.obj (I.obj X₁) ≅ U₁)
    (c₀ : M.obj (I.obj Y₀) ≅ V₀) (c₁ : M.obj (I.obj Y₁) ≅ V₁)
    (e₀ : X₀ ≅ Y₀) (e₁ : X₁ ≅ Y₁) (p₀ : U₀ ≅ V₀) (p₁ : U₁ ≅ V₁)
    (a : X₀ ⟶ X₁) (q : U₀ ⟶ U₁)
    (h₀ : M.map (I.map e₀.hom) ≫ c₀.hom = b₀.hom ≫ p₀.hom)
    (h₁ : M.map (I.map e₁.hom) ≫ c₁.hom = b₁.hom ≫ p₁.hom)
    (h : M.map (I.map a) ≫ b₁.hom = b₀.hom ≫ q) :
    M.map (I.map (e₀.inv ≫ a ≫ e₁.hom)) ≫ c₁.hom =
      c₀.hom ≫ (p₀.inv ≫ q ≫ p₁.hom) := by
  simp only [Functor.map_comp, Category.assoc]
  rw [h₁, reassoc_of% h]
  have h' := congrArg (fun t ↦ M.map (I.map e₀.inv) ≫ t ≫ p₀.inv) h₀
  simp only [← Functor.map_comp, ← Functor.map_comp_assoc, Iso.inv_hom_id,
    CategoryTheory.Functor.map_id,
    Category.id_comp, Category.assoc, Iso.hom_inv_id, Category.comp_id] at h'
  rw [← Category.assoc, h'.symm, Category.assoc]

private theorem coherence_comp_square
    {C D E : Type*} [Category C] [Category D] [Category E]
    (I : C ⥤ D) (M : D ⥤ E) {X Y Z : C} {U V W : E}
    (b₀ : M.obj (I.obj X) ≅ U) (b₁ : M.obj (I.obj Y) ≅ V)
    (b₂ : M.obj (I.obj Z) ≅ W) (a : X ⟶ Y) (b : Y ⟶ Z)
    (p : U ⟶ V) (q : V ⟶ W)
    (ha : M.map (I.map a) ≫ b₁.hom = b₀.hom ≫ p)
    (hb : M.map (I.map b) ≫ b₂.hom = b₁.hom ≫ q) :
    M.map (I.map (a ≫ b)) ≫ b₂.hom = b₀.hom ≫ (p ≫ q) := by
  simp only [Functor.map_comp, Category.assoc]
  rw [hb, ← Category.assoc, ha, Category.assoc]

private theorem coherence_identity_square
    {C D E : Type*} [Category C] [Category D] [Category E]
    (I : C ⥤ D) (M : D ⥤ E) {X : C} {Y : E} (b : M.obj (I.obj X) ≅ Y) :
    M.map (I.map (𝟙 X)) ≫ b.hom = b.hom ≫ 𝟙 Y := by
  simp only [I.map_id, M.map_id, Category.id_comp, Category.comp_id]

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] coherenceEtaleCompositor
  coherenceProEtaleCompositor coherenceCompositionSource

private theorem coherence_diagram (P : WeilConjectures.PurityFiniteSetting.{u})
    {T : Scheme.{u}} {b₀ b₁ : CompactSupportSiteBoundary P.Coefficient T}
    (D : CompactSupportSiteDiagram P b₀ b₁) :
    (comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) T).mapDerivedCategory.map
        (DerivedCategory.Plus.ι.map D.etaleMap) ≫ b₁.comparison.hom =
      b₀.comparison.hom ≫ D.proEtaleMap := by
  induction D with
  | @refinement X Y _ _ _ _ f _ _ _ c d r L =>
      let := LocallyOfFiniteType.isLocallyNoetherian X.hom
      let := QuasiCompact.compactSpace_of_compactSpace X.hom
      let : IsNoetherian X.left := ⟨⟩
      let := LocallyOfFiniteType.isLocallyNoetherian Y.hom
      let := QuasiCompact.compactSpace_of_compactSpace Y.hom
      let : IsNoetherian Y.left := ⟨⟩
      dsimp only [CompactSupportSiteDiagram.etaleMap, CompactSupportSiteDiagram.proEtaleMap,
        coherenceCompactificationBoundary]
      exact coherence_refinement P.Coefficient r L
  | @composition X Y Z _ _ _ _ _ _ f g _ _ _ _ _ _ c d e L =>
      let := LocallyOfFiniteType.isLocallyNoetherian X.hom
      let := QuasiCompact.compactSpace_of_compactSpace X.hom
      let : IsNoetherian X.left := ⟨⟩
      let := LocallyOfFiniteType.isLocallyNoetherian Y.hom
      let := QuasiCompact.compactSpace_of_compactSpace Y.hom
      let : IsNoetherian Y.left := ⟨⟩
      let := LocallyOfFiniteType.isLocallyNoetherian Z.hom
      let := QuasiCompact.compactSpace_of_compactSpace Z.hom
      let : IsNoetherian Z.left := ⟨⟩
      dsimp only [CompactSupportSiteDiagram.etaleMap, CompactSupportSiteDiagram.proEtaleMap,
        coherenceCompositionBoundary, coherenceCompactificationBoundary]
      exact coherence_composition P.Coefficient c d e L
  | restriction sq c L =>
      dsimp only [CompactSupportSiteDiagram.etaleMap, CompactSupportSiteDiagram.proEtaleMap]
      exact coherence_restriction P.Coefficient sq c L
  | identity b =>
      exact coherence_identity_square DerivedCategory.Plus.ι
        (comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) _).mapDerivedCategory b.comparison
  | @comp T b₀ b₁ b₂ D E hD hE =>
      exact coherence_comp_square DerivedCategory.Plus.ι
        (comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) T).mapDerivedCategory
        b₀.comparison b₁.comparison b₂.comparison
        D.etaleMap E.etaleMap D.proEtaleMap E.proEtaleMap hD hE
  | @push X Y _ _ _ _ f _ _ _ c b₀ b₁ D hD =>
      dsimp only [CompactSupportSiteDiagram.etaleMap, CompactSupportSiteDiagram.proEtaleMap,
        coherencePushBoundary]
      exact coherence_transport_square
        (Etale.rightDerivedLowerShriekOfCompactificationPlus
          (ModuleCat.{u + 1} P.Coefficient) c) DerivedCategory.Plus.ι
        (comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) Y.left).mapDerivedCategory
        DerivedCategory.Plus.ι
        (comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) X.left).mapDerivedCategory
        (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} P.Coefficient) c)
        (compactExchangeTransportComparison P.Coefficient c)
        b₀.comparison b₁.comparison D.etaleMap D.proEtaleMap hD
  | @pull X Y _ _ _ _ v _ b₀ b₁ D hD =>
      dsimp only [CompactSupportSiteDiagram.etaleMap, CompactSupportSiteDiagram.proEtaleMap,
        coherencePullBoundary]
      exact coherence_transport_square
        (Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) v.left).mapDerivedCategoryPlus
        DerivedCategory.Plus.ι
        (comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) X.left).mapDerivedCategory
        DerivedCategory.Plus.ι
        (comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) Y.left).mapDerivedCategory
        (upperStar (ModuleCat.{u + 1} P.Coefficient) v.left).leftDerivedFunctor
        (leftDerivedUpperStarComparisonIso v.left P.Coefficient)
        b₀.comparison b₁.comparison D.etaleMap D.proEtaleMap hD
  | @change T b₀ b₁ c₀ c₁ e₀ e₁ p₀ p₁ h₀ h₁ D hD =>
      exact coherence_conjugate_square DerivedCategory.Plus.ι
        (comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) T).mapDerivedCategory
        b₀.comparison b₁.comparison c₀.comparison c₁.comparison e₀ e₁ p₀ p₁
        D.etaleMap D.proEtaleMap h₀ h₁ hD

private theorem coherence_iso_square
    {C D E : Type*} [Category C] [Category D] [Category E]
    (I : C ⥤ D) (M : D ⥤ E) {X Y : C} {U V : E}
    (a : X ⟶ Y) (ha : IsIso a)
    (b₀ : M.obj (I.obj X) ≅ U) (b₁ : M.obj (I.obj Y) ≅ V) (q : U ⟶ V)
    (h : M.map (I.map a) ≫ b₁.hom = b₀.hom ≫ q) : IsIso q := by
  let := ha
  have hi : IsIso (b₀.hom ≫ q) := by
    rw [← h]
    infer_instance
  exact (isIso_comp_left_iff b₀.hom q).mp hi

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
  refine ⟨?_, ?_, coherence_diagram P, ?_⟩
  · intros
    infer_instance
  · intro X X' Y Y' _ _ _ _ _ _ _ _ f f' u' v _ _ _ _ sq c L
    have h := coherence_restriction P.Coefficient sq c L
    have he := (Etale.compactSupportFiniteTorsion P.Coefficient sq c).1 L
    refine ⟨he, ?_⟩
    exact coherence_iso_square DerivedCategory.Plus.ι
      (comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) Y'.left).mapDerivedCategory
      ((Etale.rightDerivedLowerShriekOfCompactificationPlusBaseChangeMap
        P.Coefficient sq c).app L) he
      (coherenceRestrictionSource P.Coefficient v.left c L).comparison
      (coherenceRestrictionTarget P.Coefficient sq c L).comparison _ h
  · intro T b₀ b₁ D E h
    apply (cancel_epi b₀.comparison.hom).mp
    rw [← coherence_diagram P D, ← coherence_diagram P E, h]

end AlgebraicGeometry.ProEtale
