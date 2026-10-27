/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q31
-/
module

public import Sheaf.Paper.CompletedOpenStrictMateIdentification
public import Sheaf.Paper.RefinementExchangeCoherence
public import Sheaf.Paper.CompletedOrdinaryComparisons
public import Sheaf.Paper.PurityFiniteSetting
public import Sheaf.Paper.FiniteTorAmplitudeSites
public import Sheaf.Paper.IntegralCoefficientPresentationComparison
public import Sheaf.Paper.ExchangeFunctoriality
public import Sheaf.Paper.QcqsCompactSupportRealization
public import Sheaf.Paper.CompletedCompactSupportExchange
public import Sheaf.Paper.StrictTowerExchangeMateNormalization
public import WeilConjectures.Compactification.RefinementCategory
public import WeilConjectures.Compactification.BaseChange
public import Sheaf.Paper.AdicCoefficientDatum
public import Sheaf.AlgebraicGeometry.StrictConstantTowerOperations
public import Sheaf.AlgebraicGeometry.StrictTowerOpenExtension
public import Sheaf.AlgebraicGeometry.StrictTowerProperOpenCalculus
public import Mathlib.CategoryTheory.Adjunction.Mates
public import Sheaf.Paper.ConstantCompletionEquivalence
import Sheaf.Paper.CompleteCompactSupportProetale

/-! # Strict reduction of compact-support exchange

Source: blueprint latest, sec-six-functors/sk-thm-sf-package,
prop-pur-weil-equivariance-compatibilities.proof.md, constituent compatibility;
Stacks Tags 07A7, 03DI, 03DJ and 0F7F.
(blueprint: lem-pur-strict-reduction-compact-support-normalization).

Main definitions: `exchange`, `kappaSource`, `kappaTarget` are the specified arrows;
`refinement` and `commonRefinement` retain their actual proper/open normalization.
Main statement: `strictReductionCompactSupportNormalization`, with naturality,
compositor, identity, refinement and common-refinement clauses below.

All corners and arrows are constructed in derived categories of strict diagrams.
The quotient transitions are retained; no inverse limit or finite evaluation is taken.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u

-- Keep the canonical derived-category instance; IntegralHom exports a chosen one.

attribute [-instance] WeilConjectures.IntegralHom.derivedCategory
open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.StrictSupportNormalization

attribute [local irreducible] HasDerivedCategory.standard Functor.mapDerivedCategory
  Functor.mapDerivedCategoryFactors DerivedCategory.Q DerivedCategory.Qh completedReductionTower

variable {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)

/-- The specified quotient tower followed by termwise scalar restriction.
Source: strict normalization, proof Step 1; Stacks 099M
(blueprint: lem-pur-strict-reduction-compact-support-normalization). -/
abbrev input (X : Scheme.{u}) := completedReductionTower X d ⋙ exchangeTowerRes d X

/-- Strict compact support for a supplied compactification, before scalar restriction.
Source: strict normalization, proper/open assembly
(blueprint: lem-pur-strict-reduction-compact-support-normalization). -/
abbrev support {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :=
  cbcRealizationJ d c.i ⋙ d.towerPush c.g

/-- Scalar/open and normalized proper scalar comparison, in the prescribed order.
Source: strict normalization, proof Steps 1--3; Stacks 03DI and 07A7
(blueprint: lem-pur-strict-reduction-compact-support-normalization). -/
def supportScalar {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    support d c ⋙ exchangeTowerRes d Y ≅
      exchangeTowerRes d X ⋙ ProEtale.StrictTower.compositionF A c :=
  Functor.isoWhiskerLeft (cbcRealizationJ d c.i) (exchangeResPush d c.g) ≪≫
    Functor.isoWhiskerRight (cbcRealizationTowerScalarOpen d c.i)
      (ProEtale.StrictTower.R A c.g)

/-- Quotient/open comparison and the actual proper projection formula.
Source: strict normalization, proof Steps 2--3
(blueprint: lem-pur-strict-reduction-compact-support-normalization). -/
def supportReduction {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) (K : d.derived X) :
    (completedReductionTower Y d).obj ((cbcSupport d c).obj K) ≅
      (support d c).obj ((completedReductionTower X d).obj K) :=
  asIso (d.towerProjection c.g ((cbcJ d c.i).obj K)) ≪≫
    (d.towerPush c.g).mapIso (cbcRealizationReduction d c.i K)

/-- The full compact-support quotient corner, with its scalar normalization.
Source: strict normalization, proof Steps 2--3 and 8
(blueprint: lem-pur-strict-reduction-compact-support-normalization). -/
def quotientCorner {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) (K : d.derived X) :
    (input d Y).obj ((cbcSupport d c).obj K) ≅
      (ProEtale.StrictTower.compositionF A c).obj ((input d X).obj K) :=
  (exchangeTowerRes d Y).mapIso (supportReduction d c K) ≪≫
    (supportScalar d c).app ((completedReductionTower X d).obj K)

variable {X' X Y' Y : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
  {g : Y' ⟶ Y} {g' : X' ⟶ X}

/-- Source of the specified proper strict lift, on the quotient of j!K.
Source: strict normalization, proof Step 3
(blueprint: lem-pur-strict-reduction-compact-support-normalization). -/
abbrev source (c : Compactification f) (K : d.derived X) :=
  (d.towerPull g).obj ((d.towerPush c.g).obj
    ((completedReductionTower c.Z d).obj ((cbcJ d c.i).obj K)))

/-- Target after the actual strict finite open exchange.
Source: strict normalization, proof Step 4
(blueprint: lem-pur-strict-reduction-compact-support-normalization). -/
abbrev target (c' : Compactification f') (K : d.derived X) :=
  (d.towerPush c'.g).obj
    ((cbcOpenMateTarget d (j' := c'.i) (v := g')).obj K)

/-- The strict compact-support map: v' followed by proper image of omega.
The intervening pullback-presentation transport is the normalized derived-counit map.
Source: strict normalization, proof Steps 3--5; Definition def-cbc-completed-exchange-map
(blueprint: lem-pur-strict-reduction-compact-support-normalization). -/
def exchange (c : Compactification f) (c' : Compactification f')
    (s : c'.Z ⟶ c.Z) (sp : ChosenCartesianSquare s c'.g c.g g)
    (sj : OpenImmersionSquare g' c'.i c.i s) (K : d.derived X) :
    source d (g := g) c K ⟶ target d (g' := g') c' K :=
  d.towerV' sp ((cbcJ d c.i).obj K) ≫
    (d.towerPush c'.g).map
      ((cbcDatumTowerTransport d s).inv.app
        ((completedReductionTower c.Z d).obj ((cbcJ d c.i).obj K)) ≫
          (cbcOpenMateOmega d sj K).hom)

/-- The source kappa: proper b, then G R of the same quotient/open comparison z_j.
Source: strict normalization, proof Step 3
(blueprint: lem-pur-strict-reduction-compact-support-normalization). -/
def kappaSource (c : Compactification f) (K : d.derived X) :
    (exchangeTowerRes d Y').obj (source d (g := g) c K) ≅
      (ProEtale.StrictTower.G A g).obj
        ((ProEtale.StrictTower.compositionF A c).obj ((input d X).obj K)) :=
  (exchangeCornerB d c.g g).app
      ((completedReductionTower c.Z d).obj ((cbcJ d c.i).obj K)) ≪≫
    (ProEtale.StrictTower.G A g).mapIso
      ((ProEtale.StrictTower.R A c.g).mapIso (cbcRealizationQuotientOpen d c.i K))

/-- The target kappa: normalized proper scalar comparison followed by R of open b.
Source: strict normalization, proof Step 4
(blueprint: lem-pur-strict-reduction-compact-support-normalization). -/
def kappaTarget (c' : Compactification f') (K : d.derived X) :
    (exchangeTowerRes d Y').obj (target d (g' := g') c' K) ≅
      (ProEtale.StrictTower.compositionF A c').obj
        ((ProEtale.StrictTower.G A g').obj ((input d X).obj K)) :=
  (exchangeResPush d c'.g).app _ ≪≫
    (ProEtale.StrictTower.R A c'.g).mapIso
      (cbcOpenMateB d (j' := c'.i) (v := g') K)

/-- Canonical completed-coefficient pullback compositor on ordinary modules.
Its right-adjoint conjugate is the sectionwise fibre-product pasting comparison.
Source: strict normalization, proof Step 6; Stacks 0D6D
(blueprint: lem-pur-strict-reduction-compact-support-normalization). -/
def modulePullComp {U V W : Scheme.{u}} (h : U ⟶ V) (g : V ⟶ W) :=
  eqToIso (congrArg
    (proEtaleRingModulePullback (h ≫ g) (d.completedRing W) (d.completedRing U))
      (d.integralRingIso_comp h g)) ≪≫
    exchangeModuleComposition h g (d.completedRing W) (d.completedRing V)
      (d.completedRing U) (d.integralRingIso g) (d.integralRingIso h)

/-- Descend the actual termwise pullback compositor on the diagram site.
Source: strict normalization, proof Step 6
(blueprint: lem-pur-strict-reduction-compact-support-normalization). -/
def pullComp {U V W : Scheme.{u}} (h : U ⟶ V) (g : V ⟶ W) :
    d.towerPull (h ≫ g) ≅ d.towerPull g ⋙ d.towerPull h :=
  Functor.mapDerivedCategoryNatIso
    (((Functor.whiskeringRight ℕᵒᵖ _ _).mapIso (modulePullComp d h g)) ≪≫
      (Functor.whiskeringRightObjCompIso _ _).symm) ≪≫
    Functor.mapDerivedCategoryCompIso _ _

/-- The uniquely quotient-normalized arithmetic identification, at positive level n+1.
Source: Bhatt--Scholze 6.5 and integral coefficient presentation comparison
(blueprint: lem-pur-strict-reduction-compact-support-normalization). -/
def arithmeticQuotient (P : WeilConjectures.PurityFiniteSetting.{u}) (T : Scheme.{u})
    (n : ℕ) :=
  ((WeilConjectures.IntegralCoefficientPresentation.comparison
    P.coefficients.l P.extension T).1 n).exists.choose

/-- Canonical comparison with the completed coefficient convention used by D^b_ctf.
Existence determines this ring isomorphism uniquely by all its finite projections.
Source: Bhatt--Scholze 6.5; integral coefficient presentation comparison
(blueprint: lem-pur-strict-reduction-compact-support-normalization). -/
def arithmeticCompleted (P : WeilConjectures.PurityFiniteSetting.{u}) (T : Scheme.{u}) :=
  (((WeilConjectures.IntegralCoefficientPresentation.comparison
    P.coefficients.l P.extension T).2.2.2.choose_spec
      (arithmeticQuotient P T)
      (fun n ↦ ((WeilConjectures.IntegralCoefficientPresentation.comparison
        P.coefficients.l P.extension T).1 n).exists.choose_spec)).2.2.1).exists.choose

/-- The integral input in the actual adic datum's coefficient coordinates.
This is scalar relabelling along the specified projection-normalized ring isomorphism.
Source: strict normalization, coefficient conventions and proof Step 1
(blueprint: lem-pur-strict-reduction-compact-support-normalization). -/
def arithmeticInput (P : WeilConjectures.PurityFiniteSetting.{u}) (T : Scheme.{u})
    (K : WeilConjectures.finiteTorConstructibleIntegralCategory
      P.coefficients.l P.extension T) :
    (pbcIntegralDatum P.coefficients.l P.extension).derived T :=
  (pbcDerivedRestrict (arithmeticCompleted P T).hom).obj K.obj

/-- The source open quotient transport, using the same z_j tensor factor.
Source: strict normalization, proof Steps 2--3
(blueprint: lem-pur-strict-reduction-compact-support-normalization). -/
def sourceReduction (c : Compactification f) (K : d.derived X) :
    source d (g := g) c K ≅
      (d.towerPull g).obj ((support d c).obj ((completedReductionTower X d).obj K)) :=
  (d.towerPull g).mapIso
    ((d.towerPush c.g).mapIso (cbcRealizationReduction d c.i K))

/-- The actual refinement on strict quotient corners, obtained from the specified
integral proper/open mate by its reduction and proper projection identifications.
Source: strict normalization, proof Step 8; Stacks 0F7B--0F7C
(blueprint: lem-pur-strict-reduction-compact-support-normalization). -/
def refinement {X Y : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f]
    {c₁ c₂ : Compactification f} (r : c₁.Refinement c₂) (K : d.derived X) :
    (support d c₂).obj ((completedReductionTower X d).obj K) ⟶
      (support d c₁).obj ((completedReductionTower X d).obj K) :=
  (supportReduction d c₂ K).inv ≫
    (completedReductionTower Y d).map (cbcRefinementMap d r K) ≫
      (supportReduction d c₁ K).hom

/-- Source refinement conjugated by the fixed source open quotient transport.
Source: strict normalization, proof Steps 8--9
(blueprint: lem-pur-strict-reduction-compact-support-normalization). -/
def sourceRefinement [QuasiCompact f] {c₁ c₂ : Compactification f}
    (r : c₁.Refinement c₂) (K : d.derived X) :
    source d (g := g) c₂ K ⟶ source d (g := g) c₁ K :=
  (sourceReduction d c₂ K).hom ≫ (d.towerPull g).map (refinement d r K) ≫
    (sourceReduction d c₁ K).inv

/-- Identify strict pullback of the quotient with the quotient of ordinary pullback.
This is the actual derived-counit transport followed by the reduction tensor comparison.
Source: strict normalization, proof Steps 4 and 6; Stacks 099N
(blueprint: lem-pur-strict-reduction-compact-support-normalization). -/
def pullReduction {U V : Scheme.{u}} (h : U ⟶ V) (K : d.derived V) :
    (completedTowerPullback h d).obj ((completedReductionTower V d).obj K) ≅
      (completedReductionTower U d).obj ((d.pull h).obj K) :=
  (cbcDatumTowerTransport d h).app _ ≪≫ (d.reductionTowerPullbackIso h).app K

/-- Target reduction transport, before either scalar restriction or inverse limit.
Source: strict normalization, proof Steps 4 and 8
(blueprint: lem-pur-strict-reduction-compact-support-normalization). -/
def targetReduction (c' : Compactification f') (K : d.derived X) :
    target d (g' := g') c' K ≅
      (support d c').obj ((completedReductionTower X' d).obj ((d.pull g').obj K)) :=
  (d.towerPush c'.g).mapIso
    ((cbcRealizationJ d c'.i).mapIso (pullReduction d g' K))

/-- The induced strict target refinement uses the same pullback/reduction corner.
Source: strict normalization, proof Steps 8--9
(blueprint: lem-pur-strict-reduction-compact-support-normalization). -/
def targetRefinement [QuasiCompact f'] {c₁' c₂' : Compactification f'}
    (r' : c₁'.Refinement c₂') (K : d.derived X) :
    target d (g' := g') c₂' K ⟶ target d (g' := g') c₁' K :=
  (targetReduction d c₂' K).hom ≫ refinement d r' ((d.pull g').obj K) ≫
    (targetReduction d c₁' K).inv

/-- The canonical strict quotient/pullback comparison after scalar restriction.
Source: strict normalization, proof Step 6
(blueprint: lem-pur-strict-reduction-compact-support-normalization). -/
def inputPull {U V : Scheme.{u}} (h : U ⟶ V) (K : d.derived V) :
    (ProEtale.StrictTower.G A h).obj ((input d V).obj K) ≅
      (input d U).obj ((d.pull h).obj K) :=
  ((exchangeResPull d h).app ((completedReductionTower V d).obj K)).symm ≪≫
    (exchangeTowerRes d U).mapIso ((d.reductionTowerPullbackIso h).app K)

attribute [local irreducible] supportScalar supportReduction quotientCorner
  exchange kappaSource kappaTarget sourceReduction targetReduction inputPull pullReduction
  exchangeCornerB exchangeCornerD exchangeResPull exchangeResPush

/-- Actual strict compact-support exchange agrees with proper mate followed by the
unit-normalized open comparison under the specified kappa corners.
Source: blueprint latest, constituent compatibility; Stacks 07A7, 03DI and 03DJ
(blueprint: lem-pur-strict-reduction-compact-support-normalization).

Proof, node Steps 1--5:
1. Work on strict diagram sites. Compatible quotient coefficients give exact scalar
restriction and the K-injective-normalized proper comparison, preserving adjuncts.
2. Use the strict quotient/open tensor comparison followed by the scalar/open map,
both preserving the open unit. Quasi-compactness makes j!K complete. The supplied
finite origins apply to this intermediate object as well.
3. Apply strictTowerExchangeMateNormalization to p and j!K. Whisker its b,d corners
by the very same quotient/open comparison. Naturality of the proper mate identifies
its restricted arrow with E followed by the common middle corner.
4. completedOpenStrictMateIdentification identifies the actual omega with beta,
using the specified source and target transports. Proper image preserves this equation.
5. Compose the two equations. Their identical middle corner cancels and gives the
stated equality of strict tower maps. No faithfulness of finite evaluations is used.
The subsequent declarations record node Steps 6--9 for these same corners. -/
theorem strictReductionCompactSupportNormalization
    (P : WeilConjectures.PurityFiniteSetting.{u})
    {X' X Y' Y : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {g : Y' ⟶ Y} {g' : X' ⟶ X}
    [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [IsSeparated (X ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))]
    [IsSeparated (Y ↘ Spec (.of P.field.k))]
    [f.IsOver (Spec (.of P.field.k))] [IsSeparated f]
    [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f) (c' : Compactification f') (s : c'.Z ⟶ c.Z)
    (sp : ChosenCartesianSquare s c'.g c.g g)
    (sj : OpenImmersionSquare g' c'.i c.i s)
    (K : WeilConjectures.finiteTorConstructibleIntegralCategory
      P.coefficients.l P.extension X)
    (_origins : PbcHasCompatibleEtaleOrigins X
      (pbcIntegralDatum P.coefficients.l P.extension) (arithmeticInput P X K))
    (_openOrigins : PbcHasCompatibleEtaleOrigins c.Z
      (pbcIntegralDatum P.coefficients.l P.extension)
      ((cbcJ (pbcIntegralDatum P.coefficients.l P.extension) c.i).obj
        (arithmeticInput P X K))) :
    (exchangeTowerRes (pbcIntegralDatum P.coefficients.l P.extension) Y').map
        (exchange (pbcIntegralDatum P.coefficients.l P.extension) c c' s sp sj
          (arithmeticInput P X K)) ≫
      (kappaTarget (pbcIntegralDatum P.coefficients.l P.extension) c'
        (arithmeticInput P X K)).hom =
    (kappaSource (pbcIntegralDatum P.coefficients.l P.extension) c
      (arithmeticInput P X K)).hom ≫
      (ProEtale.StrictTower.compositionE (PbcIntegralRing P.coefficients.l P.extension)
        c c' g' g s sj.w sp.w
        (IsPullback.of_iso_pullback sj.toCommSq sj.isoPullback sj.hom_fst sj.hom_snd)).app
          ((input (pbcIntegralDatum P.coefficients.l P.extension) X).obj
            (arithmeticInput P X K)) := by
  sorry

/-- Naturality of the specified kappa corners, on the entire ambient input category.
Source: strict normalization, proof Steps 2--5; Stacks 03DI and 07A7
(blueprint: lem-pur-strict-reduction-compact-support-normalization).
Proof: the proper b,d, tensor/open and scalar comparisons are natural. Whisker their
naturality equations by the indicated functors and compose them in their specified order.
This gives both equations, with no evaluation or inverse-limit argument. -/
theorem kappa_naturality (c : Compactification f) (c' : Compactification f')
    (K L : d.derived X) (h : K ⟶ L) :
    (exchangeTowerRes d Y').map
        ((d.towerPull g).map ((d.towerPush c.g).map
          ((completedReductionTower c.Z d).map ((cbcJ d c.i).map h)))) ≫
        (kappaSource d c L).hom =
      (kappaSource d c K).hom ≫ (ProEtale.StrictTower.G A g).map
        ((ProEtale.StrictTower.compositionF A c).map ((input d X).map h)) ∧
    (exchangeTowerRes d Y').map
        ((d.towerPush c'.g).map
          ((cbcOpenMateTarget d (j' := c'.i) (v := g')).map h)) ≫
        (kappaTarget d c' L).hom =
      (kappaTarget d c' K).hom ≫ (ProEtale.StrictTower.compositionF A c').map
        ((ProEtale.StrictTower.G A g').map ((input d X).map h)) := by
  let ρ : completedReductionTower X d ⋙ cbcRealizationJ d c.i ≅
      cbcJ d c.i ⋙ completedReductionTower c.Z d :=
    NatIso.ofComponents (fun M ↦ (cbcRealizationReduction d c.i M).symm)
      (fun k ↦ (cbcRealizationReductionInv_properties d c.i).2 _ _ k)
  let z := Functor.isoWhiskerRight ρ.symm (exchangeTowerRes d c.Z) ≪≫
    Functor.isoWhiskerLeft (completedReductionTower X d)
      (cbcRealizationTowerScalarOpen d c.i)
  let ks := Functor.isoWhiskerLeft (cbcJ d c.i ⋙ completedReductionTower c.Z d)
      (exchangeCornerB d c.g g) ≪≫
    Functor.isoWhiskerRight z
      (ProEtale.StrictTower.R A c.g ⋙ ProEtale.StrictTower.G A g)
  let b : cbcOpenMateTarget d (j' := c'.i) (v := g') ⋙
      exchangeTowerRes d c'.Z ≅
      input d X ⋙ ProEtale.StrictTower.G A g' ⋙ ProEtale.StrictTower.J A c'.i :=
    Functor.isoWhiskerLeft (completedReductionTower X d)
      (Functor.isoWhiskerRight
        (Functor.isoWhiskerRight (cbcDatumTowerTransport d g')
          (cbcRealizationJ d c'.i)) (exchangeTowerRes d c'.Z)) ≪≫
    Functor.isoWhiskerLeft (completedReductionTower X d ⋙ d.towerPull g')
      (cbcRealizationTowerScalarOpen d c'.i) ≪≫
    Functor.isoWhiskerLeft (completedReductionTower X d)
      (Functor.isoWhiskerRight (exchangeResPull d g') (ProEtale.StrictTower.J A c'.i))
  let kt := Functor.isoWhiskerLeft (cbcOpenMateTarget d (j' := c'.i) (v := g'))
      (exchangeResPush d c'.g) ≪≫
    Functor.isoWhiskerRight b (ProEtale.StrictTower.R A c'.g)
  constructor
  · simpa only [ks, z, ρ, kappaSource, cbcRealizationQuotientOpen,
      Functor.comp_map, Functor.comp_obj, Iso.trans_hom, Iso.symm_hom,
      Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom, NatTrans.comp_app,
      Functor.whiskerLeft_app, Functor.whiskerRight_app, Iso.app_hom, Iso.app_inv,
      NatIso.ofComponents_inv_app, Iso.symm_inv, Functor.mapIso_hom,
      ProEtale.StrictTower.compositionF, Category.assoc,
      Functor.map_comp] using ks.hom.naturality h
  · simpa only [kt, b, kappaTarget, cbcOpenMateB,
      Functor.comp_map, Functor.comp_obj, Iso.trans_hom,
      Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom, NatTrans.comp_app,
      Functor.whiskerLeft_app, Functor.whiskerRight_app, Iso.app_hom,
      Functor.mapIso_hom, ProEtale.StrictTower.compositionF, cbcStrictOpen,
      Category.assoc, Functor.map_comp, cbcRealizationJ, cbcRealizationTowerJ,
      cbcStrictOpenModule] using kt.hom.naturality h

/-- The restriction comparison intertwines the canonical pullback compositors.
This is an equation of transformations on derived strict diagrams.
Source: strict normalization, proof Step 6; Stacks 0D6D and 07A7
(blueprint: lem-pur-strict-reduction-compact-support-normalization).
Proof: on ordinary diagram modules the scalar and pullback identifications preserve
the tensor unit and send a tensor to the same tensor on either path. Sectionwise
fibre-product pasting fixes their compositors. Exact descent preserves this equation.
The proper comparisons are its normalized mates, so mate pasting supplies the same
compositor compatibility for proper b,d, and the unit-preserving open comparisons.
No new choice of a comparison for the composite is made. -/
theorem scalarPull_composition {U V W : Scheme.{u}} (h : U ⟶ V) (g : V ⟶ W) :
    Functor.whiskerRight (pullComp d h g).hom (exchangeTowerRes d U) ≫
        Functor.whiskerLeft (d.towerPull g) (exchangeResPull d h).hom ≫
        Functor.whiskerRight (exchangeResPull d g).hom (ProEtale.StrictTower.G A h) =
      (exchangeResPull d (h ≫ g)).hom ≫
        Functor.whiskerLeft (exchangeTowerRes d W) (ProEtale.StrictTower.gComp A h g).hom := by
  sorry

private theorem constantPull_map {U V : Scheme.{u}} (h : U ⟶ V)
    {M N : ProEtale.StrictTower.Derived A V} (a : M ⟶ N) :
    (exchangeConstantPull (A := A) h).map a = (ProEtale.StrictTower.G A h).map a := by
  rfl

private theorem constantPush_map {U V : Scheme.{u}} (h : U ⟶ V)
    {M N : ProEtale.StrictTower.Derived A U} (a : M ⟶ N) :
    (exchangeConstantPush (A := A) h).map a = (ProEtale.StrictTower.R A h).map a := by
  rfl

private theorem pull_composition_corner
    {C D E C' D' E' : Type*} [Category C] [Category D] [Category E]
    [Category C'] [Category D'] [Category E']
    (rC : C ⥤ C') (rD : D ⥤ D') (rE : E ⥤ E')
    (G : C ⥤ D) (H : D ⥤ E) (GH : C ⥤ E)
    (G' : C' ⥤ D') (H' : D' ⥤ E') (GH' : C' ⥤ E')
    (bG : G ⋙ rD ≅ rC ⋙ G') (bH : H ⋙ rE ≅ rD ⋙ H')
    (bGH : GH ⋙ rE ≅ rC ⋙ GH') (c : GH ≅ G ⋙ H) (c' : GH' ≅ G' ⋙ H')
    (hc : Functor.whiskerRight c.hom rE ≫
        Functor.whiskerLeft G bH.hom ≫ Functor.whiskerRight bG.hom H' =
      bGH.hom ≫ Functor.whiskerLeft rC c'.hom)
    (M : C) {N : C'} (a : rC.obj M ⟶ N) :
    rE.map (c.hom.app M) ≫ bH.hom.app (G.obj M) ≫
        H'.map (bG.hom.app M ≫ G'.map a) =
      (bGH.hom.app M ≫ GH'.map a) ≫ c'.hom.app N := by
  have hM := congrArg (fun t ↦ t.app M) hc
  simp only [NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app] at hM
  simp only [← Category.assoc] at hM
  simp only [Functor.map_comp, ← Category.assoc]
  rw [hM]
  simp only [Category.assoc]
  apply congrArg (fun q ↦ bGH.hom.app M ≫ q)
  simpa only [Functor.comp_map] using (c'.hom.naturality a).symm

/-- Successive source substitutions use the very same intermediate kappa corner.
Source: strict normalization, proof Steps 6--7
(blueprint: lem-pur-strict-reduction-compact-support-normalization).
Proof: apply scalarPull_composition to the proper image of the quotient of j!K.
Naturality carries the fixed z_j through the pullback compositor. The two proper b
comparisons are the normalized direct-image scalar comparison, so their intermediate
components agree. Cancellation then uses that identical component and its inverse. -/
theorem kappaSource_composition {Y'' : Scheme.{u}} (h : Y'' ⟶ Y')
    (c : Compactification f) (K : d.derived X) :
    (exchangeTowerRes d Y'').map
        ((pullComp d h g).hom.app ((d.towerPush c.g).obj
          ((completedReductionTower c.Z d).obj ((cbcJ d c.i).obj K)))) ≫
        (exchangeResPull d h).hom.app (source d (g := g) c K) ≫
        (ProEtale.StrictTower.G A h).map (kappaSource d (g := g) c K).hom =
      (kappaSource d (g := h ≫ g) c K).hom ≫
        (ProEtale.StrictTower.gComp A h g).hom.app
          ((ProEtale.StrictTower.compositionF A c).obj ((input d X).obj K)) := by
  simpa only [kappaSource, exchangeCornerB, Iso.trans_hom, Iso.app_hom,
    Functor.mapIso_hom, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Iso.symm_hom,
    Category.id_comp, Category.comp_id, Functor.map_comp, Functor.map_id,
    ProEtale.StrictTower.compositionF, constantPull_map, Functor.comp_obj,
    input, source, Category.assoc] using
    pull_composition_corner (exchangeTowerRes d Y) (exchangeTowerRes d Y')
      (exchangeTowerRes d Y'') (d.towerPull g) (d.towerPull h) (d.towerPull (h ≫ g))
      (ProEtale.StrictTower.G A g) (ProEtale.StrictTower.G A h)
      (ProEtale.StrictTower.G A (h ≫ g)) (exchangeResPull d g)
      (exchangeResPull d h) (exchangeResPull d (h ≫ g))
      (pullComp d h g) (ProEtale.StrictTower.gComp A h g) (scalarPull_composition d h g)
      ((d.towerPush c.g).obj ((completedReductionTower c.Z d).obj ((cbcJ d c.i).obj K)))
      ((exchangeResPush d c.g).hom.app _ ≫
        (ProEtale.StrictTower.R A c.g).map (cbcRealizationQuotientOpen d c.i K).hom)

/-- Quotient/pullback corners obey the same compositor, including identity maps.
This fixes the input corner used inside target kappa after either base change.
Source: strict normalization, proof Steps 6--7; Stacks 07A4 and 099N
(blueprint: lem-pur-strict-reduction-compact-support-normalization).
Proof: common-quotient tensor comparisons preserve quotient units and transitions.
On one K-flat diagram their two compositions are the same tensor reassociation.
The cochain tensor compositor, the normalized scalar pullback comparison and exact
descent identify the two displayed paths. This is equality before finite evaluation. -/
theorem inputPull_composition {U V W : Scheme.{u}} (h : U ⟶ V) (g : V ⟶ W)
    (K : d.derived W) :
    (ProEtale.StrictTower.gComp A h g).hom.app ((input d W).obj K) ≫
        (ProEtale.StrictTower.G A h).map (inputPull d g K).hom ≫
        (inputPull d h ((d.pull g).obj K)).hom =
      (inputPull d (h ≫ g) K).hom ≫
        (input d U).map ((d.pullComp h g).hom.app K) := by
  sorry

/-- Scalar restriction sends the actual strict refinement to the normalized comparison.
The canonical quotient corner records all proper projection and open tensor maps.
Source: strict normalization, proof Step 8; Stacks 0F7B--0F7C
(blueprint: lem-pur-strict-reduction-compact-support-normalization).
Proof: the proper/open inverse-image arrow is open base change followed by the clopen
section projector. Scalar restriction leaves identity on that section and zero on its
complement unchanged. Open tensor comparisons preserve its unit; the scalar pullback
square and mate cube send its proper mate to the actual normalized gamma. Whisker by
the outer proper image and the fixed projection/open quotient comparisons. -/
theorem refinement_normalization {X Y : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f]
    {c₁ c₂ : Compactification f} (r : c₁.Refinement c₂) (K : d.derived X) :
    (exchangeTowerRes d Y).map (refinement d r K) ≫
        (supportScalar d c₁).hom.app ((completedReductionTower X d).obj K) =
      (supportScalar d c₂).hom.app ((completedReductionTower X d).obj K) ≫
        (ProEtale.StrictTower.refinementComparison A r).app ((input d X).obj K) := by
  sorry

private theorem refinementComparison_proof_irrel
    {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c₁ c₂ : Compactification f} (r : c₁.Refinement c₂)
    (hf : QuasiCompact f) {hg : QuasiCompact f} :
    ProEtale.StrictTower.refinementComparison A r hg =
      ProEtale.StrictTower.refinementComparison A r hf := by
  exact congrArg (fun h : QuasiCompact f ↦
    ProEtale.StrictTower.refinementComparison A r h) (Subsingleton.elim hg hf)

private theorem refinementCommonComparison_proof_irrel
    {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c₁ c₂ e : Compactification f} (r₁ : e.Refinement c₁) (r₂ : e.Refinement c₂)
    (M : ProEtale.StrictTower.Derived A X)
    (hM : ∀ n : ℕ, Nonempty (ProEtale.StrictTower.ScalarEtaleOrigin A X
      ((ProEtale.StrictTower.ev A X n).obj M)))
    (hf : QuasiCompact f) {hg : QuasiCompact f} :
    ProEtale.StrictTower.refinementCommonComparison A r₁ r₂ M hM hg =
      ProEtale.StrictTower.refinementCommonComparison A r₁ r₂ M hM hf := by
  exact congrArg (fun h : QuasiCompact f ↦
    ProEtale.StrictTower.refinementCommonComparison A r₁ r₂ M hM h)
    (Subsingleton.elim hg hf)

private theorem scalar_map_square
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    (P : C ⥤ D) (rC : C ⥤ E) (rD : D ⥤ F) (R : E ⥤ F)
    (δ : P ⋙ rD ≅ rC ⋙ R) {M N : C} {V W : E}
    (t : M ⟶ N) (a : rC.obj M ⟶ V) (b : rC.obj N ⟶ W) (β : V ⟶ W)
    (ht : rC.map t ≫ b = a ≫ β) :
    rD.map (P.map t) ≫ δ.hom.app N ≫ R.map b =
      δ.hom.app M ≫ R.map a ≫ R.map β := by
  have hn := δ.hom.naturality t
  dsimp only [Functor.comp_map] at hn
  rw [← Category.assoc, hn, Category.assoc, ← R.map_comp, ht,
    R.map_comp]

/-- The identified strict refinement comparisons retain identity and cocycle equations.
Source: strict normalization, proof Step 9; Stacks 0F7C
(blueprint: lem-pur-strict-reduction-compact-support-normalization).
Proof: refinement_normalization carries every factor to the published constant-tower
comparison. Apply refinementExchangeCoherence for identities and composition. At each
interior corner the same supportScalar isomorphism and its inverse cancel. Equivalently,
the original reduction maps already satisfy these equations and supportReduction
conjugates them. All maps remain strict diagram maps. -/
theorem refinement_cocycle {X Y : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f]
    (K : d.derived X) :
    (∀ c : Compactification f, refinement d (Compactification.Refinement.id c) K = 𝟙 _) ∧
    (∀ {c₁ c₂ c₃ : Compactification f} (r : c₁.Refinement c₂) (s : c₂.Refinement c₃),
      refinement d (r.comp s) K = refinement d s K ≫ refinement d r K) := by
  constructor
  · intro c
    have := c.isSeparated
    have := c.locallyOfFiniteType
    dsimp only [refinement]
    rw [(cbcRefinementMap_functoriality d K).1 c,
      (completedReductionTower Y d).map_id, Category.id_comp]
    exact (supportReduction d c K).inv_hom_id
  · intro c₁ c₂ c₃ r s
    have := c₁.isSeparated
    have := c₁.locallyOfFiniteType
    simp only [refinement, (cbcRefinementMap_functoriality d K).2 c₁ c₂ c₃ r s,
      Functor.map_comp, Category.assoc, Iso.hom_inv_id_assoc]

private theorem scalar_open_transport
    {C D C' D' E E' : Type*} [Category C] [Category D]
    [Category C'] [Category D'] [Category E] [Category E']
    (J : C ⥤ D) (rC : C ⥤ C') (rD : D ⥤ D') (J' : C' ⥤ D')
    (β : J ⋙ rD ≅ rC ⋙ J')
    (P : D ⥤ E) (rE : E ⥤ E') (P' : D' ⥤ E')
    (γ : P ⋙ rE ≅ rD ⋙ P')
    {M N Q : C} {Z : C'} (t : M ⟶ N) (e : N ⟶ Q) (a : rC.obj N ≅ Z) :
    rE.map (P.map (J.map (t ≫ e))) ≫ γ.hom.app (J.obj Q) ≫ P'.map (β.hom.app Q) =
      (γ.hom.app (J.obj M) ≫
        P'.map (rD.map (J.map t) ≫ β.hom.app N ≫ J'.map a.hom)) ≫
          P'.map (J'.map (a.inv ≫ rC.map e)) := by
  calc
    _ = γ.hom.app (J.obj M) ≫
        P'.map (rD.map (J.map (t ≫ e)) ≫ β.hom.app Q) := by
      rw [← Category.assoc]
      rw [show rE.map (P.map (J.map (t ≫ e))) ≫ γ.hom.app (J.obj Q) =
        γ.hom.app (J.obj M) ≫ P'.map (rD.map (J.map (t ≫ e))) from
          γ.hom.naturality (J.map (t ≫ e))]
      rw [Category.assoc, ← P'.map_comp]
    _ = γ.hom.app (J.obj M) ≫
        P'.map (rD.map (J.map t) ≫ β.hom.app N ≫ J'.map (rC.map e)) := by
      have h := β.hom.naturality e
      simp only [Functor.comp_map] at h
      rw [J.map_comp, rD.map_comp, Category.assoc, h]
    _ = _ := by
      have hc : P'.map (J'.map a.hom) ≫ P'.map (J'.map a.inv) = 𝟙 _ := by
        rw [← P'.map_comp, ← J'.map_comp, a.hom_inv_id, J'.map_id, P'.map_id]
      simp only [Functor.map_comp, Category.assoc]
      rw [← Category.assoc (P'.map (J'.map a.hom)), hc, Category.id_comp]

/-- Strict target corners use the same quotient/pullback corner as the source.
Source: strict normalization, proof Steps 4, 6 and 8
(blueprint: lem-pur-strict-reduction-compact-support-normalization).
Proof: expand cbcOpenMateB: its three factors are pullback presentation transport,
scalar/open comparison and scalar pullback. Naturality of scalar/open moves the
pullback/reduction isomorphism through it. Proper scalar naturality gives the equation.
Thus the target for one substitution is the source for the next after the compositor. -/
theorem kappaTarget_reduction (c' : Compactification f') (K : d.derived X) :
    (exchangeTowerRes d Y').map (targetReduction d (g' := g') c' K).hom ≫
        (supportScalar d c').hom.app
          ((completedReductionTower X' d).obj ((d.pull g').obj K)) =
      (kappaTarget d (g' := g') c' K).hom ≫
        (ProEtale.StrictTower.compositionF A c').map (inputPull d g' K).hom := by
  simpa only [targetReduction, pullReduction, supportScalar, kappaTarget,
    cbcOpenMateB, inputPull, Iso.trans_hom, Iso.app_hom, Iso.symm_hom,
    Functor.mapIso_hom, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    ProEtale.StrictTower.compositionF, cbcStrictOpen, cbcStrictOpenModule,
    cbcRealizationJ, cbcRealizationTowerJ, Functor.comp_map, Functor.comp_obj,
    Functor.map_comp, Category.assoc] using
    scalar_open_transport (cbcRealizationJ d c'.i) (exchangeTowerRes d X')
      (exchangeTowerRes d c'.Z) (ProEtale.StrictTower.J A c'.i)
      (cbcRealizationTowerScalarOpen d c'.i) (d.towerPush c'.g)
      (exchangeTowerRes d Y') (ProEtale.StrictTower.R A c'.g) (exchangeResPush d c'.g)
      ((cbcDatumTowerTransport d g').hom.app ((completedReductionTower X d).obj K))
      ((d.reductionTowerPullbackIso g').hom.app K)
      ((exchangeResPull d g').app ((completedReductionTower X d).obj K))

private theorem source_corner_transport
    {C D : Type*} [Category C] [Category D] (res : C ⥤ D)
    {Q₁ Q₂ S₁ S₂ : C} {Z₁ Z₂ : D}
    (e₁ : Q₁ ≅ S₁) (e₂ : Q₂ ≅ S₂)
    (b₁ : res.obj S₁ ⟶ Z₁) (b₂ : res.obj S₂ ⟶ Z₂)
    (k₁ : res.obj Q₁ ⟶ Z₁) (k₂ : res.obj Q₂ ⟶ Z₂)
    (h₁ : res.map e₁.hom ≫ b₁ = k₁)
    (h₂ : res.map e₂.hom ≫ b₂ = k₂)
    (r : S₂ ⟶ S₁) (t : Z₂ ⟶ Z₁) (hr : res.map r ≫ b₁ = b₂ ≫ t) :
    res.map (e₂.hom ≫ r ≫ e₁.inv) ≫ k₁ = k₂ ≫ t := by
  rw [← h₁, Functor.map_comp, Functor.map_comp]
  simp only [Category.assoc, ← res.map_comp_assoc, e₁.inv_hom_id,
    res.map_id, Category.id_comp]
  rw [res.map_comp, Category.assoc, hr, ← Category.assoc, h₂]

private theorem target_corner_transport_square
    {C D : Type*} [Category C] [Category D] (res : C ⥤ D)
    {Q₁ Q₂ S₁ S₂ : C} {Z₁ Z₂ W₁ W₂ : D}
    (e₁ : Q₁ ≅ S₁) (e₂ : Q₂ ≅ S₂)
    (b₁ : res.obj S₁ ⟶ W₁) (b₂ : res.obj S₂ ⟶ W₂)
    (k₁ : res.obj Q₁ ⟶ Z₁) (k₂ : res.obj Q₂ ⟶ Z₂)
    (q₁ : Z₁ ≅ W₁) (q₂ : Z₂ ≅ W₂)
    (h₁ : res.map e₁.hom ≫ b₁ = k₁ ≫ q₁.hom)
    (h₂ : res.map e₂.hom ≫ b₂ = k₂ ≫ q₂.hom)
    (r : S₂ ⟶ S₁) (tV : W₂ ⟶ W₁) (tU : Z₂ ⟶ Z₁)
    (ht : q₂.hom ≫ tV = tU ≫ q₁.hom)
    (hr : res.map r ≫ b₁ = b₂ ≫ tV) :
    res.map (e₂.hom ≫ r ≫ e₁.inv) ≫ k₁ = k₂ ≫ tU := by
  apply (Iso.cancel_iso_hom_right _ _ q₁).1
  have h := source_corner_transport res e₁ e₂ b₁ b₂
    (k₁ ≫ q₁.hom) (k₂ ≫ q₂.hom) h₁ h₂ r tV hr
  rw [Category.assoc, ht, ← Category.assoc] at h
  simpa only [Category.assoc] using h

/-- The same target corners transport refinements after arbitrary base change.
Source: strict normalization, proof Steps 8--9
(blueprint: lem-pur-strict-reduction-compact-support-normalization).
Proof: insert kappaTarget_reduction at both endpoints of targetRefinement. Apply
refinement_normalization to the pulled-back object. Naturality of the published
refinement transformation carries inputPull through it, leaving exactly this equation. -/
theorem targetRefinement_normalization [QuasiCompact f']
    {c₁' c₂' : Compactification f'} (r' : c₁'.Refinement c₂') (K : d.derived X) :
    (exchangeTowerRes d Y').map (targetRefinement d (g' := g') r' K) ≫
        (kappaTarget d (g' := g') c₁' K).hom =
      (kappaTarget d (g' := g') c₂' K).hom ≫
        (ProEtale.StrictTower.refinementComparison A r').app
          ((ProEtale.StrictTower.G A g').obj ((input d X).obj K)) := by
  rw [refinementComparison_proof_irrel (A := A) r'
    (inferInstance : QuasiCompact f')]
  have hn := refinement_normalization d r' ((d.pull g').obj K)
  rw [refinementComparison_proof_irrel (A := A) r'
    (inferInstance : QuasiCompact f')] at hn
  have ht := (ProEtale.StrictTower.refinementComparison A r'
    (inferInstance : QuasiCompact f')).naturality (inputPull d g' K).hom
  exact target_corner_transport_square (exchangeTowerRes d Y')
    (targetReduction d (g' := g') c₁' K) (targetReduction d (g' := g') c₂' K)
    ((supportScalar d c₁').hom.app ((completedReductionTower X' d).obj ((d.pull g').obj K)))
    ((supportScalar d c₂').hom.app ((completedReductionTower X' d).obj ((d.pull g').obj K)))
    (kappaTarget d (g' := g') c₁' K).hom (kappaTarget d (g' := g') c₂' K).hom
    ((ProEtale.StrictTower.compositionF A c₁').mapIso (inputPull d g' K))
    ((ProEtale.StrictTower.compositionF A c₂').mapIso (inputPull d g' K))
    (kappaTarget_reduction d (g' := g') c₁' K)
    (kappaTarget_reduction d (g' := g') c₂' K) (refinement d r' ((d.pull g').obj K))
    ((ProEtale.StrictTower.refinementComparison A r' (inferInstance : QuasiCompact f')).app
      ((input d X').obj ((d.pull g').obj K)))
    ((ProEtale.StrictTower.refinementComparison A r' (inferInstance : QuasiCompact f')).app
      ((ProEtale.StrictTower.G A g').obj ((input d X).obj K))) ht hn

/-- Refinement and exchange intertwine as actual restricted strict-tower arrows.
Source: strict normalization, proof Step 9; Stacks 0F7F
(blueprint: lem-pur-strict-reduction-compact-support-normalization).
Proof: substitute the exchange and refinement normalizations at the four vertices.
The constant-tower equation is refinementExchangeCoherence. The compositor identities
above identify each intermediate corner, so adjacent corner isomorphisms cancel.
The maps g,g' are arbitrary underlying scheme maps, including semilinear ones. -/
theorem refinement_exchange [QuasiCompact f] [QuasiCompact f']
    (c₁ c₂ : Compactification f) (c₁' c₂' : Compactification f')
    (s₁ : c₁'.Z ⟶ c₁.Z) (s₂ : c₂'.Z ⟶ c₂.Z)
    (sp₁ : ChosenCartesianSquare s₁ c₁'.g c₁.g g)
    (sp₂ : ChosenCartesianSquare s₂ c₂'.g c₂.g g)
    (sj₁ : OpenImmersionSquare g' c₁'.i c₁.i s₁)
    (sj₂ : OpenImmersionSquare g' c₂'.i c₂.i s₂)
    (r : c₁.Refinement c₂) (r' : c₁'.Refinement c₂')
    (_hr : r'.hom ≫ s₂ = s₁ ≫ r.hom) (K : d.derived X)
    (_origins : PbcHasCompatibleEtaleOrigins X d K) :
    (exchangeTowerRes d Y').map
        (sourceRefinement d (g := g) r K) ≫
        (exchangeTowerRes d Y').map (exchange d c₁ c₁' s₁ sp₁ sj₁ K) =
      (exchangeTowerRes d Y').map (exchange d c₂ c₂' s₂ sp₂ sj₂ K) ≫
        (exchangeTowerRes d Y').map (targetRefinement d r' K) := by
  sorry

/-- The input corner includes the identity base change with the prescribed unit.
Source: strict normalization, proof Steps 6--7; Stacks 07A4
(blueprint: lem-pur-strict-reduction-compact-support-normalization).
Proof: both quotient units are the tensor unit on the same diagram. The scalar
comparison preserves that unit. The unit-preserving identity conjugates therefore
give exactly the two paths below, before evaluation. -/
theorem inputPull_identity (X : Scheme.{u}) (K : d.derived X) :
    (inputPull d (𝟙 X) K).hom ≫ (input d X).map ((d.pullId X).hom.app K) =
      (ProEtale.StrictTower.gId A X).hom.app ((input d X).obj K) := by
  sorry

private theorem scalar_component_isIso {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) (K : d.derived X) :
    IsIso ((supportScalar d c).hom.app ((completedReductionTower X d).obj K)) := by
  exact NatIso.hom_app_isIso (supportScalar d c) ((completedReductionTower X d).obj K)

private theorem constant_refinement_isIso {X Y : Scheme.{u}} {f : X ⟶ Y}
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    {c₁ c₂ : Compactification f} (r : c₁.Refinement c₂) (K : d.derived X)
    (hK : ∀ n : ℕ, Nonempty (ProEtale.StrictTower.ScalarEtaleOrigin A X
      ((ProEtale.StrictTower.ev A X n).obj ((input d X).obj K)))) :
    IsIso ((ProEtale.StrictTower.refinementComparison A r (inferInstance : QuasiCompact f)).app
      ((input d X).obj K)) := by
  exact ProEtale.StrictTower.refinementComparison_isIso A r ((input d X).obj K) hK
    (inferInstance : QuasiCompact f)

private theorem normalized_component_isIso {X Y : Scheme.{u}} {f : X ⟶ Y}
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    {c₁ c₂ : Compactification f} (r : c₁.Refinement c₂) (K : d.derived X)
    (hK : ∀ n : ℕ, Nonempty (ProEtale.StrictTower.ScalarEtaleOrigin A X
      ((ProEtale.StrictTower.ev A X n).obj ((input d X).obj K)))) :
    IsIso ((supportScalar d c₂).hom.app ((completedReductionTower X d).obj K) ≫
      (ProEtale.StrictTower.refinementComparison A r (inferInstance : QuasiCompact f)).app
        ((input d X).obj K)) := by
  exact IsIso.comp_isIso' (scalar_component_isIso d c₂ K)
    (constant_refinement_isIso d r K hK)

/-- On the supplied finite-origin domain each actual restricted refinement is invertible.
Source: strict normalization, proof Steps 8--9; Stacks 0F7B and 0F7C
(blueprint: lem-pur-strict-reduction-compact-support-normalization).
Proof: refinement_normalization identifies this arrow with the normalized constant
comparison under the invertible supportScalar corners. refinementExchangeCoherence
makes that comparison invertible on exactly the displayed finite-origin domain. -/
theorem refinement_isIso {X Y : Scheme.{u}} {f : X ⟶ Y}
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    {c₁ c₂ : Compactification f} (r : c₁.Refinement c₂) (K : d.derived X)
    (_hK : ∀ n : ℕ, Nonempty (ProEtale.StrictTower.ScalarEtaleOrigin A X
      ((ProEtale.StrictTower.ev A X n).obj ((input d X).obj K)))) :
    IsIso ((exchangeTowerRes d Y).map (refinement d r K)) := by
  have hn := refinement_normalization d (f := f) (c₁ := c₁) (c₂ := c₂) r K
  rw [refinementComparison_proof_irrel (A := A) r
    (inferInstance : QuasiCompact f)] at hn
  exact @IsIso.of_isIso_fac_right _ _ _ _ _
    ((supportScalar d c₁).hom.app ((completedReductionTower X d).obj K))
    ((exchangeTowerRes d Y).map (refinement d r K))
    (((supportScalar d c₂).hom.app ((completedReductionTower X d).obj K)) ≫
      (ProEtale.StrictTower.refinementComparison A r (inferInstance : QuasiCompact f)).app
        ((input d X).obj K))
    (scalar_component_isIso d c₁ K) (normalized_component_isIso d r K _hK)
    hn

/-- Common-refinement comparison of the restricted actual strict quotient objects.
Its inverse is taken only after the named finite-origin invertibility theorem.
Source: strict normalization, proof Step 9
(blueprint: lem-pur-strict-reduction-compact-support-normalization). -/
def commonRefinement {X Y : Scheme.{u}} {f : X ⟶ Y}
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    {c₁ c₂ e : Compactification f} (r₁ : e.Refinement c₁) (r₂ : e.Refinement c₂)
    (K : d.derived X)
    (hK : ∀ n : ℕ, Nonempty (ProEtale.StrictTower.ScalarEtaleOrigin A X
      ((ProEtale.StrictTower.ev A X n).obj ((input d X).obj K)))) :
    (exchangeTowerRes d Y).obj
        ((support d c₁).obj ((completedReductionTower X d).obj K)) ≅
      (exchangeTowerRes d Y).obj
        ((support d c₂).obj ((completedReductionTower X d).obj K)) :=
  @asIso _ _ _ _ ((exchangeTowerRes d Y).map (refinement d r₁ K))
      (refinement_isIso d r₁ K hK) ≪≫
    (@asIso _ _ _ _ ((exchangeTowerRes d Y).map (refinement d r₂ K))
      (refinement_isIso d r₂ K hK)).symm

section

-- Keep the common-refinement objects abstract while elaborating their comparisons.
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

/-- The common-refinement comparison is carried to the published normalized one.
Source: strict normalization, proof Steps 8--9; Stacks 0F7F
(blueprint: lem-pur-strict-reduction-compact-support-normalization).
Proof: refinement_normalization applies to both legs of the common refinement.
Invert the second equation and compose. The common interior supportScalar cancels,
leaving the published refinementCommonComparison with the stated endpoint corners. -/
theorem commonRefinement_normalization {X Y : Scheme.{u}} {f : X ⟶ Y}
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    {c₁ c₂ e : Compactification f} (r₁ : e.Refinement c₁) (r₂ : e.Refinement c₂)
    (K : d.derived X)
    (hK : ∀ n : ℕ, Nonempty (ProEtale.StrictTower.ScalarEtaleOrigin A X
      ((ProEtale.StrictTower.ev A X n).obj ((input d X).obj K)))) :
    (commonRefinement d r₁ r₂ K hK).hom ≫
        (supportScalar d c₂).hom.app ((completedReductionTower X d).obj K) =
      (supportScalar d c₁).hom.app ((completedReductionTower X d).obj K) ≫
        (ProEtale.StrictTower.refinementCommonComparison A r₁ r₂
          ((input d X).obj K) hK).hom := by
  sorry

private theorem normalized_common {X Y : Scheme.{u}} {f : X ⟶ Y}
    [IsSeparated f] [LocallyOfFiniteType f] [hf : QuasiCompact f]
    {c₁ c₂ e : Compactification f} (r₁ : e.Refinement c₁) (r₂ : e.Refinement c₂)
    (K : d.derived X)
    (hK : ∀ n : ℕ, Nonempty (ProEtale.StrictTower.ScalarEtaleOrigin A X
      ((ProEtale.StrictTower.ev A X n).obj ((input d X).obj K)))) :
    (commonRefinement d r₁ r₂ K hK).hom ≫
        (supportScalar d c₂).hom.app ((completedReductionTower X d).obj K) =
      (supportScalar d c₁).hom.app ((completedReductionTower X d).obj K) ≫
        (ProEtale.StrictTower.refinementCommonComparison A r₁ r₂
          ((input d X).obj K) hK hf).hom := by
  have hn := commonRefinement_normalization d r₁ r₂ K hK
  rw [refinementCommonComparison_proof_irrel (A := A) r₁ r₂
    ((input d X).obj K) hK hf] at hn
  exact hn

private theorem common_cocycle_transport
    {C : Type*} [Category C] {S₁ S₂ S₃ T₁ T₂ T₃ : C}
    (b₁ : S₁ ≅ T₁) (b₂ : S₂ ≅ T₂) (b₃ : S₃ ≅ T₃)
    (a₁₂ : S₁ ≅ S₂) (a₂₃ : S₂ ≅ S₃) (a₁₃ : S₁ ≅ S₃)
    (e₁₂ : T₁ ≅ T₂) (e₂₃ : T₂ ≅ T₃) (e₁₃ : T₁ ≅ T₃)
    (h₁₂ : a₁₂.hom ≫ b₂.hom = b₁.hom ≫ e₁₂.hom)
    (h₂₃ : a₂₃.hom ≫ b₃.hom = b₂.hom ≫ e₂₃.hom)
    (h₁₃ : a₁₃.hom ≫ b₃.hom = b₁.hom ≫ e₁₃.hom)
    (hc : e₁₂ ≪≫ e₂₃ = e₁₃) : a₁₂ ≪≫ a₂₃ = a₁₃ := by
  apply Iso.ext
  apply (Iso.cancel_iso_hom_right _ _ b₃).1
  simp only [Iso.trans_hom, Category.assoc]
  rw [h₂₃, ← Category.assoc, h₁₂, Category.assoc, h₁₃]
  exact congrArg (fun q ↦ b₁.hom ≫ q) (congrArg (fun e ↦ e.hom) hc)

/-- Common-refinement independence and the common-refinement cocycle use the same corners.
Source: strict normalization, proof Step 9; Stacks 0F7F
(blueprint: lem-pur-strict-reduction-compact-support-normalization).
Proof: apply refinement_normalization to both legs of each common refinement.
The fixed supportScalar at the common vertex cancels. The resulting isomorphism is
refinementCommonComparison. Its independence and cocycle are the corresponding
clauses of refinementExchangeCoherence, transported back along the endpoint corners. -/
theorem commonRefinement_coherence {X Y : Scheme.{u}} {f : X ⟶ Y}
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] (K : d.derived X)
    (hK : ∀ n : ℕ, Nonempty (ProEtale.StrictTower.ScalarEtaleOrigin A X
      ((ProEtale.StrictTower.ev A X n).obj ((input d X).obj K)))) :
    (∀ {c₁ c₂ e e' : Compactification f}
      (r₁ : e.Refinement c₁) (r₂ : e.Refinement c₂)
      (s₁ : e'.Refinement c₁) (s₂ : e'.Refinement c₂),
      commonRefinement d r₁ r₂ K hK = commonRefinement d s₁ s₂ K hK) ∧
    (∀ {c₁ c₂ c₃ e₁₂ e₂₃ e₁₃ : Compactification f}
      (r₁ : e₁₂.Refinement c₁) (r₂ : e₁₂.Refinement c₂)
      (s₂ : e₂₃.Refinement c₂) (s₃ : e₂₃.Refinement c₃)
      (t₁ : e₁₃.Refinement c₁) (t₃ : e₁₃.Refinement c₃),
      commonRefinement d r₁ r₂ K hK ≪≫ commonRefinement d s₂ s₃ K hK =
        commonRefinement d t₁ t₃ K hK) := by
  have hc := ProEtale.StrictTower.refinementExchangeCoherence A (f := f)
    ((input d X).obj K) hK
  constructor
  · intro c₁ c₂ e e' r₁ r₂ s₁ s₂
    have hi := hc.2.2.2.2.1 r₁ r₂ s₁ s₂
    rw [refinementCommonComparison_proof_irrel (A := A) r₁ r₂
      ((input d X).obj K) hK (inferInstance : QuasiCompact f),
      refinementCommonComparison_proof_irrel (A := A) s₁ s₂
      ((input d X).obj K) hK (inferInstance : QuasiCompact f)] at hi
    apply Iso.ext
    apply (NatIso.cancel_natIso_hom_right (supportScalar d c₂) _ _).1
    rw [normalized_common, normalized_common,
      hi]
  · intro c₁ c₂ c₃ e₁₂ e₂₃ e₁₃ r₁ r₂ s₂ s₃ t₁ t₃
    have hi := hc.2.2.2.2.2.1 r₁ r₂ s₂ s₃ t₁ t₃
    rw [refinementCommonComparison_proof_irrel (A := A) r₁ r₂
      ((input d X).obj K) hK (inferInstance : QuasiCompact f),
      refinementCommonComparison_proof_irrel (A := A) s₂ s₃
      ((input d X).obj K) hK (inferInstance : QuasiCompact f),
      refinementCommonComparison_proof_irrel (A := A) t₁ t₃
      ((input d X).obj K) hK (inferInstance : QuasiCompact f)] at hi
    exact common_cocycle_transport
      ((supportScalar d c₁).app ((completedReductionTower X d).obj K))
      ((supportScalar d c₂).app ((completedReductionTower X d).obj K))
      ((supportScalar d c₃).app ((completedReductionTower X d).obj K))
      (commonRefinement d r₁ r₂ K hK) (commonRefinement d s₂ s₃ K hK)
      (commonRefinement d t₁ t₃ K hK)
      (ProEtale.StrictTower.refinementCommonComparison A r₁ r₂
        ((input d X).obj K) hK (inferInstance : QuasiCompact f))
      (ProEtale.StrictTower.refinementCommonComparison A s₂ s₃
        ((input d X).obj K) hK (inferInstance : QuasiCompact f))
      (ProEtale.StrictTower.refinementCommonComparison A t₁ t₃
        ((input d X).obj K) hK (inferInstance : QuasiCompact f))
      (normalized_common d r₁ r₂ K hK) (normalized_common d s₂ s₃ K hK)
      (normalized_common d t₁ t₃ K hK) hi

end

/-- The proper strict compositor is the mate of the canonical pullback compositor.
Source: strict normalization, proof Step 6; Stacks 07A7
(blueprint: lem-pur-strict-reduction-compact-support-normalization). -/
def pushComp {U V W : Scheme.{u}} (h : U ⟶ V) (g : V ⟶ W) :
    d.towerPush h ⋙ d.towerPush g ≅ d.towerPush (h ≫ g) :=
  conjugateIsoEquiv ((d.towerAdjunction g).comp (d.towerAdjunction h))
    (d.towerAdjunction (h ≫ g)) (pullComp d h g)

/-- The normalized proper scalar comparisons respect the direct-image compositor.
Together with scalarPull_composition this fixes both proper b,d corners for a,b,ab.
Source: strict normalization, proof Step 6; Stacks 0D6D and 07A7
(blueprint: lem-pur-strict-reduction-compact-support-normalization).
Proof: exchangeResPush is the mate of exchangeResPull, with its underived identity
on K-injective diagrams. Direct image preserves K-injectives because its left adjoint
is exact. Both successive comparisons are thus that same underived identity. Taking
mates of scalarPull_composition gives the displayed direct-image equation. -/
theorem scalarPush_composition {U V W : Scheme.{u}} (h : U ⟶ V) (g : V ⟶ W) :
    (exchangeResPush d (h ≫ g)).hom ≫
        Functor.whiskerLeft (exchangeTowerRes d U) (ProEtale.StrictTower.rComp A h g).inv =
      Functor.whiskerRight (pushComp d h g).inv (exchangeTowerRes d W) ≫
        Functor.whiskerLeft (d.towerPush h) (exchangeResPush d g).hom ≫
        Functor.whiskerRight (exchangeResPush d h).hom (ProEtale.StrictTower.R A g) := by
  sorry

/-- Source kappa uses exactly the open quotient transport in strict refinements.
Source: strict normalization, proof Steps 3 and 8
(blueprint: lem-pur-strict-reduction-compact-support-normalization).
Proof: expand exchangeCornerB and supportScalar. Naturality of exchangeResPull and
exchangeResPush moves the same quotient/open map through the proper and inverse images.
Associativity then gives the displayed equation of specified maps. -/
theorem kappaSource_reduction (c : Compactification f) (K : d.derived X) :
    (exchangeTowerRes d Y').map (sourceReduction d (g := g) c K).hom ≫
        (exchangeResPull d g).hom.app
          ((support d c).obj ((completedReductionTower X d).obj K)) ≫
        (ProEtale.StrictTower.G A g).map
          ((supportScalar d c).hom.app ((completedReductionTower X d).obj K)) =
      (kappaSource d (g := g) c K).hom := by
  have hn := (exchangeCornerB d c.g g).hom.naturality
    (cbcRealizationReduction d c.i K).hom
  have ht := congrArg (fun q ↦ q ≫ (ProEtale.StrictTower.G A g).map
    ((ProEtale.StrictTower.R A c.g).map
      ((cbcRealizationTowerScalarOpen d c.i).hom.app
        ((completedReductionTower X d).obj K)))) hn
  simpa only [sourceReduction, supportScalar, kappaSource, exchangeCornerB,
    cbcRealizationQuotientOpen, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.comp_map,
    Functor.associator_hom_app, Functor.associator_inv_app, Iso.symm_hom,
    Category.id_comp, Category.comp_id, Functor.map_comp, Functor.map_id,
    ProEtale.StrictTower.compositionF, constantPull_map, constantPush_map, cbcJ, Functor.comp_obj,
    input, source, Category.assoc] using ht

/-- The specified source kappa transports the strict source refinement.
Source: strict normalization, proof Steps 8--9
(blueprint: lem-pur-strict-reduction-compact-support-normalization).
Proof: use kappaSource_reduction at both endpoints. Naturality of exchangeResPull
moves the strict refinement across scalar pullback. Apply refinement_normalization
and cancel the identical open quotient corners, giving exactly this equality. -/
theorem sourceRefinement_normalization [QuasiCompact f]
    {c₁ c₂ : Compactification f} (r : c₁.Refinement c₂) (K : d.derived X) :
    (exchangeTowerRes d Y').map (sourceRefinement d (g := g) r K) ≫
        (kappaSource d (g := g) c₁ K).hom =
      (kappaSource d (g := g) c₂ K).hom ≫
        (ProEtale.StrictTower.G A g).map
          ((ProEtale.StrictTower.refinementComparison A r).app ((input d X).obj K)) := by
  rw [refinementComparison_proof_irrel (A := A) r
    (inferInstance : QuasiCompact f)]
  have hn := refinement_normalization d r K
  rw [refinementComparison_proof_irrel (A := A) r
    (inferInstance : QuasiCompact f)] at hn
  apply source_corner_transport (exchangeTowerRes d Y')
    (sourceReduction d (g := g) c₁ K) (sourceReduction d (g := g) c₂ K)
    ((exchangeResPull d g).hom.app _ ≫
      (ProEtale.StrictTower.G A g).map ((supportScalar d c₁).hom.app _))
    ((exchangeResPull d g).hom.app _ ≫
      (ProEtale.StrictTower.G A g).map ((supportScalar d c₂).hom.app _))
    (kappaSource d (g := g) c₁ K).hom (kappaSource d (g := g) c₂ K).hom
    (kappaSource_reduction d (g := g) c₁ K) (kappaSource_reduction d (g := g) c₂ K)
    ((d.towerPull g).map (refinement d r K))
    ((ProEtale.StrictTower.G A g).map
      ((ProEtale.StrictTower.refinementComparison A r (inferInstance : QuasiCompact f)).app
        ((input d X).obj K)))
  simpa only [Category.assoc] using
    scalar_map_square (d.towerPull g) (exchangeTowerRes d Y) (exchangeTowerRes d Y')
    (ProEtale.StrictTower.G A g) (exchangeResPull d g) (refinement d r K)
    ((supportScalar d c₂).hom.app ((completedReductionTower X d).obj K))
    ((supportScalar d c₁).hom.app ((completedReductionTower X d).obj K))
    ((ProEtale.StrictTower.refinementComparison A r (inferInstance : QuasiCompact f)).app
      ((input d X).obj K))
    hn

/-- The target compositor uses the same reduction corner on the intermediate input.
Source: strict normalization, proof Steps 6--7
(blueprint: lem-pur-strict-reduction-compact-support-normalization). -/
def targetComp {X'' Y'' : Scheme.{u}} {f'' : X'' ⟶ Y''}
    (h : X'' ⟶ X') (c'' : Compactification f'') (K : d.derived X) :
    target d (g' := h ≫ g') c'' K ≅
      target d (g' := h) c'' ((d.pull g').obj K) :=
  targetReduction d c'' K ≪≫
    (support d c'').mapIso
      ((completedReductionTower X'' d).mapIso ((d.pullComp h g').app K)) ≪≫
    (targetReduction d c'' ((d.pull g').obj K)).symm

private theorem target_compositor
    {C D E H : Type*} [Category C] [Category D] [Category E] [Category H]
    (S : C ⥤ E) (R : C ⥤ D) (res : E ⥤ H) (F : D ⥤ H)
    (b : S ⋙ res ≅ R ⋙ F) {L₀ L₁ : C} (a : L₀ ≅ L₁)
    {Q₀ Q₁ : E} (e₀ : Q₀ ≅ S.obj L₀) (e₁ : Q₁ ≅ S.obj L₁)
    {M₀ M₁ : D} (i₀ : M₀ ≅ R.obj L₀) (i₁ : M₁ ≅ R.obj L₁)
    (k₀ : res.obj Q₀ ≅ F.obj M₀) (k₁ : res.obj Q₁ ≅ F.obj M₁)
    (h₀ : res.map e₀.hom ≫ b.hom.app L₀ = k₀.hom ≫ F.map i₀.hom)
    (h₁ : res.map e₁.hom ≫ b.hom.app L₁ = k₁.hom ≫ F.map i₁.hom)
    (c : M₀ ⟶ M₁) (hc : c ≫ i₁.hom = i₀.hom ≫ R.map a.hom) :
    res.map (e₀.hom ≫ S.map a.hom ≫ e₁.inv) ≫ k₁.hom = k₀.hom ≫ F.map c := by
  apply (cancel_mono (F.map i₁.hom)).1
  have he : res.map e₁.inv ≫ k₁.hom ≫ F.map i₁.hom = b.hom.app L₁ := by
    rw [← h₁, ← Category.assoc, ← res.map_comp, e₁.inv_hom_id,
      res.map_id, Category.id_comp]
  have hn := b.hom.naturality a.hom
  dsimp only [Functor.comp_map] at hn
  simp only [Functor.map_comp, Category.assoc]
  rw [he, hn, ← Category.assoc, h₀]
  simp only [Category.assoc, ← F.map_comp, ← hc]

/-- The target kappa for the composite is the successive target corner.
Source: strict normalization, proof Steps 6--7; Stacks 07A4 and 07A7
(blueprint: lem-pur-strict-reduction-compact-support-normalization).
Proof: substitute kappaTarget_reduction at both ends of targetComp. Apply
inputPull_composition to its input. Naturality of supportScalar moves the ordinary
pullback compositor through the support functor; the identical intermediate reduction
corner and its inverse cancel. This gives equality before any finite evaluation. -/
theorem kappaTarget_composition {X'' Y'' : Scheme.{u}} {f'' : X'' ⟶ Y''}
    (h : X'' ⟶ X') (c'' : Compactification f'') (K : d.derived X) :
    (exchangeTowerRes d Y'').map (targetComp d (g' := g') h c'' K).hom ≫
        (kappaTarget d (g' := h) c'' ((d.pull g').obj K)).hom =
      (kappaTarget d (g' := h ≫ g') c'' K).hom ≫
        (ProEtale.StrictTower.compositionF A c'').map
          ((ProEtale.StrictTower.gComp A h g').hom.app ((input d X).obj K) ≫
            (ProEtale.StrictTower.G A h).map (inputPull d g' K).hom) := by
  exact target_compositor
      (completedReductionTower X'' d ⋙ support d c'') (input d X'')
      (exchangeTowerRes d Y'') (ProEtale.StrictTower.compositionF A c'')
      (Functor.isoWhiskerLeft (completedReductionTower X'' d) (supportScalar d c''))
      ((d.pullComp h g').app K) (targetReduction d (g' := h ≫ g') c'' K)
      (targetReduction d (g' := h) c'' ((d.pull g').obj K))
      (inputPull d (h ≫ g') K) (inputPull d h ((d.pull g').obj K))
      (kappaTarget d (g' := h ≫ g') c'' K) (kappaTarget d (g' := h) c'' ((d.pull g').obj K))
      (kappaTarget_reduction d (g' := h ≫ g') c'' K)
      (kappaTarget_reduction d (g' := h) c'' ((d.pull g').obj K))
      ((ProEtale.StrictTower.gComp A h g').hom.app ((input d X).obj K) ≫
        (ProEtale.StrictTower.G A h).map (inputPull d g' K).hom)
      (by simpa only [Category.assoc, Iso.app_hom] using
        inputPull_composition d h g' K)

end AlgebraicGeometry.Scheme.StrictSupportNormalization

attribute [instance] WeilConjectures.IntegralHom.derivedCategory
