/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.StrictTower.StrictTowerCompositionMaps

public import WeilConjectures.AlgebraicGeometry.Strict.Tower.StrictTowerExchangeMateNormalization

public import WeilConjectures.AlgebraicGeometry.AdicCoefficientDatum.CompletedOrdinaryComparisons

public import WeilConjectures.AlgebraicGeometry.Completed.CompletedStrictOpenExchange

public import WeilConjectures.AlgebraicGeometry.Complete.CompleteProetaleStrictTowerRealization

public import WeilConjectures.AlgebraicGeometry.SmoothPurity.CompactifiableCompatibleTower

public import WeilConjectures.AlgebraicGeometry.StrictTower.StrictTowerProperOpenCalculus

public import WeilConjectures.AlgebraicGeometry.Completed.Open.CompletedOpenExchangeTransport

public import WeilConjectures.AlgebraicGeometry.AdicCoefficientDatum.CompletedDirectImageLimits

public import WeilConjectures.AlgebraicGeometry.WeilSheaf.ProfiniteCoefficientInverseImageSupplement

public import WeilConjectures.AlgebraicGeometry.ChosenCartesianSquare
public import Mathlib.AlgebraicGeometry.Pullbacks
public import WeilConjectures.SixFunctors.BaseChange.Square

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityFiniteSetting
public import WeilConjectures.AlgebraicGeometry.Pur.PurCompletedReductionReindexing
public import WeilConjectures.AlgebraicGeometry.Completed.CompletedCompactSupportExchange
public import WeilConjectures.AlgebraicGeometry.Complete.CompleteCompactSupportProetale
public import WeilConjectures.AlgebraicGeometry.Completed.Open.CompletedOpenStrictMateIdentification
public import WeilConjectures.AlgebraicGeometry.StrictTower.StrictTowerCompositionPasting
public import WeilConjectures.Compactification.RefinementCategory
public import WeilConjectures.AlgebraicGeometry.Completed.CompletedRingStrictFiniteExchange

/-! # Strict integral exchange equals isomorphism reindexing

Source: blueprint sec-six-functors/sk-thm-sf-package,
prop-pur-weil-equivariance-compatibilities.proof.md, constituent compatibility,
extracted semilinear-exchange steps 12--14
(blueprint: def-pur-strict-integral-exchange-data).

All reduction objects are derived objects of actual strict tower categories.
The named predicates expand the clauses of this single normalization statement.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe t
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

variable {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A)

/-- The ordinary proper-then-open reindexing transformation, with beta defined by
its inverse open-unit transpose. Source: constituent compatibility, steps 7--9
(blueprint: def-pur-strict-integral-exchange-data). -/
def purIntegralReindexingExchange
    {X' X Y' Y : Scheme.{t}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {g : Y' ⟶ Y} {g' : X' ⟶ X}
    (c : Compactification f) (c' : Compactification f') (gb : c'.Z ⟶ c.Z)
    (sp : ChosenCartesianSquare gb c'.g c.g g)
    (sj : OpenImmersionSquare g' c'.i c.i gb) :
    cbcSupport d c ⋙ d.pull g ⟶ d.pull g' ⋙ cbcSupport d c' :=
  Functor.whiskerLeft (cbcJ d c.i) (purReindexingDerivedMate d sp) ≫
    Functor.whiskerRight
      (cbcBeta d g' c'.i c.i gb sj.w
        (IsPullback.of_iso_pullback sj.toCommSq sj.isoPullback sj.hom_fst sj.hom_snd)).hom
      (d.push c'.g)

/-- The two strict identities with precisely the specified H and H prime, and the
proper comparison with precisely the ordinary-to-completed quotient units. The
last equation is equivalent to the reconstructed proper factor being r_M, because
those units are invertible on the complete domain.
Source: constituent compatibility, steps 1--6
(blueprint: def-pur-strict-integral-exchange-data). -/
def PurIntegralProperNormalization
    {X' X Y' Y : Scheme.{t}} {v : X' ⟶ X} {p' : X' ⟶ Y'}
    {p : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : ChosenCartesianSquare v p' p g) (M : d.derived X) : Prop :=
  (exchangeRealizationH (f := p) (g := g) d M).hom ≫
      (purReindexingRingedSquare d sq).exchangeTowerMate.app
        ((completedReductionTower X d).obj M) =
    (completedReductionTower Y' d).map ((purReindexingDerivedMate d sq).app M) ≫
      (exchangeRealizationHPrime (f' := p') (g' := v) d M).hom ∧
  d.towerV' sq M = (purReindexingRingedSquare d sq).exchangeTowerMate.app
    ((completedReductionTower X d).obj M) ∧
  IsIso (d.ordinaryToCompleted g ((d.push p).obj M)) ∧
  IsIso (d.ordinaryToCompleted v M) ∧
  d.ordinaryToCompleted g ((d.push p).obj M) ≫ d.completedExchange sq M =
    (purReindexingDerivedMate d sq).app M ≫
      (d.push p').map (d.ordinaryToCompleted v M)

/-- Open and total normalization use the actual completed maps. The ordinary beta
is literally the inverse of cbcBetaInv, the transpose of the pulled-back open unit.
The last equation is equality of the natural transformations componentwise on the
entire complete domain, not just an equation after finite evaluation.
Source: constituent compatibility, steps 7--9
(blueprint: def-pur-strict-integral-exchange-data). -/
def PurIntegralSupportNormalization
    {X' X Y' Y : Scheme.{t}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {g : Y' ⟶ Y} {g' : X' ⟶ X} [QuasiCompact f]
    (c : Compactification f) (c' : Compactification f') (gb : c'.Z ⟶ c.Z)
    (sp : ChosenCartesianSquare gb c'.g c.g g)
    (sj : OpenImmersionSquare g' c'.i c.i gb)
    (r : ℕ) (a : Fin r → A) (ha : Ideal.span (Set.range a) = d.ideal)
    (K : (cbcCompleteProperty d X r a ha).FullSubcategory) : Prop :=
  PurIntegralProperNormalization d sp ((cbcJ d c.i).obj K.obj) ∧
  IsIso (d.ordinaryToCompleted g' K.obj) ∧
  (cbcDatumOrdinaryExchange d sj).app K.obj =
    (cbcBeta d g' c'.i c.i gb sj.w
      (IsPullback.of_iso_pullback sj.toCommSq sj.isoPullback sj.hom_fst sj.hom_snd)).hom.app
        K.obj ∧
  d.ordinaryToCompleted gb ((cbcJ d c.i).obj K.obj) ≫
      cbcRealizationOpenFactor d c c' gb sj r a ha K =
    (cbcBeta d g' c'.i c.i gb sj.w
      (IsPullback.of_iso_pullback sj.toCommSq sj.isoPullback sj.hom_fst sj.hom_snd)).hom.app
        K.obj ≫ (cbcJ d c'.i).map (d.ordinaryToCompleted g' K.obj) ∧
  d.ordinaryToCompleted g ((cbcSupport d c).obj K.obj) ≫
      completedCompactSupportExchange d c c' gb sp sj r a ha K =
    (purIntegralReindexingExchange d c c' gb sp sj).app K.obj ≫
      (cbcSupport d c').map (d.ordinaryToCompleted g' K.obj)

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme.PurIntegralTower

variable {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A)

/-- Canonical pullback compositor on actual completed-ring strict towers, obtained
by applying the ordinary tensor comparison to the entire diagram and localizing.
Source: constituent compatibility, steps 10--12
(blueprint: def-pur-strict-integral-exchange-data). -/
def pullComp {U V W : Scheme.{t}} (h : U ⟶ V) (g : V ⟶ W) :
    d.towerPull (h ≫ g) ≅ d.towerPull g ⋙ d.towerPull h :=
  Functor.mapDerivedCategoryNatIso
    ((Functor.whiskeringRight ℕᵒᵖ _ _).mapIso
      (eqToIso (congrArg
        (proEtaleRingModulePullback (h ≫ g) (d.completedRing W) (d.completedRing U))
          (d.integralRingIso_comp h g)) ≪≫
        exchangeModuleComposition h g (d.completedRing W) (d.completedRing V)
          (d.completedRing U) (d.integralRingIso g) (d.integralRingIso h))) ≪≫
    Functor.mapDerivedCategoryCompIso (d.towerModulePull g) (d.towerModulePull h)

/-- Identity pullback on strict towers, normalized by the ordinary section unit.
Source: constituent compatibility, step 10
(blueprint: def-pur-strict-integral-exchange-data). -/
def pullId (T : Scheme.{t}) : d.towerPull (𝟙 T) ≅ 𝟭 _ :=
  Functor.mapDerivedCategoryNatIso
    ((Functor.whiskeringRight ℕᵒᵖ _ _).mapIso
      ((proEtaleRingModuleAdjunction (𝟙 T) (d.completedRing T) (d.completedRing T)
        (d.integralRingIso (𝟙 T))).leftAdjointIdIso (d.modulePushId T))) ≪≫
    Functor.mapDerivedCategoryIdIso _

/-- The proper direct-image compositor is the conjugate of that same pullback
compositor, with the specified strict adjunctions. Source: steps 11--12
(blueprint: def-pur-strict-integral-exchange-data). -/
def pushComp {U V W : Scheme.{t}} (h : U ⟶ V) (g : V ⟶ W) :
    d.towerPush h ⋙ d.towerPush g ≅ d.towerPush (h ≫ g) :=
  conjugateIsoEquiv ((d.towerAdjunction g).comp (d.towerAdjunction h))
    (d.towerAdjunction (h ≫ g)) (pullComp d h g)

/-- The published strict open comparison transported to the datum's exact
pullback presentation, without changing its representative or unit normalization.
Source: constituent compatibility, steps 7, 10 and 11
(blueprint: def-pur-strict-integral-exchange-data). -/
def beta {U' U T' T : Scheme.{t}} {v : U' ⟶ U} {j' : U' ⟶ T'}
    {j : U ⟶ T} {g : T' ⟶ T} [IsOpenImmersion j] [IsOpenImmersion j']
    (sq : OpenImmersionSquare v j' j g) :
    cbcRealizationJ d j ⋙ d.towerPull g ≅ d.towerPull v ⋙ cbcRealizationJ d j' :=
  Functor.isoWhiskerLeft (cbcRealizationJ d j) (cbcDatumTowerTransport d g).symm ≪≫
    cbcStrictExchange d sq ≪≫
    Functor.isoWhiskerRight (cbcDatumTowerTransport d v) (cbcRealizationJ d j')

/-- The already chosen open square associated with a Cartesian square of opens.
Source: constituent compatibility, compatible tower in step 11
(blueprint: def-pur-strict-integral-exchange-data). -/
def openSquare {U' U T' T : Scheme.{t}} {v : U' ⟶ U} {j' : U' ⟶ T'}
    {j : U ⟶ T} {g : T' ⟶ T} [IsOpenImmersion j] [IsOpenImmersion j']
    (sq : IsPullback v j' j g) : OpenImmersionSquare v j' j g where
  w := sq.w
  isoPullback := sq.isoPullback
  hom_fst := sq.isoPullback_hom_fst
  hom_snd := sq.isoPullback_hom_snd
  isOpenImmersion := inferInstance
  isOpenImmersion' := inferInstance

/-- Strict-tower compact support for the supplied compactification.
Source: constituent compatibility, step 12
(blueprint: def-pur-strict-integral-exchange-data). -/
abbrev support {X Y : Scheme.{t}} {f : X ⟶ Y} (c : Compactification f) :=
  cbcRealizationJ d c.i ⋙ d.towerPush c.g

/-- The canonical completed-ring pullback square, on whole strict towers.
Source: constituent compatibility, steps 10--12
(blueprint: def-pur-strict-integral-exchange-data). -/
def square {V W S T : Scheme.{t}} (k : V ⟶ W) (r : V ⟶ S)
    (p : W ⟶ T) (i : S ⟶ T) (w : k ≫ p = r ≫ i) :
    d.towerPull i ⋙ d.towerPull r ≅ d.towerPull p ⋙ d.towerPull k :=
  (pullComp d r i).symm ≪≫
    eqToIso (congrArg (fun f ↦ d.towerPull f) w.symm) ≪≫ pullComp d k p

/-- Strict completed-ring proper reindexing followed by the strict open comparison.
Source: constituent compatibility, steps 10--12
(blueprint: def-pur-strict-integral-exchange-data). -/
def exchange {X' X Y' Y : Scheme.{t}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    (c : Compactification f) (c' : Compactification f')
    (x : X' ⟶ X) (y : Y' ⟶ Y) (s : c'.Z ⟶ c.Z)
    (_wi : x ≫ c.i = c'.i ≫ s) (wp : s ≫ c.g = c'.g ≫ y)
    (si : IsPullback x c'.i c.i s) :
    support d c ⋙ d.towerPull y ⟶ d.towerPull x ⋙ support d c' :=
  Functor.whiskerLeft (cbcRealizationJ d c.i)
      (mateEquiv (d.towerAdjunction c.g) (d.towerAdjunction c'.g)
        (square d s c'.g c.g y wp).hom) ≫
    Functor.whiskerRight (beta d (openSquare si)).hom (d.towerPush c'.g)

/-- Equality transport for the already specified strict open extension.
Source: constituent compatibility, step 12
(blueprint: def-pur-strict-integral-exchange-data). -/
def openCongr {U T : Scheme.{t}} {j k : U ⟶ T}
    [IsOpenImmersion j] [IsOpenImmersion k] (h : j = k) :
    cbcRealizationJ d j ≅ cbcRealizationJ d k := by
  subst k
  exact Iso.refl _

/-- The compatible-tower composition map R_q Gamma_Q J_c, on completed-ring
strict diagrams. Gamma_Q is the proper mate of the specified strict open beta.
Source: constituent compatibility, steps 11--12
(blueprint: def-pur-strict-integral-exchange-data). -/
def composition {X Y Z : Scheme.{t}} {f : X ⟶ Y} {h : Y ⟶ Z}
    (T : Compactification.Triangle f h) :
    support d T.cf ⋙ support d T.cg ⟶ support d T.cfg :=
  Functor.whiskerLeft (cbcRealizationJ d T.cf.i)
    (Functor.whiskerRight
      (mateEquiv (d.towerAdjunction T.cf.g) (d.towerAdjunction T.p)
        (beta d (openSquare T.isPullback)).hom) (d.towerPush T.cg.g)) ≫
    Functor.whiskerRight
      ((Adjunction.leftAdjointCompIso (cbcRealizationTowerAdj d T.cf.i)
        (cbcRealizationTowerAdj d T.q) (cbcRealizationTowerAdj d (T.cf.i ≫ T.q))
        (pullComp d T.cf.i T.q).symm).hom ≫
        (openCongr d T.i_q).hom)
      (d.towerPush T.p ⋙ d.towerPush T.cg.g) ≫
    Functor.whiskerLeft (cbcRealizationJ d T.cfg.i)
      ((pushComp d T.p T.cg.g).hom ≫
        (eqToIso (congrArg (fun f ↦ d.towerPush f) T.p_g)).hom)

/-- Reduction of compact support, with the open tensor mate followed by the
inverse proper projection mate. Source: constituent compatibility, steps 7, 13--14;
coefficient comparisons of lem-fix-operation-reduction
(blueprint: def-pur-strict-integral-exchange-data). -/
def supportReduction {X Y : Scheme.{t}} {f : X ⟶ Y}
    (c : Compactification f) (K : d.derived X) :
    (support d c).obj ((completedReductionTower X d).obj K) ≅
      (completedReductionTower Y d).obj ((cbcSupport d c).obj K) :=
  (d.towerPush c.g).mapIso (cbcRealizationReduction d c.i K).symm ≪≫
    (asIso (d.towerProjection c.g ((cbcJ d c.i).obj K))).symm

/-- Source corner for reduction of strict compact-support exchange. The order is
support reduction, then the fixed pullback/tensor comparison. Source: steps 13--14
(blueprint: def-pur-strict-integral-exchange-data). -/
def exchangeReductionSource {X Y Y' : Scheme.{t}} {f : X ⟶ Y}
    (c : Compactification f) (g : Y' ⟶ Y) (K : d.derived X) :=
  (d.towerPull g).mapIso (supportReduction d c K) ≪≫
    (d.reductionTowerPullbackIso g).app ((cbcSupport d c).obj K)

/-- Target corner for reduction of strict compact-support exchange. Source:
steps 13--14, with the same tensor comparisons as lem-fix-operation-reduction
(blueprint: def-pur-strict-integral-exchange-data). -/
def exchangeReductionTarget {X' X Y' : Scheme.{t}} {f' : X' ⟶ Y'}
    (c' : Compactification f') (g' : X' ⟶ X) (K : d.derived X) :=
  (support d c').mapIso ((d.reductionTowerPullbackIso g').app K) ≪≫
    supportReduction d c' ((d.pull g').obj K)

/-- Source corner for reduction of the compatible-tower composition map. Both
compact-support reductions are the fixed proper/open mates. Source: steps 13--14
(blueprint: def-pur-strict-integral-exchange-data). -/
def compositionReductionSource {X Y Z : Scheme.{t}} {f : X ⟶ Y} {h : Y ⟶ Z}
    (T : Compactification.Triangle f h) (K : d.derived X) :=
  (support d T.cg).mapIso (supportReduction d T.cf K) ≪≫
    supportReduction d T.cg ((cbcSupport d T.cf).obj K)

/-- Evaluate a specified strict corner using the fixed K-flat quotient comparison.
The target retains the actual P_(n+1) scalar action under restriction. Source:
steps 13--14; lem-fix-operation-reduction, tensor and adjunction normalization
(blueprint: def-pur-strict-integral-exchange-data). -/
def finiteCorner {T : Scheme.{t}} {N : DerivedCategory (d.towers T)}
    {K : d.derived T} (e : N ≅ (completedReductionTower T d).obj K) (n : ℕ) :
    (reductionTowerDerivedEvaluation T
        (reductionModuleRing T (d.completedRing T)) n).obj N ≅
      (reductionDerivedRestrict T (d.projection T n)).obj ((d.reduction T n).obj K) :=
  (reductionTowerDerivedEvaluation T (reductionModuleRing T (d.completedRing T)) n).mapIso e ≪≫
    (asIso (completedReductionEvaluation T d n)).app K

/-- The four finite corners fixed by tensor balancing, projection and chi, in
that order. This is data, with no existential choice of corner isomorphisms.
Source: steps 13--14 (blueprint: def-pur-strict-integral-exchange-data). -/
def properFiniteCorner
    {X' X Y' Y : Scheme.{t}} {v : X' ⟶ X} {p' : X' ⟶ Y'}
    {p : X ⟶ Y} {g : Y' ⟶ Y} [IsProper p]
    (sq : ChosenCartesianSquare v p' p g) (M : d.derived X)
    (hM : d.TowerComplete X M)
    (W : ∀ n : ℕ, FiniteEtaleOriginWitness X (A ⧸ d.ideal ^ (n + 1))
      ((d.reduction X n).obj M)) (n : ℕ) (i : Fin 4) :
    (reductionTowerDerivedEvaluation Y'
        (reductionModuleRing Y' (d.completedRing Y')) n).obj
      (d.fourTowerCorners (f := p) (f' := p') (g := g) (g' := v) M i) ≅
    (reductionDerivedRestrict Y' (d.projection Y' n)).obj
      (d.fourCorners (f := p) (f' := p') (g := g) (g' := v) M n i) :=
  match i with
  | 0 => finiteCorner d ((d.reductionTowerPullbackIso g).app ((d.push p).obj M)) n ≪≫
      (reductionDerivedRestrict Y' (d.projection Y' n)).mapIso
        ((d.chi g n).symm.app ((d.push p).obj M))
  | 1 => (reductionTowerDerivedEvaluation Y'
        (reductionModuleRing Y' (d.completedRing Y')) n).mapIso
        (d.towerH (f := p) (f' := p') (g := g) (g' := v) M).symm ≪≫
      finiteCorner d ((d.reductionTowerPullbackIso g).app ((d.push p).obj M)) n ≪≫
      (reductionDerivedRestrict Y' (d.projection Y' n)).mapIso
        (((d.chi g n).symm.app ((d.push p).obj M)) ≪≫ (d.fourArrows sq M hM W n).h)
  | 2 => (asIso (completedReductionEvaluation Y' d n)).app
      ((d.push p').obj ((d.pull v).obj M))
  | 3 => (reductionTowerDerivedEvaluation Y'
        (reductionModuleRing Y' (d.completedRing Y')) n).mapIso
        (d.towerH' (f := p) (f' := p') (g := g) (g' := v) M).symm ≪≫
      (asIso (completedReductionEvaluation Y' d n)).app
        ((d.push p').obj ((d.pull v).obj M)) ≪≫
      (reductionDerivedRestrict Y' (d.projection Y' n)).mapIso
        (d.fourArrows sq M hM W n).h'

end AlgebraicGeometry.Scheme.PurIntegralTower

namespace AlgebraicGeometry.Scheme
open ProEtale.StrictTower
variable {A : Type (t + 1)} [CommRing A]

/-- The completed-ring tower maps retain their two adjunction normalizations.
In particular these identify the strict maps used in pasting with the proper
reindexing mate and the inverse-open-unit transpose used in the normalization.
Source: constituent compatibility, steps 3, 7 and 11
(blueprint: def-pur-strict-integral-exchange-data). -/
def PurIntegralStrictMapNormalization (d : AdicCoefficientDatum A) (S : Scheme.{t}) : Prop :=
  (∀ {X' X Y' Y : Scheme.{t}} {v : X' ⟶ X} {p' : X' ⟶ Y'}
      {p : X ⟶ Y} {g : Y' ⟶ Y}
      [X.Over S] [IsSeparated (X ↘ S)]
      [LocallyOfFiniteType (X ↘ S)] [QuasiCompact (X ↘ S)]
      [Y.Over S] [IsSeparated (Y ↘ S)]
      [LocallyOfFiniteType (Y ↘ S)] [QuasiCompact (Y ↘ S)]
      [p.IsOver S]
      [IsIso v] [IsIso g]
      (sq : ChosenCartesianSquare v p' p g),
    mateEquiv (d.towerAdjunction p) (d.towerAdjunction p')
        (PurIntegralTower.square d v p' p g sq.w).hom =
      (purReindexingRingedSquare d sq).exchangeTowerMate) ∧
  (∀ {U' U T' T : Scheme.{t}} {v : U' ⟶ U} {j' : U' ⟶ T'}
      {j : U ⟶ T} {g : T' ⟶ T}
      [U.Over S] [IsSeparated (U ↘ S)]
      [LocallyOfFiniteType (U ↘ S)] [QuasiCompact (U ↘ S)]
      [T.Over S] [IsSeparated (T ↘ S)]
      [LocallyOfFiniteType (T ↘ S)] [QuasiCompact (T ↘ S)]
      [j.IsOver S]
      [IsOpenImmersion j] [IsOpenImmersion j']
      (sq : OpenImmersionSquare v j' j g),
    (PurIntegralTower.beta d sq).inv =
      (((cbcRealizationTowerAdj d j').whiskerRight _).homEquiv _ _).symm
        ((Functor.leftUnitor (d.towerPull v)).inv ≫
          Functor.whiskerRight (cbcRealizationTowerAdj d j).unit (d.towerPull v) ≫
          (Functor.associator (cbcRealizationJ d j) (d.towerPull j)
            (d.towerPull v)).hom ≫
          Functor.whiskerLeft (cbcRealizationJ d j)
            (PurIntegralTower.square d v j' j g sq.w).inv ≫
          (Functor.associator (cbcRealizationJ d j) (d.towerPull g)
            (d.towerPull j')).inv))

/-- Identity and successive base changes for the strict proper-then-open maps.
The equations are on whole strict towers with the canonical pullback compositors.
Source: constituent compatibility, step 10
(blueprint: def-pur-strict-integral-exchange-data). -/
def PurIntegralStrictHorizontal (d : AdicCoefficientDatum A) (S : Scheme.{t}) : Prop :=
  (∀ {X Y : Scheme.{t}} {f : X ⟶ Y}
      [X.Over S] [IsSeparated (X ↘ S)]
      [LocallyOfFiniteType (X ↘ S)] [QuasiCompact (X ↘ S)]
      [Y.Over S] [IsSeparated (Y ↘ S)]
      [LocallyOfFiniteType (Y ↘ S)] [QuasiCompact (Y ↘ S)]
      [f.IsOver S]
      (c : Compactification f)
      (wi : (𝟙 X) ≫ c.i = c.i ≫ (𝟙 c.Z))
      (wp : (𝟙 c.Z) ≫ c.g = c.g ≫ (𝟙 Y))
      (si : IsPullback (𝟙 X) c.i c.i (𝟙 c.Z)) (M : DerivedCategory (d.towers X)),
    (PurIntegralTower.exchange d c c (𝟙 X) (𝟙 Y) (𝟙 c.Z) wi wp si).app M ≫
        (PurIntegralTower.support d c).map ((PurIntegralTower.pullId d X).hom.app M) =
      (PurIntegralTower.pullId d Y).hom.app ((PurIntegralTower.support d c).obj M)) ∧
  (∀ {X X' X'' Y Y' Y'' : Scheme.{t}}
      {f : X ⟶ Y} {f' : X' ⟶ Y'} {f'' : X'' ⟶ Y''}
      [X.Over S] [IsSeparated (X ↘ S)]
      [LocallyOfFiniteType (X ↘ S)] [QuasiCompact (X ↘ S)]
      [Y.Over S] [IsSeparated (Y ↘ S)]
      [LocallyOfFiniteType (Y ↘ S)] [QuasiCompact (Y ↘ S)]
      [f.IsOver S]
      (c : Compactification f) (c' : Compactification f') (c'' : Compactification f'')
      (x : X' ⟶ X) (y : Y' ⟶ Y) (s : c'.Z ⟶ c.Z)
      (x' : X'' ⟶ X') (y' : Y'' ⟶ Y') (s' : c''.Z ⟶ c'.Z)
      [IsIso x] [IsIso y] [IsIso s] [IsIso x'] [IsIso y'] [IsIso s']
      (wi : x ≫ c.i = c'.i ≫ s) (wp : s ≫ c.g = c'.g ≫ y)
      (si : IsPullback x c'.i c.i s)
      (wi' : x' ≫ c'.i = c''.i ≫ s') (wp' : s' ≫ c'.g = c''.g ≫ y')
      (si' : IsPullback x' c''.i c'.i s')
      (wio : (x' ≫ x) ≫ c.i = c''.i ≫ (s' ≫ s))
      (wpo : (s' ≫ s) ≫ c.g = c''.g ≫ (y' ≫ y))
      (sio : IsPullback (x' ≫ x) c''.i c.i (s' ≫ s)) (M : DerivedCategory (d.towers X)),
    (PurIntegralTower.pullComp d y' y).hom.app ((PurIntegralTower.support d c).obj M) ≫
        (d.towerPull y').map ((PurIntegralTower.exchange d c c' x y s wi wp si).app M) ≫
        (PurIntegralTower.exchange d c' c'' x' y' s' wi' wp' si').app ((d.towerPull x).obj M) =
      (PurIntegralTower.exchange d c c'' (x' ≫ x) (y' ≫ y) (s' ≫ s) wio wpo sio).app M ≫
        (PurIntegralTower.support d c'').map ((PurIntegralTower.pullComp d x' x).hom.app M))

/-- Vertical interchange on the supplied compatible compactification towers.
The comparison is invertible only on the retained finite-etale-origin domain;
the interchange equation itself is an equality of strict natural transformations.
Source: constituent compatibility, steps 11--12
(blueprint: def-pur-strict-integral-exchange-data). -/
def PurIntegralStrictVertical (d : AdicCoefficientDatum A) (S : Scheme.{t}) : Prop :=
  (∀ {X Y Z : Scheme.{t}} (f : X ⟶ Y) (h : Y ⟶ Z)
      [X.Over S] [IsSeparated (X ↘ S)]
      [LocallyOfFiniteType (X ↘ S)] [QuasiCompact (X ↘ S)]
      [Y.Over S] [IsSeparated (Y ↘ S)]
      [LocallyOfFiniteType (Y ↘ S)] [QuasiCompact (Y ↘ S)]
      [Z.Over S] [IsSeparated (Z ↘ S)]
      [LocallyOfFiniteType (Z ↘ S)] [QuasiCompact (Z ↘ S)]
      [f.IsOver S]
      [h.IsOver S]
      [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
      [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
      (T : Compactification.Triangle f h)
      [QuasiCompact T.cf.i] [QuasiCompact T.cg.i] [QuasiCompact T.q]
      (M : DerivedCategory (d.towers X))
      (_origins : ∀ n : ℕ, Nonempty (ScalarEtaleOrigin A X
        ((ev A X n).obj ((exchangeTowerRes d X).obj M)))),
    IsIso ((PurIntegralTower.composition d T).app M)) ∧
  (∀ {X Y Z X' Y' Z' : Scheme.{t}}
      (f : X ⟶ Y) (h : Y ⟶ Z) (f' : X' ⟶ Y') (h' : Y' ⟶ Z')
      [X.Over S] [IsSeparated (X ↘ S)]
      [LocallyOfFiniteType (X ↘ S)] [QuasiCompact (X ↘ S)]
      [Y.Over S] [IsSeparated (Y ↘ S)]
      [LocallyOfFiniteType (Y ↘ S)] [QuasiCompact (Y ↘ S)]
      [Z.Over S] [IsSeparated (Z ↘ S)]
      [LocallyOfFiniteType (Z ↘ S)] [QuasiCompact (Z ↘ S)]
      [f.IsOver S]
      [h.IsOver S]
      [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
      [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
      (T : Compactification.Triangle f h) (T' : Compactification.Triangle f' h')
      [QuasiCompact T.cf.i] [QuasiCompact T.cg.i] [QuasiCompact T.q]
      [QuasiCompact T'.cf.i] [QuasiCompact T'.cg.i] [QuasiCompact T'.q]
      (x : X' ⟶ X) (y : Y' ⟶ Y) (g : Z' ⟶ Z) [IsIso x] [IsIso y] [IsIso g]
      (bc : CompositionBaseChange T T' x y g),
    Functor.whiskerRight (PurIntegralTower.composition d T) (d.towerPull g) ≫
        PurIntegralTower.exchange d T.cfg T'.cfg x g bc.s bc.cfg_i.w bc.cfg_g.w bc.cfg_i =
      (Functor.whiskerLeft (PurIntegralTower.support d T.cf)
        (PurIntegralTower.exchange d T.cg T'.cg y g bc.t bc.cg_i.w bc.cg_g.w bc.cg_i) ≫
        Functor.whiskerRight
          (PurIntegralTower.exchange d T.cf T'.cf x y bc.d bc.cf_i.w bc.cf_g.w bc.cf_i)
          (PurIntegralTower.support d T'.cg)) ≫
        Functor.whiskerLeft (d.towerPull x) (PurIntegralTower.composition d T'))

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme

/-- Integral reduction squares for the actual strict proper/open exchange and
compatible-tower composition. All corners are fixed composites of open tensor,
proper projection, pullback/quotient and K-flat evaluation comparisons. The same
squares are stated before finite evaluation and at each positive quotient. These
natural comparisons transport the identity and pasting equations with their
canonical unitors and compositors; no corner is chosen existentially.
Source: constituent compatibility, steps 7, 8, 13 and 14
(blueprint: def-pur-strict-integral-exchange-data). -/
def PurIntegralStrictReduction
    {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A) (S : Scheme.{t}) : Prop :=
  (∀ (T : Scheme.{t}) [T.Over S] [IsSeparated (T ↘ S)]
      [LocallyOfFiniteType (T ↘ S)] [QuasiCompact (T ↘ S)] (K : d.derived T),
    (PurIntegralTower.pullId d T).hom.app ((completedReductionTower T d).obj K) =
      (d.reductionTowerPullbackIso (𝟙 T)).hom.app K ≫
        (completedReductionTower T d).map ((d.pullId T).hom.app K)) ∧
  (∀ {U V W : Scheme.{t}} (h : U ⟶ V) (g : V ⟶ W)
      [W.Over S] [IsSeparated (W ↘ S)]
      [LocallyOfFiniteType (W ↘ S)] [QuasiCompact (W ↘ S)]
      [IsIso h] [IsIso g] (K : d.derived W),
    (PurIntegralTower.pullComp d h g).hom.app ((completedReductionTower W d).obj K) ≫
        (d.towerPull h).map ((d.reductionTowerPullbackIso g).hom.app K) ≫
        (d.reductionTowerPullbackIso h).hom.app ((d.pull g).obj K) =
      (d.reductionTowerPullbackIso (h ≫ g)).hom.app K ≫
        (completedReductionTower U d).map ((d.pullComp h g).hom.app K)) ∧
  (∀ {X' X Y' Y : Scheme.{t}} {v : X' ⟶ X} {p' : X' ⟶ Y'}
      {p : X ⟶ Y} {g : Y' ⟶ Y}
      [X.Over S] [IsSeparated (X ↘ S)]
      [LocallyOfFiniteType (X ↘ S)] [QuasiCompact (X ↘ S)]
      [Y.Over S] [IsSeparated (Y ↘ S)]
      [LocallyOfFiniteType (Y ↘ S)] [QuasiCompact (Y ↘ S)]
      [p.IsOver S]
      [IsIso v] [IsIso g] [IsProper p]
      (sq : ChosenCartesianSquare v p' p g) (M : d.derived X)
      (hM : d.TowerComplete X M)
      (W : ∀ n : ℕ, FiniteEtaleOriginWitness X (A ⧸ d.ideal ^ (n + 1))
        ((d.reduction X n).obj M)) (n : ℕ),
    (reductionTowerDerivedEvaluation Y'
          (reductionModuleRing Y' (d.completedRing Y')) n).map
          (d.towerH (f := p) (f' := p') (g := g) (g' := v) M).hom
        ≫ (PurIntegralTower.properFiniteCorner d sq M hM W n 1).hom =
        (PurIntegralTower.properFiniteCorner d sq M hM W n 0).hom
        ≫ (reductionDerivedRestrict Y' (d.projection Y' n)).map
          (d.fourArrows sq M hM W n).h.hom ∧
      (reductionTowerDerivedEvaluation Y'
          (reductionModuleRing Y' (d.completedRing Y')) n).map
          (d.towerH' (f := p) (f' := p') (g := g) (g' := v) M).hom
        ≫ (PurIntegralTower.properFiniteCorner d sq M hM W n 3).hom =
        (PurIntegralTower.properFiniteCorner d sq M hM W n 2).hom
        ≫ (reductionDerivedRestrict Y' (d.projection Y' n)).map
          (d.fourArrows sq M hM W n).h'.hom ∧
      (reductionTowerDerivedEvaluation Y'
          (reductionModuleRing Y' (d.completedRing Y')) n).map
          (d.towerV sq M) ≫ (PurIntegralTower.properFiniteCorner d sq M hM W n 2).hom =
        (PurIntegralTower.properFiniteCorner d sq M hM W n 0).hom
        ≫ (reductionDerivedRestrict Y' (d.projection Y' n)).map
          (d.fourArrows sq M hM W n).v ∧
      (reductionTowerDerivedEvaluation Y'
          (reductionModuleRing Y' (d.completedRing Y')) n).map
          (d.towerV' sq M) ≫ (PurIntegralTower.properFiniteCorner d sq M hM W n 3).hom =
        (PurIntegralTower.properFiniteCorner d sq M hM W n 1).hom
        ≫ (reductionDerivedRestrict Y' (d.projection Y' n)).map
          (d.fourArrows sq M hM W n).v'.hom) ∧
  (∀ {U' U T' T : Scheme.{t}} {v : U' ⟶ U} {j' : U' ⟶ T'}
      {j : U ⟶ T} {g : T' ⟶ T}
      [U.Over S] [IsSeparated (U ↘ S)]
      [LocallyOfFiniteType (U ↘ S)] [QuasiCompact (U ↘ S)]
      [T.Over S] [IsSeparated (T ↘ S)]
      [LocallyOfFiniteType (T ↘ S)] [QuasiCompact (T ↘ S)]
      [j.IsOver S]
      [IsOpenImmersion j] [IsOpenImmersion j']
      [IsIso v] [IsIso g] (sq : OpenImmersionSquare v j' j g) (K : d.derived U),
    (exchangeTowerRes d T').map (cbcOpenMateOmega d sq K).hom ≫
        (cbcOpenMateB d (j' := j') (v := v) K).hom =
      (cbcOpenMateA d (j := j) (g := g) K).hom ≫ (cbcOpenMateBeta d sq K).hom) ∧
  (∀ {U' U T' T : Scheme.{t}} {v : U' ⟶ U} {j' : U' ⟶ T'}
      {j : U ⟶ T} {g : T' ⟶ T}
      [U.Over S] [IsSeparated (U ↘ S)]
      [LocallyOfFiniteType (U ↘ S)] [QuasiCompact (U ↘ S)]
      [T.Over S] [IsSeparated (T ↘ S)]
      [LocallyOfFiniteType (T ↘ S)] [QuasiCompact (T ↘ S)]
      [j.IsOver S]
      [IsOpenImmersion j] [IsOpenImmersion j']
      [IsIso v] [IsIso g] (sq : OpenImmersionSquare v j' j g) (K : d.derived U),
    ∀ n : ℕ,
      HEq
        ((pbcTowerEvaluation T' (pbcAdicCompletion T' d) n).map
            ((cbcReductionStrictExchange d sq).hom.app K) ≫
          (cbcTargetFiniteComparison d sq n).hom.app K)
        ((cbcSourceFiniteComparison d sq n).hom.app K ≫
          (cbcFiniteExchange d sq n).hom.app ((cbcFiniteReduction d U n).obj K))) ∧
  (∀ {X' X Y' Y : Scheme.{t}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
      {g : Y' ⟶ Y} {g' : X' ⟶ X}
      [X.Over S] [IsSeparated (X ↘ S)]
      [LocallyOfFiniteType (X ↘ S)] [QuasiCompact (X ↘ S)]
      [Y.Over S] [IsSeparated (Y ↘ S)]
      [LocallyOfFiniteType (Y ↘ S)] [QuasiCompact (Y ↘ S)]
      [f.IsOver S] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
      [IsIso g] [IsIso g']
      (c : Compactification f) (c' : Compactification f') (gb : c'.Z ⟶ c.Z)
      [IsIso gb] (sp : ChosenCartesianSquare gb c'.g c.g g)
      (sj : OpenImmersionSquare g' c'.i c.i gb)
      (r : ℕ) (a : Fin r → A) (ha : Ideal.span (Set.range a) = d.ideal)
      (K : (cbcCompleteProperty d X r a ha).FullSubcategory),
    ((PurIntegralTower.exchange d c c' g' g gb sj.w sp.w
        (IsPullback.of_iso_pullback sj.toCommSq sj.isoPullback sj.hom_fst sj.hom_snd)).app
          ((completedReductionTower X d).obj K.obj) ≫
        (PurIntegralTower.exchangeReductionTarget d c' g' K.obj).hom =
      (PurIntegralTower.exchangeReductionSource d c g K.obj).hom ≫
        (completedReductionTower Y' d).map
          ((purIntegralReindexingExchange d c c' gb sp sj).app K.obj)) ∧
    ∀ n : ℕ,
      (reductionTowerDerivedEvaluation Y'
          (reductionModuleRing Y' (d.completedRing Y')) n).map
        ((PurIntegralTower.exchange d c c' g' g gb sj.w sp.w
          (IsPullback.of_iso_pullback sj.toCommSq sj.isoPullback sj.hom_fst sj.hom_snd)).app
            ((completedReductionTower X d).obj K.obj)) ≫
          (PurIntegralTower.finiteCorner d
            (PurIntegralTower.exchangeReductionTarget d c' g' K.obj) n).hom =
        (PurIntegralTower.finiteCorner d
          (PurIntegralTower.exchangeReductionSource d c g K.obj) n).hom ≫
          (reductionDerivedRestrict Y' (d.projection Y' n)).map
            ((d.reduction Y' n).map
              ((purIntegralReindexingExchange d c c' gb sp sj).app K.obj))) ∧
  (∀ {X Y Z : Scheme.{t}} {f : X ⟶ Y} {h : Y ⟶ Z}
      [X.Over S] [IsSeparated (X ↘ S)]
      [LocallyOfFiniteType (X ↘ S)] [QuasiCompact (X ↘ S)]
      [Y.Over S] [IsSeparated (Y ↘ S)]
      [LocallyOfFiniteType (Y ↘ S)] [QuasiCompact (Y ↘ S)]
      [Z.Over S] [IsSeparated (Z ↘ S)]
      [LocallyOfFiniteType (Z ↘ S)] [QuasiCompact (Z ↘ S)]
      [f.IsOver S] [h.IsOver S]
      [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
      [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
      (T : Compactification.Triangle f h)
      [QuasiCompact T.cf.i] [QuasiCompact T.cg.i] [QuasiCompact T.q]
      (r : ℕ) (a : Fin r → A) (ha : Ideal.span (Set.range a) = d.ideal)
      (K : (cbcCompleteProperty d X r a ha).FullSubcategory)
      (_origins : PbcHasCompatibleEtaleOrigins X d K.obj),
    ((PurIntegralTower.composition d T).app ((completedReductionTower X d).obj K.obj) ≫
        (PurIntegralTower.supportReduction d T.cfg K.obj).hom =
      (PurIntegralTower.compositionReductionSource d T K.obj).hom ≫
        (completedReductionTower Z d).map
          (cbcTowerCompositionMap d T.cf T.cg T.cfg T.q T.p T.i_q
            T.isPullback.w.symm T.p_g T.isPullback.flip K.obj)) ∧
    ∀ n : ℕ,
      (reductionTowerDerivedEvaluation Z
          (reductionModuleRing Z (d.completedRing Z)) n).map
        ((PurIntegralTower.composition d T).app ((completedReductionTower X d).obj K.obj)) ≫
          (PurIntegralTower.finiteCorner d (PurIntegralTower.supportReduction d T.cfg K.obj)
            n).hom =
        (PurIntegralTower.finiteCorner d (PurIntegralTower.compositionReductionSource d T K.obj)
          n).hom ≫
          (reductionDerivedRestrict Z (d.projection Z n)).map
            ((d.reduction Z n).map
              (cbcTowerCompositionMap d T.cf T.cg T.cfg T.q T.p T.i_q
                T.isPullback.w.symm T.p_g T.isPullback.flip K.obj)))

/-- The images of the strict identity and pasting equations under Rlim, with
exactly the published completion and composition comparisons. Compatible etale
origins are retained for the vertical comparison isomorphisms.
Source: constituent compatibility, final step
(blueprint: def-pur-strict-integral-exchange-data). -/
def PurIntegralCompletedCoherence
    {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A) (S : Scheme.{t}) : Prop :=
  (∀
    {X Y : Scheme.{t}} {f : X ⟶ Y}
      [X.Over S] [IsSeparated (X ↘ S)]
      [LocallyOfFiniteType (X ↘ S)] [QuasiCompact (X ↘ S)]
      [Y.Over S] [IsSeparated (Y ↘ S)]
      [LocallyOfFiniteType (Y ↘ S)] [QuasiCompact (Y ↘ S)]
      [f.IsOver S]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f)
    (sp : ChosenCartesianSquare (𝟙 c.Z) c.g c.g (𝟙 Y))
    (sj : OpenImmersionSquare (𝟙 X) c.i c.i (𝟙 c.Z))
    (r : ℕ) (a : Fin r → A) (ha : Ideal.span (Set.range a) = d.ideal)
    (K : (cbcCompleteProperty d X r a ha).FullSubcategory),
    ∃ (hK : d.TowerComplete X K.obj)
      (hF : d.TowerComplete Y ((cbcSupport d c).obj K.obj)),
      cbcExchange d c c (𝟙 c.Z) sp sj r a ha K ≫
          (cbcSupport d c).map (d.completedPullId X K.obj hK).hom =
        (d.completedPullId Y ((cbcSupport d c).obj K.obj) hF).hom) ∧
  (∀
    {X X' X'' Y Y' Y'' : Scheme.{t}}
    {f : X ⟶ Y} {f' : X' ⟶ Y'} {f'' : X'' ⟶ Y''}
    {g : Y' ⟶ Y} {g' : X' ⟶ X} {h : Y'' ⟶ Y'} {h' : X'' ⟶ X'}
      [X.Over S] [IsSeparated (X ↘ S)]
      [LocallyOfFiniteType (X ↘ S)] [QuasiCompact (X ↘ S)]
      [Y.Over S] [IsSeparated (Y ↘ S)]
      [LocallyOfFiniteType (Y ↘ S)] [QuasiCompact (Y ↘ S)]
      [f.IsOver S]
    [IsIso g] [IsIso g'] [IsIso h] [IsIso h']
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f) (c' : Compactification f') (c'' : Compactification f'')
    (gb : c'.Z ⟶ c.Z) (hb : c''.Z ⟶ c'.Z)
    (sp₁ : ChosenCartesianSquare gb c'.g c.g g)
    (sj₁ : OpenImmersionSquare g' c'.i c.i gb)
    (sp₂ : ChosenCartesianSquare hb c''.g c'.g h)
    (sj₂ : OpenImmersionSquare h' c''.i c'.i hb)
    (sp : ChosenCartesianSquare (hb ≫ gb) c''.g c.g (h ≫ g))
    (sj : OpenImmersionSquare (h' ≫ g') c''.i c.i (hb ≫ gb))
    (r : ℕ) (a : Fin r → A) (ha : Ideal.span (Set.range a) = d.ideal)
    (K : (cbcCompleteProperty d X r a ha).FullSubcategory),
    ∃ hK' : cbcCompleteProperty d X' r a ha ((d.completedPull g').obj K.obj),
      cbcExchange d c c'' (hb ≫ gb) sp sj r a ha K =
        (d.completedPullComp h g).hom.app ((cbcSupport d c).obj K.obj) ≫
          (d.completedPull h).map (cbcExchange d c c' gb sp₁ sj₁ r a ha K) ≫
          cbcExchange d (qf := cbcBaseChangeQuasiCompact c c' gb sj₁)
            c' c'' hb sp₂ sj₂ r a ha ⟨(d.completedPull g').obj K.obj, hK'⟩ ≫
          (cbcSupport d c'').map ((d.completedPullComp h' g').inv.app K.obj)) ∧
  (∀
    {X X' Y Y' Z Z' : Scheme.{t}}
    {f : X ⟶ Y} {f' : X' ⟶ Y'} {h : Y ⟶ Z} {h' : Y' ⟶ Z'}
    {gx : X' ⟶ X} {gy : Y' ⟶ Y} {gz : Z' ⟶ Z}
      [X.Over S] [IsSeparated (X ↘ S)]
      [LocallyOfFiniteType (X ↘ S)] [QuasiCompact (X ↘ S)]
      [Y.Over S] [IsSeparated (Y ↘ S)]
      [LocallyOfFiniteType (Y ↘ S)] [QuasiCompact (Y ↘ S)]
      [Z.Over S] [IsSeparated (Z ↘ S)]
      [LocallyOfFiniteType (Z ↘ S)] [QuasiCompact (Z ↘ S)]
      [f.IsOver S]
      [h.IsOver S]
    [IsIso gx] [IsIso gy] [IsIso gz]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    (cf : Compactification f) (ch : Compactification h)
    (chf : Compactification (f ≫ h))
    (cf' : Compactification f') (ch' : Compactification h')
    (chf' : Compactification (f' ≫ h'))
    (gbf : cf'.Z ⟶ cf.Z) (gbh : ch'.Z ⟶ ch.Z) (gbhf : chf'.Z ⟶ chf.Z)
    (spf : ChosenCartesianSquare gbf cf'.g cf.g gy)
    (sjf : OpenImmersionSquare gx cf'.i cf.i gbf)
    (sph : ChosenCartesianSquare gbh ch'.g ch.g gz)
    (sjh : OpenImmersionSquare gy ch'.i ch.i gbh)
    (sphf : ChosenCartesianSquare gbhf chf'.g chf.g gz)
    (sjhf : OpenImmersionSquare gx chf'.i chf.i gbhf)
    (b : cf.Z ⟶ chf.Z) (p : chf.Z ⟶ ch.Z)
    (b' : cf'.Z ⟶ chf'.Z) (p' : chf'.Z ⟶ ch'.Z)
    [IsProper p]
    [IsProper p']
    (hb : cf.i ≫ b = chf.i) (hp : b ≫ p = cf.g ≫ ch.i)
    (hq : p ≫ ch.g = chf.g)
    (hb' : cf'.i ≫ b' = chf'.i) (hp' : b' ≫ p' = cf'.g ≫ ch'.i)
    (hq' : p' ≫ ch'.g = chf'.g)
    (sq : IsPullback b cf.g p ch.i) (sq' : IsPullback b' cf'.g p' ch'.i)
    (_wb : b' ≫ gbhf = gbf ≫ b) (_wp : p' ≫ gbh = gbhf ≫ p)
    (r : ℕ) (a : Fin r → A) (ha : Ideal.span (Set.range a) = d.ideal)
    (K : (cbcCompleteProperty d X r a ha).FullSubcategory)
    (_origins : PbcHasCompatibleEtaleOrigins X d K.obj),
    IsIso (cbcTowerCompositionMap d cf ch chf b p hb hp hq sq K.obj) ∧
    IsIso (cbcTowerCompositionMap d
      (qh := cbcBaseChangeQuasiCompact ch ch' gbh sjh)
      cf' ch' chf' b' p' hb' hp' hq' sq' ((d.completedPull gx).obj K.obj)) ∧
    ∃ hF : cbcCompleteProperty d Y r a ha ((cbcSupport d cf).obj K.obj),
      (d.completedPull gz).map (cbcTowerCompositionMap d cf ch chf b p hb hp hq sq K.obj) ≫
          cbcExchange d chf chf' gbhf sphf sjhf r a ha K =
        cbcExchange d ch ch' gbh sph sjh r a ha ⟨(cbcSupport d cf).obj K.obj, hF⟩ ≫
          (cbcSupport d ch').map (cbcExchange d cf cf' gbf spf sjf r a ha K) ≫
          cbcTowerCompositionMap d
            (qh := cbcBaseChangeQuasiCompact ch ch' gbh sjh)
            cf' ch' chf' b' p' hb' hp' hq' sq' ((d.completedPull gx).obj K.obj))

/-- The finite-field geometric domain of the node, without base-linearity on any
of the isomorphisms. Only f is a morphism over the fixed algebraic closure.
The coefficient universe is raised by the published canonical ULift of O_E.
Source: constituent compatibility, hypotheses and steps 1--9
(blueprint: def-pur-strict-integral-exchange-data). -/
def PurStrictIntegralGeometricNormalization (P : WeilConjectures.PurityFiniteSetting.{t}) : Prop :=
  ∀ {X' X Y' Y : Scheme.{t}} [X.Over (Spec (.of P.field.k))]
      [Y.Over (Spec (.of P.field.k))]
      [IsSeparated (X ↘ Spec (.of P.field.k))]
      [IsSeparated (Y ↘ Spec (.of P.field.k))]
      [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
      [QuasiCompact (X ↘ Spec (.of P.field.k))]
      [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
      [QuasiCompact (Y ↘ Spec (.of P.field.k))]
      {f : X ⟶ Y} [f.IsOver (Spec (.of P.field.k))]
      [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
      {f' : X' ⟶ Y'} {g : Y' ⟶ Y} {g' : X' ⟶ X} [IsIso g] [IsIso g']
      (c : Compactification f) (c' : Compactification f') (gb : c'.Z ⟶ c.Z) [IsIso gb]
      (sp : ChosenCartesianSquare gb c'.g c.g g)
      (sj : OpenImmersionSquare g' c'.i c.i gb)
      (r : ℕ) (a : Fin r → PbcIntegralRing P.coefficients.l P.extension)
      (ha : Ideal.span (Set.range a) = (pbcIntegralDatum P.coefficients.l P.extension).ideal)
      (K : (cbcCompleteProperty (pbcIntegralDatum P.coefficients.l P.extension)
        X r a ha).FullSubcategory),
    PurIntegralSupportNormalization (pbcIntegralDatum P.coefficients.l P.extension)
      c c' gb sp sj r a ha K

end AlgebraicGeometry.Scheme
