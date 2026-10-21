/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q03
-/
module

public import Sheaf.SixFunctors.IntegralCompactificationBridgeCoordinates
public import Sheaf.SixFunctors.ConstantSemilinearGeneratorComparison
public import Sheaf.Paper.QcqsCompactSupportRealization
public import Sheaf.Paper.SfCbcCompactSupportCompositionLimit
public import Sheaf.AlgebraicGeometry.StrictTowerProperOpenCalculus
public import WeilConjectures.Compactification.Triangle
import Sheaf.CategoryTheory.RingedTowerPushforwardLimitComparison
import Sheaf.SixFunctors.AmbientProperOpenPasting

/-! # Integral compactification comparison bridge

Source: blueprint main-20261015, fix-lem-exchanges, proof Step 5; the additional
constant/semilinear comparison obligation
(blueprint: def-sf-integral-compactification-word-comparisons).

The helpers fix the small-site coordinate transports by sections and adjunction mates.
The two composition maps are constructed independently, before any finite evaluation.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralCompactificationBridge
open IntegralSystemRealization GeneratorReduction

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The actual semilinear compactification word, with its termwise open factor.
Source: blueprint fix-lem-exchanges Step 5
(blueprint: def-sf-integral-compactification-word-comparisons). -/
abbrev systemWord (o : IntegralSystemRealization.Operations l E)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :=
  IntegralSystemRealization.Operations.shriek l E o c.i ⋙
    IntegralSystemRealization.Operations.push l E o c.g

/-- The two-letter word in the published constant-tower calculus.
Source: blueprint fix-lem-exchanges Step 5
(blueprint: def-sf-integral-compactification-word-comparisons). -/
def word {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) : SfCbcWord X Y :=
  ((SfCbcWord.nil X).snoc (.openExtension c.i inferInstance)).snoc (.directImage c.g)

/-- The strict constant word on the original small site, before model transport.
Source: Stacks 0941 (blueprint: def-sf-integral-compactification-word-comparisons). -/
abbrev originalWord {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :=
  ProEtale.StrictTower.J (ULift.{u + 1} (constantRing l E)) c.i ⋙
    ProEtale.StrictTower.R (ULift.{u + 1} (constantRing l E)) c.g

/-- Word transport uses only the normalized direct and open transports.
Source: Stacks 00VC, 0941
(blueprint: def-sf-integral-compactification-word-comparisons). -/
def wordTransport {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (a : sfCbcModelExtension c.i (constantRing l E) ⊣
      (sfCbcMorphism c.i).modulePull (ULift.{u + 1} (constantRing l E)))
    (M : ProEtale.StrictTower.Derived (ULift.{u + 1} (constantRing l E)) X) :
    (derivedTowerModel l E Y).obj ((originalWord l E c).obj M) ≅
      ((word c).strict (A := constantRing l E)).obj ((derivedTowerModel l E X).obj M) :=
  (directModel l E c.g).app _ ≪≫
    ((sfCbcMorphism c.g).towerPush _).mapIso ((openModel l E c.i a).app M)

/-- Compactification composition in semilinear systems, using the intrinsic proper/open
mate and the recorded unital compositors, with no finite evaluation.
Source: Stacks 0F7B--0F7F; blueprint fix-lem-exchanges Step 5
(blueprint: def-sf-integral-compactification-word-comparisons). -/
def systemBeta {D : FiniteFieldDatum.{u}} (o : IntegralSystemRealization.Operations l E)
    (r : Realizations l E D o) {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    (t : Compactification.Triangle f g) [QuasiCompact t.q] [QuasiCompact t.cg.i]
    (M : System l E X) :
    (systemWord l E o t.cg).obj ((systemWord l E o t.cf).obj M) ⟶
      (systemWord l E o t.cfg).obj M :=
  (IntegralSystemRealization.Operations.push l E o t.cg.g).map
    ((r.properOpen.gamma t.q t.cf.g t.p t.cg.i t.isPullback.w.symm).app
      ((IntegralSystemRealization.Operations.shriek l E o t.cf.i).obj M)) ≫
  (IntegralSystemRealization.Operations.push l E o t.cg.g).map
    ((IntegralSystemRealization.Operations.push l E o t.p).map
      ((r.compositors.openComp l E t.cf.i t.q).hom.app M ≫
        (IntegralSystemRealization.openCongr l E o t.i_q).hom.app M)) ≫
  (r.compositors.pushComp l E t.p t.cg.g).hom.app
    ((IntegralSystemRealization.Operations.shriek l E o t.cfg.i).obj M) ≫
  eqToHom (congrArg (fun p ↦ (IntegralSystemRealization.Operations.push l E o p).obj
    ((IntegralSystemRealization.Operations.shriek l E o t.cfg.i).obj M)) t.p_g)

/-- Constant proper/open composition on the original strict diagram category.
Source: Stacks 0F7B--0F7F
(blueprint: def-sf-integral-compactification-word-comparisons). -/
def originalBeta {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    (t : Compactification.Triangle f g) [QuasiCompact t.q] [QuasiCompact t.cg.i]
    (M : ProEtale.StrictTower.Derived (ULift.{u + 1} (constantRing l E)) X) :
    (originalWord l E t.cg).obj ((originalWord l E t.cf).obj M) ⟶
      (originalWord l E t.cfg).obj M :=
  (ProEtale.StrictTower.R (ULift.{u + 1} (constantRing l E)) t.cg.g).map
    ((ProEtale.StrictTower.gamma (ULift.{u + 1} (constantRing l E))
      t.q t.cf.g t.p t.cg.i t.isPullback.w.symm).app
        ((ProEtale.StrictTower.J (ULift.{u + 1} (constantRing l E)) t.cf.i).obj M)) ≫
  (ProEtale.StrictTower.R (ULift.{u + 1} (constantRing l E)) t.cg.g).map
    ((ProEtale.StrictTower.R (ULift.{u + 1} (constantRing l E)) t.p).map
      ((ProEtale.StrictTower.jComp (ULift.{u + 1} (constantRing l E))
        t.cf.i t.q).hom.app M ≫
        (ProEtale.StrictTower.jCongr (ULift.{u + 1} (constantRing l E)) t.i_q).hom.app M)) ≫
  (ProEtale.StrictTower.rComp (ULift.{u + 1} (constantRing l E))
    t.p t.cg.g).hom.app
      ((ProEtale.StrictTower.J (ULift.{u + 1} (constantRing l E)) t.cfg.i).obj M) ≫
  eqToHom (congrArg (fun p ↦ (ProEtale.StrictTower.R
    (ULift.{u + 1} (constantRing l E)) p).obj
      ((ProEtale.StrictTower.J (ULift.{u + 1} (constantRing l E)) t.cfg.i).obj M)) t.p_g)



/-- The normalized strict constant-tower beta, transported through the exact site model.
Both the input counit and all letter transports are the canonical ones; this definition
chooses no lift of finite evaluations.
Source: Stacks 00VC, 0F7B--0F7F
(blueprint: def-sf-integral-compactification-word-comparisons). -/
def constantBeta {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    (t : Compactification.Triangle f g) [QuasiCompact t.q] [QuasiCompact t.cg.i]
    (af : sfCbcModelExtension t.cf.i (constantRing l E) ⊣
      (sfCbcMorphism t.cf.i).modulePull (ULift.{u + 1} (constantRing l E)))
    (ag : sfCbcModelExtension t.cg.i (constantRing l E) ⊣
      (sfCbcMorphism t.cg.i).modulePull (ULift.{u + 1} (constantRing l E)))
    (ah : sfCbcModelExtension t.cfg.i (constantRing l E) ⊣
      (sfCbcMorphism t.cfg.i).modulePull (ULift.{u + 1} (constantRing l E)))
    (N : (sfCbcSite X).towerDerived (ULift.{u + 1} (constantRing l E))) :
    ((word t.cg).strict (A := constantRing l E)).obj
      (((word t.cf).strict (A := constantRing l E)).obj N) ⟶
        ((word t.cfg).strict (A := constantRing l E)).obj N :=
  let e := (derivedTowerModel l E X).asEquivalence
  let M := e.inverse.obj N
  ((word t.cg).strict (A := constantRing l E)).map
    (((word t.cf).strict (A := constantRing l E)).map (e.counitIso.inv.app N)) ≫
  ((word t.cg).strict (A := constantRing l E)).map
    ((wordTransport l E t.cf af M).inv) ≫
  (wordTransport l E t.cg ag ((originalWord l E t.cf).obj M)).inv ≫
  (derivedTowerModel l E Z).map (originalBeta l E t M) ≫
  (wordTransport l E t.cfg ah M).hom ≫
  ((word t.cfg).strict (A := constantRing l E)).map (e.counitIso.hom.app N)

end WeilConjectures.IntegralCompactificationBridge
