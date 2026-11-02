/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeart
public import WeilConjectures.DeligneLaumon.SfWeilSheafComplex
public import WeilConjectures.WeilSheaf.CondensedModule.CondensedModuleLocalFrobenius
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.FiniteEtaleStalk
public import WeilConjectures.TraceFormula.PointFiberFunctor
public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.Topology.Defs.Filter
import WeilConjectures.AlgebraicGeometry.FiniteLocallyClosedStratification
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Limits
import WeilConjectures.AlgebraicGeometry.FiniteGenericFiberStratumInteriors
import WeilConjectures.AlgebraicGeometry.FiniteEtaleNoetherianClopenAssembly
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Etale
import WeilConjectures.AlgebraicGeometry.ProfinitePointPullback
import WeilConjectures.AlgebraicGeometry.FiniteEtaleEtaleLocalSplit
import WeilConjectures.AlgebraicGeometry.Closed.ClosedPointField
import WeilConjectures.AlgebraicGeometry.Pullback.PullbackConstantModelConstructible

/-! # Condensed finite etale stalk cycles

Source: latest blueprint, sec-deligne-laumon-a1/sk-lem-wft-finite-map,
lem-a1-finite-map-purity.proof.md, first paragraph; Stacks 03QP(1), with the
condensed and Weil refinement recorded in the DAG
(blueprint: lem-a1-condensed-finite-etale-stalk-cycles).

The coefficient field is the standard chosen algebraic closure, with its universe lift.
All fibres are the existing point-sections functor applied to module pullback. All
restriction arrows are the existing adjunction-counit arrows. The local operators below
are the degree-zero specialization of the recorded local-return convention: the canonical
point reparametrization, pullback composition, and the iterated Weil isomorphism.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj DirectSum

namespace WeilConjectures.CondensedFiniteEtale

open WeilConjectures.CondensedModule

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
  {X₀ Y₀ : Over (Spec (.of D.k₀))}
  [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
  [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]

/-- The existing base-change functor applied to g_0.
Source: blueprint geometric base change (blueprint: lem-a1-condensed-finite-etale-stalk-cycles).
-/
def geometricMap (g₀ : X₀ ⟶ Y₀) :
    (D.geometricFiber X₀).left ⟶ (D.geometricFiber Y₀).left :=
  ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map g₀).left

/-- The ordinary module direct image, including its canonical coefficient action.
Source: blueprint definition G=g_*F; det-def-sfb-module-pushforward-pullback
(blueprint: lem-a1-condensed-finite-etale-stalk-cycles). -/
def directImage (g₀ : X₀ ⟶ Y₀) (M : Modules l (D.geometricFiber X₀).left) :=
  (CondensedRing.lowerStar (Profinite.padicAlgClRingObj l) (geometricMap D g₀)).obj M

/-- The specified exchange followed by g_*theta, with no choice of a Weil structure.
Source: blueprint Weil-structure clause
(blueprint: lem-a1-condensed-finite-etale-stalk-cycles). -/
def directImageWeil (g₀ : X₀ ⟶ Y₀)
    (h : (D.geometricFrobenius X₀).hom ≫ geometricMap D g₀ =
      geometricMap D g₀ ≫ (D.geometricFrobenius Y₀).hom)
    (M : Modules l (D.geometricFiber X₀).left)
    (θ : (CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
      (D.geometricFrobenius X₀).hom).obj M ≅ M) :
    (CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
      (D.geometricFrobenius Y₀).hom).obj (directImage D l g₀ M) ≅ directImage D l g₀ M :=
  (asIso (CondensedRing.lowerStarBaseChange (Profinite.padicAlgClRingObj l)
    (CommSq.mk h))).app M ≪≫
    (CondensedRing.lowerStar (Profinite.padicAlgClRingObj l) (geometricMap D g₀)).mapIso θ

end WeilConjectures.CondensedFiniteEtale
