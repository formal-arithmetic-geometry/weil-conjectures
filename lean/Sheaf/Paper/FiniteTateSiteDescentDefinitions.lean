/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N1
-/
module

public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.Paper.CoefficientTwistsDetailed
public import Sheaf.AlgebraicGeometry.EtaleFiniteTwistPullback
public import Sheaf.Paper.RingedTopoiDerivedTensorPullback
public import Sheaf.AlgebraicGeometry.ProEtaleSiteComparison
public import WeilConjectures.SixFunctors.ProEtale.Comparison.Monoidal
public import Sheaf.CategoryTheory.CommutativeSiteDerivedConstantModuleFunctor
public import Sheaf.CategoryTheory.ConstantRingModuleSheaves

import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted

/-! # Normalization predicates for finite Tate descent

Source: Stacks Project, Tags 03PK and 099R.
The definitions are retained verbatim from `FiniteTateSiteDescent`.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures
open scoped ChangeOfRings

namespace AlgebraicGeometry.Scheme

/-- The existing finite quotient ring, lifted only to the sheaf universe.
Source: coefficient notation (blueprint: def-pur-finite-tate-site-comparison). -/
abbrev finiteTateCoefficient (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (n : ℕ) :=
  ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1))

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
  [FiniteDimensional ℚ_[l] E] (n : ℕ) (T : Scheme.{u})

/-- Restrict the recorded finite Tate module to its constant scalar action.
Source: Stacks Tag 03CY (blueprint: def-pur-finite-tate-site-comparison). -/
def finiteTateConstantRestriction :
    SheafOfModules.{u + 1} (integralCoefficientSheaf l E T n) ⥤
      Sheaf (ProEt.topology T)
        (ModuleCat.{u + 1} (finiteTateCoefficient l E n)) :=
  letI := purTwistForgetPreservesSheafification T
  SheafOfModules.restrictScalars
      ((constantCommuteCompose (ProEt.topology T)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).app
          (CommRingCat.of (finiteTateCoefficient l E n))).inv ⋙
    constantRingModuleRestriction (ProEt.topology T) (finiteTateCoefficient l E n)

/-- The original finite pro-etale twist, in the fixed-coefficient encoding.
Source: coefficient-twist blueprint, order 1505
(blueprint: def-pur-finite-tate-site-comparison). -/
abbrev finiteTateProSheaf (a : ℕ) :=
  (finiteTateConstantRestriction l E n T).obj (finiteCoefficientTwist l E T n (a : ℤ))

/-- A sectionwise pure tensor in the first finite twist.
Source: Stacks Tag 03EK (blueprint: def-pur-finite-tate-site-comparison). -/
def finiteTateProGenerator (W : T.ProEtᵒᵖ)
    (a : finiteTateCoefficient l E n)
    (x : (purTwistZlOne T l).obj.obj W) :
    (finiteTateProSheaf l E n T 1).obj.obj W :=
  (((PresheafOfModules.sheafificationAdjunction
    (𝟙 (integralCoefficientSheaf l E T n).obj)).unit.app
      (SheafOfModules.changeOfRingsPresheafOfUniverses.{u, u + 1, u + 1, u + 1}
        (purTwistIntegralQuotient T l E n) (purTwistIntegralOne T l E))).app W)
    (((realizationRingUnit (ProEt.topology T)
      (finiteTateCoefficient l E n)).app W a) ⊗ₜ[_,
        ((purTwistIntegralQuotient T l E n).hom.app W).hom]
      (purTwistIntegralTensor T l E W 1 x))

/-- Pure local tensors in the prescribed nonnegative pro-etale powers.
Source: Stacks Tag 03EK (blueprint: def-pur-finite-tate-site-comparison). -/
def finiteTateProPowerGenerator (W : T.ProEtᵒᵖ)
    (a : finiteTateCoefficient l E n) :
    (k : ℕ) → (Fin k → (purTwistZlOne T l).obj.obj W) →
      (finiteTateProSheaf l E n T k).obj.obj W
  | 0, _ => (realizationRingUnit (ProEt.topology T)
      (finiteTateCoefficient l E n)).app W a
  | 1, x => finiteTateProGenerator l E n T W a (x 0)
  | k + 2, x => SheafOfModules.siteSheafTensorTmul
      (coefficientTwistPower T (purTwistFiniteOne T l E n) (k + 1))
      (purTwistFiniteOne T l E n) W
      (finiteTateProPowerGenerator W a (k + 1) (fun i ↦ x i.castSucc))
      (finiteTateProGenerator l E n T W 1 (x (Fin.last (k + 1))))

/-- Pure local tensors in the recorded etale Tate powers.
Source: Stacks Tags 03PK and 03EK (blueprint: def-pur-finite-tate-site-comparison). -/
def finiteTateEtalePowerGenerator (A : Type (u + 1)) [CommRing A]
    (m : ℕ) (hA : (m : A) = 0) (W : T.Etaleᵒᵖ) (a : A) :
    (k : ℕ) → (Fin k → (T.rootsOfUnitySheaf m).obj.obj W) →
      (finiteEtaleTateTwist T m A hA k).obj.obj W
  | 0, _ => (toSheafify T.smallEtaleTopology
      ((Functor.const T.Etaleᵒᵖ).obj (ModuleCat.of A A))).app W a
  | 1, x => finiteEtaleTateOneGenerator A m T hA W a (x 0)
  | k + 2, x =>
      (Functor.LaxMonoidal.μ (sheafToPresheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))
        (finiteEtaleTateTwist T m A hA (k + 1)) (finiteEtaleTateLine T m A hA)).app W
        (finiteTateEtalePowerGenerator A m hA W a (k + 1) (fun i ↦ x i.castSucc) ⊗ₜ[A]
          finiteEtaleTateOneGenerator A m T hA W 1 (x (Fin.last (k + 1))))

/-- The actual unit underlying a finite root section on the etale site.
Source: Stacks Tag 03PK (blueprint: def-pur-finite-tate-site-comparison). -/
def finiteTateEtaleRootValue (m : ℕ) (W : T.Etaleᵒᵖ)
    (z : (T.rootsOfUnitySheaf m).obj.obj W) : Γ(W.unop.left, ⊤)ˣ :=
  Additive.toMul (((kernel.ι (m • 𝟙 T.gmSheaf)).hom.app W z).down)

/-- The actual unit in a specified projection of the root limit.
Source: Stacks Tag 03PK (blueprint: def-pur-finite-tate-site-comparison). -/
def finiteTateLimitRootValue (r : ℕ) (W : T.ProEtᵒᵖ)
    (x : (purTwistZlOne T l).obj.obj W) : Γ(W.unop.left, ⊤)ˣ :=
  Additive.toMul (((proEtaleRootsOfUnityInclusion T (l ^ (r + 1))).hom.app W
    ((limit.π (proEtaleRootsOfUnityTower T l (Fact.out : l.Prime)) (op r)).hom.app W x)).down)

/-- Root-projection normalization of the comparison, on every local pure tensor.
The arrow `f` allows arbitrary pro-etale tests over an etale object, so roots may be
lifted to the infinite root tower pro-etale locally, without requiring an etale lift.
Source: Stacks Tags 03PK and 0GLZ
(blueprint: def-pur-finite-tate-site-comparison). -/
def IsFiniteTateSiteComparison (r : ℕ)
    (hA : ((l ^ (r + 1) : ℕ) : finiteTateCoefficient l E n) = 0) (k : ℕ)
    (b : (ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} (finiteTateCoefficient l E n)) T).obj
        (finiteEtaleTateTwist T (l ^ (r + 1)) _ hA k) ≅ finiteTateProSheaf l E n T k) : Prop :=
  ∀ (U : T.Etaleᵒᵖ) (W : T.ProEtᵒᵖ)
    (f : W.unop ⟶ (toProEt T).obj U.unop)
    (a : finiteTateCoefficient l E n)
    (z : Fin k → (T.rootsOfUnitySheaf (l ^ (r + 1))).obj.obj U)
    (x : Fin k → (purTwistZlOne T l).obj.obj W),
    (∀ i : Fin k, finiteTateLimitRootValue l T r W (x i) =
      Units.map f.left.appTop.hom.toMonoidHom (finiteTateEtaleRootValue T (l ^ (r + 1)) U (z i))) →
    b.hom.hom.app W
      (((ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} (finiteTateCoefficient l E n)) T).obj
          (finiteEtaleTateTwist T (l ^ (r + 1)) _ hA k)).obj.map f.op
        (((ProEtale.comparisonAdjunction
          (ModuleCat.{u + 1} (finiteTateCoefficient l E n)) T).unit.app
            (finiteEtaleTateTwist T (l ^ (r + 1)) _ hA k)).hom.app U
              (finiteTateEtalePowerGenerator T _ (l ^ (r + 1)) hA U a k z))) =
      finiteTateProPowerGenerator l E n T W a k x

/-- The pullback comparison on etale powers is fixed on root tensors.
Source: Stacks Tags 03PK and 03Q1
(blueprint: def-pur-finite-tate-site-comparison). -/
def IsFiniteTateEtalePullback {T' : Scheme.{u}} (v : T' ⟶ T) (r : ℕ)
    (hA : ((l ^ (r + 1) : ℕ) : finiteTateCoefficient l E n) = 0) (k : ℕ)
    (c : (Etale.upperStar (ModuleCat.{u + 1} (finiteTateCoefficient l E n)) v).obj
      (finiteEtaleTateTwist T (l ^ (r + 1)) _ hA k) ≅
        finiteEtaleTateTwist T' (l ^ (r + 1)) _ hA k) : Prop :=
  ∀ (U : T.Etaleᵒᵖ) (a : finiteTateCoefficient l E n)
    (z : Fin k → (T.rootsOfUnitySheaf (l ^ (r + 1))).obj.obj U)
    (z' : Fin k → (T'.rootsOfUnitySheaf (l ^ (r + 1))).obj.obj
      ((MorphismProperty.Over.pullback @Etale ⊤ v).op.obj U)),
    (∀ i : Fin k,
      finiteTateEtaleRootValue T' (l ^ (r + 1)) _ (z' i) =
        Units.map (pullback.fst U.unop.hom v).appTop.hom.toMonoidHom
          (finiteTateEtaleRootValue T (l ^ (r + 1)) U (z i))) →
    ((Etale.upperStarLowerStarAdjunction
      (ModuleCat.{u + 1} (finiteTateCoefficient l E n)) v).homEquiv _ _ c.hom).hom.app U
        (finiteTateEtalePowerGenerator T _ (l ^ (r + 1)) hA U a k z) =
      finiteTateEtalePowerGenerator T' _ (l ^ (r + 1)) hA _ a k z'

/-- The usual pro-etale pullback comparison, fixed by every root projection.
Source: Stacks Tag 09A5; the root tower limit universal property
(blueprint: def-pur-finite-tate-site-comparison). -/
def IsFiniteTateProPullback {T' : Scheme.{u}} (v : T' ⟶ T) (k : ℕ)
    (b : (ProEtale.upperStar (ModuleCat.{u + 1} (finiteTateCoefficient l E n)) v).obj
      (finiteTateProSheaf l E n T k) ≅ finiteTateProSheaf l E n T' k) : Prop :=
  ∀ (U : T.ProEtᵒᵖ) (a : finiteTateCoefficient l E n)
    (x : Fin k → (purTwistZlOne T l).obj.obj U)
    (x' : Fin k → (purTwistZlOne T' l).obj.obj
      ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ v).op.obj U)),
    (∀ (s : ℕ) (i : Fin k), finiteTateLimitRootValue l T' s _ (x' i) =
      Units.map (pullback.fst U.unop.hom v).appTop.hom.toMonoidHom
        (finiteTateLimitRootValue l T s U (x i))) →
    ((ProEtale.upperStarLowerStarAdjunction
      (ModuleCat.{u + 1} (finiteTateCoefficient l E n)) v).homEquiv _ _ b.hom).hom.app U
        (finiteTateProPowerGenerator l E n T U a k x) =
      finiteTateProPowerGenerator l E n T' _ a k x'

/-- The exponent-change comparison is induced by the specified root power map.
Source: Stacks Tag 03PK (blueprint: def-pur-finite-tate-site-comparison). -/
def IsFiniteTateEtaleTransition (r r' : ℕ)
    (hA : ((l ^ (r + 1) : ℕ) : finiteTateCoefficient l E n) = 0)
    (hA' : ((l ^ (r' + 1) : ℕ) : finiteTateCoefficient l E n) = 0) (k : ℕ)
    (t : finiteEtaleTateTwist T (l ^ (r' + 1)) _ hA' k ≅
      finiteEtaleTateTwist T (l ^ (r + 1)) _ hA k) : Prop :=
  ∀ (U : T.Etaleᵒᵖ) (a : finiteTateCoefficient l E n)
    (z' : Fin k → (T.rootsOfUnitySheaf (l ^ (r' + 1))).obj.obj U)
    (z : Fin k → (T.rootsOfUnitySheaf (l ^ (r + 1))).obj.obj U),
    (∀ i : Fin k, finiteTateEtaleRootValue T (l ^ (r + 1)) U (z i) =
      finiteTateEtaleRootValue T (l ^ (r' + 1)) U (z' i) ^ (l ^ (r' - r))) →
    t.hom.hom.app U (finiteTateEtalePowerGenerator T _ (l ^ (r' + 1)) hA' U a k z') =
      finiteTateEtalePowerGenerator T _ (l ^ (r + 1)) hA U a k z

end AlgebraicGeometry.Scheme
