/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q22
-/
module

public import Sheaf.SixFunctors.IntegralSystemExpressionDomain
public import Sheaf.SixFunctors.IntegralSystemCanonicalBridge
public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.Paper.IntegralCompactSupportCoefficientComparison
import Sheaf.Paper.NormalizedDVRTower
import Sheaf.Paper.ExchangeProjectionSuppliedDomains
import Sheaf.Paper.IntegralDerivedOperationsOnSlices
import WeilConjectures.Compactification.Refinement
public import WeilConjectures.Compactification.RefinementCategory
import Sheaf.Paper.DerivedCompleteOnSlices
import Sheaf.Paper.SfIntegralConstructible
import Sheaf.AlgebraicGeometry.ProEtaleCohomologicalSupport
import Sheaf.Paper.IntrinsicFiniteTorsionConstructibility
import Sheaf.Paper.SfDerivedComplete
import Sheaf.Paper.SfDerivedDirectImage
import Sheaf.AlgebraicGeometry.ProEtaleConstantDerivedDirectImage
import Sheaf.Paper.SfIntegralReductionTower
import Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import Sheaf.Paper.QcqsCompactSupportRealization
import Sheaf.AlgebraicGeometry.CompactifiableCompatibleTower
import Sheaf.AlgebraicGeometry.StrictTowerProperOpenCalculus
import Sheaf.Paper.CoefDerivedSystemEvaluationCalculus
import Sheaf.Paper.NormalizedDVREffectivity
import Sheaf.Paper.SemilinearDerivedSections
import Sheaf.Paper.CoefficientSystemDerivedComparison
import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
import Sheaf.Paper.IntegralOperationsWellDefined
import Sheaf.SecSmoothPurity.IntrinsicCompactSupportRestriction
import Sheaf.SixFunctors.IntegralOpenReductionComparison
import Sheaf.SixFunctors.OpenTensorNormalization
import Sheaf.SixFunctors.SemilinearProperOpenMatePasting
import Sheaf.Paper.RingedExchangeTensorCoherence
import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
import Sheaf.Paper.SfCommonStageDirectImage
import Sheaf.SixFunctors.GeneratorReductionStatement

/-! # Coherent integral realization of compactification expressions

Source: Stacks 0941; blueprint fix-prop-coherence, all seven realization-proof steps
(blueprint: lem-sf-integral-compactification-system-realization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
namespace IntegralSystemRealization

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Exchange is exactly the mate of the normalized pullback square.
Source: Stacks 07A7; def-exchange-projection
(blueprint: lem-sf-integral-compactification-system-realization). -/
def properExchange (o : Operations l E) (c : Compositors l E o)
    {U V W Z : Scheme.{u}} (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
    (h : k ≫ p = r ≫ i) :
    Operations.push l E o p ⋙ pull l E i ⟶ pull l E k ⋙ Operations.push l E o r :=
  (mateEquiv (o.direct p).adj (o.direct r).adj
    (TwoSquare.mk _ _ _ _ (c.square l E k r p i h).hom)).natTrans

/-- The proper projection is the published counit-defined right-adjoint projection mate.
Source: Stacks 0E48; def-exchange-projection
(blueprint: lem-sf-integral-compactification-system-realization). -/
def properProjection (o : Operations l E) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Operations.push l E o f ⋙ Functor.curryObj (calculus l E Y).systemClosed.tensor ⟶
      (Functor.postcompose₂.obj (Operations.push l E o f)).obj
        ((((Functor.whiskeringLeft₂ _).obj (𝟭 _)).obj (pull l E f)).obj
          (Functor.curryObj (calculus l E X).systemClosed.tensor)) :=
  (o.direct f).adj.rightAdjointProjectionMap
    (Functor.curry.mapIso (pullbackTensorSystemComparison l E f) ≪≫
      Functor.curryObjProdComp (pull l E f) (pull l E f)
        (calculus l E X).systemClosed.tensor).hom

/-- Compactification exchange uses the recorded supplied-domain composite: proper
exchange on J, followed by proper image of the canonical open base-change map.
Source: blueprint def-exchange-projection
(blueprint: lem-sf-integral-compactification-system-realization). -/
def compactificationExchange (o : Operations l E) (c : Compositors l E o)
    (a : OpenComparisons l E o c) {X Y X' Y' : Scheme.{u}}
    {f : X ⟶ Y} {f' : X' ⟶ Y'} (d : Compactification f) (d' : Compactification f')
    (x : X' ⟶ X) (y : Y' ⟶ Y) (z : d'.Z ⟶ d.Z)
    (wi : x ≫ d.i = d'.i ≫ z) (wp : z ≫ d.g = d'.g ≫ y)
    (hi : IsPullback x d'.i d.i z) :
    (Operations.shriek l E o d.i ⋙ Operations.push l E o d.g) ⋙ pull l E y ⟶
      pull l E x ⋙ (Operations.shriek l E o d'.i ⋙ Operations.push l E o d'.g) :=
  SuppliedExchangeProjection.compactificationExchangeFromData
    (Operations.shriek l E o d.i) (Operations.shriek l E o d'.i)
    (pull l E d.g) (Operations.push l E o d.g) (o.direct d.g).adj
    (pull l E d'.g) (Operations.push l E o d'.g) (o.direct d'.g).adj
    (pull l E y) (pull l E x) (pull l E z)
    (c.square l E z d'.g d.g y wp) (a.beta x d'.i d.i z wi hi)

/-- Compactification projection is proper projection, open projection, then the
inverse pullback compositor and the actual compactification equation.
Source: blueprint def-exchange-projection
(blueprint: lem-sf-integral-compactification-system-realization). -/
def compactificationProjection (o : Operations l E) (c : Compositors l E o)
    (a : OpenComparisons l E o c) {X Y : Scheme.{u}} {f : X ⟶ Y}
    (d : Compactification f) (M : System l E X) (N : System l E Y) :
    (calculus l E Y).systemClosed.tensor.obj
      ((Operations.push l E o d.g).obj ((Operations.shriek l E o d.i).obj M), N) ⟶
    (Operations.push l E o d.g).obj ((Operations.shriek l E o d.i).obj
      ((calculus l E X).systemClosed.tensor.obj (M, (pull l E f).obj N))) :=
  ((properProjection l E o d.g).app ((Operations.shriek l E o d.i).obj M)).app N ≫
    (Operations.push l E o d.g).map
      ((a.projection d.i).hom.app (M, (pull l E d.g).obj N) ≫
        (Operations.shriek l E o d.i).map
          ((calculus l E X).systemClosed.tensor.map
            (Prod.mkHom (𝟙 M) ((c.pullComp d.i d.g).inv.app N ≫
              eqToHom (congrArg (fun g : X ⟶ Y ↦ (pull l E g).obj N) d.comm.symm)))))

/-- The localized ringed-site projection mate, in its explicit curried tensor shape.
Source: Stacks 0E48; blueprint def-exchange-projection
(blueprint: lem-sf-integral-compactification-system-realization). -/
def ringedProperProjection (d : RingedModels l E) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ringedPush l E f ⋙ Functor.curryObj (d.tensor Y).ordinary.tensor ⟶
      (Functor.postcompose₂.obj (ringedPush l E f)).obj
        ((((Functor.whiskeringLeft₂ _).obj (𝟭 _)).obj (ringedPull l E f)).obj
          (Functor.curryObj (d.tensor X).ordinary.tensor)) :=
  (ringedAdj l E f).rightAdjointProjectionMap
    (Functor.curry.mapIso (ringedTensorPull l E d f) ≪≫
      Functor.curryObjProdComp (ringedPull l E f) (ringedPull l E f)
        (d.tensor X).ordinary.tensor).hom

/-- The localized integral compactification exchange is the same recorded
supplied-domain composite, on the completed coefficient sheaves.
Source: blueprint def-exchange-projection
(blueprint: lem-sf-integral-compactification-system-realization). -/
def ringedCompactificationExchange (d : RingedModels l E)
    (a : RingedOpenComparisons l E d) {X Y X' Y' : Scheme.{u}}
    {f : X ⟶ Y} {f' : X' ⟶ Y'} (cf : Compactification f) (cf' : Compactification f')
    (x : X' ⟶ X) (y : Y' ⟶ Y) (z : cf'.Z ⟶ cf.Z)
    (wi : x ≫ cf.i = cf'.i ≫ z) (wp : z ≫ cf.g = cf'.g ≫ y)
    (hi : IsPullback x cf'.i cf.i z) :=
  SuppliedExchangeProjection.compactificationExchangeFromData
    (ringedOpen l E cf.i) (ringedOpen l E cf'.i)
    (ringedPull l E cf.g) (ringedPush l E cf.g) (ringedAdj l E cf.g)
    (ringedPull l E cf'.g) (ringedPush l E cf'.g) (ringedAdj l E cf'.g)
    (ringedPull l E y) (ringedPull l E x) (ringedPull l E z)
    (ringedSquare l E z cf'.g cf.g y wp) (a.beta x cf'.i cf.i z wi hi)

/-- The localized integral compactification projection uses the canonical tensor
mate, open tensor map, and inverse pullback composition, in the recorded order.
Source: blueprint def-exchange-projection
(blueprint: lem-sf-integral-compactification-system-realization). -/
def ringedCompactificationProjection (d : RingedModels l E)
    (a : RingedOpenComparisons l E d) {X Y : Scheme.{u}} {f : X ⟶ Y}
    (cf : Compactification f) (M : Integral l E X) (N : Integral l E Y) :
    (d.tensor Y).ordinary.tensor.obj
      ((ringedPush l E cf.g).obj ((ringedOpen l E cf.i).obj M), N) ⟶
    (ringedPush l E cf.g).obj ((ringedOpen l E cf.i).obj
      ((d.tensor X).ordinary.tensor.obj (M, (ringedPull l E f).obj N))) :=
  (((ringedProperProjection l E d cf.g).app ((ringedOpen l E cf.i).obj M)).app N) ≫
    (ringedPush l E cf.g).map
      ((a.projection cf.i).hom.app (M, (ringedPull l E cf.g).obj N) ≫
        (ringedOpen l E cf.i).map ((d.tensor X).ordinary.tensor.map
          (Prod.mkHom (𝟙 M) ((ringedPullComp l E cf.i cf.g).inv.app N ≫
            eqToHom (congrArg (fun g : X ⟶ Y ↦ (ringedPull l E g).obj N) cf.comm.symm)))))

/-- Canonical proper/open interchange and intrinsic pasting equations.
Source: Stacks 0F7B--0F7F
(blueprint: lem-sf-integral-compactification-system-realization). -/
structure ProperOpenCoherence (o : Operations l E) (c : Compositors l E o)
    (a : OpenComparisons l E o c) (b : CanonicalBridge l E o) where
  gamma : ∀ {U V W Z : Scheme.{u}} (k : U ⟶ V) (r : U ⟶ W)
      (p : V ⟶ Z) (i : W ⟶ Z) [IsOpenImmersion k] [IsOpenImmersion i]
      [QuasiCompact k] [QuasiCompact i] [IsProper r] [IsProper p] (_h : k ≫ p = r ≫ i),
      Operations.push l E o r ⋙ Operations.shriek l E o i ⟶
        Operations.shriek l E o k ⋙ Operations.push l E o p
  adjunct : ∀ {U V W Z : Scheme.{u}} (k : U ⟶ V) (r : U ⟶ W)
      (p : V ⟶ Z) (i : W ⟶ Z) [IsOpenImmersion k] [IsOpenImmersion i]
      [QuasiCompact k] [QuasiCompact i] [IsProper r] [IsProper p]
      (h : k ≫ p = r ≫ i) (M : System l E U),
      (o.extension i).adj.homEquiv _ _ ((gamma k r p i h).app M) =
        (properOpenLambda l E o c a k r p i h).inv.app M
  canonical : ∀ {U V W Z : Scheme.{u}} (k : U ⟶ V) (r : U ⟶ W)
      (p : V ⟶ Z) (i : W ⟶ Z) [IsOpenImmersion k] [IsOpenImmersion i]
      [QuasiCompact k] [QuasiCompact i] [IsProper r] [IsProper p]
      (h : k ≫ p = r ≫ i) (M : System l E U),
      (gamma k r p i h).app M ≫
        (b.push l E p).hom.app ((Operations.shriek l E o k).obj M) ≫
        (ProEtale.SemilinearProperOpen.R (scalarRings l E) (scalarTransitions l E) p).map
          ((b.shriek l E k).hom.app M) =
      (b.shriek l E i).hom.app ((Operations.push l E o r).obj M) ≫
        (ProEtale.SemilinearProperOpen.J (scalarRings l E) (scalarTransitions l E) i).map
          ((b.push l E r).hom.app M) ≫
        (ProEtale.SemilinearProperOpen.gamma (scalarRings l E) (scalarTransitions l E)
          k r p i h).app M
  vertical : ∀ {A C E₀ B₀ D F : Scheme.{u}}
      (k : A ⟶ B₀) (i : C ⟶ D) (j : E₀ ⟶ F)
      (r₁ : A ⟶ C) (r₂ : C ⟶ E₀) (p₁ : B₀ ⟶ D) (p₂ : D ⟶ F)
      [IsOpenImmersion k] [IsOpenImmersion i] [IsOpenImmersion j]
      [QuasiCompact k] [QuasiCompact i] [QuasiCompact j]
      [IsProper r₁] [IsProper r₂] [IsProper p₁] [IsProper p₂]
      (h₁ : k ≫ p₁ = r₁ ≫ i) (h₂ : i ≫ p₂ = r₂ ≫ j)
      (h : k ≫ (p₁ ≫ p₂) = (r₁ ≫ r₂) ≫ j) (M : System l E A),
      (Operations.shriek l E o j).map ((c.pushComp l E r₁ r₂).hom.app M) ≫
          (gamma k (r₁ ≫ r₂) (p₁ ≫ p₂) j h).app M ≫
          (c.pushComp l E p₁ p₂).inv.app ((Operations.shriek l E o k).obj M) =
        (gamma i r₂ p₂ j h₂).app ((Operations.push l E o r₁).obj M) ≫
          (Operations.push l E o p₂).map ((gamma k r₁ p₁ i h₁).app M)
  horizontal : ∀ {A C E₀ B₀ D F : Scheme.{u}}
      (k : A ⟶ B₀) (ll : B₀ ⟶ E₀) (i : C ⟶ D) (j : D ⟶ F)
      (r : A ⟶ C) (p : B₀ ⟶ D) (q : E₀ ⟶ F)
      [IsOpenImmersion k] [IsOpenImmersion ll] [IsOpenImmersion i] [IsOpenImmersion j]
      [QuasiCompact k] [QuasiCompact ll] [QuasiCompact i] [QuasiCompact j]
      [IsProper r] [IsProper p] [IsProper q]
      (h₁ : k ≫ p = r ≫ i) (h₂ : ll ≫ q = p ≫ j)
      (h : (k ≫ ll) ≫ q = r ≫ (i ≫ j)) (M : System l E A),
      (c.openComp l E i j).hom.app ((Operations.push l E o r).obj M) ≫
          (gamma (k ≫ ll) r q (i ≫ j) h).app M ≫
          (Operations.push l E o q).map ((c.openComp l E k ll).inv.app M) =
        (Operations.shriek l E o j).map ((gamma k r p i h₁).app M) ≫
          (gamma ll p q j h₂).app ((Operations.shriek l E o k).obj M)
  baseChange : ∀ {V W S T V₁ W₁ S₁ T₁ : Scheme.{u}}
      (k : V ⟶ W) (i : S ⟶ T) (r : V ⟶ S) (p : W ⟶ T)
      (k₁ : V₁ ⟶ W₁) (i₁ : S₁ ⟶ T₁) (r₁ : V₁ ⟶ S₁) (p₁ : W₁ ⟶ T₁)
      (aa : W₁ ⟶ W) (bb : T₁ ⟶ T) (cc : S₁ ⟶ S) (d : V₁ ⟶ V)
      [IsOpenImmersion k] [IsOpenImmersion i]
      [IsOpenImmersion k₁] [IsOpenImmersion i₁]
      [QuasiCompact k] [QuasiCompact i] [QuasiCompact k₁] [QuasiCompact i₁]
      [IsProper r] [IsProper p] [IsProper r₁] [IsProper p₁]
      (h : k ≫ p = r ≫ i) (h₁ : k₁ ≫ p₁ = r₁ ≫ i₁)
      (wk : d ≫ k = k₁ ≫ aa) (wi : cc ≫ i = i₁ ≫ bb)
      (wp : aa ≫ p = p₁ ≫ bb) (wr : d ≫ r = r₁ ≫ cc)
      (sk : IsPullback d k₁ k aa) (si : IsPullback cc i₁ i bb)
      (_sp : IsPullback aa p₁ p bb) (_sr : IsPullback d r₁ r cc) (M : System l E V),
      (pull l E bb).map ((gamma k r p i h).app M) ≫
          (properExchange l E o c aa p₁ p bb wp).app ((Operations.shriek l E o k).obj M) ≫
          (Operations.push l E o p₁).map ((a.beta d k₁ k aa wk sk).hom.app M) =
        (a.beta cc i₁ i bb wi si).hom.app ((Operations.push l E o r).obj M) ≫
          (Operations.shriek l E o i₁).map ((properExchange l E o c d r₁ r cc wr).app M) ≫
          (gamma k₁ r₁ p₁ i₁ h₁).app ((pull l E d).obj M)


/-- The chosen compactification ambient scheme over the original base.
Source: blueprint fix-prop-coherence, nested compactifications
(blueprint: lem-sf-integral-compactification-system-realization). -/
def compactAmbient {B : Scheme.{u}} {U V : Over B} {f : U ⟶ V}
    (cf : Compactification f.left) : Over B := Over.mk (cf.g ≫ V.hom)

/-- The actual open compactification arrow as a morphism over the base.
Source: blueprint fix-prop-coherence, nested compactifications
(blueprint: lem-sf-integral-compactification-system-realization). -/
def compactOpen {B : Scheme.{u}} {U V : Over B} {f : U ⟶ V}
    (cf : Compactification f.left) : U ⟶ compactAmbient (f := f) cf :=
  Over.homMk cf.i ((Category.assoc cf.i cf.g V.hom).symm.trans
    ((congrArg (fun g : U.left ⟶ V.left ↦ g ≫ V.hom) cf.comm.symm).trans f.w))

/-- The actual proper compactification arrow as a morphism over the base.
Source: blueprint fix-prop-coherence, nested compactifications
(blueprint: lem-sf-integral-compactification-system-realization). -/
def compactProper {B : Scheme.{u}} {U V : Over B} {f : U ⟶ V}
    (cf : Compactification f.left) : compactAmbient (f := f) cf ⟶ V := Over.homMk cf.g rfl

/-- Evaluate the actual system expression at a specified family.
Source: Stacks 0941 (blueprint: lem-sf-integral-compactification-system-realization). -/
abbrev Expression.systemObj {B : Scheme.{u}} {I : Type u} {X : I → Over B}
    {W : Over B} (e : Expression B I X W) (o : Operations l E)
    (M : ∀ i, System l E (X i).left) :=
  (e.evaluate (systemInterpretation l E o)).obj M

/-- Evaluate the localized ordinary ringed-site expression at the same typed inputs.
Source: Stacks 07A6 (blueprint: lem-sf-integral-compactification-system-realization). -/
abbrev Expression.ringedObj {B : Scheme.{u}} {I : Type u} {X : I → Over B}
    {W : Over B} (e : Expression B I X W) (d : RingedModels l E)
    (K : ∀ i, Integral l E (X i).left) :=
  (e.evaluate (ringedInterpretation l E d)).obj K

section CanonicalPairs
variable (o : Operations l E) (c : Compositors l E o) (a : OpenComparisons l E o c)
  (bridge : CanonicalBridge l E o) (h : ProperOpenCoherence l E o c a bridge)
  (d : RingedModels l E) (b : RingedOpenComparisons l E d)
  (q : RingedProperOpen l E d b)
  {B : Scheme.{u}} {I : Type u} {X : I → Over B}
  (M : ∀ i, System l E (X i).left) (K : ∀ i, Integral l E (X i).left)

/-- Pairs of the prescribed system and localized ringed-site isomorphisms. The indices
are the actual arrows, not freely supplied maps. Inverses are included by the arrow
closure in the next definition. Source: blueprint fix-prop-coherence, generators
(blueprint: lem-sf-integral-compactification-system-realization). -/
inductive CanonicalIsoPair : {W : Over B} → (e t : Expression B I X W) →
    (e.systemObj l E o M ≅ t.systemObj l E o M) →
    (e.ringedObj l E d K ≅ t.ringedObj l E d K) → Prop where
  | pullComp {U V W : Over B} (f : U ⟶ V) (g : V ⟶ W)
      (e : Expression B I X W) :
    CanonicalIsoPair (.pull (f ≫ g) e) (.pull f (.pull g e))
      ((c.pullComp f.left g.left).app (e.systemObj l E o M))
      ((ringedPullComp l E f.left g.left).app (e.ringedObj l E d K))
  | pushComp {U V W : Over B} (f : U ⟶ V) (g : V ⟶ W)
      (hf : IsProper f.left) (hg : IsProper g.left) (hfg : IsProper (f ≫ g).left)
      (e : Expression B I X U) :
    CanonicalIsoPair (.push g hg (.push f hf e)) (.push (f ≫ g) hfg e)
      ((c.pushComp l E f.left g.left).app (e.systemObj l E o M))
      ((ringedPushComp l E f.left g.left).app (e.ringedObj l E d K))
  | openComp {U V W : Over B} (j : U ⟶ V) (k : V ⟶ W)
      [hj : IsOpenImmersion j.left] [hk : IsOpenImmersion k.left]
      (qj : QuasiCompact j.left) (qk : QuasiCompact k.left)
      (qjk : QuasiCompact (j ≫ k).left) (e : Expression B I X U) :
    CanonicalIsoPair (.shriek k hk qk (.shriek j hj qj e))
      (.shriek (j ≫ k) (inferInstance : IsOpenImmersion (j.left ≫ k.left)) qjk e)
      ((c.openComp l E j.left k.left).app (e.systemObj l E o M))
      ((ringedOpenComp l E j.left k.left).app (e.ringedObj l E d K))
  | tensorAssoc {W : Over B} (e f g : Expression B I X W) :
    CanonicalIsoPair (.tensor (.tensor e f) g) (.tensor e (.tensor f g))
      ((calculus l E W.left).systemClosed.monoidal.associator
        (e.systemObj l E o M) (f.systemObj l E o M) (g.systemObj l E o M))
      (ringedAssociator l E d W.left
        (e.ringedObj l E d K) (f.ringedObj l E d K) (g.ringedObj l E d K))
  | tensorPull {U V : Over B} (f : U ⟶ V) (e t : Expression B I X V) :
    CanonicalIsoPair (.pull f (.tensor e t)) (.tensor (.pull f e) (.pull f t))
      ((pullbackTensorSystemComparison l E f.left).app
        (e.systemObj l E o M, t.systemObj l E o M))
      ((ringedTensorPull l E d f.left).app (e.ringedObj l E d K, t.ringedObj l E d K))
  | beta {U' U V' V : Over B} (v : U' ⟶ U) (j' : U' ⟶ V')
      (j : U ⟶ V) (g : V' ⟶ V)
      [hj : IsOpenImmersion j.left] [hj' : IsOpenImmersion j'.left]
      (qj : QuasiCompact j.left) (qj' : QuasiCompact j'.left)
      (w : v.left ≫ j.left = j'.left ≫ g.left)
      (sq : IsPullback v.left j'.left j.left g.left) (e : Expression B I X U) :
    CanonicalIsoPair (.pull g (.shriek j hj qj e))
      (.shriek j' hj' qj' (.pull v e))
      ((a.beta v.left j'.left j.left g.left w sq).app (e.systemObj l E o M))
      ((b.beta v.left j'.left j.left g.left w sq).app (e.ringedObj l E d K))
  | clopen {U V : Over B} (j : U ⟶ V)
      [hj : IsOpenImmersion j.left] [IsClosedImmersion j.left]
      (qj : QuasiCompact j.left) (hp : IsProper j.left) (e : Expression B I X U) :
    CanonicalIsoPair (.shriek j hj qj e) (.push j hp e)
      ((a.clopen j.left).app (e.systemObj l E o M))
      ((b.clopen j.left).app (e.ringedObj l E d K))
  | supportExpansion {U V : Over B} (f : U ⟶ V) (cf : Compactification f.left)
      (qj : QuasiCompact cf.i) (e : Expression B I X U) :
    CanonicalIsoPair (.compactSupport f cf e)
      (.push (compactProper (f := f) cf) (inferInstance : IsProper cf.g)
        (.shriek (compactOpen (f := f) cf) (inferInstance : IsOpenImmersion cf.i) qj e))
      (Iso.refl _) (Iso.refl _)
  | openProjection {U V : Over B} (j : U ⟶ V)
      [hj : IsOpenImmersion j.left] (qj : QuasiCompact j.left)
      (e : Expression B I X U) (t : Expression B I X V) :
    CanonicalIsoPair (.tensor (.shriek j hj qj e) t)
      (.shriek j hj qj (.tensor e (.pull j t)))
      ((a.projection j.left).app (e.systemObj l E o M, t.systemObj l E o M))
      ((b.projection j.left).app (e.ringedObj l E d K, t.ringedObj l E d K))

/-- The basic structural generator pairs have their actual maps as indices.
There is no constructor for a freely supplied pair of arrows.
Source: blueprint fix-prop-coherence, generator sentence
(blueprint: lem-sf-integral-compactification-system-realization). -/
inductive BasicPair : {W : Over B} → (e t : Expression B I X W) →
    (e.systemObj l E o M ⟶ t.systemObj l E o M) →
    (e.ringedObj l E d K ⟶ t.ringedObj l E d K) → Prop where
  | isoHom {W : Over B} {e t : Expression B I X W}
      {s : e.systemObj l E o M ≅ t.systemObj l E o M}
      {r : e.ringedObj l E d K ≅ t.ringedObj l E d K} :
    CanonicalIsoPair l E o c a d b M K e t s r → BasicPair e t s.hom r.hom
  | isoInv {W : Over B} {e t : Expression B I X W}
      {s : e.systemObj l E o M ≅ t.systemObj l E o M}
      {r : e.ringedObj l E d K ≅ t.ringedObj l E d K} :
    CanonicalIsoPair l E o c a d b M K e t s r → BasicPair t e s.inv r.inv
  | pullUnit {U V : Over B} (f : U ⟶ V) (hf : IsProper f.left)
      (e : Expression B I X V) :
    BasicPair e (.push f hf (.pull f e))
      (((o.direct f.left).adj).unit.app (e.systemObj l E o M))
      ((ringedAdj l E f.left).unit.app (e.ringedObj l E d K))
  | pullCounit {U V : Over B} (f : U ⟶ V) (hf : IsProper f.left)
      (e : Expression B I X U) :
    BasicPair (.pull f (.push f hf e)) e
      (((o.direct f.left).adj).counit.app (e.systemObj l E o M))
      ((ringedAdj l E f.left).counit.app (e.ringedObj l E d K))
  | openUnit {U V : Over B} (j : U ⟶ V) [hj : IsOpenImmersion j.left] (qj : QuasiCompact j.left)
      (e : Expression B I X U) :
    BasicPair e (.pull j (.shriek j hj qj e))
      (((o.extension j.left).adj).unit.app (e.systemObj l E o M))
      ((ringedOpenAdj l E j.left).unit.app (e.ringedObj l E d K))
  | openCounit {U V : Over B} (j : U ⟶ V) [hj : IsOpenImmersion j.left] (qj : QuasiCompact j.left)
      (e : Expression B I X V) :
    BasicPair (.shriek j hj qj (.pull j e)) e
      (((o.extension j.left).adj).counit.app (e.systemObj l E o M))
      ((ringedOpenAdj l E j.left).counit.app (e.ringedObj l E d K))
  | properOpen {U V W Z : Over B}
      (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
      [hk : IsOpenImmersion k.left] [hi : IsOpenImmersion i.left]
      [qk : QuasiCompact k.left] [qi : QuasiCompact i.left]
      [hr : IsProper r.left] [hp : IsProper p.left]
      (w : k.left ≫ p.left = r.left ≫ i.left) (e : Expression B I X U) :
    BasicPair (.shriek i hi qi (.push r hr e))
      (.push p hp (.shriek k hk qk e))
      ((h.gamma k.left r.left p.left i.left w).app (e.systemObj l E o M))
      ((q.gamma k.left r.left p.left i.left w).app (e.ringedObj l E d K))
  | exchange {U V W Z : Over B}
      (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
      (hr : IsProper r.left) (hp : IsProper p.left)
      (w : k.left ≫ p.left = r.left ≫ i.left) (e : Expression B I X V) :
    BasicPair (.pull i (.push p hp e)) (.push r hr (.pull k e))
      ((properExchange l E o c k.left r.left p.left i.left w).app
        (e.systemObj l E o M))
      ((mateEquiv (ringedAdj l E p.left) (ringedAdj l E r.left)
        (TwoSquare.mk _ _ _ _ (ringedSquare l E k.left r.left p.left i.left w).hom)).natTrans.app
          (e.ringedObj l E d K))
  | projection {U V : Over B} (f : U ⟶ V) (hf : IsProper f.left)
      (e : Expression B I X U) (t : Expression B I X V) :
    BasicPair (.tensor (.push f hf e) t) (.push f hf (.tensor e (.pull f t)))
      (((properProjection l E o f.left).app (e.systemObj l E o M)).app
        (t.systemObj l E o M))
      (((ringedProperProjection l E d f.left).app (e.ringedObj l E d K)).app
        (t.ringedObj l E d K))
  | compactExchange {U V U' V' : Over B}
      (f : U ⟶ V) (f' : U' ⟶ V') (cf : Compactification f.left)
      (cf' : Compactification f'.left) (x : U' ⟶ U) (y : V' ⟶ V) (z : cf'.Z ⟶ cf.Z)
      (wi : x.left ≫ cf.i = cf'.i ≫ z) (wp : z ≫ cf.g = cf'.g ≫ y.left)
      (hi : IsPullback x.left cf'.i cf.i z) (e : Expression B I X U) :
    BasicPair (.pull y (.compactSupport f cf e)) (.compactSupport f' cf' (.pull x e))
      ((compactificationExchange l E o c a cf cf' x.left y.left z wi wp hi).app
        (e.systemObj l E o M))
      ((ringedCompactificationExchange l E d b cf cf' x.left y.left z wi wp hi).app
        (e.ringedObj l E d K))
  | compactProjection {U V : Over B} (f : U ⟶ V) (cf : Compactification f.left)
      (e : Expression B I X U) (t : Expression B I X V) :
    BasicPair (.tensor (.compactSupport f cf e) t)
      (.compactSupport f cf (.tensor e (.pull f t)))
      (compactificationProjection l E o c a cf (e.systemObj l E o M) (t.systemObj l E o M))
      (ringedCompactificationProjection l E d b cf
        (e.ringedObj l E d K) (t.ringedObj l E d K))

/-- Canonical integral generators and their finite expression contexts. A basic
integral map is the recorded localized ringed-site map transported by the recursively
specified completion units. Whiskering uses the actual Expression constructors.
Source: Stacks 099N, 07A4, 0E48; blueprint fix-prop-coherence
(blueprint: lem-sf-integral-compactification-system-realization). -/
inductive CanonicalPair : {W : Over B} → (e t : Expression B I X W) →
    (e.systemObj l E o M ⟶ t.systemObj l E o M) →
    ((e.evaluate (integralInterpretation l E)).obj K ⟶
      (t.evaluate (integralInterpretation l E)).obj K) → Prop where
  | basic {W : Over B} {e t : Expression B I X W}
      {s : e.systemObj l E o M ⟶ t.systemObj l E o M}
      {r : e.ringedObj l E d K ⟶ t.ringedObj l E d K}
      (g : BasicPair l E o c a bridge h d b q M K e t s r)
      (he : IsIso (e.completionMap l E d K)) :
    CanonicalPair e t s
      (@inv _ _ _ _ (e.completionMap l E d K) he ≫ r ≫ t.completionMap l E d K)
  | identity {W : Over B} (e : Expression B I X W) : CanonicalPair e e (𝟙 _) (𝟙 _)
  | comp {W : Over B} {e t v : Expression B I X W}
      {s₁ : e.systemObj l E o M ⟶ t.systemObj l E o M}
      {s₂ : t.systemObj l E o M ⟶ v.systemObj l E o M}
      {r₁ : (e.evaluate (integralInterpretation l E)).obj K ⟶
        (t.evaluate (integralInterpretation l E)).obj K}
      {r₂ : (t.evaluate (integralInterpretation l E)).obj K ⟶
        (v.evaluate (integralInterpretation l E)).obj K}
      (_gt : t.geometric) (_ht : t.admissible l E o M) :
    CanonicalPair e t s₁ r₁ → CanonicalPair t v s₂ r₂ →
      CanonicalPair e v (s₁ ≫ s₂) (r₁ ≫ r₂)
  | pull {U V : Over B} (f : U ⟶ V)
      {e t : Expression B I X V}
      {s : e.systemObj l E o M ⟶ t.systemObj l E o M}
      {r : (e.evaluate (integralInterpretation l E)).obj K ⟶
        (t.evaluate (integralInterpretation l E)).obj K} :
    CanonicalPair e t s r → CanonicalPair (.pull f e) (.pull f t)
      ((pull l E f.left).map s) ((integralDerivedPullback l E f.left).map r)
  | push {U V : Over B} (f : U ⟶ V) (hf : IsProper f.left)
      {e t : Expression B I X U}
      {s : e.systemObj l E o M ⟶ t.systemObj l E o M}
      {r : (e.evaluate (integralInterpretation l E)).obj K ⟶
        (t.evaluate (integralInterpretation l E)).obj K} :
    CanonicalPair e t s r → CanonicalPair (.push f hf e) (.push f hf t)
      ((Operations.push l E o f.left).map s) ((ringedPush l E f.left).map r)
  | shriek {U V : Over B} (f : U ⟶ V) [hf : IsOpenImmersion f.left] (hq : QuasiCompact f.left)
      {e t : Expression B I X U}
      {s : e.systemObj l E o M ⟶ t.systemObj l E o M}
      {r : (e.evaluate (integralInterpretation l E)).obj K ⟶
        (t.evaluate (integralInterpretation l E)).obj K} :
    CanonicalPair e t s r → CanonicalPair (.shriek f hf hq e) (.shriek f hf hq t)
      ((Operations.shriek l E o f.left).map s) ((ringedOpen l E f.left).map r)
  | compactSupport {U V : Over B} (f : U ⟶ V) (cf : Compactification f.left)
      {e t : Expression B I X U}
      {s : e.systemObj l E o M ⟶ t.systemObj l E o M}
      {r : (e.evaluate (integralInterpretation l E)).obj K ⟶
        (t.evaluate (integralInterpretation l E)).obj K} :
    CanonicalPair e t s r → CanonicalPair (.compactSupport f cf e) (.compactSupport f cf t)
      ((Operations.shriek l E o cf.i ⋙ Operations.push l E o cf.g).map s)
      ((PurCompactSupport.image (PurCompactSupport.completed l E) cf).map r)
  | tensor {W : Over B} {e t v z : Expression B I X W}
      {s₁ : e.systemObj l E o M ⟶ t.systemObj l E o M}
      {s₂ : v.systemObj l E o M ⟶ z.systemObj l E o M}
      {r₁ : (e.evaluate (integralInterpretation l E)).obj K ⟶
        (t.evaluate (integralInterpretation l E)).obj K}
      {r₂ : (v.evaluate (integralInterpretation l E)).obj K ⟶
        (z.evaluate (integralInterpretation l E)).obj K} :
    CanonicalPair e t s₁ r₁ → CanonicalPair v z s₂ r₂ →
      CanonicalPair (.tensor e v) (.tensor t z)
        ((calculus l E W.left).systemClosed.tensor.map (Prod.mkHom s₁ s₂))
        ((integralCompletedTensor l E W.left).map (Prod.mkHom r₁ r₂))

end CanonicalPairs

/-- Natural realization comparisons for every finite geometric expression.
Source: Stacks 0941 (blueprint: lem-sf-integral-compactification-system-realization).
Proof: strict-system models and expression-tree induction; cited nodes give generator,
whiskering, and refinement coherence. -/
structure Realizations (D : FiniteFieldDatum.{u}) (o : Operations l E) where
  /-- The proper/open mate, scalar restriction, and normalized pasting package. -/
  compositors : Compositors l E o
  openComparisons : OpenComparisons l E o compositors
  canonicalBridge : CanonicalBridge l E o
  properOpen : ProperOpenCoherence l E o compositors openComparisons canonicalBridge
  /-- The tensor/square identifications obey the displayed equation of
      lem-weil-pbc-ringed-exchange-tensor-coherence, before evaluation. -/
  ringedTensorCoherence : ∀ {U V W Z : Scheme.{u}}
    (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
    (h : k ≫ p = r ≫ i) (M : System l E V) (N : System l E Z),
    (IntegralSystemRealization.pull l E i).map
        (((properProjection l E o p).app M).app N) ≫
      (properExchange l E o compositors k r p i h).app
        ((calculus l E V).systemClosed.tensor.obj
          (M, (IntegralSystemRealization.pull l E p).obj N)) ≫
      (Operations.push l E o r).map
        ((pullbackTensorSystemComparison l E k).hom.app
          (M, (IntegralSystemRealization.pull l E p).obj N) ≫
        (calculus l E U).systemClosed.tensor.map
          (Prod.mkHom (𝟙 _) ((compositors.square l E k r p i h).inv.app N))) =
    (pullbackTensorSystemComparison l E i).hom.app ((Operations.push l E o p).obj M, N) ≫
      (calculus l E W).systemClosed.tensor.map
        (Prod.mkHom ((properExchange l E o compositors k r p i h).app M) (𝟙 _)) ≫
      ((properProjection l E o r).app ((IntegralSystemRealization.pull l E k).obj M)).app
        ((IntegralSystemRealization.pull l E i).obj N)
  /-- Every finite geometric expression has its natural realization comparison. -/
  comparison : ∀ {I : Type u} [Finite I]
    {X : I → Over (Spec (CommRingCat.of D.k))}
    {W : Over (Spec (CommRingCat.of D.k))}
    (e : Expression _ I X W) (_geometric : e.geometric),
    e.realizationSource l E o ≅ e.realizationTarget l E o
  realizationModel : RealizationModel l E o
  /-- The open comparison is the actual reduction mate followed by the inverse
      reconstruction unit. Its displayed equation fixes it without finite evaluation. -/
  openRealization : ∀ {U V : Scheme.{u}} (j : U ⟶ V)
    [IsOpenImmersion j] (_hq : QuasiCompact j) (M : System l E U)
    (_hM : Good l E U M) (_hJ : Good l E V ((Operations.shriek l E o j).obj M)),
    (coefficientSequenceLimit l E V).obj ((Operations.shriek l E o j).obj M) ≅
      ((PurCompactSupport.openExtension (PurCompactSupport.completed l E) j).mapDerivedCategory).obj
        ((coefficientSequenceLimit l E U).obj M)
  openNormalization : ∀ {U V : Scheme.{u}} (j : U ⟶ V)
    [IsOpenImmersion j] [QuasiCompact j] (M : System l E U)
    (hM : Good l E U M) (hJ : Good l E V ((Operations.shriek l E o j).obj M)),
    (coefficientSequenceLimit l E V).map
      ((Operations.shriek l E o j).map ((calculus l E U).adjunction.counit.app M)) ≫
      (openRealization j inferInstance M hM hJ).hom ≫
      (calculus l E V).adjunction.unit.app
        (((PurCompactSupport.openExtension
          (PurCompactSupport.completed l E) j).mapDerivedCategory).obj
          ((coefficientSequenceLimit l E U).obj M)) =
    (coefficientSequenceLimit l E V).map
      ((realizationModel.openReduction l E j).app ((coefficientSequenceLimit l E U).obj M))
  /-- Variable comparisons are the inverse of the actual reconstruction unit. -/
  inputNormalization : ∀ {I : Type u} [Finite I]
    {X : I → Over (Spec (CommRingCat.of D.k))} (i : I)
    (g : (Expression.var (X := X) i).geometric)
    (K : ((Expression.var (X := X) i).domain l E o).FullSubcategory),
    (calculus l E (X i).left).adjunction.unit.app (K.obj i) ≫
      (comparison (.var i) g).hom.app K = 𝟙 (K.obj i)
  /-- The proper-image comparison is the right-adjoint conjugate, recursively
      followed by proper image of the inner comparison. -/
  push : ∀ {I : Type u} [Finite I]
    {X : I → Over (Spec (CommRingCat.of D.k))}
    {U V : Over (Spec (CommRingCat.of D.k))}
    (f : U ⟶ V) (hp : IsProper f.left) (e : Expression _ I X U)
    (ge : e.geometric) (g : (Expression.push f hp e).geometric)
    (K : ((Expression.push f hp e).domain l E o).FullSubcategory),
    (comparison (.push f hp e) g).hom.app K =
      (realizationModel.push l E f.left).hom.app
        ((e.evaluate (systemInterpretation l E o)).obj ((inputReduction l E X).obj K.obj)) ≫
      (PurCompactSupport.push (PurCompactSupport.completed l E) f.left).map
        ((comparison e ge).hom.app ⟨K.obj, K.property.1, by
          simpa [Expression.admissible] using K.property.2.2⟩)
  /-- Pullback comparison is fixed by the published K-flat quotient-tower model. -/
  pull : ∀ {I : Type u} [Finite I]
    {X : I → Over (Spec (CommRingCat.of D.k))}
    {U V : Over (Spec (CommRingCat.of D.k))}
    (f : U ⟶ V) (e : Expression _ I X V)
    (ge : e.geometric) (g : (Expression.pull f e).geometric)
    (K : ((Expression.pull f e).domain l E o).FullSubcategory),
    (coefficientSequenceLimit l E U.left).map
      ((IntegralSystemRealization.pull l E f.left).map
        ((calculus l E V.left).adjunction.counit.app
          ((e.evaluate (systemInterpretation l E o)).obj ((inputReduction l E X).obj K.obj)))) ≫
      (comparison (.pull f e) g).hom.app K =
    (pullbackTensorIntegralPullbackModel l E f.left).inv.app
      ((coefficientSequenceLimit l E V.left).obj
        ((e.evaluate (systemInterpretation l E o)).obj ((inputReduction l E X).obj K.obj))) ≫
      (integralDerivedPullback l E f.left).map
        ((comparison e ge).hom.app ⟨K.obj, K.property.1, by
          simpa [Expression.admissible] using K.property.2.2⟩)
  /-- Open comparison uses the specified open-reduction mate and actual unit. -/
  shriek : ∀ {I : Type u} [Finite I]
    {X : I → Over (Spec (CommRingCat.of D.k))}
    {U V : Over (Spec (CommRingCat.of D.k))}
    (j : U ⟶ V) [hj : IsOpenImmersion j.left] [hq : QuasiCompact j.left]
    (e : Expression _ I X U) (ge : e.geometric)
    (g : (Expression.shriek j hj hq e).geometric)
    (K : ((Expression.shriek j hj hq e).domain l E o).FullSubcategory),
    (comparison (.shriek j hj hq e) g).hom.app K =
      (openRealization j.left hq
        ((e.evaluate (systemInterpretation l E o)).obj ((inputReduction l E X).obj K.obj))
        (e.admissibleGood l E o _ (by
          simpa [Expression.admissible] using K.property.2.2)) K.property.2.1).hom ≫
      ((PurCompactSupport.openExtension
        (PurCompactSupport.completed l E) j.left).mapDerivedCategory).map
        ((comparison e ge).hom.app ⟨K.obj, K.property.1, by
          simpa [Expression.admissible] using K.property.2.2⟩)
  /-- Tensor comparison is fixed by the canonical two-input K-flat total tensor model. -/
  tensor : ∀ {I : Type u} [Finite I]
    {X : I → Over (Spec (CommRingCat.of D.k))}
    {W : Over (Spec (CommRingCat.of D.k))}
    (e t : Expression _ I X W) (ge : e.geometric) (gt : t.geometric)
    (g : (Expression.tensor e t).geometric)
    (K : ((Expression.tensor e t).domain l E o).FullSubcategory),
    (coefficientSequenceLimit l E W.left).map
      ((calculus l E W.left).systemClosed.tensor.map
        (((calculus l E W.left).adjunction.counit.app
            ((e.evaluate (systemInterpretation l E o)).obj ((inputReduction l E X).obj K.obj))),
          ((calculus l E W.left).adjunction.counit.app
            ((t.evaluate (systemInterpretation l E o)).obj ((inputReduction l E X).obj K.obj))))) ≫
      (comparison (.tensor e t) g).hom.app K =
    (pullbackTensorIntegralTensorModel l E W.left).inv.app
      (((coefficientSequenceLimit l E W.left).obj
          ((e.evaluate (systemInterpretation l E o)).obj ((inputReduction l E X).obj K.obj))),
        ((coefficientSequenceLimit l E W.left).obj
          ((t.evaluate (systemInterpretation l E o)).obj ((inputReduction l E X).obj K.obj)))) ≫
      (integralCompletedTensor l E W.left).map
        (Prod.mkHom
          ((comparison e ge).hom.app ⟨K.obj, K.property.1, by
            simpa [Expression.admissible] using K.property.2.2.1⟩)
          ((comparison t gt).hom.app ⟨K.obj, K.property.1, by
            simpa [Expression.admissible] using K.property.2.2.2⟩))
  /-- Compact support uses exactly the recursively realized J-then-S composite. -/
  supportRecursion : ∀ {I : Type u} [Finite I]
    {X : I → Over (Spec (CommRingCat.of D.k))}
    {U V : Over (Spec (CommRingCat.of D.k))}
    (f : U ⟶ V) (c : Compactification f.left) (e : Expression _ I X U)
    (ge : e.geometric) (g : (Expression.compactSupport f c e).geometric)
    (K : ((Expression.compactSupport f c e).domain l E o).FullSubcategory),
    (comparison (.compactSupport f c e) g).hom.app K =
      (realizationModel.push l E c.g).hom.app
        ((Operations.shriek l E o c.i).obj
          ((e.evaluate (systemInterpretation l E o)).obj ((inputReduction l E X).obj K.obj))) ≫
      (PurCompactSupport.push (PurCompactSupport.completed l E) c.g).map
        ((openRealization c.i (compactOpenQuasiCompact c g.2.2.2.2.1)
          ((e.evaluate (systemInterpretation l E o)).obj ((inputReduction l E X).obj K.obj))
          (e.admissibleGood l E o _ (by
            simpa [Expression.admissible] using K.property.2.2.1))
          (by simpa [Expression.admissible] using K.property.2.2.2)).hom ≫
        ((PurCompactSupport.openExtension
          (PurCompactSupport.completed l E) c.i).mapDerivedCategory).map
          ((comparison e ge).hom.app ⟨K.obj, K.property.1, by
            simpa [Expression.admissible] using K.property.2.2.1⟩))
  /-- The actual reduction comparison for each expression, in the derived system
      category itself. It is never assembled from unrelated evaluated arrows. -/
  reduction : ∀ {I : Type u} [Finite I]
    {X : I → Over (Spec (CommRingCat.of D.k))}
    {W : Over (Spec (CommRingCat.of D.k))}
    (e : Expression _ I X W) (_geometric : e.geometric),
    (e.domain l E o).ι ⋙ inputReduction l E X ⋙
      e.evaluate (systemInterpretation l E o) ≅
    e.realizationTarget l E o ⋙ (calculus l E W.left).reduction
  /-- Fix the reconstruction comparison by the actual reduction-limit counit. -/
  normalization : ∀ {I : Type u} [Finite I]
    {X : I → Over (Spec (CommRingCat.of D.k))}
    {W : Over (Spec (CommRingCat.of D.k))}
    (e : Expression _ I X W) (g : e.geometric)
    (K : (e.domain l E o).FullSubcategory),
    (calculus l E W.left).reduction.map ((comparison e g).hom.app K) ≫
      (reduction e g).inv.app K =
    (calculus l E W.left).adjunction.counit.app
      ((e.evaluate (systemInterpretation l E o)).obj ((inputReduction l E X).obj K.obj))
  /-- Published completion-unit models fix the localized integral generators. -/
  ringedModels : RingedModels l E
  ringedOpenComparisons : RingedOpenComparisons l E ringedModels
  ringedProperOpen : RingedProperOpen l E ringedModels ringedOpenComparisons
  /-- The actual ordinary-to-completed expression comparison is invertible on
      the stated domain; no additional input assumption is imposed. -/
  completionIso : ∀ {I : Type u} [Finite I]
    {X : I → Over (Spec (CommRingCat.of D.k))}
    {W : Over (Spec (CommRingCat.of D.k))}
    (e : Expression _ I X W) (_ge : e.geometric)
    (K : (e.domain l E o).FullSubcategory),
    IsIso (e.completionMap l E ringedModels K.obj)
  /-- Every specific canonical generator pair and every finite outer expression
      context satisfies the required equation of actual maps. -/
  coherence : ∀ {I : Type u} [Finite I]
    {X : I → Over (Spec (CommRingCat.of D.k))}
    {W : Over (Spec (CommRingCat.of D.k))}
    (e t : Expression _ I X W) (ge : e.geometric) (gt : t.geometric)
    (K : (e.domain l E o).FullSubcategory) (ht : t.domain l E o K.obj)
    (s : e.systemObj l E o ((inputReduction l E X).obj K.obj) ⟶
      t.systemObj l E o ((inputReduction l E X).obj K.obj))
    (r : (e.evaluate (integralInterpretation l E)).obj K.obj ⟶
      (t.evaluate (integralInterpretation l E)).obj K.obj),
    CanonicalPair l E o compositors openComparisons canonicalBridge properOpen
      ringedModels ringedOpenComparisons ringedProperOpen
      ((inputReduction l E X).obj K.obj) K.obj e t s r →
    (coefficientSequenceLimit l E W.left).map s ≫
      (comparison t gt).hom.app ⟨K.obj, ht⟩ = (comparison e ge).hom.app K ≫ r
  /-- The compact-support comparison is fixed at all finite projections by the
      prescribed compactification mate, rather than an arbitrary endpoint iso. -/
  compactSupport : ∀ {I : Type u} [Finite I]
    {X : I → Over (Spec (CommRingCat.of D.k))}
    {U V : Over (Spec (CommRingCat.of D.k))}
    (f : U ⟶ V) (c : Compactification f.left) (e : Expression _ I X U)
    (g : (Expression.compactSupport f c e).geometric)
    (K : ((Expression.compactSupport f c e).domain l E o).FullSubcategory) (n : ℕ),
    (scalarReductionDerivedExtension l E V.left n).map
      ((comparison (.compactSupport f c e) g).hom.app K) ≫
        (PurCompactSupport.finiteReductionIso l E V.left n).inv.app
          ((PurCompactSupport.image (PurCompactSupport.completed l E) c).obj
            ((e.evaluate (integralInterpretation l E)).obj K.obj)) ≫
        (PurCompactSupport.comparison (PurCompactSupport.reduction l E (n + 1)
          (Nat.le_add_left 1 n)) c).app
            ((e.evaluate (integralInterpretation l E)).obj K.obj) ≫
        (PurCompactSupport.finiteImageIso l E n c).hom.app
          ((pbcDerivedExtend (PurCompactSupport.projection l E (n + 1)
            (Nat.le_add_left 1 n) U.left)).obj
              ((e.evaluate (integralInterpretation l E)).obj K.obj)) ≫
        (sfAmbientCompactSupportCandidate (Padic.coefficientExtensionRing l E (n + 1)) c).map
          ((PurCompactSupport.finiteReductionIso l E U.left n).hom.app
            ((e.evaluate (integralInterpretation l E)).obj K.obj)) =
    ((calculus l E V.left).reductionEvaluation n).inv.app
      ((coefficientSequenceLimit l E V.left).obj
        (((Expression.compactSupport f c e).evaluate (systemInterpretation l E o)).obj
          ((inputReduction l E X).obj K.obj))) ≫
      (coefficientSequenceDerivedEvaluation l E V.left n).map
        ((calculus l E V.left).adjunction.counit.app
          (((Expression.compactSupport f c e).evaluate (systemInterpretation l E o)).obj
            ((inputReduction l E X).obj K.obj))) ≫
      (supportEvaluation l E o c n).hom.app
        ((e.evaluate (systemInterpretation l E o)).obj ((inputReduction l E X).obj K.obj)) ≫
      (sfAmbientCompactSupportCandidate (Padic.coefficientExtensionRing l E (n + 1)) c).map
        ((coefficientSequenceDerivedEvaluation l E U.left n).map
          ((reduction e g.2.2.2.2.2).hom.app ⟨K.obj, K.property.1, by
            simpa [Expression.admissible] using K.property.2.2.1⟩) ≫
        ((calculus l E U.left).reductionEvaluation n).hom.app
          ((e.evaluate (integralInterpretation l E)).obj K.obj))


/-- Coherent integral realization of compactification expressions and their maps.
Source: Stacks 0941; blueprint fix-prop-coherence
(blueprint: lem-sf-integral-compactification-system-realization).

Proof:

1. Use the simultaneous semilinear-section models of [lem-coef-semilinear-derived-sections] for
the operations in the statement. In particular pullback, tensor, open extension, direct image,
their adjunctions and coefficient comparisons are constructions on one derived system category,
including their morphisms. The evaluated adjunctions are those of
[lem-pur-coefficient-system-derived-comparison]. Write $u:1\to\mathcal L\mathcal R$ and
$e:\mathcal R\mathcal L\to1$ for the actual unit and counit of
[lem-coef-derived-system-evaluation-calculus]. If $N$ is normalized,
[lem-coef-normalized-dvr-effectivity] identifies each $e_{N,n}$ with an isomorphism, the
scalar-extension adjoint of the total-limit projection. Since derived evaluations detect
isomorphisms, $e_N$ itself is an isomorphism of semilinear systems. This uses detection of
isomorphisms only. The limit $\mathcal L N$ is derived complete, and its reductions have precisely
the constructibility and common bounds of $N$, by the same counit isomorphisms and
[def-weil-derived-complete-integral-detailed].  For a derived-complete input $K$,
[def-weil-derived-complete] gives an isomorphism $K\cong\mathcal L\mathcal R K$: its Roos triangle
and the canonical total-limit Roos triangle are triangles of the same reduction tower. This
existence statement alone does not identify that isomorphism with $u_K$. Instead, the adjunction
identity $\mathcal L(e_N)\circ u_{\mathcal L N}=1$, with $e_N$ invertible, proves that
$u_{\mathcal L N}$ is invertible. Take $N=\mathcal R K$, which is normalized by derived tensor
reassociation, and use naturality of $u$ along the preceding isomorphism to conclude that the
specified $u_K$ is invertible. Thus on the complete/normalized domains we have the specific
inverse equivalence with unit $u$ and counit $e$. No arbitrary choice of a morphism between Roos
triangles defines a comparison.

2. Apply [lem-sf-semilinear-proper-open-mate-pasting] to the inverse ring sequence $C_n=A_n$. Its
intrinsic clopen projection gives $\alpha_Q$, its proper mate $\Gamma_Q$, and the specific
open-restriction isomorphism $\lambda_Q$; thus $\lambda_QP_i\Gamma_Q=1$. The geometry, properness
and quasi-compact open hypotheses are exactly those of the square under consideration. Its
scalar-restriction clause, with $B=R$ and the quotient maps $R\to A_n$, identifies this mate with
the normalized constant-$R$ tower map of [lem-cbc-strict-tower-proper-open-calculus]. The bounded
constructible etale-origin levels satisfy that node's finite evaluation hypothesis. All quotient
transitions are retained by these constructions.  The same new lemma gives horizontal, vertical,
base-change, identity and refinement pasting as identities inside $D(\mathscr S)$. In particular
its assertion is stronger than merely observing these equations after scalar restriction. These
are the proper/open generators and equations required below; the remaining projection and exchange
maps are their specified composites with tensor comparisons, units and counits
[def-exchange-projection].

3. For a basic operation $A$, first specify $d_A(K):\mathcal L A\mathcal R
K\xrightarrow{\sim}A_{\mathrm{int}}K$ (with two inputs for tensor). For $P_v$ and tensor these are
the identifications with the strict reduction-tower formulas of
[def-pur-integral-derived-operations, lem-pur-integral-operations-well-defined]: the total limit
$\mathcal L_W$ of a strict tower and the cone model $\operatorname{Cone}(1-s)[-1]$ on termwise
products are identified by the natural Roos triangle of
[lem-weil-pbc-ringed-strict-tower-homotopy-limit], the termwise products representing the derived
products; the simultaneous models ensure agreement on morphisms and transitions, not merely on
evaluated objects. For $S_p$ use the proper direct-image reduction-tower formula of
[def-weil-derived-direct-image]. For $S_pJ_j$, [lem-sf-compact-support-restriction-of-scalars]
gives the transition from $m$ to $n$: apply $Rp_{*,m}j_!$ to $K_m\to\operatorname{Res}_{m,n}K_n$,
then its coefficient-restriction isomorphism. These are exactly the transitions in
[def-weil-integral-rational-qbar-compact-support]. The simultaneous system construction and its
total limit therefore give $d_{S_pJ_j}$ to precisely that functor, including its maps.  For
standalone open extension apply [lem-sf-integral-open-reduction-comparison]. It supplies the
actual strict map $r_j$, completeness, and $d_{J_j}=u_{j_!K}^{-1}\mathcal L(r_j)^{-1}$ with the
localized ringed-site open adjunction. Its quasi-compactness hypothesis holds for these opens. The
common bounds remain the expressly assumed bounds of every intermediate system.

4. Define the comparisons by a genuine induction on expression trees. For a variable $K_i$ put
$c_{K_i}=u_{K_i}^{-1}$. For a normalized system $M$ at the source of a unary operation $A$, set
$$a_A(M)=d_A(\mathcal L M)\circ\bigl(\mathcal L A(e_M)\bigr)^{-1}:\mathcal L A M\longrightarrow
A_{\mathrm{int}}\mathcal L M.$$ For tensor use $$a_\otimes(M,N)=d_\otimes(\mathcal L M,\mathcal L
N)\circ\bigl(\mathcal L(e_M\otimes^L e_N)\bigr)^{-1}.$$ The inverses exist by step 1. If
$M=V(\mathcal R K_1,\ldots,\mathcal R K_s)$, define $c_{AV}=A_{\mathrm{int}}(c_V)\circ a_A(M)$. If
$M=V(\mathcal R K_i)$ and $N=T(\mathcal R K_i)$, define $c_{V\otimes
T}=(c_V\widehat\otimes^Lc_T)\circ a_\otimes(M,N)$. These formulas cover every unary and binary
node and decrease tree size at every invocation. Their sources and targets are the stated ones,
and each factor is natural and invertible. The induction is legitimate because every intermediate
system is assumed normalized, with compatible etale-origin witnesses and common finite
cohomological and Tor intervals.  The direct identification $d_{S_pJ_j}$ of step 3 agrees with the
recursive composite for $S_p(J_j(-))$. Indeed $r_j$ identifies $\mathcal R(j_!K)$ with
$J_j\mathcal R K$ on the very same quotient tower, and the recursion inserts $e_{J_j\mathcal R
K}^{-1}$. In the composite the adjacent $\mathcal R\mathcal L$ insertion cancels by $e_{\mathcal R
K}\circ\mathcal R(u_K)=1$ and naturality of $e$; the remaining tower is $S_pJ_j\mathcal R K$ with
the transitions specified in step 3. The total-limit and resolution comparisons of
[lem-coef-derived-system-evaluation-calculus, lem-coef-semilinear-derived-sections] make this an
equality of the prescribed comparisons. In particular the recursion does not replace the
compact-support definition by an unrelated isomorphic functor.

5. For each basic operation the actual coefficient map is $$r_A=e_{A\mathcal R K_i}\circ\mathcal
R(d_A^{-1})$$ by [lem-sf-generator-reduction-coherence]; the two-input formula holds for tensor.
Its hypotheses hold because all inputs and intermediate systems are normalized and satisfy the
stated origin and common bounds. Substitute these basic maps along a finite expression tree to
define $r_V$. Induction on tree size using step 4, naturality of $e$ and $e_{\mathcal R K}\mathcal
R(u_K)=1$ gives $$r_V=e_{V(\mathcal R K_i)}\circ\mathcal R(c_V^{-1}).$$ The base case is
$r_{K_i}=1$ by that triangle identity; for a unary node naturality moves the inner comparison past
$e$, and for a tensor node the same substitution applies in both slots.  For every basic generator
$\tau:V\to T$, the same lemma supplies the system square $$\tau_{\mathcal R K_i}r_V=r_T\mathcal
R(\tau_{\rm int}).$$ It covers the normalized open maps and proper/open interchange as well as
tensor, pullback and adjunction generators, before evaluation. Projection and exchange are the
composites prescribed by [def-exchange-projection]; paste the squares for their factors. The
tensor/square identifications in these composites are those of
[lem-weil-pbc-ringed-exchange-tensor-coherence].  Apply $\mathcal L$ to this square and substitute
the displayed expression for $r_V,r_T$. Naturality of $u$ and $\mathcal L(e_N)u_{\mathcal LN}=1$
cancel the outer unit/counit factors, giving $$c_T\circ\mathcal L(\tau_{\mathcal R K_i})=\tau_{\rm
int}\circ c_V.$$ This establishes the generator intertwining equation. Extension to arbitrary
outer expression contexts is the separate induction in step 6.

6. The generator equation remains true under every allowed expression context. For a unary outer
operation $A$, insert the two equations defining $c_{AV}$ and $c_{AT}$ from step 4 and use
naturality of $a_A$ at $\tau:V\to T$; the middle square is precisely $A_{\mathrm{int}}$ of the
equation in step 5. For tensor with a second expression use naturality of $a_\otimes$ in the
chosen slot; if both slots change, factor the map into the two slot maps and use bifunctoriality.
Induction on the number of outer nodes proves all the required whiskering equations. Composites of
generators are covered because the intervening $c_V^{-1}c_V$ cancel.  Apply this result to the
proper/open equations proved inside the semilinear category in step 2. The total-limit functor
preserves each equality of transformations. Conjugating by the $c_V$ of step 4 gives its integral
identity, with the canonical compositors checked in step 5. In particular the comparison of two
nested compactifications is the composite of their direct-image/open compositors and the
intervening proper/open generator, so the same calculation proves its compatibility. When
compatible composition towers are refined, [lem-cbc-compactifiable-compatible-tower] gives the
commuting proper maps on the ambient and intermediate schemes; the corresponding proper/open
squares need not be cartesian. Step 2 applies to precisely these general commutative squares, so
its vertical and horizontal laws identify the two refined composites. Their common-refinement
equalities then survive total limit with the comparisons just proved. This proves the required
refinement and nested-composition compatibility; it does not infer an equality from finite
evaluations or assert a canonical lift of unrelated finite-level arrows.

7. Naturality follows from the displayed recursion, since $u,e,d_A$ and all the adjunction
transposes are natural. For the zero input each additive unary operation and tensor with zero is
zero, and the maps into and out of the resulting zero object are its unique maps. For the identity
open, its open unit is identity, so the formulas for $\beta,\gamma$ and $\Gamma$ give identity
comparisons. For the empty open, $J_j=0$, so those formulas give the unique zero maps. For an
identity square the clopen projection is identity and the mate triangle identities give the
identity direct-image or open transformation. For an equal-index quotient $A_n\to A_n$, reduction
is the identity coefficient map and its comparison is the tensor unit identification. A single
compactification is exactly the $d_{S_pJ_j}$ checked in steps 3 and 4. For
$W=\operatorname{Spec}k$ and a degree-zero free coefficient module the recursion is ordinary
tensor reassociation and the inverse of its reduction-limit unit; rank zero is the preceding zero
case. All indices are $n\geq1$; no use of an undefined $n=0$ level occurs. These checks impose no
extra geometric or boundedness hypotheses.
-/
theorem integralCompactificationSystemRealization
    (D : FiniteFieldDatum.{u}) (_hl : l ≠ D.p) :
    ∃ o : Operations l E, Nonempty (Realizations l E D o) := by
  sorry

end IntegralSystemRealization
end WeilConjectures
