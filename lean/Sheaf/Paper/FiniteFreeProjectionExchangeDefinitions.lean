/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NF
-/
module

public import Sheaf.Paper.PurityFiniteSetting
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.Paper.FiniteFreeCoefficientExtension
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import Sheaf.Paper.FiniteTorAmplitudeSites
public import Sheaf.Paper.ProEtaleConstructibleOrigin
public import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import Sheaf.AlgebraicGeometry.SfIntrinsicCompactSupport
public import Sheaf.Paper.FiniteCoefficientDirectImage
public import Sheaf.Paper.ExchangeProjectionSuppliedDomains
public import Sheaf.AlgebraicGeometry.FiniteCompactProjectionFormula
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekPlusBaseChange
public import Sheaf.AlgebraicGeometry.CompactSupportRestrictionOfScalars
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekBaseChange
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekProjection
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekIndependence

/-!
# Specified maps for finite-free projection and exchange

Source: blueprint main-20261015, sk-thm-purity-transport, proof Steps 1 and 3;
Stacks 07A4, 0E47, 0GL1, 03S6, 0F7I and 0GL6
(blueprint: def-pur-finite-free-projection-exchange-data).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.Functor
open WeilConjectures.FiniteFreeCoefficients

namespace WeilConjectures.FiniteFreeProjectionExchange

/-- Dispatch to the published exact geometric inverse image on either small site.
Source: Stacks 07A4 (blueprint: lem-pur-finite-free-projection-exchange). -/
def pull (pro : Bool) (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) : Sites.D pro A Y ⥤ Sites.D pro A X := by
  cases pro
  · exact L(Etale.upperStar (ModuleCat.{u + 1} A) f)
  · exact L(ProEtale.upperStar (ModuleCat.{u + 1} A) f)

/-- The canonical scalar/pullback balancing comparisons already used by the coefficient node.
Source: Stacks 07A4 (blueprint: lem-pur-finite-free-projection-exchange). -/
def scalarPull (pro : Bool) {A B : Type (u + 1)} [CommRing A] [CommRing B]
    [Finite A] [Finite B] (φ : A →+* B) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Sites.scalar pro φ Y ⋙ pull pro B f ≅ pull pro A f ⋙ Sites.scalar pro φ X := by
  cases pro
  · exact Etale.scalarPullbackIso φ f
  · exact Sites.proScalarPull φ f

/-- Dispatch to the recorded termwise extension by zero, with its actual adjunction.
Source: Stacks 03DI (blueprint: lem-pur-finite-free-projection-exchange). -/
def openExtension (pro : Bool) (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j] :
    Sites.D pro A X ⥤ Sites.D pro A Y := by
  cases pro
  · exact (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapDerivedCategory
  · exact (ProEtale.openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapDerivedCategory

-- Keep the chosen adjoints abstract while elaborating composite adjunctions.
attribute [local irreducible] Functor.leftAdjoint Functor.rightAdjoint
  ProEtale.pbcFixedScalarExtension ProEtale.lowerStar

/-- The open coefficient balancing isomorphism, fixed by the open adjunction unit.
Source: Stacks 0GL1, 0GL6 (blueprint: lem-pur-finite-free-projection-exchange). -/
def scalarOpen (pro : Bool) {A B : Type (u + 1)} [CommRing A] [CommRing B]
    [Finite A] [Finite B] (φ : A →+* B) {X Y : Scheme.{u}}
    (j : X ⟶ Y) [IsOpenImmersion j] :
    openExtension pro A j ⋙ Sites.scalar pro φ Y ≅
      Sites.scalar pro φ X ⋙ openExtension pro B j := by
  cases pro
  · exact Etale.ExceptionalCoefficients.openIso φ j
  · dsimp only [openExtension, Sites.scalar]
    unfold ProEtale.pbcFixedScalarExtension
    exact ((ProEtale.fixedScalarOpenAdjunction A j).comp
        (Adjunction.ofIsRightAdjoint
          (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology Y) φ))).leftAdjointUniq
      (((Adjunction.ofIsRightAdjoint
          (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology X) φ)).comp
        (ProEtale.fixedScalarOpenAdjunction B j)).ofNatIsoRight
          (ProEtale.fixedScalarRestrictionPullback φ j).symm)

/-- The actual compact-support candidate, with no new functor construction.
Source: blueprint compactification formula (blueprint: lem-pur-finite-free-projection-exchange). -/
def support (pro : Bool) (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    Sites.D pro A X ⥤ Sites.D pro A Y :=
  openExtension pro A c.i ⋙ Sites.push pro A c.g

/-- The specified B-linear comparison: proper counit transpose followed by open balancing.
Source: blueprint proof Step 2; Stacks 0GL6
(blueprint: lem-pur-finite-free-projection-exchange). -/
def comparison (pro : Bool) {A B : Type (u + 1)} [CommRing A] [CommRing B]
    [Finite A] [Finite B] (φ : A →+* B) {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) (M : Sites.D pro A X) :
    (Sites.scalar pro φ Y).obj ((support pro A c).obj M) ⟶
      (support pro B c).obj ((Sites.scalar pro φ X).obj M) :=
  Sites.direct pro φ c.g ((openExtension pro A c.i).obj M) ≫
    (Sites.push pro B c.g).map ((scalarOpen pro φ c.i).hom.app M)

/-- Dispatch to the actual proper-counit/open-tensor projection transformation.
Source: def-exchange-projection (blueprint: lem-pur-finite-free-projection-exchange). -/
def projection (pro : Bool) (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (M : Sites.D pro A X) (K : Sites.D pro A Y) :
    ((Sites.tensor pro A Y).obj ((support pro A c).obj M)).obj K ⟶
      (support pro A c).obj
        (((Sites.tensor pro A X).obj M).obj ((pull pro A f).obj K)) := by
  cases pro
  · exact ((Etale.projectionMapOfCompactification (ModuleCat.{u + 1} A) c).app M).app K
  · exact ((ProEtale.projectionMapOfCompactification (ModuleCat.{u + 1} A) c).app M).app K

/-- Dispatch to the proper exchange mate followed by canonical open base change.
Source: def-cbc-exchange-map (blueprint: lem-pur-finite-free-projection-exchange). -/
def exchange (pro : Bool) (A : Type (u + 1)) [CommRing A]
    {X' X Y' Y : Scheme.{u}} {a : X' ⟶ X} {b : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : IsPullback a b f g) (c : Compactification f)
    (M : Sites.D pro A X) :
    (pull pro A g).obj ((support pro A c).obj M) ⟶
      (support pro A (c.ofIsPullback sq)).obj ((pull pro A a).obj M) := by
  cases pro
  · exact (Etale.rightDerivedLowerShriekOfCompactificationBaseChangeMap
      (ModuleCat.{u + 1} A) sq c).app M
  · exact (ProEtale.rightDerivedLowerShriekOfCompactificationBaseChangeMap
      (ModuleCat.{u + 1} A) sq c).app M




/-- The existing normalized tensor comparisons on every scheme. Normalization fixes
ordinary balancing on K-flat representatives; it is not arbitrary monoidal data.
Source: Stacks 07A4 (blueprint: lem-pur-finite-free-projection-exchange). -/
structure TensorFamily (pro : Bool) {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) where
  iso : ∀ X : Scheme.{u}, Sites.TensorComparison pro φ X
  normalized : ∀ X : Scheme.{u}, Sites.NormalizedTensor pro φ X (iso X)

/-- Tensoring two derived morphisms through the recorded curried tensor.
Source: Mathlib bifunctor convention (blueprint: lem-pur-finite-free-projection-exchange). -/
def tensorMap (pro : Bool) (A : Type (u + 1)) [CommRing A] (X : Scheme.{u})
    {M M' K K' : Sites.D pro A X} (r : M ⟶ M') (s : K ⟶ K') :=
  ((Sites.tensor pro A X).map r).app K ≫ ((Sites.tensor pro A X).obj M').map s

/-- The target tensor/pullback identification in the displayed projection square.
Source: blueprint proof Step 3 (blueprint: lem-pur-finite-free-projection-exchange). -/
def tensorPullTarget (pro : Bool) {A B : Type (u + 1)} [CommRing A] [CommRing B]
    [Finite A] [Finite B] (φ : A →+* B) (μ : TensorFamily pro φ)
    {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Sites.D pro A X) (K : Sites.D pro A Y) :
    (Sites.scalar pro φ X).obj
        (((Sites.tensor pro A X).obj M).obj ((pull pro A f).obj K)) ⟶
      ((Sites.tensor pro B X).obj ((Sites.scalar pro φ X).obj M)).obj
        ((pull pro B f).obj ((Sites.scalar pro φ Y).obj K)) :=
  (μ.iso X).hom.app (M, (pull pro A f).obj K) ≫
    ((Sites.tensor pro B X).obj ((Sites.scalar pro φ X).obj M)).map
      ((scalarPull pro φ f).inv.app K)

/-- The projection equation with all source and target scalar identifications inserted.
Source: the first displayed equality (blueprint: lem-pur-finite-free-projection-exchange). -/
def ProjectionEquation (pro : Bool) {A B : Type (u + 1)} [CommRing A] [CommRing B]
    [Finite A] [Finite B] (φ : A →+* B) (μ : TensorFamily pro φ)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (M : Sites.D pro A X) (K : Sites.D pro A Y) : Prop :=
  (Sites.scalar pro φ Y).map (projection pro A c M K) ≫
      comparison pro φ c (((Sites.tensor pro A X).obj M).obj ((pull pro A f).obj K)) ≫
      (support pro B c).map (tensorPullTarget pro φ μ f M K) =
    (μ.iso Y).hom.app ((support pro A c).obj M, K) ≫
      tensorMap pro B Y (comparison pro φ c M) (𝟙 ((Sites.scalar pro φ Y).obj K)) ≫
      projection pro B c ((Sites.scalar pro φ X).obj M) ((Sites.scalar pro φ Y).obj K)

/-- The compact-support exchange equation, as an equality in the B-derived category.
Source: the second displayed equality (blueprint: lem-pur-finite-free-projection-exchange). -/
def ExchangeEquation (pro : Bool) {A B : Type (u + 1)} [CommRing A] [CommRing B]
    [Finite A] [Finite B] (φ : A →+* B)
    {X' X Y' Y : Scheme.{u}} {a : X' ⟶ X} {b : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : IsPullback a b f g) (c : Compactification f)
    (M : Sites.D pro A X) : Prop :=
  (Sites.scalar pro φ Y').map (exchange pro A sq c M) ≫
      comparison pro φ (c.ofIsPullback sq) ((pull pro A a).obj M) =
    (scalarPull pro φ g).inv.app ((support pro A c).obj M) ≫
      (pull pro B g).map (comparison pro φ c M) ≫
      exchange pro B sq c ((Sites.scalar pro φ X).obj M) ≫
      (support pro B (c.ofIsPullback sq)).map ((scalarPull pro φ a).hom.app M)

/-- The actual proper counit-defined projection constituent on either site.
Source: def-exchange-projection (blueprint: lem-pur-finite-free-projection-exchange). -/
def properProjection (pro : Bool) (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Sites.D pro A X) (K : Sites.D pro A Y) :
    ((Sites.tensor pro A Y).obj ((Sites.push pro A f).obj M)).obj K ⟶
      (Sites.push pro A f).obj
        (((Sites.tensor pro A X).obj M).obj ((pull pro A f).obj K)) := by
  cases pro
  · exact ((Etale.rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} A) f).app M).app K
  · exact ((ProEtale.rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} A) f).app M).app K

/-- The proper exchange constituent is the published mate of the inverse-image square.
Source: Stacks 0E47 (blueprint: lem-pur-finite-free-projection-exchange). -/
def properExchange (pro : Bool) (A : Type (u + 1)) [CommRing A]
    {X' X Y' Y : Scheme.{u}} {a : X' ⟶ X} {b : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : IsPullback a b f g) (M : Sites.D pro A X) :
    (pull pro A g).obj ((Sites.push pro A f).obj M) ⟶
      (Sites.push pro A b).obj ((pull pro A a).obj M) := by
  cases pro
  · exact (Etale.derivedBaseChangeMap (ModuleCat.{u + 1} A) sq.toCommSq).app M
  · exact (ProEtale.derivedBaseChangeMap (ModuleCat.{u + 1} A) sq.toCommSq).app M

/-- Scalar compatibility for the individual proper projection map.
Source: constituent clause (blueprint: lem-pur-finite-free-projection-exchange). -/
def ProperProjectionEquation (pro : Bool) {A B : Type (u + 1)}
    [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (μ : TensorFamily pro φ) {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : Sites.D pro A X) (K : Sites.D pro A Y) : Prop :=
  (Sites.scalar pro φ Y).map (properProjection pro A f M K) ≫
      Sites.direct pro φ f (((Sites.tensor pro A X).obj M).obj ((pull pro A f).obj K)) ≫
      (Sites.push pro B f).map (tensorPullTarget pro φ μ f M K) =
    (μ.iso Y).hom.app ((Sites.push pro A f).obj M, K) ≫
      tensorMap pro B Y (Sites.direct pro φ f M) (𝟙 ((Sites.scalar pro φ Y).obj K)) ≫
      properProjection pro B f ((Sites.scalar pro φ X).obj M) ((Sites.scalar pro φ Y).obj K)

/-- Scalar compatibility for the individual proper exchange map.
Source: constituent clause (blueprint: lem-pur-finite-free-projection-exchange). -/
def ProperExchangeEquation (pro : Bool) {A B : Type (u + 1)}
    [CommRing A] [CommRing B] [Finite A] [Finite B] (φ : A →+* B)
    {X' X Y' Y : Scheme.{u}} {a : X' ⟶ X} {b : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : IsPullback a b f g) (M : Sites.D pro A X) : Prop :=
  (Sites.scalar pro φ Y').map (properExchange pro A sq M) ≫
      Sites.direct pro φ b ((pull pro A a).obj M) =
    (scalarPull pro φ g).inv.app ((Sites.push pro A f).obj M) ≫
      (pull pro B g).map (Sites.direct pro φ f M) ≫
      properExchange pro B sq ((Sites.scalar pro φ X).obj M) ≫
      (Sites.push pro B b).map ((scalarPull pro φ a).hom.app M)

/-- The canonical open tensor map, oriented as the projection formula.
Source: Stacks 0GL1 (blueprint: lem-pur-finite-free-projection-exchange). -/
def openProjection (pro : Bool) (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j]
    (M : Sites.D pro A X) (K : Sites.D pro A Y) :
    ((Sites.tensor pro A Y).obj ((openExtension pro A j).obj M)).obj K ⟶
      (openExtension pro A j).obj
        (((Sites.tensor pro A X).obj M).obj ((pull pro A j).obj K)) := by
  cases pro
  · exact inv (((Etale.derivedOpenImmersionLowerShriekProjectionMap
      (ModuleCat.{u + 1} A) j).app M).app K)
  · exact inv (((ProEtale.derivedOpenImmersionLowerShriekProjectionMap
      (ModuleCat.{u + 1} A) j).app M).app K)

/-- The actual normalized open exchange, oriented as extraordinary base change.
Source: Stacks 03S6 (blueprint: lem-pur-finite-free-projection-exchange). -/
def openExchange (pro : Bool) (A : Type (u + 1)) [CommRing A] [Finite A]
    {X' X Y' Y : Scheme.{u}} {a : X' ⟶ X} {b : X' ⟶ Y'}
    {j : X ⟶ Y} {g : Y' ⟶ Y} [IsOpenImmersion j] [IsOpenImmersion b]
    (sq : IsPullback a b j g) (M : Sites.D pro A X) :
    (pull pro A g).obj ((openExtension pro A j).obj M) ⟶
      (openExtension pro A b).obj ((pull pro A a).obj M) := by
  cases pro
  · exact (Etale.derivedOpenImmersionLowerShriekBaseChangeIso
      (ModuleCat.{u + 1} A) sq).inv.app M
  · exact (Functor.isoWhiskerRight
        (ProEtale.leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) a) _ ≪≫
      ProEtale.derivedOpenImmersionLowerShriekBaseChangeIso (ModuleCat.{u + 1} A) sq ≪≫
      Functor.isoWhiskerLeft _
        (ProEtale.leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) g).symm
      ).inv.app M

/-- Scalar compatibility for the canonical open tensor constituent.
Source: constituent clause (blueprint: lem-pur-finite-free-projection-exchange). -/
def OpenProjectionEquation (pro : Bool) {A B : Type (u + 1)}
    [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (μ : TensorFamily pro φ) {X Y : Scheme.{u}} (j : X ⟶ Y)
    [IsOpenImmersion j] (M : Sites.D pro A X) (K : Sites.D pro A Y) : Prop :=
  (Sites.scalar pro φ Y).map (openProjection pro A j M K) ≫
      (scalarOpen pro φ j).hom.app
        (((Sites.tensor pro A X).obj M).obj ((pull pro A j).obj K)) ≫
      (openExtension pro B j).map (tensorPullTarget pro φ μ j M K) =
    (μ.iso Y).hom.app ((openExtension pro A j).obj M, K) ≫
      tensorMap pro B Y ((scalarOpen pro φ j).hom.app M)
        (𝟙 ((Sites.scalar pro φ Y).obj K)) ≫
      openProjection pro B j ((Sites.scalar pro φ X).obj M) ((Sites.scalar pro φ Y).obj K)

/-- Scalar compatibility for the canonical open base-change constituent.
Source: constituent clause (blueprint: lem-pur-finite-free-projection-exchange). -/
def OpenExchangeEquation (pro : Bool) {A B : Type (u + 1)}
    [CommRing A] [CommRing B] [Finite A] [Finite B] (φ : A →+* B)
    {X' X Y' Y : Scheme.{u}} {a : X' ⟶ X} {b : X' ⟶ Y'}
    {j : X ⟶ Y} {g : Y' ⟶ Y} [IsOpenImmersion j] [IsOpenImmersion b]
    (sq : IsPullback a b j g) (M : Sites.D pro A X) : Prop :=
  (Sites.scalar pro φ Y').map (openExchange pro A sq M) ≫
      (scalarOpen pro φ b).hom.app ((pull pro A a).obj M) =
    (scalarPull pro φ g).inv.app ((openExtension pro A j).obj M) ≫
      (pull pro B g).map ((scalarOpen pro φ j).hom.app M) ≫
      openExchange pro B sq ((Sites.scalar pro φ X).obj M) ≫
      (openExtension pro B b).map ((scalarPull pro φ a).hom.app M)

/-- Bounded-below etale origin in the existing site presentation. All objects under
consideration have such origins, by boundedness and constructible pro-etale origin.
Source: lem-sf-proetale-constructible-origin
(blueprint: lem-pur-finite-free-projection-exchange). -/
def origin (pro : Bool) (A : Type (u + 1)) [CommRing A] (X : Scheme.{u}) :
    DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) ⥤
      Sites.D pro A X := by
  cases pro
  · exact DerivedCategory.Plus.ι
  · exact DerivedCategory.Plus.ι ⋙ Sites.nu A X

/-- The published coherent compactification comparison on bounded-below origins.
Source: lem-amb-etale-compact-comparisons and its pro-etale realization
(blueprint: lem-pur-finite-free-projection-exchange). -/
def refinement (pro : Bool) (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f] (c d : Compactification f) :
    origin pro A X ⋙ support pro A c ≅ origin pro A X ⋙ support pro A d := by
  cases pro
  · exact Etale.rightDerivedLowerShriekOfCompactificationPlusιIso A c d
  · exact ProEtale.rightDerivedLowerShriekOfCompactificationOriginIso A c d

/-- Independence under the canonical compactification identifications, allowing every
choice of origin for the scalar image. Naturality transports this square to arbitrary
constructible finite-Tor objects. The comparison is the published coherent comparison,
so this in particular covers every proper refinement, including identities.
Source: blueprint proof Step 9 (blueprint: lem-pur-finite-free-projection-exchange). -/
def RefinementEquation (pro : Bool) {A B : Type (u + 1)}
    [CommRing A] [CommRing B] [Finite A] [Finite B] (φ : A →+* B)
    {X Y : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f] (c d : Compactification f)
    (M : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (N : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)))
    (e : (origin pro B X).obj N ≅
      (Sites.scalar pro φ X).obj ((origin pro A X).obj M)) : Prop :=
  (Sites.scalar pro φ Y).map ((refinement pro A c d).hom.app M) ≫
      comparison pro φ d ((origin pro A X).obj M) =
    comparison pro φ c ((origin pro A X).obj M) ≫
      (support pro B c).map e.inv ≫ (refinement pro B c d).hom.app N ≫
      (support pro B d).map e.hom

/-- The equal-level field-extension arrow. Its quotient map uses the image of the
base uniformizer, hence retains ramification without changing the level to n upstairs.
Source: blueprint proof Step 3 (blueprint: lem-pur-finite-free-projection-exchange). -/
def extensionArrow {l : ℕ} [Fact l.Prime] {E : Type (u + 1)} [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (t : FiniteCoefficientAdjoints.Stage l E) :
    FiniteCoefficientAdjoints.Arrow
      (FiniteCoefficientAdjoints.baseStage t.exponent) t where
  embedding := t.inclusion
  over_base := AlgHom.comp_id _
  level := le_rfl


end WeilConjectures.FiniteFreeProjectionExchange
