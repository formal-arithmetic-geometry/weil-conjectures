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
import Sheaf.AlgebraicGeometry.Etale.DerivedExtensionZeroBaseChange
import Sheaf.Paper.SfDirectImageCTFNonproper
import Sheaf.Paper.ProEtaleFiniteCoefficientDirectImage
import Sheaf.AlgebraicGeometry.EtaleCompactSupportComparisons
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.BaseChangeSquare
import Sheaf.SixFunctors.EtaleOpenTensor
import Sheaf.SecSmoothPurity.OpenScalarExchange
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Paper.ComparisonTorAmplitude
import Sheaf.Paper.FiniteCoefficientFlatModel
import Sheaf.AlgebraicGeometry.OpenComparisonUnitNormalization
import Sheaf.SixFunctors.OpenTensorNormalization
import Sheaf.Paper.CoefficientRealizationTransport
import Sheaf.Paper.ProperOpenCoefficientRefinement
import Sheaf.AlgebraicGeometry.ProperOpenComparisonSiteNormalization
import Sheaf.Paper.OpenExtensionFiniteTor
import Sheaf.AlgebraicGeometry.FixedComparisonDirectImageMate
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
import WeilConjectures.CategoryTheory.SiteMorphismComposition
import WeilConjectures.Compactification.NagataCompactification

/-!
# Finite-free scalar extension of the specified projection and exchange maps

Source: blueprint main-20261015, sk-thm-purity-transport, proof Steps 1 and 3;
Stacks 07A4, 0E47, 0GL1, 03S6, 0F7I and 0GL6
(blueprint: lem-pur-finite-free-projection-exchange).
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

/-- The open coefficient balancing isomorphism, fixed by the open adjunction unit.
Source: Stacks 0GL1, 0GL6 (blueprint: lem-pur-finite-free-projection-exchange). -/
def scalarOpen (pro : Bool) {A B : Type (u + 1)} [CommRing A] [CommRing B]
    [Finite A] [Finite B] (φ : A →+* B) {X Y : Scheme.{u}}
    (j : X ⟶ Y) [IsOpenImmersion j] :
    openExtension pro A j ⋙ Sites.scalar pro φ Y ≅
      Sites.scalar pro φ X ⋙ openExtension pro B j := by
  cases pro
  · exact Etale.ExceptionalCoefficients.openIso φ j
  · exact ((ProEtale.fixedScalarOpenAdjunction A j).comp
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

/-- Finite-free coefficient extension preserves the specified compact-support projection
and exchange, the individual proper and open constituents, and every proper refinement.
The tensor comparison is required to be the normalized ordinary balancing map, and no
smooth orientation or trace data are parameters.

Source: blueprint main-20261015, sk-thm-purity-transport, proof Steps 1 and 3;
Stacks 07A4, 0E47, 0GL1, 03S6, 0F7I and 0GL6
(blueprint: lem-pur-finite-free-projection-exchange).

Proof plan, following the ten steps of the DAG node:
1. Finite-free extension is exact and preserves constructibility and Tor intervals.
Pullback, open extension and direct image preserve the indicated finite-Tor domains
by lem-sf-flat-model, lem-trf-open-ctf and the two direct-image closure results.
2. The proper counit-transpose comparison is lem-coef-finite-direct-image; the open
comparison is lem-coef-etale-open-tensor or lem-sf-open-tensor-normalization.
Their composite is comparison, hence is invertible and natural.
3. Compute scalar/pullback and tensor comparisons on K-flat representatives using
lem-pc-kflat-resolution and lem-pur-derived-change-of-rings. Both routes send a pure
tensor to its inverse image with the same coefficient. Balanced multiplication proves
coherence, including identities, compositions and inverse-image square identifications.
4. The direct-image map is the mate of this scalar/pullback comparison. Its counit
identity and triangle identities give its unit identity. Mate pasting gives its cocycle.
5. Take the open adjoint of the scalar/open projection square. Both sides become the
same balanced reassociation, by the unit normalizations of the open tensor maps.
6. The open base-change inverse is the adjunct of the pulled-back open unit, by
lem-cbc-extension-zero-base-change and cor-cbc-derived-extension-zero-base-change.
After taking adjuncts the scalar square is Step 3 and the open unit equation. On the
pro-etale site use lem-fix-open-scalar-exchange with these same maps.
7. Proper exchange is the mate of the inverse-image square. The coefficient cube of
left-adjoint comparisons commutes by Step 3. Mate pasting gives ProperExchangeEquation
on each site, with the actual proper exchange rather than an unspecified isomorphism.
8. Apply lem-sf-pf-coefficient-realization-transport on each closed finite-Tor domain,
using Steps 1--7. Its compactification composites are the present projection and
exchange by lem-weil-finite-compact-projection-formula and def-cbc-exchange-map.
9. For an etale proper refinement use lem-sf-proper-open-coefficient-refinement and
the direct-image composition equation. By lem-amb-etale-compact-comparisons these
are the coherent canonical comparisons of all compactifications.
10. Choose any etale-origin witness by lem-sf-proetale-constructible-origin. The
coefficient/site/open cube commutes by lem-sf-open-comparison-unit-normalization;
the proper cube commutes by the canonical mate and mate pasting. Transport Step 9
using lem-sf-proper-open-comparison-site-normalization. Naturality gives the asserted
refinement square for every witness and every isomorphic constructible input. -/
theorem finite_free_projection_exchange (D : FiniteFieldDatum.{u})
    (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E : Type (u + 1)) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (t : FiniteCoefficientAdjoints.Stage l E) :
    ∀ pro : Bool, ∃ μ : TensorFamily pro (extensionArrow t).ringMap,
    ∀ (X Y : Scheme.{u})
      [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
      [IsSeparated (X ↘ Spec (.of D.k))] [IsSeparated (Y ↘ Spec (.of D.k))]
      [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
      [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
      (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))]
      [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f],
    (∀ (c : Compactification f)
      (M : Sites.D pro (FiniteCoefficientAdjoints.baseStage t.exponent).ring X),
      Sites.Ctf pro (FiniteCoefficientAdjoints.baseStage t.exponent).ring X M →
      IsIso (comparison pro (extensionArrow t).ringMap c M)) ∧
    (∀ (c : Compactification f)
      (M N : Sites.D pro (FiniteCoefficientAdjoints.baseStage t.exponent).ring X)
      (_hM : Sites.Ctf pro (FiniteCoefficientAdjoints.baseStage t.exponent).ring X M)
      (_hN : Sites.Ctf pro (FiniteCoefficientAdjoints.baseStage t.exponent).ring X N)
      (r : M ⟶ N),
      (Sites.scalar pro (extensionArrow t).ringMap Y).map
          ((support pro (FiniteCoefficientAdjoints.baseStage t.exponent).ring c).map r) ≫
          comparison pro (extensionArrow t).ringMap c N =
        comparison pro (extensionArrow t).ringMap c M ≫
          (support pro t.ring c).map ((Sites.scalar pro (extensionArrow t).ringMap X).map r)) ∧
    (∀ (c d : Compactification f)
      (M : DerivedCategory.Plus
        (Sheaf X.smallEtaleTopology
          (ModuleCat.{u + 1} (FiniteCoefficientAdjoints.baseStage t.exponent).ring)))
      (N : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} t.ring)))
      (e : (origin pro t.ring X).obj N ≅
        (Sites.scalar pro (extensionArrow t).ringMap X).obj
          ((origin pro (FiniteCoefficientAdjoints.baseStage t.exponent).ring X).obj M)),
      Sites.Ctf pro (FiniteCoefficientAdjoints.baseStage t.exponent).ring X
          ((origin pro (FiniteCoefficientAdjoints.baseStage t.exponent).ring X).obj M) →
      RefinementEquation pro (extensionArrow t).ringMap c d M N e) ∧
    (∀ (c : Compactification f)
      (M : Sites.D pro (FiniteCoefficientAdjoints.baseStage t.exponent).ring X)
      (K : Sites.D pro (FiniteCoefficientAdjoints.baseStage t.exponent).ring Y),
      Sites.Ctf pro (FiniteCoefficientAdjoints.baseStage t.exponent).ring X M →
      Sites.Ctf pro (FiniteCoefficientAdjoints.baseStage t.exponent).ring Y K →
      ProjectionEquation pro (extensionArrow t).ringMap μ c M K) ∧
    (∀ (M : Sites.D pro (FiniteCoefficientAdjoints.baseStage t.exponent).ring X)
      (K : Sites.D pro (FiniteCoefficientAdjoints.baseStage t.exponent).ring Y),
      Sites.Ctf pro (FiniteCoefficientAdjoints.baseStage t.exponent).ring X M →
      Sites.Ctf pro (FiniteCoefficientAdjoints.baseStage t.exponent).ring Y K →
      (IsProper f → ProperProjectionEquation pro (extensionArrow t).ringMap μ f M K) ∧
      (∀ [IsOpenImmersion f],
        OpenProjectionEquation pro (extensionArrow t).ringMap μ f M K)) ∧
    (∀ (X' Y' : Scheme.{u})
      [X'.Over (Spec (.of D.k))] [Y'.Over (Spec (.of D.k))]
      [IsSeparated (X' ↘ Spec (.of D.k))] [IsSeparated (Y' ↘ Spec (.of D.k))]
      [LocallyOfFiniteType (X' ↘ Spec (.of D.k))] [QuasiCompact (X' ↘ Spec (.of D.k))]
      [LocallyOfFiniteType (Y' ↘ Spec (.of D.k))] [QuasiCompact (Y' ↘ Spec (.of D.k))]
      (a : X' ⟶ X) (b : X' ⟶ Y') (g : Y' ⟶ Y)
      [a.IsOver (Spec (.of D.k))] [b.IsOver (Spec (.of D.k))]
      [g.IsOver (Spec (.of D.k))] (sq : IsPullback a b f g)
      (M : Sites.D pro (FiniteCoefficientAdjoints.baseStage t.exponent).ring X),
      Sites.Ctf pro (FiniteCoefficientAdjoints.baseStage t.exponent).ring X M →
      (∀ c : Compactification f, ExchangeEquation pro (extensionArrow t).ringMap sq c M) ∧
      (IsProper f → ProperExchangeEquation pro (extensionArrow t).ringMap sq M) ∧
      (∀ [IsOpenImmersion f] [IsOpenImmersion b],
        OpenExchangeEquation pro (extensionArrow t).ringMap sq M)) := by
  sorry

end WeilConjectures.FiniteFreeProjectionExchange
