/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.ProEtaleCoefficients.SixFunctorOperationDatum.SixFunctorOperationDatum
public import WeilConjectures.CategoryTheory.SuppliedExchangeProjection.ExchangeProjectionSuppliedDomains
public import WeilConjectures.SmoothPurity.Qcqs.QcqsCompactSupportRealization
public import WeilConjectures.SmoothPurity.Finite.FiniteTorAmplitudeSites
public import WeilConjectures.AlgebraicGeometry.Refinement.RefinementComparisonIsomorphism
public import WeilConjectures.AlgebraicGeometry.Proper.Open.ProperOpenProjectionMate
public import WeilConjectures.AlgebraicGeometry.Compactification.CompactificationCoherence
public import WeilConjectures.SixFunctors.IntegralSystemRealization.IntegralCompactificationSystemRealization
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekProjection
public import Mathlib.CategoryTheory.Functor.Currying
public import WeilConjectures.AlgebraicGeometry.AmbientProperOpen.RefinementProjection.RefinementProjectionCounit

/-! # Fixed-scalar inputs and witnessed refinement comparisons

Source: lem-sf-projection-refinement-descent, definitions preceding its finite clause.
(blueprint: def-sf-projection-refinement-domains).

These are the original constructions in generic coefficient coordinates, so that
the independent descent steps can use them without importing the assembly theorem.
The generic wrappers are definitionally the native functors; they share their
categorical instances before the specified coefficient quotient is substituted.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProEtale
open AlgebraicGeometry.Scheme
open scoped CategoryTheory.Functor

namespace WeilConjectures.ProjectionRefinementDescent

/-- The native compactification functor, packaged at a generic coefficient ring.
Source: `rightDerivedLowerShriekOfCompactification`.
(blueprint: def-sf-projection-refinement-domains). -/
abbrev coefficientImage (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :=
  rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c

/-- The native projection source, packaged before coefficient specialization.
Source: `derivedTensorRightDerivedLowerShriek`.
(blueprint: def-sf-projection-refinement-domains). -/
abbrev coefficientProjectionSource (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :=
  derivedTensorRightDerivedLowerShriek (ModuleCat.{u + 1} A) c

/-- The native projection target, packaged before coefficient specialization.
Source: `rightDerivedLowerShriekDerivedTensorLeftDerivedUpperStar`.
(blueprint: def-sf-projection-refinement-domains). -/
abbrev coefficientProjectionTarget (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :=
  rightDerivedLowerShriekDerivedTensorLeftDerivedUpperStar (ModuleCat.{u + 1} A) c

/-- The native projection component with its tensor endpoints exposed.
The component is evaluated at a generic coefficient ring before specialization.
Source: `projectionMapOfCompactification` and `RefinementProjection.finiteProjection`.
(blueprint: def-sf-projection-refinement-domains). -/
def coefficientProjectionComponent (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (K : ProperOpenDerived A X) (L : ProperOpenDerived A Y) :
    ((ProperOpenTensor A Y).obj ((coefficientImage A c).obj K)).obj L ⟶
      (coefficientImage A c).obj
        (((ProperOpenTensor A X).obj K).obj ((ProperOpenPull A f).obj L)) :=
  ((AmbientProperOpen.RefinementProjection.finiteProjection A c).app K).app L

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (n : ℕ)

/-- Finiteness of the actual positive-level coefficient quotient, with no extra assumption.
Source: def-weil-l-adic-coefficient-extension
(blueprint: def-sf-projection-refinement-domains). -/
instance coefficientFinite : Finite (Padic.coefficientExtensionRing l E (n + 1)) :=
  Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_pos n)

/-- The canonical universe lift of the specified quotient `O_E/(t^(n+1))`.
Source: def-weil-l-adic-coefficient-extension
(blueprint: def-sf-projection-refinement-domains). -/
abbrev Coefficient := ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1))

/-- Bounded constructibility transported through the recorded intrinsic realization.
Source: def-weil-finite-torsion-constructibility, fixed-scalar presentation
(blueprint: def-sf-projection-refinement-domains). -/
def boundedConstructible (X : Scheme.{u}) :
    ObjectProperty (ProperOpenDerived (Coefficient l E n) X) :=
  fun K ↦ intrinsicFiniteTorsionConstructible l E (n + 1) (Nat.succ_pos n) X
    ((sfIntrinsicDerivedEquivalence X (Padic.coefficientExtensionRing l E (n + 1))).functor.obj K)

/-- The recorded finite-Tor constructible predicate, in the same fixed-scalar coordinates.
Source: def-weil-finite-tor-amplitude
(blueprint: def-sf-projection-refinement-domains). -/
def finiteTor (X : Scheme.{u}) : ObjectProperty (ProperOpenDerived (Coefficient l E n) X) :=
  fun L ↦ finiteTorConstructible l E (n + 1) (Nat.succ_pos n) X
    ((sfIntrinsicDerivedEquivalence X (Padic.coefficientExtensionRing l E (n + 1))).functor.obj L)

/-- The actual object `K tensor Lf*L`, with no Tor restriction on `K`.
Source: def-exchange-projection
(blueprint: def-sf-projection-refinement-domains). -/
def tensorInput {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : ProperOpenDerived (Coefficient l E n) X)
    (L : ProperOpenDerived (Coefficient l E n) Y) :=
  ((ProperOpenTensor (Coefficient l E n) X).obj K).obj
    ((ProperOpenPull (Coefficient l E n) f).obj L)

/-- The existing compactification functor in fixed-scalar coordinates.
Source: def-weil-integral-rational-qbar-compact-support, finite coefficient candidate
(blueprint: def-sf-projection-refinement-domains). -/
abbrev image {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :=
  coefficientImage (Coefficient l E n) c

/-- Transport the specified refinement comparison along an actual retained origin witness.
Its middle arrow is precisely proper composition followed by the proper image of the
inverse proper/open comparison. No Cartesian assumption is made.
Source: def-sf-refinement-comparison-isomorphism, parts (a) and (b)
(blueprint: def-sf-projection-refinement-domains). -/
def theta {X Y : Scheme.{u}} {f : X ⟶ Y} {c d : Compactification f}
    (r : c.Refinement d) (K : ProperOpenDerived (Coefficient l E n) X)
    (O : RefinementFiniteLevelOrigin l E (n + 1) (Nat.succ_pos n) X)
    (e : refinementFiniteLevelFixedObject l E (n + 1) (Nat.succ_pos n) X O ≅ K) :
    (image l E n c).obj K ≅ (image l E n d).obj K :=
  letI : TopologicalSpace (Coefficient l E n) := ⊥
  letI : DiscreteTopology (Coefficient l E n) := discreteTopology_bot _
  (image l E n c).mapIso e.symm ≪≫
    refinementComparisonAtWitness (Coefficient l E n) r O ≪≫
      (image l E n d).mapIso e

/-- The source bifunctor on the full bounded-constructible/finite-Tor input domain.
Source: def-exchange-projection
(blueprint: def-sf-projection-refinement-domains). -/
def source {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :=
  (boundedConstructible l E n X).ι.prod (finiteTor l E n Y).ι ⋙
    Functor.uncurry.obj
      (coefficientProjectionSource (Coefficient l E n) c)

/-- The target bifunctor on exactly the same full input domain.
Source: def-exchange-projection
(blueprint: def-sf-projection-refinement-domains). -/
def target {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :=
  (boundedConstructible l E n X).ι.prod (finiteTor l E n Y).ι ⋙
    Functor.uncurry.obj
      (coefficientProjectionTarget (Coefficient l E n) c)

/-- The finite refinement equation, on arbitrary bounded constructible `K` and finite-Tor
`L`. Witnesses are retained only to evaluate the already specified theta. They are
universally quantified here; their existence is part of the main statement below.
Source: fix-prop-projection-formula, refinement sentence, Stacks 0F7B and 0F7G
(blueprint: def-sf-projection-refinement-domains). -/
def refinementLaw {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c d : Compactification f) (r : c.Refinement d)
    (K : (boundedConstructible l E n X).FullSubcategory)
    (L : (finiteTor l E n Y).FullSubcategory) : Prop :=
  ∀ (O : RefinementFiniteLevelOrigin l E (n + 1) (Nat.succ_pos n) X)
    (e : refinementFiniteLevelFixedObject l E (n + 1) (Nat.succ_pos n) X O ≅ K.obj)
    (OT : RefinementFiniteLevelOrigin l E (n + 1) (Nat.succ_pos n) X)
    (eT : refinementFiniteLevelFixedObject l E (n + 1) (Nat.succ_pos n) X OT ≅
      tensorInput l E n f K.obj L.obj),
    coefficientProjectionComponent (Coefficient l E n) c K.obj L.obj ≫
      (theta l E n r (tensorInput l E n f K.obj L.obj) OT eT).hom =
    ((ProperOpenTensor (Coefficient l E n) Y).map (theta l E n r K.obj O e).hom).app
        L.obj ≫
      coefficientProjectionComponent (Coefficient l E n) d K.obj L.obj

end WeilConjectures.ProjectionRefinementDescent
