# WeilConjectures.ProjectionRefinementDescent fixed-scalar constructions

## Reason

The descent argument has independent domain, comparison and refinement-square steps.
Move its ten existing fixed-scalar declarations into
`Sheaf.SixFunctors.ProjectionRefinementData` so these steps can import the constructions
without a cycle through `finite_descent`. The item publicly imports this data module.
All existing declaration names, binders and instance attributes stay unchanged.
The image and projection bifunctors are specialized through three generic
coefficient abbreviations whose bodies are the exact native functors. The finite
projection formulas use `coefficientProjectionComponent`, whose body evaluates
`RefinementProjection.finiteProjection`, the exact native projection natural
transformation. The component declares the tensor endpoints explicitly; no native
functor computation is needed to infer them after coefficient specialization. These definitionally equal
spellings share categorical instances before substituting the large coefficient
quotient and avoid deterministic conversion timeouts. No target or mathematical
definition meaning changes. The new blueprint tags attach
the moved constructions to their dedicated definition node.

## Old

The declarations below were in `Sheaf.SixFunctors.ProjectionRefinementDescent`.

```lean
instance coefficientFinite : Finite (Padic.coefficientExtensionRing l E (n + 1)) :=
  Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_pos n)

/-- The canonical universe lift of the specified quotient `O_E/(t^(n+1))`.
Source: def-weil-l-adic-coefficient-extension
(blueprint: lem-sf-projection-refinement-descent). -/
abbrev Coefficient := ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1))

/-- Bounded constructibility transported through the recorded intrinsic realization.
Source: def-weil-finite-torsion-constructibility, fixed-scalar presentation
(blueprint: lem-sf-projection-refinement-descent). -/
def boundedConstructible (X : Scheme.{u}) :
    ObjectProperty (ProperOpenDerived (Coefficient l E n) X) :=
  fun K ↦ intrinsicFiniteTorsionConstructible l E (n + 1) (Nat.succ_pos n) X
    ((sfIntrinsicDerivedEquivalence X (Padic.coefficientExtensionRing l E (n + 1))).functor.obj K)

/-- The recorded finite-Tor constructible predicate, in the same fixed-scalar coordinates.
Source: def-weil-finite-tor-amplitude
(blueprint: lem-sf-projection-refinement-descent). -/
def finiteTor (X : Scheme.{u}) : ObjectProperty (ProperOpenDerived (Coefficient l E n) X) :=
  fun L ↦ finiteTorConstructible l E (n + 1) (Nat.succ_pos n) X
    ((sfIntrinsicDerivedEquivalence X (Padic.coefficientExtensionRing l E (n + 1))).functor.obj L)

/-- The actual object `K tensor Lf*L`, with no Tor restriction on `K`.
Source: def-exchange-projection
(blueprint: lem-sf-projection-refinement-descent). -/
def tensorInput {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : ProperOpenDerived (Coefficient l E n) X)
    (L : ProperOpenDerived (Coefficient l E n) Y) :=
  ((ProperOpenTensor (Coefficient l E n) X).obj K).obj
    ((ProperOpenPull (Coefficient l E n) f).obj L)

/-- The existing compactification functor in fixed-scalar coordinates.
Source: def-weil-integral-rational-qbar-compact-support, finite coefficient candidate
(blueprint: lem-sf-projection-refinement-descent). -/
abbrev image {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :=
  rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} (Coefficient l E n)) c

/-- Transport the specified refinement comparison along an actual retained origin witness.
Its middle arrow is precisely proper composition followed by the proper image of the
inverse proper/open comparison. No Cartesian assumption is made.
Source: def-sf-refinement-comparison-isomorphism, parts (a) and (b)
(blueprint: lem-sf-projection-refinement-descent). -/
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
(blueprint: lem-sf-projection-refinement-descent). -/
def source {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :=
  (boundedConstructible l E n X).ι.prod (finiteTor l E n Y).ι ⋙
    Functor.uncurry.obj
      (derivedTensorRightDerivedLowerShriek (ModuleCat.{u + 1} (Coefficient l E n)) c)

/-- The target bifunctor on exactly the same full input domain.
Source: def-exchange-projection
(blueprint: lem-sf-projection-refinement-descent). -/
def target {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :=
  (boundedConstructible l E n X).ι.prod (finiteTor l E n Y).ι ⋙
    Functor.uncurry.obj
      (rightDerivedLowerShriekDerivedTensorLeftDerivedUpperStar
        (ModuleCat.{u + 1} (Coefficient l E n)) c)

/-- The finite refinement equation, on arbitrary bounded constructible `K` and finite-Tor
`L`. Witnesses are retained only to evaluate the already specified theta. They are
universally quantified here; their existence is part of the main statement below.
Source: fix-prop-projection-formula, refinement sentence, Stacks 0F7B and 0F7G
(blueprint: lem-sf-projection-refinement-descent). -/
def refinementLaw {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c d : Compactification f) (r : c.Refinement d)
    (K : (boundedConstructible l E n X).FullSubcategory)
    (L : (finiteTor l E n Y).FullSubcategory) : Prop :=
  ∀ (O : RefinementFiniteLevelOrigin l E (n + 1) (Nat.succ_pos n) X)
    (e : refinementFiniteLevelFixedObject l E (n + 1) (Nat.succ_pos n) X O ≅ K.obj)
    (OT : RefinementFiniteLevelOrigin l E (n + 1) (Nat.succ_pos n) X)
    (eT : refinementFiniteLevelFixedObject l E (n + 1) (Nat.succ_pos n) X OT ≅
      tensorInput l E n f K.obj L.obj),
    ((projectionMapOfCompactification (ModuleCat.{u + 1} (Coefficient l E n)) c).app
        K.obj).app L.obj ≫
      (theta l E n r (tensorInput l E n f K.obj L.obj) OT eT).hom =
    ((ProperOpenTensor (Coefficient l E n) Y).map (theta l E n r K.obj O e).hom).app
        L.obj ≫
      ((projectionMapOfCompactification (ModuleCat.{u + 1} (Coefficient l E n)) d).app
        K.obj).app L.obj

```

## New

The data-module declarations are below. They use the same coefficient quotient,
origin presentations, tensor and native projections. In `finite_descent`, the
native projection component is spelled with `coefficientProjectionComponent`;
tau is still the restriction of the actual native natural transformation through
`RefinementProjection.finiteProjection`. All binders and the mathematical assertion
are unchanged. Unfolding the generic definitions gives the old native maps exactly.
The intrinsic-system specialization is byte-for-byte unchanged. No new axioms,
properties of a different map, or hypotheses are added.

```lean
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

```

## Users

A fresh direct-import search found `Sheaf.Paper.FiniteProjectionFromDescent`,
which compiled unchanged against the packet in 58.0 s and is not included in the delivery. The DAG still requires the item, which is proved rather than withdrawn.
The unit route is retained; no existing module besides the item is changed.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.SixFunctors.ProjectionRefinementDescent | U1 | Publicly imports the same constructions and assembles the descent proof. |
| Sheaf.SixFunctors.ProjectionRefinementInputs | U1, new | Uses the identical fixed-scalar domain predicates. |
| Sheaf.SixFunctors.ProjectionRefinementComparisons | U1, new | Uses the identical image and theta constructions. |
| Sheaf.SixFunctors.ProjectionRefinementNormalization | U1, new | Identifies the inverse theta with the specified directed mate. |
| Sheaf.SixFunctors.ProjectionRefinementSquare | U1, new | Uses refinementLaw and combines the normalized directed square. |

## Status

landed 20261027T021410-L-2765186 2026-10-27 (merge of deliver/U1/Sheaf.SixFunctors.ProjectionRefinementDescent)
