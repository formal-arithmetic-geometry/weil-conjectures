/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q06
-/
module

public import Sheaf.Paper.CompleteCompactSupportProetale
public import Sheaf.Paper.AdicCoefficientDatum
public import WeilConjectures.Compactification.BaseChange
public import Sheaf.Paper.PbcActualStrictPullback
public import Sheaf.Paper.ProjectionCompactification
public import Sheaf.Paper.CompletedCompactSupportExchange
public import Sheaf.Paper.IntegralUniformCoefficient
public import Sheaf.Paper.PbcRationalCategory
public import Sheaf.Paper.PbcRationalTransport
public import Sheaf.AlgebraicGeometry.ChosenCartesianSquare
public import WeilConjectures.Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Sheaf.Paper.IntegralCompactSupportUniformRestriction
import Sheaf.Paper.PreservationConstructible
import Sheaf.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitOfUniverses
import Sheaf.Paper.PbcUniformCompleteTriangulated
import Sheaf.Paper.IntegralStratifiedPerfectCharacterization
import Sheaf.CategoryTheory.DerivedCategory.StandardQuotientsPerfect
import Sheaf.Paper.ConstantCompletionEquivalence
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Sheaf.CategoryTheory.ScalarLocalization
import Sheaf.Paper.CompletedPullbackTriangles
import Sheaf.Paper.FiniteExtensionReductionConeBound
import Sheaf.Paper.SbcCompletedOperations

/-!
# Compact-support base change over a finite extension

Source: blueprint main-20261015, `thm-cbc-finite-extension`, order 1991
(blueprint: thm-cbc-finite-extension).

The integral compact-support exchange is transported through the raw scalar
localization.  The source and target are the completed compact-support
composites attached to the chosen compactifications; the displayed naturality
equation is the naturality required for every rational morphism.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- Additivity interface needed by scalar transport for the completed open operation.
Source: blueprint thm-cbc-finite-extension, proof step 1
(blueprint: thm-cbc-finite-extension).
Proof: extension by zero is additive on module sections. Its exact termwise functor
respects sums of chain maps, and the equation descends through the derived localization. -/
@[instance] theorem cbcDerivedOpenShriek_additive
    {A : Type (u + 1)} [CommRing A] {U T : Scheme.{u}}
    (d : AdicCoefficientDatum A) (j : U ⟶ T) (hj : IsOpenImmersion j) :
    (cbcDerivedOpenShriek d j hj).Additive := by
  sorry

/-- Additivity interface needed by scalar transport for completed pullback.
Source: blueprint thm-cbc-finite-extension, proof step 1
(blueprint: thm-cbc-finite-extension).
Proof: the reduction-tower construction and derived tower pullback respect sums on
representatives; derived inverse limit is additive. Compose these three equations. -/
@[instance] theorem completedPull_additive
    {A : Type (u + 1)} [CommRing A] {U V : Scheme.{u}}
    (d : AdicCoefficientDatum A) (f : U ⟶ V) :
    (d.completedPull f).Additive := by
  sorry

/-- The source composite is additive.
Proof: extension by zero, derived direct image, and completed pullback are additive
on representative maps. Composition preserves these addition equations.
Source: blueprint thm-cbc-finite-extension, proof step 1
(blueprint: thm-cbc-finite-extension). -/
@[instance] theorem cbcCompactSupportSource_additive
    {A : Type (u + 1)} [CommRing A] {X Y Y' : Scheme.{u}} {f : X ⟶ Y}
    (g : Y' ⟶ Y) (c : Compactification f) (d : AdicCoefficientDatum A) :
    (cbcDerivedOpenShriek d c.i c.isOpenImmersion ⋙ d.push c.g ⋙ d.completedPull g).Additive := by
  sorry

/-- The target composite is additive.
Proof: completed pullback, extension by zero, and derived direct image are additive
on representative maps. Composition preserves these addition equations.
Source: blueprint thm-cbc-finite-extension, proof step 1
(blueprint: thm-cbc-finite-extension). -/
@[instance] theorem cbcCompactSupportTarget_additive
    {A : Type (u + 1)} [CommRing A] {X X' Y' : Scheme.{u}} {f' : X' ⟶ Y'}
    (g' : X' ⟶ X) (c' : Compactification f') (d : AdicCoefficientDatum A) :
    (d.completedPull g' ⋙ cbcDerivedOpenShriek d c'.i c'.isOpenImmersion ⋙
      d.push c'.g).Additive := by
  sorry

/-- The source compact-support composite in the chosen compactification.
Source: `def-cbc-completed-exchange-map` (blueprint: thm-cbc-finite-extension). -/
abbrev cbcCompactSupportSource
    {A : Type (u + 1)} [CommRing A] {X Y Y' : Scheme.{u}}
    {f : X ⟶ Y} (g : Y' ⟶ Y) (c : Compactification f)
    (d : AdicCoefficientDatum A) :=
  cbcDerivedOpenShriek d c.i c.isOpenImmersion ⋙ d.push c.g ⋙ d.completedPull g

/-- The target compact-support composite in the chosen compactification.
Source: `def-cbc-completed-exchange-map` (blueprint: thm-cbc-finite-extension). -/
abbrev cbcCompactSupportTarget
    {A : Type (u + 1)} [CommRing A] {X X' Y' : Scheme.{u}}
    {f' : X' ⟶ Y'} (g' : X' ⟶ X) (c' : Compactification f')
    (d : AdicCoefficientDatum A) :=
  d.completedPull g' ⋙ cbcDerivedOpenShriek d c'.i c'.isOpenImmersion ⋙ d.push c'.g

/-- The source lift whose objects retain the constructibility witness.
Source: the integral category restriction in the proof
(blueprint: thm-cbc-finite-extension). -/
abbrev cbcCompactSupportSourceLift
    (l : ℕ) [Fact l.Prime] (E : Type (u + 1)) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X Y Y' : Scheme.{u}} {f : X ⟶ Y} (g : Y' ⟶ Y) (c : Compactification f)
    (d : AdicCoefficientDatum (Padic.coefficientExtensionIntegers l E))
    (hSource : ∀ K : PbcBoundedConstructibleComplete X d,
      PbcIsBoundedConstructibleComplete Y' d
        ((cbcCompactSupportSource g c d).obj K.obj)) :
    PbcBoundedConstructibleComplete X d ⥤
      PbcBoundedConstructibleComplete Y' d :=
  by
    letI := cbcCompactSupportSource_additive g c d
    exact ObjectProperty.liftFullSubcategory
      (PbcIsBoundedConstructibleComplete X d) (PbcIsBoundedConstructibleComplete Y' d)
      (cbcCompactSupportSource g c d) (fun K hK ↦ hSource ⟨K, hK⟩)

/-- The target lift whose objects retain the constructibility witness.
Source: the integral category restriction in the proof
(blueprint: thm-cbc-finite-extension). -/
abbrev cbcCompactSupportTargetLift
    (l : ℕ) [Fact l.Prime] (E : Type (u + 1)) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X X' Y' : Scheme.{u}} {f' : X' ⟶ Y'} (g' : X' ⟶ X)
    (c' : Compactification f')
    (d : AdicCoefficientDatum (Padic.coefficientExtensionIntegers l E))
    (hTarget : ∀ K : PbcBoundedConstructibleComplete X d,
      PbcIsBoundedConstructibleComplete Y' d
        ((cbcCompactSupportTarget g' c' d).obj K.obj)) :
    PbcBoundedConstructibleComplete X d ⥤
      PbcBoundedConstructibleComplete Y' d :=
  by
    letI := cbcCompactSupportTarget_additive g' c' d
    exact ObjectProperty.liftFullSubcategory
      (PbcIsBoundedConstructibleComplete X d) (PbcIsBoundedConstructibleComplete Y' d)
      (cbcCompactSupportTarget g' c' d) (fun K hK ↦ hTarget ⟨K, hK⟩)

/-- The source restriction is additive for the inherited full-subcategory addition.
Proof: the restriction maps each morphism by the ambient composite. Its additivity
equation is the ambient equation viewed through the faithful full inclusion.
Source: blueprint thm-cbc-finite-extension, proof step 1
(blueprint: thm-cbc-finite-extension). -/
@[instance] theorem cbcCompactSupportSourceLift_additive
    (l : ℕ) [Fact l.Prime] (E : Type (u + 1)) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X Y Y' : Scheme.{u}} {f : X ⟶ Y} (g : Y' ⟶ Y) (c : Compactification f)
    (d : AdicCoefficientDatum (Padic.coefficientExtensionIntegers l E))
    (hSource : ∀ K : PbcBoundedConstructibleComplete X d,
      PbcIsBoundedConstructibleComplete Y' d
        ((cbcCompactSupportSource g c d).obj K.obj)) :
    (cbcCompactSupportSourceLift l E g c d hSource).Additive := by
  sorry

/-- The target restriction is additive for the inherited full-subcategory addition.
Proof: the restriction maps each morphism by the ambient composite. Its additivity
equation is the ambient equation viewed through the faithful full inclusion.
Source: blueprint thm-cbc-finite-extension, proof step 1
(blueprint: thm-cbc-finite-extension). -/
@[instance] theorem cbcCompactSupportTargetLift_additive
    (l : ℕ) [Fact l.Prime] (E : Type (u + 1)) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X X' Y' : Scheme.{u}} {f' : X' ⟶ Y'} (g' : X' ⟶ X)
    (c' : Compactification f')
    (d : AdicCoefficientDatum (Padic.coefficientExtensionIntegers l E))
    (hTarget : ∀ K : PbcBoundedConstructibleComplete X d,
      PbcIsBoundedConstructibleComplete Y' d
        ((cbcCompactSupportTarget g' c' d).obj K.obj)) :
    (cbcCompactSupportTargetLift l E g' c' d hTarget).Additive := by
  sorry

/-- The source restriction respects the actual constant-section scalar action.
Proof: tensor, pullback and direct image commute with scalar multiples of maps on
representatives. These equations survive localization and full-subcategory restriction.
Source: blueprint thm-cbc-finite-extension, proof step 1
(blueprint: thm-cbc-finite-extension). -/
@[instance] theorem cbcCompactSupportSourceLift_linear
    (l : ℕ) [Fact l.Prime] (E : Type (u + 1)) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X Y Y' : Scheme.{u}} {f : X ⟶ Y} (g : Y' ⟶ Y) (c : Compactification f)
    (d : AdicCoefficientDatum (Padic.coefficientExtensionIntegers l E))
    (hSource : ∀ K : PbcBoundedConstructibleComplete X d,
      PbcIsBoundedConstructibleComplete Y' d
        ((cbcCompactSupportSource g c d).obj K.obj)) :
    (cbcCompactSupportSourceLift l E g c d hSource).Linear
      (Padic.coefficientExtensionIntegers l E) := by
  sorry

/-- The target restriction respects the actual constant-section scalar action.
Proof: tensor, pullback and direct image commute with scalar multiples of maps on
representatives. These equations survive localization and full-subcategory restriction.
Source: blueprint thm-cbc-finite-extension, proof step 1
(blueprint: thm-cbc-finite-extension). -/
@[instance] theorem cbcCompactSupportTargetLift_linear
    (l : ℕ) [Fact l.Prime] (E : Type (u + 1)) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X X' Y' : Scheme.{u}} {f' : X' ⟶ Y'} (g' : X' ⟶ X)
    (c' : Compactification f')
    (d : AdicCoefficientDatum (Padic.coefficientExtensionIntegers l E))
    (hTarget : ∀ K : PbcBoundedConstructibleComplete X d,
      PbcIsBoundedConstructibleComplete Y' d
        ((cbcCompactSupportTarget g' c' d).obj K.obj)) :
    (cbcCompactSupportTargetLift l E g' c' d hTarget).Linear
      (Padic.coefficientExtensionIntegers l E) := by
  sorry

/-- The two rational functors obtained by scalar transport of these lifts.
Source: `prop-weil-pbc-rational-transport`
(blueprint: thm-cbc-finite-extension). -/
abbrev cbcCompactSupportSourceTransport
    (l : ℕ) [Fact l.Prime] (E : Type (u + 1)) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X Y Y' : Scheme.{u}} {f : X ⟶ Y} (g : Y' ⟶ Y) (c : Compactification f)
    (d : AdicCoefficientDatum (Padic.coefficientExtensionIntegers l E))
    (hSource : ∀ K : PbcBoundedConstructibleComplete X d,
      PbcIsBoundedConstructibleComplete Y' d
        ((cbcCompactSupportSource g c d).obj K.obj)) :=
  ScalarLocalization.transport (Padic.coefficientExtensionIntegers l E)
    (Padic.coefficientExtensionUniformizer l E)
    (cbcCompactSupportSourceLift l E g c d hSource)

/-- The target rational functor obtained by scalar transport of the target lift.
Source: `prop-weil-pbc-rational-transport`
(blueprint: thm-cbc-finite-extension). -/
abbrev cbcCompactSupportTargetTransport
    (l : ℕ) [Fact l.Prime] (E : Type (u + 1)) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X X' Y' : Scheme.{u}} {f' : X' ⟶ Y'} (g' : X' ⟶ X)
    (c' : Compactification f')
    (d : AdicCoefficientDatum (Padic.coefficientExtensionIntegers l E))
    (hTarget : ∀ K : PbcBoundedConstructibleComplete X d,
      PbcIsBoundedConstructibleComplete Y' d
        ((cbcCompactSupportTarget g' c' d).obj K.obj)) :=
  ScalarLocalization.transport (Padic.coefficientExtensionIntegers l E)
    (Padic.coefficientExtensionUniformizer l E)
    (cbcCompactSupportTargetLift l E g' c' d hTarget)

/-- The canonical scalar-localized component for one integral representative.
Source: the completed exchange in the compact-support square
(blueprint: thm-cbc-finite-extension). -/
def finiteExtensionCompactSupportExchangeComponent
    (l : ℕ) [Fact l.Prime] (E : Type (u + 1)) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (c : Compactification f)
    (c' : Compactification f') (gbar : c'.Z ⟶ c.Z)
    (properSquare : ChosenCartesianSquare gbar c'.g c.g g)
    (openSquare : OpenImmersionSquare g' c'.i c.i gbar) [QuasiCompact f]
    (r : ℕ) (a : Fin r → Padic.coefficientExtensionIntegers l E)
    (ha : Ideal.span (Set.range a) = (pbcPadicCoefficientDatum l E).ideal)
    (hSource : ∀ K : PbcBoundedConstructibleComplete X
      (pbcPadicCoefficientDatum l E),
      PbcIsBoundedConstructibleComplete Y' (pbcPadicCoefficientDatum l E)
      (((pbcPadicCoefficientDatum l E).completedPull g).obj
        (((pbcPadicCoefficientDatum l E).push c.g).obj
          ((cbcDerivedOpenShriek (pbcPadicCoefficientDatum l E) c.i
            c.isOpenImmersion).obj K.obj))))
    (hTarget : ∀ K : PbcBoundedConstructibleComplete X
      (pbcPadicCoefficientDatum l E),
      PbcIsBoundedConstructibleComplete Y' (pbcPadicCoefficientDatum l E)
      (((pbcPadicCoefficientDatum l E).push c'.g).obj
        ((cbcDerivedOpenShriek (pbcPadicCoefficientDatum l E) c'.i
          c'.isOpenImmersion).obj
          (((pbcPadicCoefficientDatum l E).completedPull g').obj K.obj))))
    (K : PbcBoundedConstructibleComplete X (pbcPadicCoefficientDatum l E))
    (hComplete : cbcCompleteProperty (pbcPadicCoefficientDatum l E) X r a ha K.obj) :
    (cbcCompactSupportSourceTransport l E g c
      (pbcPadicCoefficientDatum l E) hSource).obj ⟨K⟩ ⟶
    (cbcCompactSupportTargetTransport l E g' c'
      (pbcPadicCoefficientDatum l E) hTarget).obj ⟨K⟩ :=
  (pbcRationalization Y' (pbcPadicCoefficientDatum l E)
    (Padic.coefficientExtensionUniformizer l E)).map
    (ObjectProperty.homMk
      (completedCompactSupportExchange (pbcPadicCoefficientDatum l E)
        c c' gbar properSquare openSquare r a ha ⟨K.obj, hComplete⟩))

/-- The compact-support exchange over a finite extension is the rational
extension of the completed integral exchange.  It is natural in rational
morphisms and every component is invertible.
Source: blueprint thm-cbc-finite-extension, proof steps 1--6
(blueprint: thm-cbc-finite-extension).
Proof:
1. The integral compact-support uniform-restriction theorem gives exact scalar-linear
restrictions of Rp_* j_! for f and its base change. The valuation ring has a length-one
free resolution of each quotient. A bounded input therefore has one common reduction
interval. Apply preservation-constructible to the proper identity square with N=l and
fibre bound zero to obtain constructible preservation by both completed pullbacks.
2. Each integral object is intrinsically complete and has compatible etale origins.
Apply thm-cbc-complete-proetale to its specified completed compact-support exchange.
The landing predicates of step 1 put both endpoints in the full integral category;
its inverse is consequently a morphism in that full category as well.
3. Rational transport extends these scalar-linear functors and their natural exchange.
On each Hom module the extended map sends u tensor a to F(u) tensor a, so extensions
of composites agree with composites of extensions.
4. Tensor the integral inverse with one. The localization composition formula makes
its two composites the localized identities, proving every rational component invertible.
5. Integral naturality extends from pure tensors to every rational map by additivity.
For a rational isomorphism identifying two representatives, this equation is exactly
independence of lattice under the two induced functorial identifications.
6. Localize the integral identity and pasting diagrams. Localization preserves identities,
composition and whiskering, and the intermediate comparison maps cancel as integrally. -/
theorem finiteExtension_compactSupportBaseChange
    (l : ℕ) [Fact l.Prime] (E : Type (u + 1)) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (c : Compactification f)
    (c' : Compactification f') (gbar : c'.Z ⟶ c.Z)
    (properSquare : ChosenCartesianSquare gbar c'.g c.g g)
    (openSquare : OpenImmersionSquare g' c'.i c.i gbar)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsNoetherian X] [IsNoetherian Y] [IsNoetherian X'] [IsNoetherian Y']
    (_dimX : ∃ n : ℕ, topologicalKrullDim X ≤ (n : WithBot ℕ∞))
    (_dimY : ∃ n : ℕ, topologicalKrullDim Y ≤ (n : WithBot ℕ∞))
    (_dimX' : ∃ n : ℕ, topologicalKrullDim X' ≤ (n : WithBot ℕ∞))
    (_dimY' : ∃ n : ℕ, topologicalKrullDim Y' ≤ (n : WithBot ℕ∞))
    (_hlX : ∀ x : X, IsUnit (l : X.presheaf.stalk x))
    (_hlY : ∀ y : Y, IsUnit (l : Y.presheaf.stalk y))
    (_hlX' : ∀ x' : X', IsUnit (l : X'.presheaf.stalk x'))
    (_hlY' : ∀ y' : Y', IsUnit (l : Y'.presheaf.stalk y')) :
    ∃ (hSource : ∀ K : PbcBoundedConstructibleComplete X
        (pbcPadicCoefficientDatum l E),
      PbcIsBoundedConstructibleComplete Y' (pbcPadicCoefficientDatum l E)
        ((cbcCompactSupportSource g c (pbcPadicCoefficientDatum l E)).obj K.obj)),
      ∃ (hTarget : ∀ K : PbcBoundedConstructibleComplete X
        (pbcPadicCoefficientDatum l E),
      PbcIsBoundedConstructibleComplete Y' (pbcPadicCoefficientDatum l E)
        ((cbcCompactSupportTarget g' c' (pbcPadicCoefficientDatum l E)).obj K.obj)),
      ∃ η : cbcCompactSupportSourceTransport l E g c
          (pbcPadicCoefficientDatum l E) hSource ≅
        cbcCompactSupportTargetTransport l E g' c'
          (pbcPadicCoefficientDatum l E) hTarget,
        ∀ (K : PbcBoundedConstructibleComplete X (pbcPadicCoefficientDatum l E))
          (r : ℕ) (a : Fin r → Padic.coefficientExtensionIntegers l E)
          (ha : Ideal.span (Set.range a) = (pbcPadicCoefficientDatum l E).ideal)
          (hComplete : cbcCompleteProperty (pbcPadicCoefficientDatum l E) X r a ha K.obj),
          η.hom.app ⟨K⟩ =
            finiteExtensionCompactSupportExchangeComponent l E c c' gbar
              properSquare openSquare r a ha hSource hTarget K hComplete := by
  sorry

/-- The category-domain hypotheses used by the identity and pasted-square clauses.
This only collects the three geometric conditions from the statement.
Source: blueprint thm-cbc-finite-extension, statement, first paragraph
(blueprint: thm-cbc-finite-extension). -/
def CbcFiniteExtensionDomain (l : ℕ) (T : Scheme.{u}) : Prop :=
  IsNoetherian T ∧ (∃ n : ℕ, topologicalKrullDim T ≤ (n : WithBot ℕ∞)) ∧
    ∀ x : T, IsUnit (l : T.presheaf.stalk x)

/-- Intrinsic completeness of a selected integral object, for every presentation of I.
Source: blueprint thm-cbc-finite-extension, proof step 2
(blueprint: thm-cbc-finite-extension).
Proof: membership includes invertibility of the intrinsic Koszul completion unit on
some generating tuple and representative. The canonical coefficient comparison transports
that unit, retaining its normalization. Koszul reconstruction identifies it with the
canonical quotient-tower completion map. For any other finite tuple generating the same
ideal and any other representative, reconstruction identifies its unit with that same map,
conjugated by the representative comparison. Its invertibility is therefore unchanged.
Use the specified Q preimage representative to obtain cbcCompleteProperty. This also
covers the empty tuple when it generates the ideal; no completeness hypothesis is added. -/
theorem finiteExtension_cbcComplete
    (l : ℕ) [Fact l.Prime] (E : Type (u + 1)) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (T : Scheme.{u}) (K : PbcBoundedConstructibleComplete T (pbcPadicCoefficientDatum l E))
    (r : ℕ) (a : Fin r → Padic.coefficientExtensionIntegers l E)
    (ha : Ideal.span (Set.range a) = (pbcPadicCoefficientDatum l E).ideal) :
    cbcCompleteProperty (pbcPadicCoefficientDatum l E) T r a ha K.obj := by
  sorry

/-- Localization of an ambient arrow between selected integral objects.
Applied to a path, this is its rational path: the full inclusion and localization preserve
composition and identities. In particular the following equations use the actual canonical
integral comparisons, with no arbitrary endpoint isomorphism.
Source: blueprint thm-cbc-finite-extension, proof steps 3 and 6
(blueprint: thm-cbc-finite-extension). -/
def finiteExtensionRationalArrow
    (l : ℕ) [Fact l.Prime] (E : Type (u + 1)) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {T : Scheme.{u}} {M N : (pbcPadicCoefficientDatum l E).derived T}
    (hM : PbcIsBoundedConstructibleComplete T (pbcPadicCoefficientDatum l E) M)
    (hN : PbcIsBoundedConstructibleComplete T (pbcPadicCoefficientDatum l E) N)
    (v : M ⟶ N) :
    (pbcRationalization T (pbcPadicCoefficientDatum l E)
      (Padic.coefficientExtensionUniformizer l E)).obj ⟨M, hM⟩ ⟶
    (pbcRationalization T (pbcPadicCoefficientDatum l E)
      (Padic.coefficientExtensionUniformizer l E)).obj ⟨N, hN⟩ :=
  (pbcRationalization T (pbcPadicCoefficientDatum l E)
    (Padic.coefficientExtensionUniformizer l E)).map (ObjectProperty.homMk v)

section Coherence

variable (l : ℕ) [Fact l.Prime] (E : Type (u + 1)) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Rational identity-base-change coherence, with the unit-normalized completed identity
comparisons. Both paths are localized in the raw rational category of Y.
Source: blueprint thm-cbc-finite-extension, identity clause and proof step 6
(blueprint: thm-cbc-finite-extension).
Proof: apply completeCompactSupportProetale_identity to the complete integral object
with its compatible origins. Integral compact support and completed pullback land in the
selected subcategories by proof step 1. Regard both paths as morphisms of the full integral
subcategory and apply its rationalization functor. This functor preserves compositions and
identities, giving precisely the displayed rational paths. The component formula of the
main theorem identifies their exchange with the rational natural isomorphism. -/
theorem finiteExtension_compactSupportBaseChange_identity
    {X Y : Scheme.{u}} {f : X ⟶ Y}
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (_hX : CbcFiniteExtensionDomain l X) (_hY : CbcFiniteExtensionDomain l Y)
    (c : Compactification f)
    (sp : ChosenCartesianSquare (𝟙 c.Z) c.g c.g (𝟙 Y))
    (sj : OpenImmersionSquare (𝟙 X) c.i c.i (𝟙 c.Z))
    (r : ℕ) (a : Fin r → Padic.coefficientExtensionIntegers l E)
    (ha : Ideal.span (Set.range a) = (pbcPadicCoefficientDatum l E).ideal)
    (K : PbcBoundedConstructibleComplete X (pbcPadicCoefficientDatum l E)) :
    ∃ (hK : (pbcPadicCoefficientDatum l E).TowerComplete X K.obj)
      (hF : (pbcPadicCoefficientDatum l E).TowerComplete Y
        ((cbcSupport (pbcPadicCoefficientDatum l E) c).obj K.obj))
      (hS : PbcIsBoundedConstructibleComplete Y (pbcPadicCoefficientDatum l E)
        (((pbcPadicCoefficientDatum l E).completedPull (𝟙 Y)).obj
          ((cbcSupport (pbcPadicCoefficientDatum l E) c).obj K.obj)))
      (hT : PbcIsBoundedConstructibleComplete Y (pbcPadicCoefficientDatum l E)
        ((cbcSupport (pbcPadicCoefficientDatum l E) c).obj K.obj)),
      finiteExtensionRationalArrow l E hS hT
        (cbcExchange (pbcPadicCoefficientDatum l E) c c (𝟙 c.Z) sp sj r a ha
            ⟨K.obj, finiteExtension_cbcComplete l E X K r a ha⟩ ≫
          (cbcSupport (pbcPadicCoefficientDatum l E) c).map
            ((pbcPadicCoefficientDatum l E).completedPullId X K.obj hK).hom) =
      finiteExtensionRationalArrow l E hS hT
        ((pbcPadicCoefficientDatum l E).completedPullId Y
          ((cbcSupport (pbcPadicCoefficientDatum l E) c).obj K.obj) hF).hom := by
  sorry

/-- Rational horizontal-pasting coherence for two arbitrary successive base changes.
The paths retain the canonical completion-unit-normalized pullback compositors.
Source: blueprint thm-cbc-finite-extension, pasted-square clause and proof step 6
(blueprint: thm-cbc-finite-extension).
Proof: proof step 1 gives constructible complete landing for the intermediate pullback
and all endpoints. Apply completeCompactSupportProetale_horizontal, using the input's
intrinsic completeness and compatible etale origins. Localize its two paths in the full
selected category of Y''. Functoriality of localization and the pure-tensor formula for
scalar transport identify these with the two rational pasted paths. The main component
formula identifies every exchange factor with its specified rational component. -/
theorem finiteExtension_compactSupportBaseChange_horizontal
    {X X' X'' Y Y' Y'' : Scheme.{u}}
    {f : X ⟶ Y} {f' : X' ⟶ Y'} {f'' : X'' ⟶ Y''}
    {g : Y' ⟶ Y} {g' : X' ⟶ X} {h : Y'' ⟶ Y'} {h' : X'' ⟶ X'}
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (_hX : CbcFiniteExtensionDomain l X) (_hX' : CbcFiniteExtensionDomain l X')
    (_hX'' : CbcFiniteExtensionDomain l X'') (_hY : CbcFiniteExtensionDomain l Y)
    (_hY' : CbcFiniteExtensionDomain l Y') (_hY'' : CbcFiniteExtensionDomain l Y'')
    (c : Compactification f) (c' : Compactification f') (c'' : Compactification f'')
    (gb : c'.Z ⟶ c.Z) (hb : c''.Z ⟶ c'.Z)
    (sp₁ : ChosenCartesianSquare gb c'.g c.g g)
    (sj₁ : OpenImmersionSquare g' c'.i c.i gb)
    (sp₂ : ChosenCartesianSquare hb c''.g c'.g h)
    (sj₂ : OpenImmersionSquare h' c''.i c'.i hb)
    (sp : ChosenCartesianSquare (hb ≫ gb) c''.g c.g (h ≫ g))
    (sj : OpenImmersionSquare (h' ≫ g') c''.i c.i (hb ≫ gb))
    (r : ℕ) (a : Fin r → Padic.coefficientExtensionIntegers l E)
    (ha : Ideal.span (Set.range a) = (pbcPadicCoefficientDatum l E).ideal)
    (K : PbcBoundedConstructibleComplete X (pbcPadicCoefficientDatum l E)) :
    ∃ (hK' : cbcCompleteProperty (pbcPadicCoefficientDatum l E) X' r a ha
        (((pbcPadicCoefficientDatum l E).completedPull g').obj K.obj))
      (hS : PbcIsBoundedConstructibleComplete Y'' (pbcPadicCoefficientDatum l E)
        (((pbcPadicCoefficientDatum l E).completedPull (h ≫ g)).obj
          ((cbcSupport (pbcPadicCoefficientDatum l E) c).obj K.obj)))
      (hT : PbcIsBoundedConstructibleComplete Y'' (pbcPadicCoefficientDatum l E)
        ((cbcSupport (pbcPadicCoefficientDatum l E) c'').obj
          (((pbcPadicCoefficientDatum l E).completedPull (h' ≫ g')).obj K.obj))),
      finiteExtensionRationalArrow l E hS hT
        (cbcExchange (pbcPadicCoefficientDatum l E) c c'' (hb ≫ gb) sp sj r a ha
          ⟨K.obj, finiteExtension_cbcComplete l E X K r a ha⟩) =
      finiteExtensionRationalArrow l E hS hT
        (((pbcPadicCoefficientDatum l E).completedPullComp h g).hom.app
            ((cbcSupport (pbcPadicCoefficientDatum l E) c).obj K.obj) ≫
          ((pbcPadicCoefficientDatum l E).completedPull h).map
            (cbcExchange (pbcPadicCoefficientDatum l E) c c' gb sp₁ sj₁ r a ha
              ⟨K.obj, finiteExtension_cbcComplete l E X K r a ha⟩) ≫
          cbcExchange (pbcPadicCoefficientDatum l E)
            (qf := cbcBaseChangeQuasiCompact c c' gb sj₁)
            c' c'' hb sp₂ sj₂ r a ha
            ⟨((pbcPadicCoefficientDatum l E).completedPull g').obj K.obj, hK'⟩ ≫
          (cbcSupport (pbcPadicCoefficientDatum l E) c'').map
            (((pbcPadicCoefficientDatum l E).completedPullComp h' g').inv.app K.obj)) := by
  sorry

/-- Rational vertical-pasting coherence, with the canonical proper/open composition
maps for supplied compatible compactification towers. No Cartesian refinement is imposed.
Source: blueprint thm-cbc-finite-extension, pasted-square clause and proof step 6
(blueprint: thm-cbc-finite-extension).
Proof: compact-support preservation in proof step 1 supplies the complete intermediate
image and all constructible endpoints. Apply completeCompactSupportProetale_vertical
with the input's compatible origins. Its comparisons are the specified proper/open mates
and are invertible. Localize its two ordered paths. Preservation of composition and the
scalar-transport formula identify these with rational vertical pasting. The integral
composition/refinement law makes the same equation valid after any common refinement,
so the supplied compatible towers do not restrict the allowed pasted squares. -/
theorem finiteExtension_compactSupportBaseChange_vertical
    {X X' Y Y' Z Z' : Scheme.{u}}
    {f : X ⟶ Y} {f' : X' ⟶ Y'} {h : Y ⟶ Z} {h' : Y' ⟶ Z'}
    {gx : X' ⟶ X} {gy : Y' ⟶ Y} {gz : Z' ⟶ Z}
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    (_hX : CbcFiniteExtensionDomain l X) (_hX' : CbcFiniteExtensionDomain l X')
    (_hY : CbcFiniteExtensionDomain l Y) (_hY' : CbcFiniteExtensionDomain l Y')
    (_hZ : CbcFiniteExtensionDomain l Z) (_hZ' : CbcFiniteExtensionDomain l Z')
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
    [IsProper p] [IsProper p']
    (hb : cf.i ≫ b = chf.i) (hp : b ≫ p = cf.g ≫ ch.i)
    (hq : p ≫ ch.g = chf.g)
    (hb' : cf'.i ≫ b' = chf'.i) (hp' : b' ≫ p' = cf'.g ≫ ch'.i)
    (hq' : p' ≫ ch'.g = chf'.g)
    (sq : IsPullback b cf.g p ch.i) (sq' : IsPullback b' cf'.g p' ch'.i)
    (_wb : b' ≫ gbhf = gbf ≫ b) (_wp : p' ≫ gbh = gbhf ≫ p)
    (r : ℕ) (a : Fin r → Padic.coefficientExtensionIntegers l E)
    (ha : Ideal.span (Set.range a) = (pbcPadicCoefficientDatum l E).ideal)
    (K : PbcBoundedConstructibleComplete X (pbcPadicCoefficientDatum l E)) :
    ∃ (hF : cbcCompleteProperty (pbcPadicCoefficientDatum l E) Y r a ha
        ((cbcSupport (pbcPadicCoefficientDatum l E) cf).obj K.obj))
      (hS : PbcIsBoundedConstructibleComplete Z' (pbcPadicCoefficientDatum l E)
        (((pbcPadicCoefficientDatum l E).completedPull gz).obj
          ((cbcSupport (pbcPadicCoefficientDatum l E) ch).obj
            ((cbcSupport (pbcPadicCoefficientDatum l E) cf).obj K.obj))))
      (hT : PbcIsBoundedConstructibleComplete Z' (pbcPadicCoefficientDatum l E)
        ((cbcSupport (pbcPadicCoefficientDatum l E) chf').obj
          (((pbcPadicCoefficientDatum l E).completedPull gx).obj K.obj))),
      finiteExtensionRationalArrow l E hS hT
        (((pbcPadicCoefficientDatum l E).completedPull gz).map
            (cbcTowerCompositionMap (pbcPadicCoefficientDatum l E)
              cf ch chf b p hb hp hq sq K.obj) ≫
          cbcExchange (pbcPadicCoefficientDatum l E) chf chf' gbhf sphf sjhf r a ha
            ⟨K.obj, finiteExtension_cbcComplete l E X K r a ha⟩) =
      finiteExtensionRationalArrow l E hS hT
        (cbcExchange (pbcPadicCoefficientDatum l E) ch ch' gbh sph sjh r a ha
            ⟨(cbcSupport (pbcPadicCoefficientDatum l E) cf).obj K.obj, hF⟩ ≫
          (cbcSupport (pbcPadicCoefficientDatum l E) ch').map
            (cbcExchange (pbcPadicCoefficientDatum l E) cf cf' gbf spf sjf r a ha
              ⟨K.obj, finiteExtension_cbcComplete l E X K r a ha⟩) ≫
          cbcTowerCompositionMap (pbcPadicCoefficientDatum l E)
            (qh := cbcBaseChangeQuasiCompact ch ch' gbh sjh)
            cf' ch' chf' b' p' hb' hp' hq' sq'
            (((pbcPadicCoefficientDatum l E).completedPull gx).obj K.obj)) := by
  sorry

end Coherence

end AlgebraicGeometry.Scheme
