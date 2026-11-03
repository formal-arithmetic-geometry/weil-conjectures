/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SkThmSfCompComposition
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ExceptionalInverseImageExistence
public import WeilConjectures.AlgebraicGeometry.BaseFieldFiniteCD.FiniteCohomologicalDimensionHypothesis
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ListedCoefficientMaps
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixDefinitions
public import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficientTwistsSupplement
public import WeilConjectures.AlgebraicGeometry.InternalModuleOperations.InternalModuleOperationsTransportSupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixDerivedPullbackNormalization
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixImmersionComparison
public import WeilConjectures.AlgebraicGeometry.RootCoordinateFace.RootTowerCoordinateFace
public import Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ProfiniteCondensedRing
public import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import WeilConjectures.CategoryTheory.ProEtaleCoefficients.LocalizingAdmissibleCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.LocalizingExceptionalAdjoint
public import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IntTensorProjection
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedLocalizingPullback
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compactification.CompactificationLocalizing
public import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.AdmissibleTensorConstructibility
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedCoefficientIsoConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralOpenImageProperFormulas
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.LocalizingClosureCtfEqualsBc
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Proper.ProperLocalizingAdmissibleCoefficients
public import WeilConjectures.AlgebraicGeometry.Rational.RationalOpenDirectImageConstructible
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.BaseCoefficientCondensedIdentification
public import WeilConjectures.AlgebraicGeometry.Compactification.CompactificationOverField
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteOpenDirectImageCtf
public import WeilConjectures.Compactification.Over
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerStarComp
public import Mathlib.CategoryTheory.Triangulated.Adjunction
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ScalarSixFiniteGeneration
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ScalarSixNonfiniteGeneration
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ScalarSixAdmissibleThickness
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ScalarSixPerfectExtension
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixCtfGenerators
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficientsMate
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Coefficient.CoefficientProjectionSquare
public import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficientsFiniteFree
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.PushIntegralDerivedIso
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.QlbarDirectImageComparison
public import WeilConjectures.AlgebraicGeometry.IntegralFiniteScalar.FiniteFreeScalarDerivedComparison
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteDiscreteScalarProjectionCase
public import WeilConjectures.AlgebraicGeometry.QuotientChange.InternalScalarRestrictionMateNormalization
public import WeilConjectures.AlgebraicGeometry.QuotientChange.InternalScalarMateProjection
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralFinitePointResolution
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ScalarSixTensorComparison
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ListedScalarCoefficientMaps
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ScalarSixCtf
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compactification.CompactificationCoherenceCocycle
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Proper.ProEtaleProperOpenInterchange
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleLocallyConstantSheaf
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsSupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedModuleDerivedPushpull
public import Mathlib.CategoryTheory.Adjunction.CompositionIso
public import WeilConjectures.SixFunctors.ScalarOpenCompositorCoherence
public import WeilConjectures.AlgebraicGeometry.QuotientChange.ScalarGeometricExchangeRectangle
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compactification.CompactificationRefinementLocalizing
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Open.OpenExtensionConstructibleFiniteTor
public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.AlgebraicGeometry.Proper.Open.ProperOpenCoefficientRefinement
public import WeilConjectures.CategoryTheory.AdjunctionSquareComposition
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.CompConjugate
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Coherence
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteCoefficientSmallCarrierComparison
public import WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.LocalizingLowerShriekCompositionModel
public import WeilConjectures.AlgebraicGeometry.ProEtale.Tate.ProEtaleTateTwists
public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import Mathlib.CategoryTheory.Whiskering
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.ProfiniteFiniteConstantLocalModel
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.DetSfCompBaseChangeDefs
import WeilConjectures.Compactification.CommonDenseRefinement
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compact.CompactSupportRefinementBaseChange
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixDefinitions
import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficients
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.AlgebraicGeometry.InternalModuleOperations.InternalModuleOperationsTransportSupplement
import WeilConjectures.Algebra.Homology.ScalarPullback.KFlatScalarComparisonNormalization
import WeilConjectures.AlgebraicGeometry.LocallyClosedExtensionData.LocallyClosedExtensionCoherence
import WeilConjectures.AlgebraicGeometry.QuotientChange.ScalarGeometricExchangeRectangle
import WeilConjectures.AlgebraicGeometry.QuotientChange.ScalarPullbackSquareCoherence
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixDerivedPullbackNormalization
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixNormalizedImmersion
import WeilConjectures.CategoryTheory.SixFunctors.MateIsoAlongEquivalences
import WeilConjectures.AlgebraicGeometry.PurityTransport.Transport
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.CategoryTheory.Sites.LocalProperties

/-! # Strict integral exchange data on condensed compact-support categories

Source: blueprint latest,
literature/blueprint/latest/blueprint/part-six-operations/sec-smooth-base-change/sec-sbc-uniform/
sk-thm-sbc-coefficients/fix-lem-exchanges.proof.md, clauses 1, 2, 4;
sk-prop-scalar-six; sk-prop-sp-composition; sk-prop-sp-purity-bc
(blueprint: def-pur-strict-integral-exchange-data).

The full subcategories are the published bounded constructible finite-Tor categories of
ordinary derived internal modules over the coefficient ring pulled from the condensed point.
The owner predicate is the current two-clause theorem `sk_thm_sf_comp_composition`.
Its existential package contains all six comparison witnesses together with refinement,
composition, unit, associativity, open/exchange normalization, independence and pasting
laws. Its arrows are morphisms in `SepFinType k`, and every underlying scheme square is
obtained with `.hom.left`; no free comparison is introduced.
Right adjoints are quantified together with their adjunctions; their conjugates and exceptional
exchange maps below are actual adjunction constructions.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u v₁ v₂ v₃ v₄ v₅ v₆
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing
namespace PurStrictIntegralExchangeData

/-- Exactly the four coefficient stages in the statement, invariant under coefficient
isomorphism. The finite quotient uses the recorded uniformizer and the discrete topology.
Source: opening coefficient convention (blueprint: def-pur-strict-integral-exchange-data). -/
def IsCoefficient (ell : ℕ) [Fact ell.Prime] (Λ : ScalarSixRing.{u}) : Prop :=
  (∃ (E : PadicAlgCl.FiniteIntermediateField ell) (n : ℕ), 1 ≤ n ∧
    Nonempty (Mon.mk Λ.X ≅ Mon.mk
      (cartesianFinitePointRing (ULift.{u} (Padic.coefficientExtensionRing ell E.1 n))))) ∨
  (∃ E : PadicAlgCl.FiniteIntermediateField ell,
    Nonempty (Mon.mk Λ.X ≅ Mon.mk (Profinite.padicIntegersRingObj ell E.1))) ∨
  (∃ E : PadicAlgCl.FiniteIntermediateField ell,
    Nonempty (Mon.mk Λ.X ≅ Mon.mk (Profinite.continuousMapRingObj E.1))) ∨
  Nonempty (Mon.mk Λ.X ≅ Mon.mk (Profinite.padicAlgClRingObj ell))

variable {k : Type u} [Field k] {Λ : ScalarSixRing.{u}}
variable {ell : ℕ} [Fact ell.Prime]

section OwnerWitnessBundle

-- As in CompactSupportRefinementBaseChange, keep the derived constructions abstract
-- while comparing signatures; their implementations are irrelevant to this conversion.
attribute [local irreducible] upperStar lowerStar openImmersionLowerShriek
  Functor.rightDerivedFunctor Functor.mapDerivedCategory Functor.leftDerivedFunctor
  derivedUpperStarLowerStarAdjunction derivedOpenImmersionLowerShriekUpperStarAdjunction
  leftDerivedUpperStarIsoMapDerivedCategory upperStarLowerStarAdjunction
  condensedAmbientPullbackComparison AlgebraicGeometry.ProEtale.upperStarFromPoint
  Mod.monoidalClosed Mod.monoidalCategory Mod.monoidalCategoryStruct
  Sheaf.monoidalCategory DerivedCategory.monoidalClosed
  DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory
  instCategoryDerivedCategory MorphismProperty.instCategoryLocalization

/-- The standing hypotheses of the current Q76 composition and base-change theorem.
Source: `sk_thm_sf_comp_composition` (blueprint: def-pur-strict-integral-exchange-data). -/
structure Standing (ell : ℕ) [Fact ell.Prime] (k : Type u) [Field k]
    (Γ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Γ] [IsCommMonObj Γ] : Prop where
  hk : Finite k ∨ IsAlgClosed k
  hp : Fact (ringChar k).Prime
  hne : Fact (ringChar k ≠ ell)
  hΓ : IsLocalizingAdmissibleCoefficient ell Γ

variable {Γ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
variable [MonObj Γ] [IsCommMonObj Γ]

/-- The actual owner theorem, with its six existentials and full predicate unchanged.
Source: `sk_thm_sf_comp_composition`
(blueprint: def-pur-strict-integral-exchange-data). -/
opaque ownerWitnessPackage (H : Standing ell k Γ) :
    type_of% (@sk_thm_sf_comp_composition ell (inferInstance : Fact ell.Prime) k
    (inferInstance : Field k) H.hp H.hne H.hk Γ
    (inferInstance : MonObj Γ) (inferInstance : IsCommMonObj Γ) H.hΓ) :=
  @sk_thm_sf_comp_composition ell (inferInstance : Fact ell.Prime) k
    (inferInstance : Field k) H.hp H.hne H.hk Γ
    (inferInstance : MonObj Γ) (inferInstance : IsCommMonObj Γ) H.hΓ

/-- A record for the six independent types of witnesses in the owner theorem.
This is only a data container; the original predicate is retained by packSix.
Source: six existential binders of Q76
(blueprint: def-pur-strict-integral-exchange-data). -/
structure SixWitnesses (A : Sort v₁) (B : Sort v₂) (C : Sort v₃)
    (D : Sort v₄) (E : Sort v₅) (F : Sort v₆) where
  preserves : A
  comparison : B
  comp : C
  openIso : D
  pullbackPreserves : E
  exchange : F

/-- Logical repackaging of six existential witnesses together with their unchanged
predicate. Its complete proof is just existential elimination and introduction.
Source: six existential binders of Q76
(blueprint: def-pur-strict-integral-exchange-data). -/
opaque packSix {A : Sort v₁} {B : Sort v₂} {C : Sort v₃}
    {D : Sort v₄} {E : Sort v₅} {F : Sort v₆}
    (P : A → B → C → D → E → F → Prop)
    (h : ∃ (a : A) (b : B) (c : C) (d : D) (e : E) (f : F), P a b c d e f) :
    ∃ W : SixWitnesses A B C D E F,
      P W.preserves W.comparison W.comp W.openIso W.pullbackPreserves W.exchange :=
  match h with
  | ⟨a, b, c, d, e, f, hP⟩ => ⟨⟨a, b, c, d, e, f⟩, hP⟩

/-- The actual Q76 theorem repackaged as one existential with the complete original
predicate. No witness or law is discarded, and no predicate is replaced by True.
Source: sk_thm_sf_comp_composition, packSix
(blueprint: def-pur-strict-integral-exchange-data). -/
opaque ownerFlat (H : Standing ell k Γ) :
    type_of% (packSix _ (ownerWitnessPackage H)) :=
  packSix _ (ownerWitnessPackage H)

-- Register a definition whose body is exactly the predicate in ownerFlat's type.
-- No proof or proposition is copied or simplified. Lean.addDecl kernel-checks it.
run_cmd Lean.Elab.Command.liftTermElabM do
  let info ← Lean.getConstInfo
    ``AlgebraicGeometry.ProEtale.CondensedRing.PurStrictIntegralExchangeData.ownerFlat
  Lean.Meta.forallTelescope info.type fun xs body => do
    let .app (.app (.const ``Exists _) _) predicate := body
      | throwError "ownerFlat must conclude an existential"
    let value ← Lean.Meta.mkLambdaFVars xs predicate
    let type ← Lean.Meta.inferType value
    let name :=
      `AlgebraicGeometry.ProEtale.CondensedRing.PurStrictIntegralExchangeData.ownerPredicate
    Lean.addDecl (.defnDecl {
      name, levelParams := info.levelParams, type, value,
      hints := .regular 0, safety := .safe }) (forceExpose := true)
    Lean.addDocStringCore name
      "The exact predicate of the packed Q76 theorem, at all six witness projections. \
      Source: sk_thm_sf_comp_composition, ownerFlat \
      (blueprint: def-pur-strict-integral-exchange-data)."

attribute [irreducible] ownerPredicate

set_option genInjectivity false in
set_option genSizeOf false in
set_option genSizeOfSpec false in
/-- The six owner witness types, read directly from Q76. Owner.lawful retains the exact
original Q76 predicate about the same six fields.
The Q76 theorem supplies the six fields together with that required predicate.
Source: `sk_thm_sf_comp_composition`
(blueprint: def-pur-strict-integral-exchange-data). -/
structure Witnesses (H : Standing ell k Γ) where
  preserves : type_of% (@SixWitnesses.preserves _ _ _ _ _ _
    (@Classical.choose _ _ (ownerFlat H)))
  comparison : type_of% (@SixWitnesses.comparison _ _ _ _ _ _
    (@Classical.choose _ _ (ownerFlat H)))
  comp : type_of% (@SixWitnesses.comp _ _ _ _ _ _
    (@Classical.choose _ _ (ownerFlat H)))
  openIso : type_of% (@SixWitnesses.openIso _ _ _ _ _ _
    (@Classical.choose _ _ (ownerFlat H)))
  pullbackPreserves : type_of% (@SixWitnesses.pullbackPreserves _ _ _ _ _ _
    (@Classical.choose _ _ (ownerFlat H)))
  exchange : type_of% (@SixWitnesses.exchange _ _ _ _ _ _
    (@Classical.choose _ _ (ownerFlat H)))

section OwnerRecord

variable (ell k Γ)

set_option genInjectivity false in
set_option genSizeOf false in
set_option genSizeOfSpec false in
/-- The standing datum and the six Q76 witnesses with the complete original
predicate about those same witnesses. In particular comp and exchange have their
normalization, independence, unit, associativity and stacked-square laws.
Source: `sk_thm_sf_comp_composition`
(blueprint: def-pur-strict-integral-exchange-data). -/
structure Owner where
  standing : Standing ell k Γ
  witnesses : Witnesses standing
  lawful : ownerPredicate standing
    ⟨@witnesses.preserves, @witnesses.comparison, @witnesses.comp,
      @witnesses.openIso, @witnesses.pullbackPreserves, @witnesses.exchange⟩

end OwnerRecord

/-- Preservation from the same lawful owner record as the two comparison maps.
Source: first Q76 witness (blueprint: def-pur-strict-integral-exchange-data). -/
abbrev ownerPreserves (H : Owner (ell := ell) (k := k) (Γ := Γ))
    {X Y : SepFinType k} (f : X ⟶ Y) (c : Compactification f.hom.left) :=
  H.witnesses.preserves f c

/-- Composition from the lawful owner record, with its full normalization in Owner.lawful.
Source: third Q76 witness (blueprint: def-pur-strict-integral-exchange-data). -/
abbrev ownerComp (H : Owner (ell := ell) (k := k) (Γ := Γ))
    {X Y Z : SepFinType k} (f : X ⟶ Y) (g : Y ⟶ Z)
    (c : Compactification f.hom.left) (d : Compactification g.hom.left)
    (e : Compactification (f.hom.left ≫ g.hom.left)) :=
  H.witnesses.comp f g c d e

/-- Pullback preservation from the same lawful owner record.
Source: fifth Q76 witness (blueprint: def-pur-strict-integral-exchange-data). -/
abbrev ownerPullbackPreserves (H : Owner (ell := ell) (k := k) (Γ := Γ))
    (X Y : SepFinType k) (v : X ⟶ Y) :=
  H.witnesses.pullbackPreserves X Y v

/-- Exchange from the lawful owner record, with its full normalization in Owner.lawful.
Source: sixth Q76 witness (blueprint: def-pur-strict-integral-exchange-data). -/
abbrev ownerExchange (H : Owner (ell := ell) (k := k) (Γ := Γ))
    {X Y X' Y' : SepFinType k} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {a : X' ⟶ X} {v : Y' ⟶ Y}
    (sq : IsPullback a.hom.left f'.hom.left f.hom.left v.hom.left)
    (c : Compactification f.hom.left) (d : Compactification f'.hom.left) :=
  H.witnesses.exchange sq c d

/-- The full twelve-clause owner predicate about the record's actual six fields.
Source: Q76 predicate, Owner.lawful
(blueprint: def-pur-strict-integral-exchange-data). -/
abbrev ownerLaws (H : Owner (ell := ell) (k := k) (Γ := Γ)) := H.lawful

end OwnerWitnessBundle

/-- Preservation and the canonical normalized comparison families supplied by composition.
Source: Q76 composition and base-change witnesses
(blueprint: def-pur-strict-integral-exchange-data). -/
abbrev preserves (H : Owner (ell := ell) (k := k) (Γ := Λ.X))
    {X Y : SepFinType k} (f : X ⟶ Y) (c : Compactification f.hom.left) :=
  ownerPreserves H (X := X) (Y := Y) f c

/-- The model compositor supplied by the owner package.
Source: Q76 composition and base-change witnesses
(blueprint: def-pur-strict-integral-exchange-data). -/
@[irreducible] def modelComposition (H : Owner (ell := ell) (k := k) (Γ := Λ.X))
    {X Y Z : SepFinType k} (f : X ⟶ Y) (g : Y ⟶ Z)
    (c : Compactification f.hom.left) (d : Compactification g.hom.left)
    (e : Compactification (f.hom.left ≫ g.hom.left)) :
    (localizingClosureProEtale Λ.X X.obj.left).ι ⋙
        (rightDerivedLowerShriekOfCompactification Λ.X c ⋙
          rightDerivedLowerShriekOfCompactification Λ.X d) ≅
      (localizingClosureProEtale Λ.X X.obj.left).ι ⋙
        rightDerivedLowerShriekOfCompactification Λ.X e :=
  ownerComp H (X := X) (Y := Y) (Z := Z) f g c d e

/-- Pullback preservation, the proof field in the same owner package.
Source: Q76 composition and base-change witnesses
(blueprint: def-pur-strict-integral-exchange-data). -/
abbrev pullPreserves (H : Owner (ell := ell) (k := k) (Γ := Λ.X))
    (X Y : SepFinType k) (v : X ⟶ Y) :=
  ownerPullbackPreserves H X Y v

/-- The exchange supplied by the owner package and its canonical normalization laws.
Source: Q76 composition and base-change witnesses
(blueprint: def-pur-strict-integral-exchange-data). -/
@[irreducible] def modelExchange (H : Owner (ell := ell) (k := k) (Γ := Λ.X))
    {X Y X' Y' : SepFinType k} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {u : X' ⟶ X} {v : Y' ⟶ Y}
    (sq : IsPullback u.hom.left f'.hom.left f.hom.left v.hom.left)
    (c : Compactification f.hom.left) (d : Compactification f'.hom.left) :
    (localizingClosureProEtale Λ.X X.obj.left).ι ⋙
        (rightDerivedLowerShriekOfCompactification Λ.X c ⋙
          moduleObjectDerivedPullback Λ.X v.hom.left) ≅
      (localizingClosureProEtale Λ.X X.obj.left).ι ⋙
        (moduleObjectDerivedPullback Λ.X u.hom.left ⋙
          rightDerivedLowerShriekOfCompactification Λ.X d) :=
  ownerExchange H (X := X) (Y := Y) (X' := X') (Y' := Y')
    (f := f) (f' := f') sq c d

/-- The fully faithful inclusion of the existing Dctf category in its ambient derived category.
Source: full-subcategory convention (blueprint: def-pur-strict-integral-exchange-data). -/
abbrev inclusion (Γ : ScalarSixRing.{u}) (X : Scheme.{u}) :
    ConstantModelConstructibleFiniteTor Γ.X X ⥤
      DerivedCategory (ModuleRingedComparison.internalModules Γ.X X) :=
  ObjectProperty.ι _

/-- The canonical inclusion of Dctf in its localizing closure, with unchanged objects and maps.
Source: composition theorem, restriction to C
(blueprint: def-pur-strict-integral-exchange-data). -/
def toLocalizing (Γ : ScalarSixRing.{u}) (X : Scheme.{u}) :
    ConstantModelConstructibleFiniteTor Γ.X X ⥤
      (localizingClosureProEtale Γ.X X).FullSubcategory :=
  ObjectProperty.ιOfLE (fun K hK _P _hP hS ↦ hS K hK)

/-- The chosen compactification functor, restricted to the actual Dctf full subcategories.
Source: sk-thm-existence (blueprint: def-pur-strict-integral-exchange-data). -/
def lower (H : Owner (ell := ell) (k := k) (Γ := Λ.X))
    {X Y : SepFinType k} (f : X ⟶ Y) :
    ConstantModelConstructibleFiniteTor Λ.X X.obj.left ⥤
      ConstantModelConstructibleFiniteTor Λ.X Y.obj.left :=
  ObjectProperty.lift _
    (inclusion Λ X.obj.left ⋙
      rightDerivedLowerShriekOfCompactification Λ.X (compactificationOverField f.hom))
    (fun K ↦ (preserves H f (compactificationOverField f.hom)).2 K.obj K.property)

/-- Derived pullback restricted by the dependency's preservation assertion. The map is a
morphism in `SepFinType k`; its underlying scheme map is `v.hom.left`.
Source: composition theorem, U and V (blueprint: def-pur-strict-integral-exchange-data). -/
def pull (H : Owner (ell := ell) (k := k) (Γ := Λ.X))
    (X Y : SepFinType k) (v : X ⟶ Y) :
    ConstantModelConstructibleFiniteTor Λ.X Y.obj.left ⥤
      ConstantModelConstructibleFiniteTor Λ.X X.obj.left :=
  ObjectProperty.lift _
    (inclusion Λ Y.obj.left ⋙
      moduleObjectDerivedPullback Λ.X v.hom.left)
    (fun K ↦ (pullPreserves H X Y v).2 K.obj K.property)

/-- Alpha is the restriction of exactly the normalized dependency compositor.
Source: first displayed comparison (blueprint: def-pur-strict-integral-exchange-data). -/
def composition (H : Owner (ell := ell) (k := k) (Γ := Λ.X))
    {X Y Z : SepFinType k} (f : X ⟶ Y) (g : Y ⟶ Z) :
    lower H f ⋙ lower H g ≅ lower H (f ≫ g) :=
  Functor.fullyFaithfulCancelRight (inclusion Λ Z.obj.left)
    (Functor.isoWhiskerLeft (toLocalizing Λ X.obj.left)
      (modelComposition H f g (compactificationOverField f.hom)
        (compactificationOverField g.hom) (compactificationOverField (f ≫ g).hom)))

/-- B is the restriction of exactly the normalized dependency exchange. Cartesian squares
are given by IsPullback, so this includes all their realizations, not only a chosen pullback.
Source: compact-support exchange (blueprint: def-pur-strict-integral-exchange-data). -/
def exchange (H : Owner (ell := ell) (k := k) (Γ := Λ.X))
    {X Y X' Y' : SepFinType k} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {u : X' ⟶ X} {v : Y' ⟶ Y}
    (sq : IsPullback u.hom.left f'.hom.left f.hom.left v.hom.left) :
    lower H f ⋙ pull H Y' Y v ≅ pull H X' X u ⋙ lower H f' :=
  Functor.fullyFaithfulCancelRight (inclusion Λ Y'.obj.left)
    (Functor.isoWhiskerLeft (toLocalizing Λ X.obj.left)
      (modelExchange H (X := X) (Y := Y) (X' := X') (Y' := Y')
        (f := f) (f' := f') sq (compactificationOverField f.hom)
        (compactificationOverField f'.hom)))

/-- The inherited identity pullback comparison, retaining its canonical unit normalization.
Source: identity square (blueprint: def-pur-strict-integral-exchange-data). -/
def pullId (H : Owner (ell := ell) (k := k) (Γ := Λ.X)) (X : SepFinType k) :
    pull H X X (𝟙 X) ≅ 𝟭 _ :=
  Functor.fullyFaithfulCancelRight (inclusion Λ X.obj.left)
    (Functor.isoWhiskerLeft (inclusion Λ X.obj.left) (leftDerivedUpperStarId Λ.X X.obj.left))

/-- The canonical inherited pullback compositor used in successive base change.
Source: vertical pasting (blueprint: def-pur-strict-integral-exchange-data). -/
def pullComp (H : Owner (ell := ell) (k := k) (Γ := Λ.X)) (X Y Z : SepFinType k)
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    pull H X Z (f ≫ g) ≅ pull H Y Z g ⋙ pull H X Y f :=
  Functor.fullyFaithfulCancelRight (inclusion Λ X.obj.left)
    (Functor.isoWhiskerLeft (inclusion Λ Z.obj.left)
      (leftDerivedUpperStarComp Λ.X f.hom.left g.hom.left))

/-- The conjugate of alpha under the specified composite adjunction and the gf adjunction.
The right adjoint to F_f then F_g is E_g then E_f in Lean's functor order.
Source: first counit identity (blueprint: def-pur-strict-integral-exchange-data). -/
def conjugate {X Y Z : SepFinType k} (H : Owner (ell := ell) (k := k) (Γ := Λ.X))
    (f : X ⟶ Y) (g : Y ⟶ Z)
    {Ef : ConstantModelConstructibleFiniteTor Λ.X Y.obj.left ⥤
      ConstantModelConstructibleFiniteTor Λ.X X.obj.left}
    {Eg : ConstantModelConstructibleFiniteTor Λ.X Z.obj.left ⥤
      ConstantModelConstructibleFiniteTor Λ.X Y.obj.left}
    {Egf : ConstantModelConstructibleFiniteTor Λ.X Z.obj.left ⥤
      ConstantModelConstructibleFiniteTor Λ.X X.obj.left}
    (af : lower H f ⊣ Ef) (ag : lower H g ⊣ Eg) (agf : lower H (f ≫ g) ⊣ Egf) :
    Egf ≅ Eg ⋙ Ef :=
  conjugateIsoEquiv agf (af.comp ag) (composition H f g)

/-- The transpose of inverse B followed by the pulled-back counit. This construction is
made for every square; invertibility is a separate geometric assertion below.
Source: second counit identity (blueprint: def-pur-strict-integral-exchange-data). -/
def exceptional {X Y X' Y' : SepFinType k}
    (H : Owner (ell := ell) (k := k) (Γ := Λ.X)) {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {u : X' ⟶ X} {v : Y' ⟶ Y}
    (sq : IsPullback u.hom.left f'.hom.left f.hom.left v.hom.left)
    {Ef : ConstantModelConstructibleFiniteTor Λ.X Y.obj.left ⥤
      ConstantModelConstructibleFiniteTor Λ.X X.obj.left}
    {Ef' : ConstantModelConstructibleFiniteTor Λ.X Y'.obj.left ⥤
      ConstantModelConstructibleFiniteTor Λ.X X'.obj.left}
    (af : lower H f ⊣ Ef) (af' : lower H f' ⊣ Ef') :
    Ef ⋙ pull H X' X u ⟶ pull H Y' Y v ⋙ Ef' :=
  (mateEquiv af af' (TwoSquare.mk _ _ _ _ (exchange H sq).inv)).natTrans

variable {D : WeilConjectures.FiniteFieldDatum.{u}} {ell : ℕ} [Fact ell.Prime]

/-- Stage-2 existence statement for the strict integral exchange package.
Source: current blueprint (blueprint: def-pur-strict-integral-exchange-data).

Proof plan from the corrected node:

1. By [sk-thm-existence] the stated compact-support functors preserve the constructible finite-Tor
   categories and have the specified right adjoints there. Apply [sk-thm-sf-comp-composition] on
   these full subcategories. It supplies exactly the compactification-independent, associative and
   unital $\alpha$, the natural compactification-independent isomorphism $B$, and its
   successive-base-change pasting equation. This applies to the k-morphism base-change squares in
   the corrected statement. Thus these structural maps are the specified maps, rather than arbitrary
   isomorphisms between their endpoints.
2. Equip $F_gF_f\dashv E_fE_g$ with the composite adjunction [def-weil-pbc-composite-adjunction].
   Its counit at $K$ is $\varepsilon_{g,K}\circ F_g(\varepsilon_{f,E_gK})$. Conjugate
   $\alpha:F_gF_f\to F_{gf}$ under this adjunction and $F_{gf}\dashv E_{gf}$
   [def-weil-pbc-adjunction-conjugate]; conjugation sends isomorphisms to isomorphisms, so it gives
   $c:E_{gf}\xrightarrow{\sim}E_fE_g$. The mate-counit identity [lem-amb-mate-unit-counit], with
   identity side functors, reads $\varepsilon_{gf}\circ\alpha_{E_{gf}}=\varepsilon_{g}\circ
   F_g(\varepsilon_f)\circ F_gF_f(c)$, which is the first displayed equation. The identity and
   composition properties of conjugation and [lem-weil-pbc-mate-pasting](2)-(4) identify its unit
   and associativity constraints with those of $\alpha$.
3. Compute $B$ on a compactification $f=pj$. By [def-sfb-compact-support-base-change-maps] it is
   $Rp'_*o_v\circ\operatorname{Ex}_{v,p}(j_!-)$, where $o_v:\bar v^*j_!\xrightarrow{\sim}j'_!u^*$ is
   inverse to the canonical open-adjunction mate. For two successive base maps $v,w$, proper
   exchange obeys $\operatorname{Ex}_{vw,p}=(\operatorname{Ex}_{w,p'}\bar
   v^*)\circ(w^*\operatorname{Ex}_{v,p})$ by [lem-weil-pbc-mate-pasting](1), applied to the
   canonical inverse-image square comparisons. Those comparisons use
   [prop-sfb-module-left-derived-upper-star-comp]. The same mate-pasting identity for the open
   adjunctions gives $o_{vw}=(o_wu^*)\circ(\bar w^*o_v)$;
   [lem-sfb-internal-module-operations-transport] identifies these with the specified internal open
   maps. The identity case follows from part (4) of the mate-pasting lemma. These arguments take
   place for ordinary module derived operations, and require no flatness or finite-coefficient
   transport.
4. Substitute the two identities of Step 3 into the proper/open formula for $B_{vw}$. Naturality of
   proper exchange with respect to $o_v$ moves the middle open comparison past the second proper
   exchange. The result is $B_{vw}=(B_wu^*)\circ(w^*B_v)$, with the pullback compositors inserted,
   and $B_{\mathrm{id}}=1$. Independence in [sk-thm-sf-comp-composition] identifies this calculation
   on the pulled-back compactifications with the original chosen ones. For the mixed
   composition/exchange equation, choose compactification triangles for two composable arrows and
   pull back the whole diagram. A pullback of a dense open need not be scheme-theoretically dense:
   before applying composition normalization, use [det-nagata-refinement-common-dense] on the
   pulled-back compactifications, then [lem-sfb-compact-support-refinement-base-change] and the
   owner refinement equations to pass to the common dense models. No density is inferred from base
   change. Expand $\alpha$ using its normalized proper/open interchange and $B$ using its normalized
   proper/open formula. The two routes are the same iterated composite: the proper faces commute by
   mate pasting for inverse-image comparisons, the open faces commute by open-adjunction mate
   pasting, and the interchange face commutes because both its restrictions are the specified
   identity under the canonical pullback compositors. Insert the proper and open compositors and
   compare arbitrary compactifications by the owner independence clauses. This derives the mixed law
   rather than attributing it to a clause absent from the current owner theorem.
5. Apply [lem-amb-mate-unit-counit] to $L_1=F_f$, $L_2=F_{f'}$, $G=U$, $H=V$, and
   $\alpha=B^{-1}:F_{f'}U\to VF_f$. Its mate is precisely the $e$ defined in the statement.
   Consequently $\varepsilon_{f',VK}\circ F_{f'}(e_K)=V(\varepsilon_{f,K})\circ B^{-1}_{E_fK}$.
   Compose on the right with $B_{E_fK}$ to obtain the second displayed counit equation. This
   equality does not assert that a mate of an arbitrary isomorphism is invertible. Naturality
   follows from the mate construction; [lem-weil-pbc-mate-pasting](1)-(4) gives its identity and
   successive-square laws from those of $B^{-1}$.
6. suppose first that $f$ is smooth of pure relative dimension $d$. Every $\Lambda$ of the statement
   is admissible ($\mathcal O_E/\pi_E^n$ is a finite ring killed by a power of $\ell$). The
   comparison on targets in [sk-prop-sp-purity-bc] is specified there as the transpose of the
   pulled-back counit composed with the inverse of compact-support base change, i.e. exactly our $e$
   (with $B$ the canonical exchange of [sk-thm-sf-comp-composition]). Its displayed equation
   therefore reads $e_K\circ u^*\gamma_{f,\Lambda}(K)=\gamma_{f',\Lambda}(v^*K)\circ s_K$, where
   $s_K:u^*f^*K(d)[2d]\xrightarrow{\sim}f'^*v^*K(d)[2d]$ is the canonical pullback-compositor and
   twist/shift identification of its sources. We do not use the word "isomorphism" attached to $e$
   there, which that statement takes from a finite-torsion-coefficient source: by
   [sk-thm-purity-transport], $\gamma_{f,\Lambda}(K)$ and $\gamma_{f',\Lambda}(v^*K)$ are
   isomorphisms for every admissible $\Lambda$, and $s_K$ is invertible, so
   $e_K=\gamma_{f',\Lambda}(v^*K)\circ s_K\circ(u^*\gamma_{f,\Lambda}(K))^{-1}$ is an isomorphism.
   In particular this applies to every open immersion $j$ (dimension zero). For general smooth $f$,
   [sbc-lem-smooth-relative-dimension-locally-constant] covers $X$ by open loci $X_d$ on which
   $f_d=f|_{X_d}$ has pure relative dimension $d$. These loci are finite-type schemes: the standing
   finite-type schemes are Noetherian by [lem-weil-pbc-finite-type-over-noetherian] and their open
   subschemes are Noetherian, hence quasi-compact, by
   [lem-weil-pbc-noetherian-open-subscheme-noetherian]. Let $j_d:X_d\hookrightarrow X$, and let
   $j'_d$ be its base change. Conjugating $F_fF_{j_d}\cong F_{f_d}$ identifies $E_{f_d}$ with
   $E_{j_d}E_f$, and similarly after base change (Step 2). By the composition/exchange equation
   derived in Step 4 for the stacked squares of $j_d$ and $f$, $B_{f_d}$ is $B_f$ pasted with
   $B_{j_d}$ through $\alpha_{f,j_d}$ and $\alpha_{f',j'_d}$; mate pasting (Step 5) therefore
   identifies $e_{f_d}$ with $E_{j'_d}(e_f)\circ e_{j_d,E_f}$. Both $e_{f_d}$ and $e_{j_d,E_f}$ are
   invertible by the pure-dimensional case, so $E_{j'_d}(e_f)$ is invertible. Purity in dimension
   zero [sk-thm-purity-transport] identifies $E_{j'_d}$ with ordinary open restriction. Apply these
   exact restrictions to every cohomology sheaf of the cone of $e_f$; all restrictions are zero. The
   cover-local isomorphism criterion [lem-sfb-sheaf-cover-local-isomorphism], applied to
   $0\to\mathcal H^r(\operatorname{Cone}(e_f))$, gives zero cohomology for every $r$. Thus $e_f$ is
   invertible also when the relative dimension varies. The empty source gives the zero category and
   the same conclusion.
7. All compactification schemes here are Noetherian by [lem-weil-pbc-finite-type-over-noetherian],
   since they are finite type over a field (a field is Noetherian because its only ideals are zero
   and the whole field). For coefficient change write $h_j:T_{\bar X}j_!\xrightarrow{\sim}j'_!T_X$
   for the coefficient comparison of an open immersion (the prime here denotes the new coefficient
   ring). It is the normalized comparison of [lem-sfb-scalar-six-normalized-immersion], whose
   restriction is inverse $\theta$, i.e. $j_j$ in the statement's notation. The geometric open
   comparison $o_v$ and its new-coefficient version are the normalized open comparisons of
   [def-sfb-compact-support-base-change-maps]. The two routes which exchange scalar change with
   $o_v$, after inserting $h_j,h_{j'}$ and the scalar/pullback $j$'s, are maps between extensions by
   zero from the same pulled-back open. Restriction to that open is faithful by
   [lem-sfb-locally-closed-extension-coherence], transported to internal modules by
   [lem-sfb-internal-module-operations-transport]. Their restrictions agree by
   [lem-sfb-scalar-pullback-square-coherence]: both are the scalar/pullback comparison for the
   composite map from that open. Hence the open coefficient/exchange rectangle commutes. This proves
   the rectangle by faithfulness, without inferring it merely from existence of its four
   isomorphisms.
8. Fix a compactification $f=pj$ and its base change. The ordinary direct-image comparison for $p$
   is the specified unit/pullback/counit composite of [det-prop-scalar-six-direct-image]. The proper
   part of the coefficient/exchange rectangle is exactly
   [lem-sfb-scalar-geometric-exchange-rectangle], applied to $p$ and $j_!K$; that lemma imposes no
   constructibility, properness or flatness assumption for its equality. Replace its $\lambda$ by
   $j^{-1}$: the comparison of [det-prop-scalar-six-pullback](1) is the $\theta$ of
   [lem-sfb-scalar-six-derived-pullback-normalization], whose forward map is the scalar-adjunction
   mate of the restriction/inverse-image identification [def-sfb-scalar-six-coefficient-interfaces],
   and [lem-sfb-kflat-scalar-comparison-normalization] identifies this same mate with the inverse of
   the balanced K-flat comparison $\lambda$. With $\lambda_p=j_p^{-1}$ the rectangle's $\rho_p$ is
   the unit/pullback/counit composite $\gamma_p$ above. Paste this rectangle with the open rectangle
   of Step 7 and apply the proper pushforward. By [det-prop-scalar-six-compact-support], its two
   coefficient sides are exactly $b_f$ and $b_{f'}$; by [def-sfb-compact-support-base-change-maps],
   its two exchange sides are exactly $B$ and $B'$. Cancelling the adjacent inverse $j$'s therefore
   gives $F'_{f'}(j_u)\circ b_{f',U}\circ T_{Y'}(B)=B'_{T_X}\circ V'(b_f)\circ j_{v,F_f}$, with the
   source $T_{Y'}VF_f$ and target $F'_{f'}U'T_X$. The listed coefficient hypotheses are used only to
   ensure that the $b$'s are isomorphisms on the specified constructible categories.
9. For successive base changes, paste two instances of the equation of Step 8. Replace the
   successive $B$'s by $B_{vw}$ using Step 4, and the successive scalar/pullback comparisons by the
   composite comparison using [det-prop-scalar-six-pullback](1). Cancelling the shared interior
   edges gives exactly the equation for the outer rectangle. For a composite $gf$, paste the
   equations for $g$ and $f$; [det-prop-scalar-six-compact-support] identifies the composite $b$
   with $b_{gf}$, and the mixed law of Step 4 identifies both composite exchange sides through
   $\alpha$. The resulting outer equation is the one for $gf$. Identities are obtained by deleting
   identity edges. Thus these are equations compatible with pasting and $\alpha$, not additional
   choices of comparisons.
-/
theorem purStrictIntegralExchangeData (D : WeilConjectures.FiniteFieldDatum.{u})
    (ell : ℕ) [Fact ell.Prime] (_hne : ell ≠ D.p) :
    ∃ S : Data D ell, Laws S := by
  sorry

end PurStrictIntegralExchangeData
end AlgebraicGeometry.ProEtale.CondensedRing
