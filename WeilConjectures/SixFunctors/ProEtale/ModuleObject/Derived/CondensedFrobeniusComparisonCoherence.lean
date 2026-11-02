/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.FiniteFieldDatum.SchemeFrobeniusGeometry
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixDefinitions
public import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficientTwistsSupplement
public import WeilConjectures.AlgebraicGeometry.InternalModuleOperations.InternalModuleOperationsTransportSupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixDerivedPullbackNormalization
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixImmersionComparison
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.AbsoluteFrobenius
public import WeilConjectures.AlgebraicGeometry.IntegralModelsEmbedded.IntegralModelsEmbedded
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.ProfiniteFiniteConstantLocalModel
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ExceptionalInverseImageExistence
public import WeilConjectures.AlgebraicGeometry.ProEtale.Tate.ProEtaleTateTwists
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ProfiniteCondensedRing
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
import WeilConjectures.AlgebraicGeometry.SixFunctors.AbsoluteFrobeniusSite
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.AbsoluteFrobenius
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperStarCoherence
import Mathlib.CategoryTheory.Sites.Monoidal
import Mathlib.CategoryTheory.Skeletal
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import WeilConjectures.CategoryTheory.SiteCoveringAxioms
import Mathlib.CategoryTheory.Monoidal.Braided.Transport
import WeilConjectures.WeilObject.Sheaf.StalkFrobenius
import WeilConjectures.SixFunctors.ProEtale.AbsoluteFrobenius
import Mathlib.AlgebraicGeometry.Scheme
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.AbsoluteFrobeniusNaturality
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.FrobeniusNaturality
import WeilConjectures.CategoryTheory.RingedKFlatWord.RingedKFlatWordComparisonDescent
import WeilConjectures.AlgebraicGeometry.PullbackExtendScalarsComparison
import WeilConjectures.AlgebraicGeometry.Base.BaseFieldCohomologicalDimension
import WeilConjectures.AlgebraicGeometry.ProEtale.Module.ProEtaleModuleObjects
import WeilConjectures.AlgebraicGeometry.Picard.TraceFormulaCoefficientConventions.SelectedSchemeGaloisComparison
import WeilConjectures.SmoothPurity.FiniteFieldDatum.FrobeniusFactorization
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import WeilConjectures.AlgebraicGeometry.Cohomological.CohomologicalDimension
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedPullbackCoherence

/-!
# Condensed coefficient coherence of the canonical Frobenius comparison

Source: latest blueprint, sec-six-functors/sk-thm-sf-package,
prop-pur-weil-equivariance-scheme-frobenius.proof.md, canonical comparisons;
Stacks Tag 0F6W (blueprint: lem-pur-condensed-frobenius-comparison-coherence).
All functors act on ordinary unbounded derived internal modules. Exact pullback
is represented termwise, using the canonical identification with total derivation.

## Main definitions

- `IsPurityFrobeniusCoefficient`: the four coefficient cases for the fixed E.
- `condensedFrobeniusComparison`: the specified factorization/trivialization composite.
- `condensedFrobeniusSquare`: the canonical comparison for a commuting scheme square.
- Scalar and model identity/composition helpers fix all comparison normalizations.

## Main statements

- `CondensedFrobeniusComparisonCoherence`: both equations and their simultaneous laws.
- `condensedFrobeniusComparison_coherence`: these laws for the specified comparison.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

attribute [local irreducible] DerivedCategory CategoryTheory.Functor.mapDerivedCategory
  HasDerivedCategory.ofHasKInjectiveResolutions HasDerivedCategory.standard

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- The canonical relative-Frobenius module trivialization, localized termwise.
Its coefficient map is the pullback-from-point comparison by FrobeniusPoint.
Source: absolute-Frobenius normalization, Stacks 0F6W
(blueprint: lem-pur-condensed-frobenius-comparison-coherence). -/
def condensedAbsoluteFrobeniusTrivialization (D : WeilConjectures.FiniteFieldDatum.{u})
    (Λ : ScalarSixRing.{u}) (T₀ : Over (Spec (CommRingCat.of D.k₀))) :
    scalarSixPull Λ (D.purityAbsoluteFrobenius T₀) ≅ 𝟭 _ :=
  Functor.mapDerivedCategoryNatIso
    (G := 𝟭 (ModuleRingedComparison.internalModules Λ.X (D.purityFrobeniusFiber T₀).left))
    (upperStarIterateFrobeniusIso Λ.X D.prime
      (D.model_characteristic (pullback.fst T₀.hom
        (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) ≫ T₀.hom)) D.a) ≪≫
    Functor.mapDerivedCategoryIdIso _

/-- The specified kappa: factor Phi as absolute Frobenius followed by geometric
Galois, apply the canonical module compositor, then the canonical trivialization.
Source: specified comparison construction, Stacks 0F6W
(blueprint: lem-pur-condensed-frobenius-comparison-coherence). -/
def condensedFrobeniusComparison (D : WeilConjectures.FiniteFieldDatum.{u})
    (Λ : ScalarSixRing.{u}) (T₀ : Over (Spec (CommRingCat.of D.k₀))) :
    scalarSixPull Λ (D.puritySchemeFrobenius T₀) ≅
      scalarSixPull Λ (D.purityGaloisMap T₀) :=
  eqToIso (congrArg (scalarSixPull Λ) ((D.purityFrobenius_geometry).1 T₀)) ≪≫
    scalarSixPullComp Λ (D.purityAbsoluteFrobenius T₀) (D.purityGaloisMap T₀) ≪≫
    Functor.isoWhiskerLeft (scalarSixPull Λ (D.purityGaloisMap T₀))
      (condensedAbsoluteFrobeniusTrivialization D Λ T₀) ≪≫ Functor.rightUnitor _

/-- Commuting-square pullback comparison from inverse compositor, scheme equality,
and compositor. Only commutativity is used.
Source: canonical square comparisons
(blueprint: lem-pur-condensed-frobenius-comparison-coherence). -/
def condensedFrobeniusSquare (Λ : ScalarSixRing.{u}) {S T : Scheme.{u}}
    (h : S ⟶ T) (rS : S ⟶ S) (rT : T ⟶ T) (w : h ≫ rT = rS ≫ h) :
    scalarSixPull Λ rT ⋙ scalarSixPull Λ h ≅
      scalarSixPull Λ h ⋙ scalarSixPull Λ rS :=
  (scalarSixPullComp Λ h rT).symm ≪≫
    eqToIso (congrArg (scalarSixPull Λ) w) ≪≫ scalarSixPullComp Λ rS h

/-- The canonical scheme Frobenius square, without a Cartesian assumption.
Source: the second commuting square
(blueprint: lem-pur-condensed-frobenius-comparison-coherence). -/
def condensedSchemeFrobeniusSquare (D : WeilConjectures.FiniteFieldDatum.{u})
    (Λ : ScalarSixRing.{u}) {S₀ T₀ : Over (Spec (CommRingCat.of D.k₀))} (h₀ : S₀ ⟶ T₀) :=
  condensedFrobeniusSquare Λ (D.purityFrobeniusMap h₀)
    (D.puritySchemeFrobenius S₀) (D.puritySchemeFrobenius T₀)
    (((D.purityFrobenius_geometry).2 h₀).1)

/-- The canonical geometric Galois commuting-square pullback comparison.
Source: the first commuting square
(blueprint: lem-pur-condensed-frobenius-comparison-coherence). -/
def condensedGaloisFrobeniusSquare (D : WeilConjectures.FiniteFieldDatum.{u})
    (Λ : ScalarSixRing.{u}) {S₀ T₀ : Over (Spec (CommRingCat.of D.k₀))} (h₀ : S₀ ⟶ T₀) :=
  condensedFrobeniusSquare Λ (D.purityFrobeniusMap h₀)
    (D.purityGaloisMap S₀) (D.purityGaloisMap T₀)
    (((D.purityFrobenius_geometry).2 h₀).2)

/-- The identity coefficient change, normalized by identity restriction of scalars.
Source: identity changes
(blueprint: lem-pur-condensed-frobenius-comparison-coherence). -/
def condensedFrobeniusScalarId (Λ : ScalarSixRing.{u}) (X : Scheme.{u}) :
    scalarSixChange (𝟙 Λ) X ≅ 𝟭 _ :=
  (conjugateIsoEquiv (Adjunction.id (C := DerivedCategory
      (ModuleRingedComparison.internalModules Λ.X X)))
    (Mod.derivedExtendMapDerivedCategoryAdjunction
      (coefficientMap (Λ := Λ.X) (Λ' := Λ.X) (𝟙 Λ.X) X))).symm
    (Functor.mapDerivedCategoryNatIso (Mod.comapCongr (coefficientMap_id (Λ := Λ.X) X)) ≪≫
      Functor.mapDerivedCategoryNatIso (Mod.comapId (condensedRingObj Λ.X X)) ≪≫
        Functor.mapDerivedCategoryIdIso _).symm

/-- A selector for the two specified scheme endomorphisms: true is Galois,
false is scheme Frobenius. Source: both commuting squares
(blueprint: lem-pur-condensed-frobenius-comparison-coherence). -/
def condensedFrobeniusEndomorphism (D : WeilConjectures.FiniteFieldDatum.{u})
    (b : Bool) (T₀ : Over (Spec (CommRingCat.of D.k₀))) :
    (D.purityFrobeniusFiber T₀).left ⟶ (D.purityFrobeniusFiber T₀).left :=
  if b then D.purityGaloisMap T₀ else D.puritySchemeFrobenius T₀

/-- The corresponding canonical commuting-square comparison.
Source: both commuting squares
(blueprint: lem-pur-condensed-frobenius-comparison-coherence). -/
def condensedSelectedFrobeniusSquare (D : WeilConjectures.FiniteFieldDatum.{u})
    (Λ : ScalarSixRing.{u}) (b : Bool)
    {S₀ T₀ : Over (Spec (CommRingCat.of D.k₀))} (h₀ : S₀ ⟶ T₀) :
    scalarSixPull Λ (condensedFrobeniusEndomorphism D b T₀) ⋙
        scalarSixPull Λ (D.purityFrobeniusMap h₀) ≅
      scalarSixPull Λ (D.purityFrobeniusMap h₀) ⋙
        scalarSixPull Λ (condensedFrobeniusEndomorphism D b S₀) :=
  match b with
  | true => condensedGaloisFrobeniusSquare D Λ h₀
  | false => condensedSchemeFrobeniusSquare D Λ h₀

/-- The identity model pullback comparison, using the base-change functor's map_id.
Source: identity geometric changes
(blueprint: lem-pur-condensed-frobenius-comparison-coherence). -/
def condensedFrobeniusModelId (D : WeilConjectures.FiniteFieldDatum.{u})
    (Λ : ScalarSixRing.{u}) (T₀ : Over (Spec (CommRingCat.of D.k₀))) :
    scalarSixPull Λ (D.purityFrobeniusMap (𝟙 T₀)) ≅ 𝟭 _ :=
  eqToIso (congrArg (scalarSixPull Λ)
    (((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))) ⋙
      Over.forget _).map_id T₀)) ≪≫
    Functor.mapDerivedCategoryNatIso (upperStarId Λ.X _) ≪≫
      Functor.mapDerivedCategoryIdIso _

/-- The canonical compositor for successive geometric model changes.
Source: composition of h
(blueprint: lem-pur-condensed-frobenius-comparison-coherence). -/
def condensedFrobeniusModelComp (D : WeilConjectures.FiniteFieldDatum.{u})
    (Λ : ScalarSixRing.{u}) {R₀ S₀ T₀ : Over (Spec (CommRingCat.of D.k₀))}
    (h₀ : R₀ ⟶ S₀) (k₀ : S₀ ⟶ T₀) :
    scalarSixPull Λ (D.purityFrobeniusMap (h₀ ≫ k₀)) ≅
      scalarSixPull Λ (D.purityFrobeniusMap k₀) ⋙
        scalarSixPull Λ (D.purityFrobeniusMap h₀) :=
  eqToIso (congrArg (scalarSixPull Λ)
    (((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))) ⋙
      Over.forget _).map_comp h₀ k₀)) ≪≫
    scalarSixPullComp Λ (D.purityFrobeniusMap h₀) (D.purityFrobeniusMap k₀)

/-- Ambient unbounded derived category, with the actual pulled-back coefficient ring.
Source: the ambient categories
(blueprint: lem-pur-condensed-frobenius-comparison-coherence). -/
abbrev frobeniusD (D : WeilConjectures.FiniteFieldDatum.{u}) (Λ : ScalarSixRing.{u})
    (T₀ : Over (Spec (CommRingCat.of D.k₀))) :=
  DerivedCategory (ModuleRingedComparison.internalModules Λ.X (D.purityFrobeniusFiber T₀).left)

/-- P is exact scheme-Frobenius pullback applied termwise.
Source: definition of P (blueprint: lem-pur-condensed-frobenius-comparison-coherence). -/
abbrev frobeniusP (D : WeilConjectures.FiniteFieldDatum.{u}) (Λ : ScalarSixRing.{u})
    (T₀ : Over (Spec (CommRingCat.of D.k₀))) :=
  scalarSixPull Λ (D.puritySchemeFrobenius T₀)

/-- G is exact geometric-Galois pullback applied termwise.
Source: definition of G (blueprint: lem-pur-condensed-frobenius-comparison-coherence). -/
abbrev frobeniusG (D : WeilConjectures.FiniteFieldDatum.{u}) (Λ : ScalarSixRing.{u})
    (T₀ : Over (Spec (CommRingCat.of D.k₀))) :=
  scalarSixPull Λ (D.purityGaloisMap T₀)

/-- U is exact pullback along the geometric base change of a model morphism.
Source: definition of Lh* (blueprint: lem-pur-condensed-frobenius-comparison-coherence). -/
abbrev frobeniusU (D : WeilConjectures.FiniteFieldDatum.{u}) (Λ : ScalarSixRing.{u})
    {S₀ T₀ : Over (Spec (CommRingCat.of D.k₀))} (h₀ : S₀ ⟶ T₀) :=
  scalarSixPull Λ (D.purityFrobeniusMap h₀)

end AlgebraicGeometry.ProEtale.CondensedRing

namespace AlgebraicGeometry.ProEtale.CondensedRing

private theorem towerCalculation {A B H : Type*}
    [Category A] [Category B] [Category H]
    (T : A ⥤ B) (U : B ⥤ H) (V : A ⥤ H) (τ : T ⋙ U ⟶ V)
    {P G : A} (κ : P ⟶ G) {x y z w : H}
    (a : U.obj (T.obj G) ⟶ x) (b : x ⟶ y) (c : y ⟶ z)
    (q : V.obj G ⟶ z) (r : V.obj P ⟶ w) (t : w ⟶ z)
    (ht : τ.app G ≫ q = a ≫ b ≫ c) (hk : V.map κ ≫ q = r ≫ t) :
    U.map (T.map κ) ≫ a ≫ b ≫ c = τ.app P ≫ r ≫ t := by
  rw [← ht]
  exact (τ.naturality_assoc κ q).trans (by rw [hk])

end AlgebraicGeometry.ProEtale.CondensedRing
