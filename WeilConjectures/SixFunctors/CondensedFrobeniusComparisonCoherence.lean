/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.SchemeFrobeniusGeometry
public import WeilConjectures.SixFunctors.ScalarSixPullback
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.AbsoluteFrobenius
public import WeilConjectures.AlgebraicGeometry.IntegralModelsEmbedded
public import WeilConjectures.AlgebraicGeometry.ProfiniteFiniteConstantLocalModel
public import WeilConjectures.AlgebraicGeometry.ExceptionalInverseImageExistence
public import WeilConjectures.AlgebraicGeometry.ProEtaleTateTwistsOfUniverses
public import WeilConjectures.Topology.ProfiniteCondensedRing
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
import WeilConjectures.AlgebraicGeometry.CondensedFrobeniusLinearTrivialization
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.FrobeniusNaturality
import WeilConjectures.Algebra.Homology.RingedKFlatWordComparisonDescent
import WeilConjectures.AlgebraicGeometry.PullbackExtendScalarsComparison
import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import WeilConjectures.AlgebraicGeometry.BaseFieldCohomologicalDimension
import WeilConjectures.AlgebraicGeometry.ProEtaleModuleObjects
import WeilConjectures.SixFunctors.SelectedSchemeGaloisComparison
import WeilConjectures.AlgebraicGeometry.FrobeniusFactorization
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import WeilConjectures.AlgebraicGeometry.CondensedModulePullbackExact
import WeilConjectures.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
import WeilConjectures.AlgebraicGeometry.CohomologicalDimension
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctorialitySupplement
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits

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

/-- The indicated family of four coefficient rings, with positive finite levels.
The last case uses finite-subextension-valued sections, not all continuous functions.
Source: coefficient convention (blueprint: lem-pur-condensed-frobenius-comparison-coherence). -/
def IsPurityFrobeniusCoefficient (ell : ℕ) [Fact ell.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ell) (Λ : ScalarSixRing.{u}) : Prop :=
  ∃ n : ℕ, 1 ≤ n ∧
    (Nonempty (Mon.mk Λ.X ≅ Mon.mk
      (IntegralModelsEmbedded.discreteObj (Padic.coefficientExtensionRing ell E.1 n))) ∨
    Nonempty (Mon.mk Λ.X ≅ Mon.mk (Profinite.padicIntegersRingObj ell E)) ∨
    Nonempty (Mon.mk Λ.X ≅ Mon.mk (Profinite.continuousMapRingObj E)) ∨
    Nonempty (Mon.mk Λ.X ≅ Mon.mk (Profinite.padicAlgClRingObj ell)))

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

/-- The two equations and their simultaneous identity, tower and geometric composition
laws, on the whole unbounded derived categories. The arbitrary-arrow equation includes
all arrows of the full constructible finite-Tor subcategories, in particular purity,
constructible exceptional-adjunction counits and compact-support comparisons when typed.
Source: the two equations and the final coherence paragraph
(blueprint: lem-pur-condensed-frobenius-comparison-coherence). -/
structure CondensedFrobeniusComparisonCoherence (D : WeilConjectures.FiniteFieldDatum.{u})
    (ell : ℕ) [Fact ell.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ell)
    (C : ScalarSixPullbackData.{u}) : Prop where
  /-- Coefficient naturality, with no flatness assumption on a. -/
  scalar : ∀ {Λ Λ' : ScalarSixRing.{u}}
    (_hΛ : IsPurityFrobeniusCoefficient ell E Λ)
    (_hΛ' : IsPurityFrobeniusCoefficient ell E Λ')
    (a : Λ ⟶ Λ') (T₀ : Over (Spec (CommRingCat.of D.k₀)))
    [LocallyOfFiniteType T₀.hom] [QuasiCompact T₀.hom] [IsSeparated T₀.hom]
    (K : frobeniusD D Λ T₀),
    (scalarSixChange a (D.purityFrobeniusFiber T₀).left).map
        ((condensedFrobeniusComparison D Λ T₀).hom.app K) ≫
        (C.theta a (D.purityGaloisMap T₀)).hom.app K =
      (C.theta a (D.puritySchemeFrobenius T₀)).hom.app K ≫
        (condensedFrobeniusComparison D Λ' T₀).hom.app
          ((scalarSixChange a (D.purityFrobeniusFiber T₀).left).obj K)
  /-- Geometric pullback naturality for every finite-type separated model pair. -/
  pullback : ∀ (Λ : ScalarSixRing.{u}) (_hΛ : IsPurityFrobeniusCoefficient ell E Λ)
    {S₀ T₀ : Over (Spec (CommRingCat.of D.k₀))}
    [LocallyOfFiniteType S₀.hom] [QuasiCompact S₀.hom] [IsSeparated S₀.hom]
    [LocallyOfFiniteType T₀.hom] [QuasiCompact T₀.hom] [IsSeparated T₀.hom]
    (h₀ : S₀ ⟶ T₀) (K : frobeniusD D Λ T₀),
    (frobeniusU D Λ h₀).map ((condensedFrobeniusComparison D Λ T₀).hom.app K) ≫
        (condensedGaloisFrobeniusSquare D Λ h₀).hom.app K =
      (condensedSchemeFrobeniusSquare D Λ h₀).hom.app K ≫
        (condensedFrobeniusComparison D Λ S₀).hom.app ((frobeniusU D Λ h₀).obj K)
  /-- The two orders of changing coefficients and pulling back give the same map. -/
  mixed : ∀ {Λ Λ' : ScalarSixRing.{u}}
    (_hΛ : IsPurityFrobeniusCoefficient ell E Λ)
    (_hΛ' : IsPurityFrobeniusCoefficient ell E Λ') (a : Λ ⟶ Λ')
    {S₀ T₀ : Over (Spec (CommRingCat.of D.k₀))}
    [LocallyOfFiniteType S₀.hom] [QuasiCompact S₀.hom] [IsSeparated S₀.hom]
    [LocallyOfFiniteType T₀.hom] [QuasiCompact T₀.hom] [IsSeparated T₀.hom]
    (h₀ : S₀ ⟶ T₀) (K : frobeniusD D Λ T₀),
    (scalarSixChange a (D.purityFrobeniusFiber S₀).left).map
        ((frobeniusU D Λ h₀).map ((condensedFrobeniusComparison D Λ T₀).hom.app K)) ≫
        (scalarSixChange a (D.purityFrobeniusFiber S₀).left).map
          ((condensedGaloisFrobeniusSquare D Λ h₀).hom.app K) ≫
        (C.theta a (D.purityGaloisMap S₀)).hom.app ((frobeniusU D Λ h₀).obj K) ≫
        (frobeniusG D Λ' S₀).map ((C.theta a (D.purityFrobeniusMap h₀)).hom.app K) =
      (C.theta a (D.purityFrobeniusMap h₀)).hom.app ((frobeniusP D Λ T₀).obj K) ≫
        (frobeniusU D Λ' h₀).map
          ((C.theta a (D.puritySchemeFrobenius T₀)).hom.app K) ≫
        (frobeniusU D Λ' h₀).map
          ((condensedFrobeniusComparison D Λ' T₀).hom.app
            ((scalarSixChange a (D.purityFrobeniusFiber T₀).left).obj K)) ≫
        (condensedGaloisFrobeniusSquare D Λ' h₀).hom.app
          ((scalarSixChange a (D.purityFrobeniusFiber T₀).left).obj K)
  /-- Identity coefficient changes use the scalar-unit comparison for both P and G. -/
  scalar_identity : ∀ (Λ : ScalarSixRing.{u})
    (_hΛ : IsPurityFrobeniusCoefficient ell E Λ) (b : Bool)
    (T₀ : Over (Spec (CommRingCat.of D.k₀)))
    [LocallyOfFiniteType T₀.hom] [QuasiCompact T₀.hom] [IsSeparated T₀.hom]
    (K : frobeniusD D Λ T₀),
    (C.theta (𝟙 Λ) (condensedFrobeniusEndomorphism D b T₀)).hom.app K ≫
        (scalarSixPull Λ (condensedFrobeniusEndomorphism D b T₀)).map
          ((condensedFrobeniusScalarId Λ (D.purityFrobeniusFiber T₀).left).hom.app K) =
      (condensedFrobeniusScalarId Λ (D.purityFrobeniusFiber T₀).left).hom.app
        ((scalarSixPull Λ (condensedFrobeniusEndomorphism D b T₀)).obj K)
  /-- The two-step scalar equation agrees with the single equation for b after a. -/
  scalar_tower : ∀ {Λ Λ' Λ'' : ScalarSixRing.{u}}
    (_hΛ : IsPurityFrobeniusCoefficient ell E Λ)
    (_hΛ' : IsPurityFrobeniusCoefficient ell E Λ')
    (_hΛ'' : IsPurityFrobeniusCoefficient ell E Λ'') (a : Λ ⟶ Λ') (b : Λ' ⟶ Λ'')
    (T₀ : Over (Spec (CommRingCat.of D.k₀)))
    [LocallyOfFiniteType T₀.hom] [QuasiCompact T₀.hom] [IsSeparated T₀.hom]
    (K : frobeniusD D Λ T₀),
    (scalarSixChange b (D.purityFrobeniusFiber T₀).left).map
        ((scalarSixChange a (D.purityFrobeniusFiber T₀).left).map
          ((condensedFrobeniusComparison D Λ T₀).hom.app K)) ≫
        (scalarSixChange b (D.purityFrobeniusFiber T₀).left).map
          ((C.theta a (D.purityGaloisMap T₀)).hom.app K) ≫
        (C.theta b (D.purityGaloisMap T₀)).hom.app
          ((scalarSixChange a (D.purityFrobeniusFiber T₀).left).obj K) ≫
        (frobeniusG D Λ'' T₀).map
          ((scalarSixTower a b (D.purityFrobeniusFiber T₀).left).hom.app K) =
      (scalarSixTower a b (D.purityFrobeniusFiber T₀).left).hom.app
          ((frobeniusP D Λ T₀).obj K) ≫
        (C.theta (a ≫ b) (D.puritySchemeFrobenius T₀)).hom.app K ≫
        (condensedFrobeniusComparison D Λ'' T₀).hom.app
          ((scalarSixChange (a ≫ b) (D.purityFrobeniusFiber T₀).left).obj K)
  /-- Identity geometric changes use the pullback unitor for both P and G. -/
  pullback_identity : ∀ (Λ : ScalarSixRing.{u})
    (_hΛ : IsPurityFrobeniusCoefficient ell E Λ) (b : Bool)
    (T₀ : Over (Spec (CommRingCat.of D.k₀)))
    [LocallyOfFiniteType T₀.hom] [QuasiCompact T₀.hom] [IsSeparated T₀.hom]
    (K : frobeniusD D Λ T₀),
    (condensedSelectedFrobeniusSquare D Λ b (𝟙 T₀)).hom.app K ≫
        (scalarSixPull Λ (condensedFrobeniusEndomorphism D b T₀)).map
          ((condensedFrobeniusModelId D Λ T₀).hom.app K) =
      (condensedFrobeniusModelId D Λ T₀).hom.app
        ((scalarSixPull Λ (condensedFrobeniusEndomorphism D b T₀)).obj K)
  /-- For either endomorphism, the square for a composite is the pasted square. -/
  pullback_composition : ∀ (Λ : ScalarSixRing.{u})
    (_hΛ : IsPurityFrobeniusCoefficient ell E Λ) (b : Bool)
    {R₀ S₀ T₀ : Over (Spec (CommRingCat.of D.k₀))}
    [LocallyOfFiniteType R₀.hom] [QuasiCompact R₀.hom] [IsSeparated R₀.hom]
    [LocallyOfFiniteType S₀.hom] [QuasiCompact S₀.hom] [IsSeparated S₀.hom]
    [LocallyOfFiniteType T₀.hom] [QuasiCompact T₀.hom] [IsSeparated T₀.hom]
    (h₀ : R₀ ⟶ S₀) (k₀ : S₀ ⟶ T₀) (K : frobeniusD D Λ T₀),
    (condensedFrobeniusModelComp D Λ h₀ k₀).hom.app
        ((scalarSixPull Λ (condensedFrobeniusEndomorphism D b T₀)).obj K) ≫
        (frobeniusU D Λ h₀).map
          ((condensedSelectedFrobeniusSquare D Λ b k₀).hom.app K) ≫
        (condensedSelectedFrobeniusSquare D Λ b h₀).hom.app ((frobeniusU D Λ k₀).obj K) =
      (condensedSelectedFrobeniusSquare D Λ b (h₀ ≫ k₀)).hom.app K ≫
        (scalarSixPull Λ (condensedFrobeniusEndomorphism D b R₀)).map
          ((condensedFrobeniusModelComp D Λ h₀ k₀).hom.app K)
  /-- Naturality on every ambient arrow, hence on every arrow of the full subcategories. -/
  arrow : ∀ (Λ : ScalarSixRing.{u}) (_hΛ : IsPurityFrobeniusCoefficient ell E Λ)
    (T₀ : Over (Spec (CommRingCat.of D.k₀)))
    [LocallyOfFiniteType T₀.hom] [QuasiCompact T₀.hom] [IsSeparated T₀.hom]
    {K L : frobeniusD D Λ T₀} (v : K ⟶ L),
    (frobeniusP D Λ T₀).map v ≫ (condensedFrobeniusComparison D Λ T₀).hom.app L =
      (condensedFrobeniusComparison D Λ T₀).hom.app K ≫ (frobeniusG D Λ T₀).map v

/-- Canonical scheme/Galois comparison over the indicated condensed coefficients,
with simultaneous coefficient and geometric naturality on the entire derived category.
Source: latest blueprint, prop-pur-weil-equivariance-scheme-frobenius.proof.md,
canonical comparison paragraph; Stacks Tag 0F6W
(blueprint: lem-pur-condensed-frobenius-comparison-coherence).

Proof:
1. Factor Phi as absolute q-power Frobenius followed by geometric Galois Frobenius.
   The relative Frobenius on each weakly etale test object is the specified isomorphism
   (0F6W). condensed-frobenius-linear-trivialization identifies its coefficient component
   with the canonical pullback-from-point map. Thus kappa is exactly the defined composite.
2. Normalize the module compositor by the balanced tensor map
   c tensor (b tensor m) to c alpha(b) tensor m. Its transpose is the section-normalized
   pushforward compositor. Three-arrow associativity and the unit identities hold on pure
   tensors and hence after sheafification. ringed-kflat-word-comparison-descent descends
   each finite pasting, with composition and whiskering, to the whole unbounded category.
3. For scalar change the two maps of the absolute trivialization on a local pure tensor
   are s tensor x to s tensor tau(x). pullback-extend-scalars-comparison supplies exactly
   this balancing. Use a common flat-term K-flat resolution, without flatness of the
   coefficient map, to obtain scalar compatibility of tau.
4. Scalar-six-pullback (1) gives the factorization compositor's scalar compatibility.
   Substitute step 3 and move the Galois comparison past tau by naturality. This is scalar.
5. Absolute Frobenius pullback naturality is the upstream FrobeniusNaturality theorem.
   Expand both commuting-square comparisons into compositors, apply associativity twice,
   and cancel inverse pairs. Substitute tau naturality to obtain pullback. Only scheme
   commutativity enters this calculation, not Cartesianity of the Phi square.
6. In the finite diagram containing h, Frobenius and the coefficient changes, both mixed
   paths send a tensor to s tensor tau(x). For a coefficient tower both send it to
   s'' t'(s') tensor tau(x); the coefficient unit sends s tensor x to sx. Descend these
   simultaneous identities by the same K-flat-word theorem. For successive h, expansion
   into compositors and the three-arrow law give the pasted square; units give identity
   squares. Naturality of the defined natural isomorphism is arrow. All these equations
   restrict to the full constructible finite-Tor subcategories.
7. The exceptional-adjunction context uses the constructible right adjoints of
   sk-thm-existence. The algebraic closure of a finite field has ell-cohomological
   dimension zero by sk-lem-base-field-cd, so its finite-cd hypothesis holds. Purity,
   counit and compact-support arrows are instances of arrow whenever their source and
   target lie in these categories; no exceptional right adjoint on the entire ambient
   category is asserted or used.
-/
theorem condensedFrobeniusComparison_coherence (D : WeilConjectures.FiniteFieldDatum.{u})
    (ell : ℕ) [Fact ell.Prime] (_hDifferent : ell ≠ D.p)
    (E : PadicAlgCl.FiniteIntermediateField ell)
    (C : ScalarSixPullbackData.{u}) :
    CondensedFrobeniusComparisonCoherence D ell E C := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
