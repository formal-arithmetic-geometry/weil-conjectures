/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Cohomological.CohomologicalSmoothnessFiniteComparison
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarIdCoherence
public import WeilConjectures.Compactification.BaseChange
public import WeilConjectures.SmoothPurity.PurityConventions.PurityConventions
public import WeilConjectures.AlgebraicGeometry.Compact.CompactSupportExchangeTransport
public import WeilConjectures.AlgebraicGeometry.ProEtale.Fixed.ProEtaleFixedModuleConstructible
public import WeilConjectures.CategoryTheory.Ringed.RingedProEtaleTorAmplitudeOfUniverses
public import WeilConjectures.CategoryTheory.DerivedCategory.TorAmplitude
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Tensor
public import Mathlib.Data.ZMod.Basic
import WeilConjectures.AlgebraicGeometry.Morphisms.RegularImmersion
import WeilConjectures.SixFunctors.Etale.Derived.SmoothDuality.SmoothBaseChange
import Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import WeilConjectures.AlgebraicGeometry.ProEtaleLisseFiniteModelsFromLisse
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import WeilConjectures.AlgebraicGeometry.ProEtaleFixedModuleLocalConstancy
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleLocallyConstantSheaf
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
import Mathlib.Algebra.Category.ModuleCat.AB
import WeilConjectures.AlgebraicGeometry.ProEtaleGeometricStalk
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.Ring.Colimits
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Algebra.Category.ModuleCat.Presheaf.ColimitFunctor
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
import WeilConjectures.AlgebraicGeometry.ProEtaleFiniteModelStalks
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import WeilConjectures.Mathlib.CategoryTheory.Sites.Point.ConstantSheaf
import Mathlib.CategoryTheory.Sites.Point.Over
import WeilConjectures.AlgebraicGeometry.ProEtaleFiniteModelLocalConstancy
import WeilConjectures.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.CategoryTheory.Sites.Over
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.CategoryTheory.Sites.CoverLifting
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafEquivalence
import Mathlib.CategoryTheory.Functor.TypeValuedFlat
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Perfect
import WeilConjectures.AlgebraicGeometry.Affine.Linear.AffineLinearExchangeCoherence
import WeilConjectures.AlgebraicGeometry.Derived.DerivedPullbackCompositionMonoidal
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleTorAmplitudePresentations

/-! # The counit-defined diagonal-exchange cube

Source: latest blueprint, sec-smooth-purity/sk-prop-sp-purity-bc,
`sk-prop-sp-purity-bc-factors.proof.md`, Proof (1), expanded six-step DAG interface
(blueprint: lem-sp-diagonal-exchange-cube).

The displayed equations live in the ordinary uncompleted pro-etale module derived
categories. We write them through canonical etale-origin comparison coordinates;
every arrow is the comparison image of the specified counit mate. The equalities
include the pullback compositors and the inverse-mate diagonal restriction.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.Functor

namespace WeilConjectures

attribute [local irreducible] Etale.rightDerivedLowerShriekBaseChangeMap
  Etale.rightDerivedUpperShriekBaseChangeMap Etale.leftDerivedUpperStarComp

open AlgebraicGeometry.Etale CategoryTheory.MonoidalCategory in
open AlgebraicGeometry.Etale CategoryTheory.MonoidalCategory in
open AlgebraicGeometry.Etale in
end WeilConjectures

namespace WeilConjectures

/-- The map on self-products induced by a change of base.
Source: diagonal cube, Proof (1) (blueprint: lem-sp-diagonal-exchange-cube). -/
def diagonalCubeMap {X Y Y' : Scheme.{u}} (f : X ⟶ Y) (v : Y' ⟶ Y) :
    pullback (pullback.snd f v) (pullback.snd f v) ⟶ pullback f f :=
  pullback.map (pullback.snd f v) (pullback.snd f v) f f
    (pullback.fst f v) (pullback.fst f v) v
    (pullback.condition (f := f) (g := v)).symm (pullback.condition (f := f) (g := v)).symm

/-- The two pullbacks associated to equal composite maps, with the specified compositors.
Source: diagonal cube, canonical pullback compositors
(blueprint: lem-sp-diagonal-exchange-cube). -/
def diagonalCubePullbackIso (Λ : Type (u + 1)) [CommRing Λ]
    {A B C D : Scheme.{u}} (a : A ⟶ B) (b : B ⟶ D)
    (c : A ⟶ C) (e : C ⟶ D) (h : a ≫ b = c ≫ e) :
    (Etale.upperStar (ModuleCat.{u + 1} Λ) b).leftDerivedFunctor ⋙
        (Etale.upperStar (ModuleCat.{u + 1} Λ) a).leftDerivedFunctor ≅
      (Etale.upperStar (ModuleCat.{u + 1} Λ) e).leftDerivedFunctor ⋙
        (Etale.upperStar (ModuleCat.{u + 1} Λ) c).leftDerivedFunctor :=
  (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) a b).symm ≪≫
    Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) c e (a ≫ b) h

/-- On the constructible finite-Tor domain, retain an etale antecedent and identify the
specified compact-support exchange with its witnessed proper/open transport, for every
compactification. Source: diagonal cube, etale-origin and exchange-normalization paragraph
(blueprint: lem-sp-diagonal-exchange-cube). -/
def diagonalCubeWitnessed (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X X' Y Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {a : X' ⟶ X} {v : Y' ⟶ Y} (sq : IsPullback a f' f v) : Prop :=
  ∀ K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)),
    (∃ a b : ℤ,
      (∀ i : ℤ, Scheme.IsConstructibleProEtaleFixedModuleSheaf X Λ
        ((DerivedCategory.homologyFunctor _ i).obj K)) ∧
      (∀ i : ℤ, (i < a ∨ b < i) →
        IsZero ((DerivedCategory.homologyFunctor _ i).obj K)) ∧
      Scheme.HasFixedCoefficientProEtaleTorAmplitude X Λ K a b) →
    ∃ L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
      Etale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X L.obj ∧
      ∃ alpha : (ProEtale.comparisonUpperStar
          (ModuleCat.{u + 1} Λ) X).mapDerivedCategory.obj L.obj ≅ K,
        ∀ c : Compactification f,
          IsIso ((ProEtale.rightDerivedLowerShriekOfCompactificationBaseChangeMap
            (ModuleCat.{u + 1} Λ) sq c).app K) ∧
          ProEtale.compactExchangeTransportAtWitness Λ sq c L K alpha =
            (ProEtale.rightDerivedLowerShriekOfCompactificationBaseChangeMap
              (ModuleCat.{u + 1} Λ) sq c).app K

/-- The two equations on the specified mates, read in the canonical etale-origin
coordinates of the ordinary pro-etale derived categories. The four isomorphisms are
required to have exactly the specified counit-mate homomorphisms; they are not supplied
as independent data. Source: diagonal cube, its two displayed equations
(blueprint: lem-sp-diagonal-exchange-cube). -/
def diagonalCubeComparisons (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X Y Y' : Scheme.{u}} (f : X ⟶ Y) (v : Y' ⟶ Y)
    [HasCompactification f] [QuasiCompact f] [IsSeparated f] (d : ℕ) : Prop :=
  ∃ (sq₁ : IsPullback (diagonalCubeMap f v) (pullback.fst (pullback.snd f v) (pullback.snd f v))
        (pullback.fst f f) (pullback.fst f v))
    (sq₂ : IsPullback (diagonalCubeMap f v) (pullback.snd (pullback.snd f v) (pullback.snd f v))
        (pullback.snd f f) (pullback.fst f v))
    (hΔ : (pullback.diagonal (pullback.snd f v)) ≫ (diagonalCubeMap f v) = (pullback.fst f v) ≫
        (pullback.diagonal f)),
    SmoothOfRelativeDimension d (pullback.snd f v) ∧
    SmoothOfRelativeDimension d (pullback.fst f f) ∧
    SmoothOfRelativeDimension d (pullback.snd f f) ∧
    SmoothOfRelativeDimension d (pullback.fst (pullback.snd f v) (pullback.snd f v)) ∧
    SmoothOfRelativeDimension d (pullback.snd (pullback.snd f v) (pullback.snd f v)) ∧
    PurityConventions.IsRegularOfPureCodimension (pullback.diagonal f) d ∧
    PurityConventions.IsRegularOfPureCodimension (pullback.diagonal (pullback.snd f v)) d ∧
    diagonalCubeWitnessed Λ (IsPullback.of_hasPullback f f).flip ∧
    diagonalCubeWitnessed Λ (IsPullback.of_hasPullback (pullback.snd f v) (pullback.snd f v)).flip ∧
    diagonalCubeWitnessed Λ sq₁ ∧
    diagonalCubeWitnessed Λ (IsPullback.of_hasPullback f v) ∧
    ∃ (b : (Etale.upperStar (ModuleCat.{u + 1} Λ) (pullback.snd f f)).leftDerivedFunctor.obj
        (Etale.dualizingComplex Λ f) ≅ (Etale.dualizingComplex Λ (pullback.fst f f)))
      (b' : (Etale.upperStar (ModuleCat.{u + 1} Λ) (pullback.snd (pullback.snd f v) (pullback.snd
        f v))).leftDerivedFunctor.obj (Etale.dualizingComplex Λ (pullback.snd
        f v)) ≅ (Etale.dualizingComplex Λ (pullback.fst (pullback.snd f v)
        (pullback.snd f v))))
      (bp : (Etale.upperStar (ModuleCat.{u + 1} Λ) (diagonalCubeMap f v)).leftDerivedFunctor.obj
        (Etale.dualizingComplex Λ (pullback.fst f f)) ≅
        (Etale.dualizingComplex Λ (pullback.fst (pullback.snd f v)
        (pullback.snd f v))))
      (e : (Etale.upperStar (ModuleCat.{u + 1} Λ) (pullback.fst f v)).leftDerivedFunctor.obj
        (Etale.dualizingComplex Λ f) ≅ (Etale.dualizingComplex Λ (pullback.snd f v))),
      b.hom = Etale.dualizingComplexBaseChangeMap Λ
        (IsPullback.of_hasPullback f f).flip ∧
      b'.hom = Etale.dualizingComplexBaseChangeMap Λ
        (IsPullback.of_hasPullback (pullback.snd f v) (pullback.snd f v)).flip ∧
      bp.hom = Etale.dualizingComplexBaseChangeMap Λ sq₁ ∧
      e.hom = Etale.dualizingComplexBaseChangeMap Λ (IsPullback.of_hasPullback f v) ∧
      (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} Λ) (pullback (pullback.snd f v)
        (pullback.snd f v))).mapDerivedCategory.map
        ((Etale.upperStar (ModuleCat.{u + 1} Λ) (diagonalCubeMap f v)).leftDerivedFunctor.map
        b.hom ≫ bp.hom) =
      (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} Λ) (pullback (pullback.snd f v)
        (pullback.snd f v))).mapDerivedCategory.map
        ((diagonalCubePullbackIso Λ (diagonalCubeMap f v) (pullback.snd f f)
          (pullback.snd (pullback.snd f v) (pullback.snd f v)) (pullback.fst f v) sq₂.w).hom.app
        (Etale.dualizingComplex Λ f) ≫
          (Etale.upperStar (ModuleCat.{u + 1} Λ) (pullback.snd (pullback.snd f v) (pullback.snd f
        v))).leftDerivedFunctor.map e.hom ≫ b'.hom) ∧
      (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} Λ) (pullback f v)).mapDerivedCategory.map
        ((diagonalCubePullbackIso Λ (pullback.fst f v) (pullback.diagonal f)
          (pullback.diagonal (pullback.snd f v)) (diagonalCubeMap f v) hΔ.symm).hom.app
        (Etale.dualizingComplex Λ (pullback.fst f f)) ≫
          (Etale.upperStar (ModuleCat.{u + 1} Λ) (pullback.diagonal (pullback.snd f
        v))).leftDerivedFunctor.map bp.hom ≫
          ((Etale.upperStar (ModuleCat.{u + 1} Λ)
            (pullback.diagonal (pullback.snd f v))).leftDerivedFunctor.mapIso b'.symm ≪≫
            (Etale.leftDerivedUpperStarCompSectionIso (ModuleCat.{u + 1} Λ)
              (pullback.diagonal (pullback.snd f v))
              (pullback.snd (pullback.snd f v) (pullback.snd f v))
              (pullback.diagonal_snd (pullback.snd f v))).app _).hom) =
      (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} Λ) (pullback f v)).mapDerivedCategory.map
        ((Etale.upperStar (ModuleCat.{u + 1} Λ) (pullback.fst f v)).leftDerivedFunctor.map
          ((Etale.upperStar (ModuleCat.{u + 1} Λ)
            (pullback.diagonal f)).leftDerivedFunctor.mapIso b.symm ≪≫
            (Etale.leftDerivedUpperStarCompSectionIso (ModuleCat.{u + 1} Λ)
              (pullback.diagonal f) (pullback.snd f f)
              (pullback.diagonal_snd f)).app _).hom ≫ e.hom)

end WeilConjectures
