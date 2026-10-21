/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NZ
-/
module

public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Mathlib.Algebra.Homology.BifunctorShift
public import Sheaf.Paper.PbcQbarCompletedPullback
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import WeilConjectures.CategoryTheory.Limits.TowerTransitionEndomorphism
public import Mathlib.Algebra.Homology.HomologicalComplex
import Sheaf.Paper.ConstantCompletionEquivalence
import Sheaf.Paper.CartesianCoefficients
import Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Sheaf.Paper.PulledReductionStrictTowerComparison
public import Sheaf.Paper.SfImmersionCompletedPullbackComparison
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
public import Sheaf.CategoryTheory.StrictRoosModel
public import Sheaf.Algebra.Homology.FlatScalarRestrictionKFlat
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
import Sheaf.AlgebraicGeometry.ProEtaleIntegralCoefficientLimit
import Sheaf.Algebra.Homology.RoosConeCalculus
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
import Sheaf.AlgebraicGeometry.CondensedPullbackTensorComparison
import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
import WeilConjectures.Algebra.Homology.RoosComplex
import WeilConjectures.CategoryTheory.RingedSiteGrothendieckAbelian

/-! # Strict Roos normalization of integral pullback

Source: main-20261015, det-lem-int-tensor-pullback, first and comparison paragraphs;
Stacks Tags 099M, 099N and 099I
(blueprint: lem-sfb-integral-pullback-strict-roos-normalization).

The completed ring is presented by its finite projections, using the existing
projection-normalized coefficient isomorphism. The natural-number index n means n+1.
Constant and completed module categories are kept distinct.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
attribute [local irreducible] HasDerivedCategory.standard
  pbcIntegralDatum completedAdicChangeData
namespace WeilConjectures.IntegralPullbackStrictRoos

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The actual small pro-etale site, retaining its distinct object and morphism universes.
Source: main-20261015, det-lem-int-tensor-pullback, strict cochain refinement; Stacks Tags 099M,
099N and 099I
(blueprint: lem-sfb-integral-pullback-strict-roos-normalization). -/
instance (priority := 3000) siteSmall (W : Scheme.{u}) :
    EssentiallySmall.{u + 1} W.ProEt := essentiallySmallSelf.{0} _

/-- The existing uniformizer-adic datum of the finite extension, with its harmless size lift.
Source: main-20261015, det-lem-int-tensor-pullback, strict cochain refinement; Stacks Tags 099M,
099N and 099I
(blueprint: lem-sfb-integral-pullback-strict-roos-normalization). -/
abbrev datum : AdicCoefficientDatum (PbcIntegralRing l E) := pbcIntegralDatum l E
/-- Completed coefficients presented by their canonical finite quotient limit. The existing
ImmersionCompletedPullback.completedRingIso identifies this presentation with the pulled
continuous integral coefficients, preserving every finite projection.
Source: main-20261015, det-lem-int-tensor-pullback, strict cochain refinement; Stacks Tags 099M,
099N and 099I
(blueprint: lem-sfb-integral-pullback-strict-roos-normalization). -/
abbrev R (T : Scheme.{u}) : Sheaf (ProEt.topology T) CommRingCat.{u + 1} :=
  (datum l E).completedRing T
/-- The existing constant coefficient ring sheaf, in the same size convention as R.
Source: main-20261015, det-lem-int-tensor-pullback, strict cochain refinement; Stacks Tags 099M,
099N and 099I
(blueprint: lem-sfb-integral-pullback-strict-roos-normalization). -/
abbrev C (T : Scheme.{u}) : Sheaf (ProEt.topology T) CommRingCat.{u + 1} :=
  exchangeConstantRing T (PbcIntegralRing l E)
/-- The ambient module category over completed coefficients; no completeness is imposed.
Source: main-20261015, det-lem-int-tensor-pullback, strict cochain refinement; Stacks Tags 099M,
099N and 099I
(blueprint: lem-sfb-integral-pullback-strict-roos-normalization). -/
abbrev ModR (T : Scheme.{u}) := reductionModules T (R l E T)
/-- The distinct ambient category of modules over constant coefficients.
Source: main-20261015, det-lem-int-tensor-pullback, strict cochain refinement; Stacks Tags 099M,
099N and 099I
(blueprint: lem-sfb-integral-pullback-strict-roos-normalization). -/
abbrev ModC (T : Scheme.{u}) := reductionModules T (C l E T)
/-- Restriction along the existing constant-function coefficient map.
Source: main-20261015, det-lem-int-tensor-pullback, strict cochain refinement; Stacks Tags 099M,
099N and 099I
(blueprint: lem-sfb-integral-pullback-strict-roos-normalization). -/
abbrev res (T : Scheme.{u}) := PulledReduction.res (datum l E) T
/-- The existing strict completed-coefficient quotient tower, including quotient transitions.
Source: main-20261015, det-lem-int-tensor-pullback, strict cochain refinement; Stacks Tags 099M,
099N and 099I
(blueprint: lem-sfb-integral-pullback-strict-roos-normalization). -/
abbrev redR (T : Scheme.{u}) := completedReductionModuleTowerFunctor T (datum l E)
/-- The existing strict constant-coefficient quotient tower, including quotient transitions.
Source: main-20261015, det-lem-int-tensor-pullback, strict cochain refinement; Stacks Tags 099M,
099N and 099I
(blueprint: lem-sfb-integral-pullback-strict-roos-normalization). -/
abbrev redC (T : Scheme.{u}) := OrderedExchange.reductionModule (datum l E) T

variable {X Y : Scheme.{u}} (g : X ⟶ Y)
/-- The actual ringed-site module inverse image for completed coefficients.
Source: main-20261015, det-lem-int-tensor-pullback, strict cochain refinement; Stacks Tags 099M,
099N and 099I
(blueprint: lem-sfb-integral-pullback-strict-roos-normalization). -/
abbrev pullR := completedModulePullback g (datum l E)
/-- The actual constant-coefficient module inverse image.
Source: main-20261015, det-lem-int-tensor-pullback, strict cochain refinement; Stacks Tags 099M,
099N and 099I
(blueprint: lem-sfb-integral-pullback-strict-roos-normalization). -/
abbrev pullC := PulledReduction.pull (A := PbcIntegralRing l E) g
/-- Levelwise completed-coefficient inverse image.
Source: main-20261015, det-lem-int-tensor-pullback, strict cochain refinement; Stacks Tags 099M,
099N and 099I
(blueprint: lem-sfb-integral-pullback-strict-roos-normalization). -/
abbrev towerPullR := (Functor.whiskeringRight ℕᵒᵖ _ _).obj (pullR l E g)
/-- Levelwise constant-coefficient inverse image.
Source: main-20261015, det-lem-int-tensor-pullback, strict cochain refinement; Stacks Tags 099M,
099N and 099I
(blueprint: lem-sfb-integral-pullback-strict-roos-normalization). -/
abbrev towerPullC := (Functor.whiskeringRight ℕᵒᵖ _ _).obj (pullC l E g)
/-- Levelwise restriction of scalars on strict diagrams.
Source: main-20261015, det-lem-int-tensor-pullback, strict cochain refinement; Stacks Tags 099M,
099N and 099I
(blueprint: lem-sfb-integral-pullback-strict-roos-normalization). -/
abbrev towerRes (T : Scheme.{u}) := (Functor.whiskeringRight ℕᵒᵖ _ _).obj (res l E T)
/-- The pulled quotient tower, with index n denoting the positive quotient n+1.
Source: main-20261015, det-lem-int-tensor-pullback, strict cochain refinement; Stacks Tags 099M,
099N and 099I
(blueprint: lem-sfb-integral-pullback-strict-roos-normalization). -/
abbrev T := redR l E Y ⋙ towerPullR l E g
/-- The quotient tower of the ordinary pulled complex.
Source: main-20261015, det-lem-int-tensor-pullback, strict cochain refinement; Stacks Tags 099M,
099N and 099I
(blueprint: lem-sfb-integral-pullback-strict-roos-normalization). -/
abbrev U := pullR l E g ⋙ redR l E X
/-- The constant-coefficient inverse image of the restricted quotient tower.
Source: main-20261015, det-lem-int-tensor-pullback, strict cochain refinement; Stacks Tags 099M,
099N and 099I
(blueprint: lem-sfb-integral-pullback-strict-roos-normalization). -/
abbrev V := res l E Y ⋙ redC l E Y ⋙ towerPullC l E g
/-- All integer-indexed cochain complexes of completed-coefficient modules.
Source: main-20261015, det-lem-int-tensor-pullback, strict cochain refinement; Stacks Tags 099M,
099N and 099I
(blueprint: lem-sfb-integral-pullback-strict-roos-normalization). -/
abbrev complexesR (W : Scheme.{u}) := CochainComplex (ModR l E W) ℤ
/-- All integer-indexed cochain complexes of constant-coefficient modules.
Source: main-20261015, det-lem-int-tensor-pullback, strict cochain refinement; Stacks Tags 099M,
099N and 099I
(blueprint: lem-sfb-integral-pullback-strict-roos-normalization). -/
abbrev complexesC (W : Scheme.{u}) := CochainComplex (ModC l E W) ℤ
/-- The existing additivity instance for module inverse image.
Source: main-20261015, det-lem-int-tensor-pullback, strict cochain refinement; Stacks Tags 099M,
099N and 099I
(blueprint: lem-sfb-integral-pullback-strict-roos-normalization). -/
instance pullR_additive : (pullR l E g).Additive :=
  completedModulePullback_additive g (datum l E)
/-- The existing additivity instance for the strict reduction functor.
Source: main-20261015, det-lem-int-tensor-pullback, strict cochain refinement; Stacks Tags 099M,
099N and 099I
(blueprint: lem-sfb-integral-pullback-strict-roos-normalization). -/
instance redR_additive (W : Scheme.{u}) : (redR l E W).Additive :=
  completedReductionModuleTowerFunctor_additive W (datum l E)
/-- Zero preservation obtained from the existing additive reduction functor.
Source: main-20261015, det-lem-int-tensor-pullback, strict cochain refinement; Stacks Tags 099M,
099N and 099I
(blueprint: lem-sfb-integral-pullback-strict-roos-normalization). -/
instance redR_zero (W : Scheme.{u}) :
    (completedReductionModuleTowerFunctor W (datum l E)).PreservesZeroMorphisms :=
  Functor.preservesZeroMorphisms_of_additive _
/-- Additivity of the composite giving the tower U.
Source: main-20261015, det-lem-int-tensor-pullback, strict cochain refinement; Stacks Tags 099M,
099N and 099I
(blueprint: lem-sfb-integral-pullback-strict-roos-normalization). -/
instance U_additive : (U l E g).Additive where
  map_add {_M _N} {a b} := (congrArg (redR l E X).map
    ((pullR l E g).map_add (f := a) (g := b))).trans ((redR l E X).map_add)

/-- Zero preservation of U, without unfolding the chosen derived-category structures.
Source: main-20261015, det-lem-int-tensor-pullback, strict cochain refinement; Stacks Tags 099M,
099N and 099I
(blueprint: lem-sfb-integral-pullback-strict-roos-normalization). -/
instance U_zero : (U l E g).PreservesZeroMorphisms :=
  Functor.preservesZeroMorphisms_of_additive _

/-- Apply the tower T degree by degree to a cochain complex.
Source: main-20261015, det-lem-int-tensor-pullback, strict cochain refinement; Stacks Tags 099M,
099N and 099I
(blueprint: lem-sfb-integral-pullback-strict-roos-normalization). -/
abbrev cxT := (T l E g).mapHomologicalComplex (.up ℤ)
/-- Apply the tower U degree by degree to a cochain complex.
Source: main-20261015, det-lem-int-tensor-pullback, strict cochain refinement; Stacks Tags 099M,
099N and 099I
(blueprint: lem-sfb-integral-pullback-strict-roos-normalization). -/
abbrev cxU := (U l E g).mapHomologicalComplex (.up ℤ)
/-- Apply the tower V degree by degree to a cochain complex.
Source: main-20261015, det-lem-int-tensor-pullback, strict cochain refinement; Stacks Tags 099M,
099N and 099I
(blueprint: lem-sfb-integral-pullback-strict-roos-normalization). -/
abbrev cxV := (V l E g).mapHomologicalComplex (.up ℤ)
/-- Degreewise completed-coefficient inverse image.
Source: main-20261015, det-lem-int-tensor-pullback, strict cochain refinement; Stacks Tags 099M,
099N and 099I
(blueprint: lem-sfb-integral-pullback-strict-roos-normalization). -/
abbrev cxPullR := (pullR l E g).mapHomologicalComplex (.up ℤ)
/-- Degreewise constant-coefficient inverse image.
Source: main-20261015, det-lem-int-tensor-pullback, strict cochain refinement; Stacks Tags 099M,
099N and 099I
(blueprint: lem-sfb-integral-pullback-strict-roos-normalization). -/
abbrev cxPullC := (pullC l E g).mapHomologicalComplex (.up ℤ)
/-- Degreewise scalar restriction.
Source: main-20261015, det-lem-int-tensor-pullback, strict cochain refinement; Stacks Tags 099M,
099N and 099I
(blueprint: lem-sfb-integral-pullback-strict-roos-normalization). -/
abbrev cxRes (W : Scheme.{u}) := (res l E W).mapHomologicalComplex (.up ℤ)
/-- The conjunction of the recorded K-flat predicate and flatness of every term over R.
Source: main-20261015, det-lem-int-tensor-pullback, strict cochain refinement; Stacks Tags 099M,
099N and 099I
(blueprint: lem-sfb-integral-pullback-strict-roos-normalization). -/
abbrev GoodR (W : Scheme.{u}) (P : complexesR l E W) : Prop :=
  CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1} (R := R l E W) P ∧
    ∀ i : ℤ, SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1} 
      (J := ProEt.topology W) (R := R l E W) (P.X i)
/-- The same resolving class over the constant ring C, using the recorded predicates.
Source: main-20261015, det-lem-int-tensor-pullback, strict cochain refinement; Stacks Tags 099M,
099N and 099I
(blueprint: lem-sfb-integral-pullback-strict-roos-normalization). -/
abbrev GoodC (W : Scheme.{u}) (P : complexesC l E W) : Prop :=
  CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1} (R := C l E W) P ∧
    ∀ i : ℤ, SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1} 
      (J := ProEt.topology W) (R := C l E W) (P.X i)

/-- The natural chain isomorphism induced by the normalized coefficient-square map d.
Source: main-20261015, det-lem-int-tensor-pullback, strict cochain refinement; Stacks Tags 099M,
099N and 099I
(blueprint: lem-sfb-integral-pullback-strict-roos-normalization). -/
abbrev dComplex
    (d : pullR l E g ⋙ res l E X ≅ res l E Y ⋙ pullC l E g) :=
  NatIso.mapHomologicalComplex d (.up ℤ)

/-- The evaluated strict theta comparison on one positive quotient complex.
Source: main-20261015, det-lem-int-tensor-pullback, strict cochain refinement; Stacks Tags 099M,
099N and 099I
(blueprint: lem-sfb-integral-pullback-strict-roos-normalization). -/
abbrev levelMap
    (e : T l E g ⋙ towerRes l E X ≅ V l E g)
    (P : complexesR l E Y) (n : ℕ) :=
  (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map
    ((NatIso.mapHomologicalComplex e (.up ℤ)).hom.app P)).app (op n)

/-- The product of theta level maps after the canonical product comparison for restriction.
Source: main-20261015, det-lem-int-tensor-pullback, strict cochain refinement; Stacks Tags 099M,
099N and 099I
(blueprint: lem-sfb-integral-pullback-strict-roos-normalization). -/
abbrev productMap
    (e : T l E g ⋙ towerRes l E X ≅ V l E g)
    (P : complexesR l E Y) :=
  piComparison (cxRes l E X)
      (fun n : ℕ ↦ ((cxT l E g).obj P).asFunctor.obj (op n)) ≫
    Limits.Pi.map (fun n : ℕ ↦ levelMap l E g e P n)

/-- The actual quotient augmentation of T: apply inverse image to the existing quotient unit. Its
chain condition is the naturality equation of that unit.
Source: main-20261015, det-lem-int-tensor-pullback, strict cochain refinement; Stacks Tags 099M,
099N and 099I
(blueprint: lem-sfb-integral-pullback-strict-roos-normalization). -/
def bT (P : complexesR l E Y) (n : ℕ) :
    (cxPullR l E g).obj P ⟶ ((cxT l E g).obj P).asFunctor.obj (op n) where
  f i := (pullR l E g).map
    (((completedReductionModuleUnit (datum l E) Y).app (P.X i)).app (op n))
  comm' i j _ := by
    dsimp only [cxT, cxPullR, cxV, cxPullC, cxRes, T, V, towerPullR, towerPullC,
      Functor.mapHomologicalComplex, HomologicalComplex.asFunctor, Functor.comp,
      Functor.whiskeringRight, Functor.whiskerRight_app]
    simpa only [NatTrans.comp_app, Functor.map_comp, Functor.const_map_app,
      Functor.const_obj_obj, completedTowerConstant, Functor.whiskerRight_app,
      cxRes, Functor.mapHomologicalComplex] using congrArg
      (fun a ↦ (pullR l E g).map (a.app (op n)))
      ((completedReductionModuleUnit (datum l E) Y).naturality (P.d i j)).symm


/-- The actual quotient augmentation of U, evaluated on the ordinary pulled complex. Its chain
condition is the naturality equation of the existing quotient unit.
Source: main-20261015, det-lem-int-tensor-pullback, strict cochain refinement; Stacks Tags 099M,
099N and 099I
(blueprint: lem-sfb-integral-pullback-strict-roos-normalization). -/
def bU (P : complexesR l E Y) (n : ℕ) :
    (cxPullR l E g).obj P ⟶ ((cxU l E g).obj P).asFunctor.obj (op n) where
  f i := ((completedReductionModuleUnit (datum l E) X).app
    (((cxPullR l E g).obj P).X i)).app (op n)
  comm' i j _ := congrArg (fun a ↦ a.app (op n))
    ((completedReductionModuleUnit (datum l E) X).naturality
      (((cxPullR l E g).obj P).d i j)).symm


/-- The actual constant-coefficient quotient augmentation of V, followed by inverse image. Its chain
condition is the naturality equation of the existing constant quotient unit.
Source: main-20261015, det-lem-int-tensor-pullback, strict cochain refinement; Stacks Tags 099M,
099N and 099I
(blueprint: lem-sfb-integral-pullback-strict-roos-normalization). -/
def bV (P : complexesR l E Y) (n : ℕ) :
    (cxPullC l E g).obj ((cxRes l E Y).obj P) ⟶
      ((cxV l E g).obj P).asFunctor.obj (op n) where
  f i := (pullC l E g).map
    (((OrderedExchange.ordinaryAugmentation (datum l E) Y).app
      (((cxRes l E Y).obj P).X i)).app (op n))
  comm' i j _ := by
    dsimp only [cxT, cxPullR, cxV, cxPullC, cxRes, T, V, towerPullR, towerPullC,
      Functor.mapHomologicalComplex, HomologicalComplex.asFunctor, Functor.comp,
      Functor.whiskeringRight, Functor.whiskerRight_app]
    simpa only [NatTrans.comp_app, Functor.map_comp, Functor.const_map_app,
      Functor.const_obj_obj, completedTowerConstant, Functor.whiskerRight_app,
      cxRes, Functor.mapHomologicalComplex] using congrArg
      (fun a ↦ (pullC l E g).map (a.app (op n)))
      ((OrderedExchange.ordinaryAugmentation (datum l E) Y).naturality
        ((res l E Y).map (P.d i j))).symm


/-- The strict complex comparison induced degreewise by lambda.
Source: main-20261015, det-lem-int-tensor-pullback, strict cochain refinement; Stacks Tags 099M,
099N and 099I
(blueprint: lem-sfb-integral-pullback-strict-roos-normalization). -/
abbrev lamComplex (a : T l E g ≅ U l E g) :=
  letI : (U l E g).PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_additive _
  NatIso.mapHomologicalComplex a (.up ℤ)

/-- The actual shifted-cone map of lambda. The existing roosF_map_χ equation gives the product of
the level maps in both cone coordinates.
Source: main-20261015, det-lem-int-tensor-pullback, strict cochain refinement; Stacks Tags 099M,
099N and 099I
(blueprint: lem-sfb-integral-pullback-strict-roos-normalization). -/
abbrev Lmap (a : T l E g ≅ U l E g) (P : complexesR l E Y) :=
  roosF.mapIso ((lamComplex l E g a).app P)

/-- Strict tower complexes in the indicated ambient module category.
Source: main-20261015, det-lem-int-tensor-pullback, strict cochain refinement; Stacks Tags 099M,
099N and 099I
(blueprint: lem-sfb-integral-pullback-strict-roos-normalization). -/
abbrev towerComplexes (W : Scheme.{u})
    (B : Sheaf (ProEt.topology W) CommRingCat.{u + 1}) :=
  CochainComplex (ℕᵒᵖ ⥤ reductionModules W B) ℤ

/-- The type of comparisons from the existing strict Roos functor to total derived limit.
Source: main-20261015, det-lem-int-tensor-pullback, strict cochain refinement; Stacks Tags 099M,
099N and 099I
(blueprint: lem-sfb-integral-pullback-strict-roos-normalization). -/
abbrev kappaType (W : Scheme.{u})
    (B : Sheaf (ProEt.topology W) CommRingCat.{u + 1}) :=
  (roosF (A := reductionModules W B)) ⋙ DerivedCategory.Q ≅
    DerivedCategory.Q ⋙ completedRlim W B

/-- The type of ordinary-limit inclusions into the actual strict Roos cone.
Source: main-20261015, det-lem-int-tensor-pullback, strict cochain refinement; Stacks Tags 099M,
099N and 099I
(blueprint: lem-sfb-integral-pullback-strict-roos-normalization). -/
abbrev inclusionType (W : Scheme.{u})
    (B : Sheaf (ProEt.topology W) CommRingCat.{u + 1}) :=
  (completedTowerLimit W B).mapHomologicalComplex (.up ℤ) ⟶
    (roosF (A := reductionModules W B))

/-- The compatible-family map to the degreewise product, with the canonical evaluation-product
comparison inserted explicitly.
Source: main-20261015, det-lem-int-tensor-pullback, strict cochain refinement; Stacks Tags 099M,
099N and 099I
(blueprint: lem-sfb-integral-pullback-strict-roos-normalization). -/
def limitProduct (W : Scheme.{u})
    (B : Sheaf (ProEt.topology W) CommRingCat.{u + 1})
    (I : towerComplexes W B) (q : ℤ) :
    limit (I.X q) ⟶ (roosP I).X q :=
  Limits.Pi.lift (fun n : ℕ ↦ limit.π (I.X q) (op n)) ≫
    inv (piComparison (HomologicalComplex.eval _ _ q)
      (fun n : ℕ ↦ I.asFunctor.obj (op n)))

/-- The ordinary-limit inclusion has coordinates (0,z), and its image followed by kappa is exactly
the existing universal total-right-derived-limit unit. This fixes the K-injective comparison and
its extension to all strict tower complexes.
Source: main-20261015, det-lem-int-tensor-pullback, strict cochain refinement; Stacks Tags 099M,
099N and 099I
(blueprint: lem-sfb-integral-pullback-strict-roos-normalization). -/
def IsUnitNormalized (W : Scheme.{u})
    (B : Sheaf (ProEt.topology W) CommRingCat.{u + 1})
    (κ : kappaType W B) (j : inclusionType W B) : Prop :=
  (∀ (I : towerComplexes W B) (p : ℤ),
    (j.app I).f (p + 1) ≫ (roosχ I p).hom =
      biprod.lift 0 (limitProduct W B I (p + 1))) ∧
  ∀ I : towerComplexes W B,
    DerivedCategory.Q.map (j.app I) ≫ κ.hom.app I = OrderedExchange.limitComplexUnit W B I

/-- The existing quotient-completion unit over completed coefficients: the
constant-tower/derived-limit unit followed by derived limit of the quotient augmentation.
Source: main-20261015, det-lem-int-tensor-pullback, strict cochain refinement; Stacks Tags 099M,
099N and 099I
(blueprint: lem-sfb-integral-pullback-strict-roos-normalization). -/
def unitR (W : Scheme.{u}) (K : reductionDerivedCategory W (R l E W)) :=
  (completedConstantRlimUnit (datum l E) W).app K ≫
    (completedRlim W (R l E W)).map ((completedReductionTowerUnit (datum l E) W).app K)

/-- The specified comparison V to the quotient tower of constant inverse image. It is theta inverse,
then restricted lambda, inverse finite coefficient comparison, and d. Every factor is the
recorded canonical natural isomorphism.
Source: main-20261015, det-lem-int-tensor-pullback, strict cochain refinement; Stacks Tags 099M,
099N and 099I
(blueprint: lem-sfb-integral-pullback-strict-roos-normalization). -/
def constantTowerIso
    (d : pullR l E g ⋙ res l E X ≅ res l E Y ⋙ pullC l E g)
    (a : T l E g ≅ U l E g)
    (e : T l E g ⋙ towerRes l E X ≅ V l E g) :
    V l E g ≅ (res l E Y ⋙ pullC l E g) ⋙ redC l E X :=
  e.symm ≪≫ Functor.isoWhiskerRight a (towerRes l E X) ≪≫
    Functor.isoWhiskerLeft (pullR l E g) (OrderedExchange.ordinaryRho (datum l E) X).symm ≪≫
    Functor.isoWhiskerRight d (redC l E X)

/-- The canonical comparison from the derived pulled reduction tower to the strict representative T,
using the two existing universal counits.
Source: main-20261015, det-lem-int-tensor-pullback, strict cochain refinement; Stacks Tags 099M,
099N and 099I
(blueprint: lem-sfb-integral-pullback-strict-roos-normalization). -/
def towerCounit (P : complexesR l E Y) :=
  (completedTowerPullback g (datum l E)).map
      (completedReductionTowerComplexCounit Y (datum l E) P) ≫
    completedTowerPullbackComplexCounit g (datum l E)
      ((completedReductionComplexTowerFunctor Y (datum l E)).obj P)


/-- The balanced-generator formula for lambda, with the finite scalar transported by its canonical
coefficient identification.
Source: main-20261015, det-lem-int-tensor-pullback, strict cochain refinement; Stacks Tags 099M,
099N and 099I
(blueprint: lem-sfb-integral-pullback-strict-roos-normalization). -/
def IsLambdaNormalized (a : T l E g ≅ U l E g) : Prop :=
  ∀ (M : ModR l E Y) (n : ℕ) (Z : Y.ProEtᵒᵖ)
    (s : ((datum l E).finiteRing Y n).obj.obj Z) (x : M.val.obj Z),
    ((a.hom.app M).app (op n)).val.app ((proEtaleBaseChange g).op.obj Z)
      (PulledReduction.insertion (datum l E) g
        ((completedReductionLevel Y (datum l E) n).obj M) Z
        (reductionTensorSection Y ((datum l E).projection Y n) M Z s x)) =
      reductionTensorSection X ((datum l E).projection X n) ((pullR l E g).obj M)
        ((proEtaleBaseChange g).op.obj Z)
        ((proEtaleRingDirectImageMap g ((datum l E).finiteRing Y n)
          ((datum l E).finiteRing X n) ((datum l E).finiteRingIso g n)).hom.app Z s)
        (PulledReduction.insertion (datum l E) g M Z x)

/-- The type of augmented Roos maps for T.
Source: main-20261015, det-lem-int-tensor-pullback, strict cochain refinement; Stacks Tags 099M,
099N and 099I
(blueprint: lem-sfb-integral-pullback-strict-roos-normalization). -/
abbrev alphaTType := ∀ P : complexesR l E Y,
  (cxPullR l E g).obj P ⟶ roosF.obj ((cxT l E g).obj P)
/-- The type of augmented Roos maps for U.
Source: main-20261015, det-lem-int-tensor-pullback, strict cochain refinement; Stacks Tags 099M,
099N and 099I
(blueprint: lem-sfb-integral-pullback-strict-roos-normalization). -/
abbrev alphaUType := ∀ P : complexesR l E Y,
  (cxPullR l E g).obj P ⟶ roosF.obj ((cxU l E g).obj P)
/-- The type of augmented Roos maps for V, in the constant-coefficient category.
Source: main-20261015, det-lem-int-tensor-pullback, strict cochain refinement; Stacks Tags 099M,
099N and 099I
(blueprint: lem-sfb-integral-pullback-strict-roos-normalization). -/
abbrev alphaVType := ∀ P : complexesR l E Y,
  (cxPullC l E g).obj ((cxRes l E Y).obj P) ⟶ roosF.obj ((cxV l E g).obj P)
/-- The type of scalar-restriction Roos comparisons, retaining both ambient categories.
Source: main-20261015, det-lem-int-tensor-pullback, strict cochain refinement; Stacks Tags 099M,
099N and 099I
(blueprint: lem-sfb-integral-pullback-strict-roos-normalization). -/
abbrev EType := ∀ P : complexesR l E Y,
  (cxRes l E X).obj (roosF.obj ((cxT l E g).obj P)) ≅ roosF.obj ((cxV l E g).obj P)

/-- Each augmentation is the actual cone lift with coordinates (0,b), where b is its existing strict
quotient augmentation.
Source: main-20261015, det-lem-int-tensor-pullback, strict cochain refinement; Stacks Tags 099M,
099N and 099I
(blueprint: lem-sfb-integral-pullback-strict-roos-normalization). -/
def IsAugmentationNormalized (αT : alphaTType l E g) (αU : alphaUType l E g)
    (αV : alphaVType l E g) : Prop :=
  (∀ (P : complexesR l E Y) (p : ℤ),
    (αT P).f (p + 1) ≫ (roosχ ((cxT l E g).obj P) p).hom =
      biprod.lift 0 ((Limits.Pi.lift (bT l E g P)).f (p + 1))) ∧
  (∀ (P : complexesR l E Y) (p : ℤ),
    (αU P).f (p + 1) ≫ (roosχ ((cxU l E g).obj P) p).hom =
      biprod.lift 0 ((Limits.Pi.lift (bU l E g P)).f (p + 1))) ∧
  ∀ (P : complexesR l E Y) (p : ℤ),
    (αV P).f (p + 1) ≫ (roosχ ((cxV l E g).obj P) p).hom =
      biprod.lift 0 ((Limits.Pi.lift (bV l E g P)).f (p + 1))

/-- The E comparison is the product of the stated theta maps on both cone coordinates, and commutes
with all chain maps in P.
Source: main-20261015, det-lem-int-tensor-pullback, strict cochain refinement; Stacks Tags 099M,
099N and 099I
(blueprint: lem-sfb-integral-pullback-strict-roos-normalization). -/
def IsENormalized (e : T l E g ⋙ towerRes l E X ≅ V l E g)
    (ε : EType l E g) : Prop :=
  (∀ (P : complexesR l E Y) (p : ℤ),
    (ε P).hom.f (p + 1) ≫ (roosχ ((cxV l E g).obj P) p).hom =
      (res l E X).map (roosχ ((cxT l E g).obj P) p).hom ≫
        Functor.biprodComparison (res l E X)
          ((roosP ((cxT l E g).obj P)).X p)
          ((roosP ((cxT l E g).obj P)).X (p + 1)) ≫
        biprod.map ((productMap l E g e P).f p)
          ((productMap l E g e P).f (p + 1))) ∧
  ∀ (P P' : complexesR l E Y) (a : P ⟶ P'),
    (cxRes l E X).map (roosF.map ((cxT l E g).map a)) ≫ (ε P').hom =
      (ε P).hom ≫ roosF.map ((cxV l E g).map a)


/-- Localization of L is derived limit of lambda. Localization of E is the canonical
restriction/derived-limit comparison followed by derived limit of theta. The last two equations
identify alphaU with the quotient-completion unit and alphaT with the existing
completed-pullback unit, through the canonical representative counits.
Source: main-20261015, det-lem-int-tensor-pullback, strict cochain refinement; Stacks Tags 099M,
099N and 099I
(blueprint: lem-sfb-integral-pullback-strict-roos-normalization). -/
def IsLocalized (a : T l E g ≅ U l E g)
    (e : T l E g ⋙ towerRes l E X ≅ V l E g)
    (ε : EType l E g) (αT : alphaTType l E g) (αU : alphaUType l E g)
    (κR : kappaType X (R l E X)) (κC : kappaType X (C l E X)) : Prop :=
  (∀ P : complexesR l E Y,
    DerivedCategory.Q.map (Lmap l E g a P).hom ≫ κR.hom.app ((cxU l E g).obj P) =
      κR.hom.app ((cxT l E g).obj P) ≫
        (completedRlim X (R l E X)).map
          (DerivedCategory.Q.map ((lamComplex l E g a).hom.app P))) ∧
  (∀ P : complexesR l E Y,
    (res l E X).mapDerivedCategory.map (κR.hom.app ((cxT l E g).obj P)) ≫
        (OrderedExchange.lambda (datum l E) X).hom.app
          (DerivedCategory.Q.obj ((cxT l E g).obj P)) ≫
        (completedRlim X (C l E X)).map
          ((towerRes l E X).mapDerivedCategoryFactors.hom.app ((cxT l E g).obj P)) ≫
        (completedRlim X (C l E X)).map
          (DerivedCategory.Q.map ((NatIso.mapHomologicalComplex e (.up ℤ)).hom.app P)) =
      (res l E X).mapDerivedCategoryFactors.hom.app
          (roosF.obj ((cxT l E g).obj P)) ≫
        DerivedCategory.Q.map (ε P).hom ≫ κC.hom.app ((cxV l E g).obj P)) ∧
  (∀ (P : complexesR l E Y), GoodR l E Y P →
    DerivedCategory.Q.map (αU P) ≫ κR.hom.app ((cxU l E g).obj P) =
      unitR l E X (DerivedCategory.Q.obj ((cxPullR l E g).obj P)) ≫
        (completedRlim X (R l E X)).map
          (completedReductionTowerComplexCounit X (datum l E)
            ((cxPullR l E g).obj P))) ∧
  ∀ (P : complexesR l E Y), GoodR l E Y P →
    completedOrdinaryPullbackComplexCounit g (datum l E) P ≫
        DerivedCategory.Q.map (αT P) ≫ κR.hom.app ((cxT l E g).obj P) =
      completedPullbackComparison g (datum l E) (DerivedCategory.Q.obj P) ≫
        (completedRlim X (R l E X)).map (towerCounit l E g P)

/-- After the specified strict constant-tower comparison, localized alphaV is the existing constant
quotient-completion unit, followed by the universal reduction counit. This is the
constant-coefficient completed-pullback unit on the given representative.
Source: main-20261015, det-lem-int-tensor-pullback, strict cochain refinement; Stacks Tags 099M,
099N and 099I
(blueprint: lem-sfb-integral-pullback-strict-roos-normalization). -/
def IsConstantUnitNormalized
    (d : pullR l E g ⋙ res l E X ≅ res l E Y ⋙ pullC l E g)
    (a : T l E g ≅ U l E g)
    (e : T l E g ⋙ towerRes l E X ≅ V l E g)
    (αV : alphaVType l E g) (κC : kappaType X (C l E X)) : Prop :=
  ∀ (P : complexesR l E Y), GoodR l E Y P →
    DerivedCategory.Q.map (αV P) ≫ κC.hom.app ((cxV l E g).obj P) ≫
        (completedRlim X (C l E X)).map
          (DerivedCategory.Q.map
            ((NatIso.mapHomologicalComplex (constantTowerIso l E g d a e)
              (.up ℤ)).hom.app P)) =
      (OrderedExchange.unit (datum l E) X).app
          (DerivedCategory.Q.obj ((cxPullC l E g).obj ((cxRes l E Y).obj P))) ≫
        (completedRlim X (C l E X)).map
          (OrderedExchange.reductionComplexCounit (datum l E) X
            (((res l E Y ⋙ pullC l E g).mapHomologicalComplex (.up ℤ)).obj P))


/-- All clauses of the strict Roos normalization, bundled as an explicit proposition:
coefficient-square and balanced-generator normalizations, strict transitions, flat K-flat
preservation, both cone lifts, both chain augmentation identities, universal derived-limit
normalization and the two completion units. The final counit isomorphisms identify the
representatives on the resolving class.
Source: main-20261015, det-lem-int-tensor-pullback, strict cochain refinement; Stacks Tags 099M,
099N and 099I
(blueprint: lem-sfb-integral-pullback-strict-roos-normalization). -/
def IsComparison
    (d : pullR l E g ⋙ res l E X ≅ res l E Y ⋙ pullC l E g)
    (a : T l E g ≅ U l E g)
    (e : T l E g ⋙ towerRes l E X ≅ V l E g)
    (αT : alphaTType l E g) (αU : alphaUType l E g) (αV : alphaVType l E g)
    (ε : EType l E g) (κR : kappaType X (R l E X))
    (jR : inclusionType X (R l E X)) (κC : kappaType X (C l E X))
    (jC : inclusionType X (C l E X)) : Prop :=
  PulledReduction.IsOrdinaryNormalized (datum l E) g d.inv ∧
  IsLambdaNormalized l E g a ∧
  (∀ (M : ModR l E Y) (n : ℕ),
    (e.hom.app M).app (op n) =
      d.hom.app (((redR l E Y).obj M).obj (op n)) ≫
        (pullC l E g).map
          (((OrderedExchange.ordinaryRho (datum l E) Y).inv.app M).app (op n))) ∧
  (∀ P : complexesR l E Y, GoodR l E Y P →
    GoodR l E X ((cxPullR l E g).obj P) ∧
    GoodC l E Y ((cxRes l E Y).obj P) ∧
    GoodC l E X ((cxPullC l E g).obj ((cxRes l E Y).obj P))) ∧
  IsAugmentationNormalized l E g αT αU αV ∧ IsENormalized l E g e ε ∧
  (∀ P : complexesR l E Y, αT P ≫ (Lmap l E g a P).hom = αU P) ∧
  (∀ P : complexesR l E Y,
    (cxRes l E X).map (αT P) ≫ (ε P).hom =
      (dComplex l E g d).hom.app P ≫ αV P) ∧
  IsUnitNormalized X (R l E X) κR jR ∧ IsUnitNormalized X (C l E X) κC jC ∧
  IsLocalized l E g a e ε αT αU κR κC ∧
  IsConstantUnitNormalized l E g d a e αV κC ∧
  ∀ P : complexesR l E Y, GoodR l E Y P →
    IsIso (towerCounit l E g P) ∧
    IsIso (completedOrdinaryPullbackComplexCounit g (datum l E) P) ∧
    IsIso (completedReductionTowerComplexCounit X (datum l E)
      ((cxPullR l E g).obj P)) ∧
    IsIso (OrderedExchange.reductionComplexCounit (datum l E) X
      (((res l E Y ⋙ pullC l E g).mapHomologicalComplex (.up ℤ)).obj P))

/-- Strict Roos normalization of integral pullback and constant scalar restriction.

Source: main-20261015, det-lem-int-tensor-pullback, first paragraph and Comparison with the
Stacks Project; Stacks proetale.tex Tags 099M, 099N and algebraization.tex Tag 099I.
(blueprint: lem-sfb-integral-pullback-strict-roos-normalization).

Proof plan (the ten steps of this DAG node):

1. Identify $R_T$ with $\varprojlim_n A_{n,T}$ by [det-prop-sfb-qlbar-colimit-x-integral-limit],
using its canonical finite projections. The coefficient datum makes $A$ a discrete valuation
ring, hence a principal ideal domain; every ideal is finitely generated, so $A$ is Noetherian.
Apply [lem-weil-pbc-constant-completion-equivalence] on each small pro-étale site with
$I=(\pi)$. Its flatness and quotient assertions give $R_T$ flat over $C_T$ and
$R_T/\pi^nR_T\cong A_{n,T}$ for every $n\geq1$, compatibly with the quotient projections. These
assertions concern the entire module categories and require no completeness of $[P]$.

2. Write $a_C:g^{-1}C_Y\cong C_X$ and $a_R:g^{-1}R_Y\cong R_X$. The constant identification
comes from inverse image of constant sheaves; the completed identification and exactness of
module inverse image are [sk-prop-sfb-cartesian-coefficients]. If $i_T:C_T\to R_T$ is the
constant-function map, naturality of the comparison $g^{-1}p_Y^*\cong p_X^*$ at the map from
discrete $A$ to continuous $A$ gives $a_R\,g^{-1}i_Y=i_Xa_C$
[sk-def-sfb-pullback-from-point-comp, sk-def-sfb-coefficient-morphisms]. By
[sk-def-sfb-module-pushforward-pullback], $g^*H=R_X\otimes_{g^{-1}R_Y}g^{-1}H$. Its
identification with $g^{-1}H$ sends $r\otimes h$ to $a_R^{-1}(r)h$, with inverse
$h\mapsto1\otimes h$. The analogous formula using $a_C$ identifies $g_C^*\operatorname{Res}_YH$
with the same abelian sheaf. The displayed coefficient-square equation makes these two
$C_X$-actions identical. Define $d_H$ by the identity on that sheaf. It therefore sends each
scalar-extension generator to its specified constant-coefficient generator, is invertible, and
is natural in $H$. Both module inverse images therefore have the same exact underlying abelian
inverse-image functor. Applying the construction in every degree gives a chain isomorphism for
every complex $H$, in particular $d=d_P$.

3. Apply [lem-weil-pbc-flat-scalar-restriction-kflat] to $C_Y\to R_Y$, flat by step 1. Since $P$
is K-flat with flat terms, $Q=\operatorname{Res}_YP$ is K-flat with flat terms over $C_Y$. Apply
the flat-term K-flat pullback assertion of [lem-weil-pbc-ringed-topoi-derived-tensor-pullback]
to the ringed-topos morphisms with coefficients $R_Y,R_X$ and $C_Y,C_X$, respectively. It gives
flat terms and K-flatness for $g^*P$ and $g_C^*Q$. These applications impose neither boundedness
nor a condition on the cohomology of $P$.

4. For any $R_T$-module $H$, construct the underived comparison
$$\beta_{T,n,H}:\operatorname{Res}_TH\otimes_{C_T}A_{n,T}\longrightarrow
\operatorname{Res}_T(H\otimes_{R_T}A_{n,T}),\qquad
h\otimes\bar a\longmapsto h\otimes\bar a.$$
Both sides are the cokernel of multiplication by $\pi^n$ on the same underlying sheaf $H$: on
the left use $A_{n,T}=C_T/(\pi^n)$, and on the right use $A_{n,T}=R_T/(\pi^n)$ from
[lem-weil-pbc-constant-completion-equivalence]. The two identifications send $h\otimes1$ to the
class of $h$, so $\beta$ is invertible. This also proves the inverse formula, including
balancing by arbitrary local $R_T$-sections, without assuming that those sections are constant.
Applying it degreewise gives a natural chain isomorphism. On each tensor generator both orders
of reduction from $n+1$ to $n$ send $h\otimes\bar a$ to $h\otimes(\bar a\bmod\pi^n)$, and
$\beta$ sends the quotient augmentation $h\mapsto h\otimes1$ to the same augmentation. Thus all
these compatibilities are strict.

5. Use the ordinary balanced tensor comparison of [def-sfb-condensed-pullback-tensor-comparison]
with $H=P^q$ and the coefficient module $A_{n,Y}$, and identify $g^*A_{n,Y}=A_{n,X}$ by
[sk-prop-sfb-cartesian-coefficients]. Degreewise this gives $\lambda_n:T_n\cong U_n$. The same
balanced calculation over $C$ gives
$g_C^*(Q\otimes_{C_Y}A_{n,Y})\cong(g_C^*Q)\otimes_{C_X}A_{n,X}$. Under inverse-coefficient
transport its formula is the balanced map sending the inverse-image tensor $h\otimes\bar a$ to
the tensor of the two inverse images; it commutes with differentials by naturality in $P^q$.
Define
$$\theta_n=g_C^*(\beta_{Y,n,P}^{-1})\circ
d_{P\otimes_{R_Y}A_{n,Y}}:\operatorname{Res}_XT_n\xrightarrow{\sim}V_n.$$
Here step 2 constructs $d$ for all complexes, so it applies even though the finite tensor need
not be K-flat. The formulas for $\beta$ and $d$ show that $\theta_n$ also sends an inverse-image
tensor $h\otimes\bar a$ to the same tensor. For either $\lambda$ or $\theta$, composing in
either order with the transition sends this generator to $h\otimes(\bar a\bmod\pi^n)$. Composing
with the augmentation sends $h$ to $h\otimes1$; on the source of $\theta$ this uses $d_P(h)=h$.
These generator equations prove equality of sheaf maps, hence of chain maps. Thus $\lambda$ and
$\theta$ are isomorphisms of strict towers, preserving their specified augmentations.

6. Restriction of scalars is the identity on underlying abelian sheaves
[def-pc-sheaf-restrict-scalars]. Kernels and local lifts of sections through epimorphisms are
therefore unchanged, so it is exact. Products of module sheaves exist and are computed
sectionwise by [lem-weil-proetale-countable-products-exact]. Consequently the canonical map
$\operatorname{Res}_X(\prod_nT_n)\to\prod_n\operatorname{Res}_XT_n$ is an isomorphism: over
every site object it sends a tuple to that same tuple, and both $C_X$-actions are componentwise.
It commutes with projections, differentials and $s$. Finite direct sums and their maps are
unchanged as well. This fixes the product and cone identifications used for $E_P$.

7. For $W$ put $B_W=\prod_nW_n$ and $F_W=1-s_W$. In the coordinate order fixed in the statement,
$$\mathsf R(W)^q=B_W^{q-1}\oplus B_W^q,\qquad D_W(y,x)=(-d_Wy-F_Wx,d_Wx).$$
Let $a=\prod_n\lambda_n$ and let $e=\prod_n\theta_n$, using step 6 for the source of $e$. Strict
transition compatibility from step 5 gives $aF_T=F_Ua$ and $eF_{\operatorname{Res}T}=F_Ve$.
Define $L_P(y,x)=(ay,ax)$ and $E_P(y,x)=(ey,ex)$. For example,
$$D_U(ay,ax)=(-a\,d_Ty-aF_Tx,a\,d_Tx)=L_P D_T(y,x).$$
The identical computation with $e$ proves the chain equation for $E_P$. Their inverses are
diagonal products of the levelwise inverses and satisfy the same equations. Naturality in $P$
follows from the natural level maps and the componentwise product formulas. Thus these are
precisely the asserted cochain isomorphisms, with no cone-map choice.

8. For a compatible augmentation $b:L\to W$, set $b^\Pi=(b_n)_n$. Compatibility says
$F_Wb^\Pi=0$. Hence
$$D_W(0,b^\Pi z)=(0,b^\Pi d_Lz),$$
so the specified $\alpha_W(z)=(0,b^\Pi z)$ is a chain map with exactly the given cone signs.
Step 5 gives $a b_T^\Pi=b_U^\Pi$ and $e\operatorname{Res}_X(b_T^\Pi)=b_V^\Pi d$. Evaluating the
diagonal maps of step 7 now gives
$$L_P\alpha_T(z)=(0,b_U^\Pi z)=\alpha_U(z),\qquad
E_P\operatorname{Res}_X(\alpha_T)(z)=(0,b_V^\Pi d(z))=\alpha_Vd(z).$$
These are equalities of actual chain maps, rather than equalities inferred only from their
finite projections.

9. It remains to identify these actual cone maps with the total derived strict-tower
comparisons. By [lem-weil-proetale-countable-products-exact], products are exact for each
coefficient sheaf here. Thus [lem-pe-roos-cone-calculus] applies: its reordered cone is exactly
$\mathsf R(W)$ with coordinates $(x,y)$, and its action on strict maps is the diagonal product
map of step 7. For a K-injective tower resolution $W\to I$, as used in
[lem-weil-pbc-ringed-strict-tower-homotopy-limit], this gives a quasi-isomorphism $\mathsf
R(W)\to\mathsf R(I)$. By [lem-weil-derived-limit-roos-complex] the natural map $\varprojlim
I_n\to\mathsf R(I)$ is a quasi-isomorphism, explicitly $z\mapsto(0,(z_n)_n)$. The remaining
hypothesis of the K-injective Roos lemma holds: the module category on a small pro-étale
skeleton is Grothendieck by [lem-pur-ringed-site-grothendieck-abelian] and hence has enough
injectives by [lem-sp-grothendieck-enough-injectives]. The strict tower resolution is supplied
by the ringed strict-tower theorem. The resulting zigzag identifies $Q\mathsf R(W)$ with the
total right derived inverse limit. For an augmented tower, both composites from $L$ to $\mathsf
R(I)$ are $(0,(L\to W_n\to I_n)_n)$, so this zigzag identifies the augmentation with the
strict-derived-tower unit. Where the unit is defined as in [def-weil-pbc-completed-pullback],
through a resolution $\Delta L\to I'$ and $R\lim$ of $\Delta L\to W$, choose a lift $I'\to I$;
by K-injectivity of $I$ its composite with $\Delta L\to I'$ is homotopic to $\Delta L\to W\to
I$, and the diagonal product of that homotopy is a homotopy on $\mathsf R(I)$, so both
descriptions give the same map in the derived category. It is natural in strict maps; hence the
localizations of $L_P,E_P$ are the claimed canonical comparisons, not arbitrary isomorphisms of
Roos triangles.

10. By step 3, $P$, $g^*P$, $Q$ and $g_C^*Q$ are valid flat-term K-flat representatives for
their respective derived tensor calculations
[lem-weil-pbc-ringed-topoi-derived-tensor-pullback]. Thus $U$ computes the finite derived
reductions of $g^*[P]$, and $V$ computes those of $g_C^*[Q]$ (constant-coefficient inverse image
commutes with reduction by the same balanced calculation of step 5). The quotient-tower units
are the derived-completion units by [lem-weil-pbc-constant-completion-equivalence], including
for inputs which are not complete. In the notation of [def-weil-pbc-completed-pullback], use the
identification of step 1 [det-prop-sfb-qlbar-colimit-x-integral-limit] of its
$A_T=\varprojlim_n(A_n)_T$ with $R_T$. Its structure map $c_g$ is then $a_R$ of step 2:
naturality of $g^{-1}p_Y^*\cong p_X^*$ at $\mathcal O_E\to\mathcal O_E/\pi^n$
[sk-def-sfb-pullback-from-point-comp, sk-def-sfb-coefficient-morphisms] gives the $n$-th
projection of $a_R$ as the constant-sheaf comparison $g^{-1}(A_n)_Y\cong(A_n)_X$, which, like
the $n$-th component of $c_g$, sends each constant section to itself; maps into the limit agree
when their projections do. So module pullback along $c_g$ is the item's $g^*$. Applying derived
pullback to the augmented strict reduction tower gives the tower represented here by $T$:
inverse image on $R$-modules is exact by [sk-prop-sfb-cartesian-coefficients], so it computes
this operation on any representative of the tower. Step 9 identifies its chosen total derived
inverse limit and unit with $Q\mathsf R(T)$ and $Q\alpha_T$. Therefore step 8 proves both
required normalized derived identities. On derived-complete input the constant formula is
precisely Stacks completed pullback (099N(2),(5)); on arbitrary input it is the same ordinary
pullback followed by completion and its unit. This argument never identifies the two ambient
coefficient categories, or asserts that an arbitrary $[P]$ is complete.
-/
theorem integralPullbackStrictRoosNormalization
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)]
    [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [g.IsOver (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [IsSeparated (Y ↘ Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))] :
    ∃ (d : pullR l E g ⋙ res l E X ≅ res l E Y ⋙ pullC l E g)
      (a : T l E g ≅ U l E g)
      (e : T l E g ⋙ towerRes l E X ≅ V l E g)
      (αT : alphaTType l E g) (αU : alphaUType l E g) (αV : alphaVType l E g)
      (ε : EType l E g) (κR : kappaType X (R l E X))
      (jR : inclusionType X (R l E X)) (κC : kappaType X (C l E X))
      (jC : inclusionType X (C l E X)),
      IsComparison l E g d a e αT αU αV ε κR jR κC jC := by
  sorry

end WeilConjectures.IntegralPullbackStrictRoos
