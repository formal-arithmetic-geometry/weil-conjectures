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
public import Sheaf.Paper.PulledReductionStrictTowerComparison
public import Sheaf.Paper.SfImmersionCompletedPullbackComparison
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
public import Sheaf.CategoryTheory.StrictRoosModel
public import Sheaf.Algebra.Homology.FlatScalarRestrictionKFlat
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible

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
attribute [local irreducible] roosF roosχ roosConeFunctor
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
  pbcAdicCompletion T (datum l E)
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
abbrev ModR (T : Scheme.{u}) := pbcModules T (R l E T)
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

/-- Zero preservation of the pulled quotient tower, shared by the chain constructions.
Source: additivity of reduction and pullback
(blueprint: def-sfb-integral-pullback-strict-roos-data). -/
instance T_zero : (T l E g).PreservesZeroMorphisms := by
  dsimp only [T, towerPullR]
  infer_instance

/-- Zero preservation of restricted pullback, shared by the chain constructions.
Source: additivity of pullback and scalar restriction
(blueprint: def-sfb-integral-pullback-strict-roos-data). -/
instance pullRes_zero : (pullR l E g ⋙ res l E X).PreservesZeroMorphisms := by
  infer_instance

/-- Zero preservation of the restricted strict tower, shared by the chain constructions.
Source: additivity of reduction, pullback and scalar restriction
(blueprint: def-sfb-integral-pullback-strict-roos-data). -/
instance towerRes_zero : (T l E g ⋙ towerRes l E X).PreservesZeroMorphisms := by
  infer_instance

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
@[irreducible]
def productMap
    (e : T l E g ⋙ towerRes l E X ≅ V l E g)
    (P : complexesR l E Y) :
    (cxRes l E X).obj (roosP ((cxT l E g).obj P)) ⟶
      roosP ((cxV l E g).obj P) :=
  piComparison (cxRes l E X)
      (fun n : ℕ ↦ ((cxT l E g).obj P).asFunctor.obj (op n)) ≫
    Limits.Pi.map (fun n : ℕ ↦ levelMap l E g e P n)


/-- The actual quotient augmentation of T: apply inverse image to the existing quotient unit. Its
chain condition is the naturality equation of that unit.
Source: main-20261015, det-lem-int-tensor-pullback, strict cochain refinement; Stacks Tags 099M,
099N and 099I
(blueprint: lem-sfb-integral-pullback-strict-roos-normalization). -/
@[irreducible]
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
@[irreducible]
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
@[irreducible]
def lamComplex (a : T l E g ≅ U l E g) : cxT l E g ≅ cxU l E g :=
  letI : (U l E g).PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_additive _
  NatIso.mapHomologicalComplex a (.up ℤ)


/-- The actual shifted-cone map of lambda. The existing roosF_map_χ equation gives the product of
the level maps in both cone coordinates.
Source: main-20261015, det-lem-int-tensor-pullback, strict cochain refinement; Stacks Tags 099M,
099N and 099I
(blueprint: lem-sfb-integral-pullback-strict-roos-normalization). -/
@[irreducible]
def Lmap (a : T l E g ≅ U l E g) (P : complexesR l E Y) :
    roosF.obj ((cxT l E g).obj P) ≅ roosF.obj ((cxU l E g).obj P) :=
  roosF.mapIso ((lamComplex l E g a).app P)


/-- The pulled quotient augmentation on one degree.
Source: the concrete quotient-unit construction
(blueprint: def-sfb-integral-pullback-strict-roos-data). -/
theorem bT_f (P : complexesR l E Y) (n : ℕ) (q : ℤ) :
    (bT l E g P n).f q = (pullR l E g).map
      (((completedReductionModuleUnit (datum l E) Y).app (P.X q)).app (op n)) := by
  unfold bT
  rfl

/-- The quotient augmentation of the pulled complex on one degree.
Source: the concrete quotient-unit construction
(blueprint: def-sfb-integral-pullback-strict-roos-data). -/
theorem bU_f (P : complexesR l E Y) (n : ℕ) (q : ℤ) :
    (bU l E g P n).f q = ((completedReductionModuleUnit (datum l E) X).app
      ((pullR l E g).obj (P.X q))).app (op n) := by
  unfold bU
  rfl

/-- The complex comparison is the given module comparison in each degree and level.
Source: degreewise extension of the strict comparison
(blueprint: def-sfb-integral-pullback-strict-roos-data). -/
theorem lamComplex_hom_component (a : T l E g ≅ U l E g)
    (P : complexesR l E Y) (n : ℕ) (q : ℤ) :
    ((HomologicalComplex.complexOfFunctorsToFunctorToComplex.map
      ((lamComplex l E g a).hom.app P)).app (op n)).f q =
      (a.hom.app (P.X q)).app (op n) := by
  unfold lamComplex
  rfl

/-- The cone comparison is Roos applied to the strict comparison.
Source: the concrete shifted-cone construction
(blueprint: def-sfb-integral-pullback-strict-roos-data). -/
theorem Lmap_hom (a : T l E g ≅ U l E g) (P : complexesR l E Y) :
    (Lmap l E g a P).hom = roosF.map ((lamComplex l E g a).hom.app P) := by
  unfold Lmap
  rfl

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
@[irreducible]
def unitR (W : Scheme.{u}) (K : reductionDerivedCategory W (R l E W)) :
    K ⟶ (completedRlim W (R l E W)).obj ((completedReductionTower W (datum l E)).obj K) :=
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
@[irreducible]
def towerCounit (P : complexesR l E Y) :
    (completedTowerPullback g (datum l E)).obj
        ((completedReductionTower Y (datum l E)).obj (DerivedCategory.Q.obj P)) ⟶
      DerivedCategory.Q.obj ((cxT l E g).obj P) :=
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

attribute [local irreducible] Functor.mapDerivedCategory Functor.mapDerivedCategoryFactors
  completedReductionTower completedReductionTowerUnit completedConstantRlimUnit
  OrderedExchange.limitComplexUnit OrderedExchange.lambda


/-- Each augmentation is the actual cone lift with coordinates (0,b), where b is its existing strict
quotient augmentation.
Source: main-20261015, det-lem-int-tensor-pullback, strict cochain refinement; Stacks Tags 099M,
099N and 099I
(blueprint: lem-sfb-integral-pullback-strict-roos-normalization). -/
def IsAugmentationNormalized (αT : alphaTType l E g) (αU : alphaUType l E g)
    (αV : alphaVType l E g) : Prop :=
  (∀ (P : complexesR l E Y) (p : ℤ),
    (αT P).f (p + 1) ≫ (roosχ ((cxT l E g).obj P) p).hom =
      biprod.lift
        (0 : ((cxPullR l E g).obj P).X (p + 1) ⟶ (roosP ((cxT l E g).obj P)).X p)
        ((Limits.Pi.lift (bT l E g P)).f (p + 1))) ∧
  (∀ (P : complexesR l E Y) (p : ℤ),
    (αU P).f (p + 1) ≫ (roosχ ((cxU l E g).obj P) p).hom =
      biprod.lift
        (0 : ((cxPullR l E g).obj P).X (p + 1) ⟶ (roosP ((cxU l E g).obj P)).X p)
        ((Limits.Pi.lift (bU l E g P)).f (p + 1))) ∧
  ∀ (P : complexesR l E Y) (p : ℤ),
    (αV P).f (p + 1) ≫ (roosχ ((cxV l E g).obj P) p).hom =
      biprod.lift
        (0 : ((cxPullC l E g).obj ((cxRes l E Y).obj P)).X (p + 1) ⟶
          (roosP ((cxV l E g).obj P)).X p)
        ((Limits.Pi.lift (bV l E g P)).f (p + 1))




/-- The T coordinate equation of normalized augmentations.
Source: unpacking the recorded normalization
(blueprint: def-sfb-integral-pullback-strict-roos-data). -/
theorem IsAugmentationNormalized.t
    {αT : alphaTType l E g} {αU : alphaUType l E g} {αV : alphaVType l E g}
    (h : IsAugmentationNormalized l E g αT αU αV) (P : complexesR l E Y) (p : ℤ) :
    (αT P).f (p + 1) ≫ (roosχ ((cxT l E g).obj P) p).hom =
      biprod.lift
        (0 : ((cxPullR l E g).obj P).X (p + 1) ⟶ (roosP ((cxT l E g).obj P)).X p)
        ((Limits.Pi.lift (bT l E g P)).f (p + 1)) := h.1 P p

/-- The U coordinate equation of normalized augmentations.
Source: unpacking the recorded normalization
(blueprint: def-sfb-integral-pullback-strict-roos-data). -/
theorem IsAugmentationNormalized.u
    {αT : alphaTType l E g} {αU : alphaUType l E g} {αV : alphaVType l E g}
    (h : IsAugmentationNormalized l E g αT αU αV) (P : complexesR l E Y) (p : ℤ) :
    (αU P).f (p + 1) ≫ (roosχ ((cxU l E g).obj P) p).hom =
      biprod.lift
        (0 : ((cxPullR l E g).obj P).X (p + 1) ⟶ (roosP ((cxU l E g).obj P)).X p)
        ((Limits.Pi.lift (bU l E g P)).f (p + 1)) := h.2.1 P p

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





attribute [local irreducible] completedReductionTowerComplexCounit
  completedOrdinaryPullbackComplexCounit
  completedPullbackComparison

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







attribute [local irreducible] IsLambdaNormalized IsAugmentationNormalized IsENormalized
  IsUnitNormalized IsLocalized IsConstantUnitNormalized bV

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

/-- Product-coordinate extensionality for strict Roos maps.
Source: the normalized strict Roos coordinate calculation
(blueprint: def-sfb-integral-pullback-strict-roos-data). -/
theorem roosProduct_augmentation
    {A : Type*} [Category A] [Abelian A] [HasCountableProducts A]
    {I J : CochainComplex (ℕᵒᵖ ⥤ A) ℤ} {P : CochainComplex A ℤ}
    (f : I ⟶ J)
    (b : ∀ n : ℕ, P ⟶ I.asFunctor.obj (op n))
    (c : ∀ n : ℕ, P ⟶ J.asFunctor.obj (op n))
    (h : ∀ (n : ℕ) (q : ℤ),
      (b n).f q ≫ ((HomologicalComplex.complexOfFunctorsToFunctorToComplex.map f).app
        (op n)).f q = (c n).f q) :
    Limits.Pi.lift b ≫ roosPmap f = Limits.Pi.lift c := by
  apply Limits.Pi.hom_ext
  intro n
  simp only [roosPmap, Category.assoc, Limits.Pi.map_π, Limits.Pi.lift_π_assoc,
    Limits.Pi.lift_π]
  apply HomologicalComplex.hom_ext
  intro q
  exact h n q

/-- Biproduct-coordinate extensionality for normalized Roos maps.
Source: the normalized strict Roos coordinate calculation
(blueprint: def-sfb-integral-pullback-strict-roos-data). -/
theorem biprod_augmentation
    {A : Type*} [Category A] [HasZeroMorphisms A] [HasBinaryBiproducts A]
    {P X Y A₁ A₂ B₁ B₂ : A} (χ : X ≅ A₁ ⊞ A₂) (ψ : Y ≅ B₁ ⊞ B₂)
    (α : P ⟶ X) (β : P ⟶ Y) (f : X ⟶ Y)
    (b : P ⟶ A₂) (c : P ⟶ B₂) (x : A₁ ⟶ B₁) (y : A₂ ⟶ B₂)
    (hα : α ≫ χ.hom = biprod.lift 0 b) (hβ : β ≫ ψ.hom = biprod.lift 0 c)
    (hf : f ≫ ψ.hom = χ.hom ≫ biprod.map x y) (h : b ≫ y = c) :
    α ≫ f = β := by
  apply (cancel_mono ψ.hom).1
  rw [Category.assoc, hf, ← Category.assoc, hα, hβ]
  apply biprod.hom_ext
  · simp only [Category.assoc, biprod.map_fst, biprod.lift_fst_assoc,
      biprod.lift_fst, zero_comp]
  · simp only [Category.assoc, biprod.map_snd, biprod.lift_snd_assoc,
      biprod.lift_snd, h]

/-- Cone-coordinate extensionality for normalized strict Roos maps.
Source: the normalized strict Roos coordinate calculation
(blueprint: def-sfb-integral-pullback-strict-roos-data). -/
theorem roosMap_augmentation
    {A : Type*} [Category A] [Abelian A] [HasCountableProducts A]
    {I J : CochainComplex (ℕᵒᵖ ⥤ A) ℤ} {P : CochainComplex A ℤ}
    (f : I ⟶ J) (α : P ⟶ roosF.obj I) (β : P ⟶ roosF.obj J)
    (b : P ⟶ roosP I) (c : P ⟶ roosP J)
    (hα : ∀ p : ℤ, α.f (p + 1) ≫ (roosχ I p).hom =
      biprod.lift (0 : P.X (p + 1) ⟶ (roosP I).X p) (b.f (p + 1)))
    (hβ : ∀ p : ℤ, β.f (p + 1) ≫ (roosχ J p).hom =
      biprod.lift (0 : P.X (p + 1) ⟶ (roosP J).X p) (c.f (p + 1)))
    (h : b ≫ roosPmap f = c) : α ≫ roosF.map f = β := by
  apply HomologicalComplex.hom_ext
  intro q
  obtain ⟨p, rfl⟩ : ∃ p : ℤ, q = p + 1 := ⟨q - 1, by omega⟩
  exact biprod_augmentation (roosχ I p) (roosχ J p)
    (α.f (p + 1)) (β.f (p + 1)) ((roosF.map f).f (p + 1))
    (b.f (p + 1)) (c.f (p + 1)) ((roosPmap f).f p) ((roosPmap f).f (p + 1))
    (hα p) (hβ p) (roosF_map_χ f p) (HomologicalComplex.congr_hom h (p + 1))
end WeilConjectures.IntegralPullbackStrictRoos
