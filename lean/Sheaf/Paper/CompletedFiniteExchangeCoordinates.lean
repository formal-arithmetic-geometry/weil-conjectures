/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NA
-/
module

public import Sheaf.Paper.CompletedStrictOpenExchange
public import Sheaf.AlgebraicGeometry.FiniteOpenExchangeScalars
public import Sheaf.AlgebraicGeometry.ProEtaleDerivedExtensionZeroBaseChange
import Sheaf.Paper.ConstantCompletionEquivalence
import Sheaf.CategoryTheory.LocalizedModuleExactForSystems
import Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction
import Sheaf.Paper.LocalizeRingedSiteMorphismGeneral
import Sheaf.Algebra.Homology.DiagramKFlatReplacements
import Sheaf.SixFunctors.OpenTensorNormalization

/-!
# Fixed finite coordinates for completed-ring open exchange

Source: Stacks 03DI, 03D7, 04J0 and 099N; blueprint finite exchange before Rlim
(blueprint: def-cbc-completed-finite-exchange-coordinates).

The scalar comparisons are mates of the sectionwise specified right comparisons.
The level coordinate change is identity on sections. Thus no unrelated finite
coordinate isomorphism is selected.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

attribute [local irreducible] HasDerivedCategory.standard SheafOfModules.monoidalCategory
  Functor.leftAdjoint

variable {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)

variable {U' U X' X : Scheme.{u}} {gU : U' ⟶ U} {j' : U' ⟶ X'}
  {j : U ⟶ X} {g : X' ⟶ X} (sq : OpenImmersionSquare gU j' j g)

open AlgebraicGeometry.ProEtale.StrictTower

/-- The positive finite quotient, bundled once to avoid repeated ring elaboration.
Source: the coefficient datum (blueprint: def-cbc-completed-finite-exchange-coordinates). -/
def cbcFiniteRing (n : ℕ) : CommRingCat.{u + 1} :=
  CommRingCat.of (A ⧸ d.ideal ^ (n + 1))

/-- The bundled finite ring is finite by the coefficient datum.
Source: the coefficient datum (blueprint: def-cbc-completed-finite-exchange-coordinates).
Proof: this is exactly d.quotientFinite at the positive exponent n+1. -/
@[instance] theorem cbcFiniteRing_finite (n : ℕ) : Finite (cbcFiniteRing d n) := by
  sorry

/-- The completed-ring action on constant finite coefficients is the projection
followed by the inverse of the fixed constant-section comparison.
Source: Stacks 099N (blueprint: def-cbc-completed-finite-exchange-coordinates). -/
def cbcFiniteProjection (T : Scheme.{u}) (n : ℕ) :
    pbcAdicCompletion T d ⟶ coefficients (cbcFiniteRing d n) T :=
  pbcAdicProjection T d n ≫ (pbcLevelConstantComparison T d n).inv

/-- Finite modules with their actual completed-ring scalar action.
Source: Stacks 03CY (blueprint: def-cbc-completed-finite-exchange-coordinates). -/
def cbcFiniteRes (T : Scheme.{u}) (n : ℕ) := pbcRestrict (cbcFiniteProjection d T n)

/-- Direct-image coefficient restriction is the identity on underlying sections.
This normalization fixes its mate, rather than choosing a pullback isomorphism.
Source: Stacks 03D7 (blueprint: def-cbc-completed-finite-exchange-coordinates).
Proof: both direct images evaluate on the same base-changed site object. Their
scalar actions agree after the completed finite projection. Identity on sections
is thus linear, natural, and invertible, and it determines the comparison uniquely. -/
theorem cbcFiniteDirectRes_existsUnique {S T : Scheme.{u}} (f : S ⟶ T) (n : ℕ) :
    ∃! e : moduleDirectImage (cbcFiniteRing d n) f ⋙ cbcFiniteRes d T n ≅
        cbcFiniteRes d S n ⋙ cbcCompletedModuleDirectImage d f,
      ∀ (M : ProEtale.StrictTower.Modules (cbcFiniteRing d n) S) (V : T.ProEtᵒᵖ)
        (x : M.val.obj ((proEtaleBaseChange f).op.obj V)),
        (e.hom.app M).val.app V x = x := by
  sorry

/-- The sectionwise direct-image comparison, with its fixed identity normalization.
Source: Stacks 03D7 (blueprint: def-cbc-completed-finite-exchange-coordinates). -/
@[irreducible] def cbcFiniteDirectRes {S T : Scheme.{u}} (f : S ⟶ T) (n : ℕ) :=
  (cbcFiniteDirectRes_existsUnique d f n).exists.choose

/-- The finite pullback comparison is the mate of identity on direct-image sections.
Source: Stacks 03D7 (blueprint: def-cbc-completed-finite-exchange-coordinates). -/
def cbcFinitePullRes {S T : Scheme.{u}} (f : S ⟶ T) (n : ℕ) :
    cbcFiniteRes d T n ⋙ completedModulePullback f d ⟶
      modulePullback (cbcFiniteRing d n) f ⋙ cbcFiniteRes d S n :=
  ((mateEquiv
    (proEtaleRingModuleAdjunction f _ _ (constantRingIso (cbcFiniteRing d n) f))
    (cbcModulePullbackAdjunction d f)).symm
      (TwoSquare.mk _ _ _ _ (cbcFiniteDirectRes d f n).hom)).natTrans

/-- The ordinary pullback mate is invertible at finite coefficients.
Source: Stacks 03EK, 099N (blueprint: def-cbc-completed-finite-exchange-coordinates).
Proof: on inverse-image tensor generators the mate sends b tensor m to pi_n(b)
tensor m. The inverse inserts 1 in the completed tensor factor. The finite
constant-ring comparison and balancing make these maps mutually inverse. -/
@[instance] theorem cbcFinitePullRes_isIso {S T : Scheme.{u}} (f : S ⟶ T) (n : ℕ) :
    IsIso (cbcFinitePullRes d f n) := by
  sorry

/-- Open restriction commutes with finite scalar restriction, normalized on the
inverse-image unit generators. The site adjunction supplies the actual restricted
section, so no unidentified comparison of underlying abelian sheaves is used.
Source: Stacks 03DI, 04J0 (blueprint: def-cbc-completed-finite-exchange-coordinates).
Proof: localization evaluates a sheaf on the same object over the open. On a
base-change generator its value is restriction along the adjoint site arrow.
The coefficient projections identify scalar actions. These formulas give inverse
linear maps after sheafification; the generators determine them uniquely. -/
theorem cbcFiniteOpenRestriction_existsUnique {W T : Scheme.{u}}
    (e : W ⟶ T) (he : IsOpenImmersion e) (n : ℕ) :
    ∃! q : modulePullback (cbcFiniteRing d n) e ⋙ cbcFiniteRes d W n ≅
        cbcFiniteRes d T n ⋙ cbcOpenRestriction d e he,
      ∀ (M : ProEtale.StrictTower.Modules (cbcFiniteRing d n) T) (V : W.ProEt) (Z : T.ProEt)
        (f : V ⟶ (proEtaleBaseChange e).obj Z) (m : M.val.obj (op Z)),
        (q.hom.app M).val.app (op V)
          (((modulePullback (cbcFiniteRing d n) e).obj M).val.map f.op
            (((proEtaleRingModuleAdjunction e _ _
              (constantRingIso (cbcFiniteRing d n) e)).unit.app M).val.app (op Z) m)) =
          M.val.map
            (((MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ e
              (cbcOpenWeaklyEtale e he) trivial).homEquiv V Z).symm f).op m := by
  sorry

/-- The uniquely normalized finite open-restriction comparison.
Source: Stacks 03DI (blueprint: def-cbc-completed-finite-exchange-coordinates). -/
@[irreducible] def cbcFiniteOpenRestriction {W T : Scheme.{u}}
    (e : W ⟶ T) (he : IsOpenImmersion e) (n : ℕ) :=
  (cbcFiniteOpenRestriction_existsUnique d e he n).exists.choose

/-- Open extension commutes with the completed action through the finite projection.
This is the mate of the specified open-restriction comparison.
Source: Stacks 03DI (blueprint: def-cbc-completed-finite-exchange-coordinates). -/
def cbcFiniteOpenRes {W T : Scheme.{u}}
    (e : W ⟶ T) (he : IsOpenImmersion e) (n : ℕ) :
    cbcFiniteRes d W n ⋙ cbcOpenShriek d e he ⟶
      (@moduleJ.{u} (cbcFiniteRing d n) _ W T e he) ⋙ cbcFiniteRes d T n :=
  ((mateEquiv (@moduleJAdj.{u} (cbcFiniteRing d n) _ W T e he)
    (cbcOpenAdjunction d e he)).symm
      (TwoSquare.mk _ _ _ _ (cbcFiniteOpenRestriction d e he n).hom)).natTrans

/-- The normalized open-extension comparison is invertible.
Source: Stacks 03DI (blueprint: def-cbc-completed-finite-exchange-coordinates).
Proof: both extensions are the same direct-sum extension followed by sheafification,
with scalars restricted along the finite projection. The mate sends each extension
summand to the identical summand. Its inverse does the same; sheafification gives
the two inverse identities. -/
@[instance] theorem cbcFiniteOpenRes_isIso {W T : Scheme.{u}}
    (e : W ⟶ T) (he : IsOpenImmersion e) (n : ℕ) :
    IsIso (cbcFiniteOpenRes d e he n) := by
  sorry

/-- Finite coordinates for the source of the ordinary exchange, built by the
specified open and pullback mates.
Source: Stacks 03DI, 099N (blueprint: def-cbc-completed-finite-exchange-coordinates). -/
def cbcFiniteSourceRes (n : ℕ) :
    cbcFiniteRes d U n ⋙ cbcOpenShriek d j sq.isOpenImmersion ⋙ completedModulePullback g d ≅
      (@moduleJ.{u} (cbcFiniteRing d n) _ U X j sq.isOpenImmersion) ⋙
        modulePullback (cbcFiniteRing d n) g ⋙ cbcFiniteRes d X' n :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (asIso (cbcFiniteOpenRes d j sq.isOpenImmersion n)) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (asIso (cbcFinitePullRes d g n))

/-- Finite coordinates for the target, in the prescribed pullback-then-open order.
Source: Stacks 03DI, 099N (blueprint: def-cbc-completed-finite-exchange-coordinates). -/
def cbcFiniteTargetRes (n : ℕ) :
    cbcFiniteRes d U n ⋙ completedModulePullback gU d ⋙
        cbcOpenShriek d j' sq.isOpenImmersion' ≅
      modulePullback (cbcFiniteRing d n) gU ⋙
        (@moduleJ.{u} (cbcFiniteRing d n) _ U' X' j' sq.isOpenImmersion') ⋙
          cbcFiniteRes d X' n :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (asIso (cbcFinitePullRes d gU n)) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (asIso (cbcFiniteOpenRes d j' sq.isOpenImmersion' n))

/-- Reduction to finite constant coefficients, using the existing scalar extension
and the fixed constant-section coefficient isomorphism.
Source: Stacks 099N (blueprint: def-cbc-completed-finite-exchange-coordinates). -/
def cbcFiniteReductionModule (T : Scheme.{u}) (n : ℕ) :=
  reductionChange T (pbcAdicProjection T d n) ⋙
    pbcRestrict (pbcLevelConstantComparison T d n).hom

/-- Finite reduction followed by coefficient restriction is additive.
Source: Stacks 03EK, 099N
(blueprint: def-cbc-completed-finite-exchange-coordinates).
Proof: sheafified scalar extension and scalar restriction both preserve sums of
morphisms. Composing their sum equations proves additivity. -/
@[instance] theorem cbcFiniteReductionModule_additive (T : Scheme.{u}) (n : ℕ) :
    (cbcFiniteReductionModule d T n).Additive := by
  sorry

/-- The finite quotient object in its own constant coefficient derived category.
Source: Stacks 099N (blueprint: def-cbc-completed-finite-exchange-coordinates). -/
def cbcFiniteReduction (T : Scheme.{u}) (n : ℕ) :=
  reductionDerivedChange T (pbcAdicProjection T d n) ⋙
    pbcDerivedRestrict (pbcLevelConstantComparison T d n).hom

/-- Reexpressing an ordinary reduction tower level in constant finite coordinates
leaves every section unchanged and only transports its coefficient action.
Source: Stacks 099N (blueprint: def-cbc-completed-finite-exchange-coordinates).
Proof: the projection followed by the inverse constant comparison is the specified
completed action. Restricting successively along the comparison and its inverse
cancels, so identity sections give the unique natural isomorphism. -/
theorem cbcFiniteLevel_existsUnique (T : Scheme.{u}) (n : ℕ) :
    ∃! e : completedReductionModuleTowerFunctor T d ⋙
          (CategoryTheory.evaluation ℕᵒᵖ (pbcModules T (pbcAdicCompletion T d))).obj (op n) ≅
        cbcFiniteReductionModule d T n ⋙ cbcFiniteRes d T n,
      ∀ (M : pbcModules T (pbcAdicCompletion T d)) (V : T.ProEtᵒᵖ)
        (x : ((reductionChange T (pbcAdicProjection T d n)).obj M).val.obj V),
        (e.hom.app M).val.app V x = x := by
  sorry

/-- The finite coordinate change fixed by identity on sections.
Source: Stacks 099N (blueprint: def-cbc-completed-finite-exchange-coordinates). -/
@[irreducible] def cbcFiniteLevel (T : Scheme.{u}) (n : ℕ) :=
  (cbcFiniteLevel_existsUnique d T n).exists.choose

/-- The finite source functor, including the completed action through the projection.
Source: Stacks 03DI, 099N (blueprint: def-cbc-completed-finite-exchange-coordinates). -/
def cbcFiniteSource (n : ℕ) :=
  (@moduleJ.{u} (cbcFiniteRing d n) _ U X j sq.isOpenImmersion) ⋙
    modulePullback (cbcFiniteRing d n) g ⋙ cbcFiniteRes d X' n

/-- The finite target functor in the pullback-then-extension order.
Source: Stacks 03DI, 099N (blueprint: def-cbc-completed-finite-exchange-coordinates). -/
def cbcFiniteTarget (n : ℕ) :=
  modulePullback (cbcFiniteRing d n) gU ⋙
    (@moduleJ.{u} (cbcFiniteRing d n) _ U' X' j' sq.isOpenImmersion') ⋙
      cbcFiniteRes d X' n

/-- Both finite source and target are exact and additive.
Source: Stacks 03DI, 03DJ, 03EK
(blueprint: def-cbc-completed-finite-exchange-coordinates).
Proof: open extension and finite constant pullback are exact and additive, as
is scalar restriction. Compose these properties in the indicated order. -/
@[instance] theorem cbcFiniteSource_additive (n : ℕ) :
    (cbcFiniteSource d sq n).Additive := by
  sorry

/-- Exactness of the finite source, checked before derived localization.
Source: Stacks 03DJ, 03EK (blueprint: def-cbc-completed-finite-exchange-coordinates).
Proof: compose exact open extension, finite pullback and scalar restriction. -/
@[instance] theorem cbcFiniteSource_limits (n : ℕ) :
    PreservesFiniteLimits (cbcFiniteSource d sq n) := by
  sorry

/-- The finite source preserves cokernels and finite sums.
Source: Stacks 03DI, 03EK (blueprint: def-cbc-completed-finite-exchange-coordinates).
Proof: all three functors preserve finite colimits, hence so does their composite. -/
@[instance] theorem cbcFiniteSource_colimits (n : ℕ) :
    PreservesFiniteColimits (cbcFiniteSource d sq n) := by
  sorry

/-- Additivity of the finite target.
Source: Stacks 03DI, 03EK (blueprint: def-cbc-completed-finite-exchange-coordinates).
Proof: finite pullback, open extension and scalar restriction are additive. -/
@[instance] theorem cbcFiniteTarget_additive (n : ℕ) :
    (cbcFiniteTarget d sq n).Additive := by
  sorry

/-- Exactness of the finite target on kernels.
Source: Stacks 03DJ, 03EK (blueprint: def-cbc-completed-finite-exchange-coordinates).
Proof: each of the three factors preserves finite limits. -/
@[instance] theorem cbcFiniteTarget_limits (n : ℕ) :
    PreservesFiniteLimits (cbcFiniteTarget d sq n) := by
  sorry

/-- Exactness of the finite target on cokernels.
Source: Stacks 03DI, 03EK (blueprint: def-cbc-completed-finite-exchange-coordinates).
Proof: each of the three factors preserves finite colimits. -/
@[instance] theorem cbcFiniteTarget_colimits (n : ℕ) :
    PreservesFiniteColimits (cbcFiniteTarget d sq n) := by
  sorry

/-- Finite reduction followed by the finite source preserves zero morphisms.
Source: Stacks 03DI, 03EK, 099N
(blueprint: def-cbc-completed-finite-exchange-coordinates).
Proof: both functors are additive. Their sum equations imply that their composite
sends the zero map to zero, including the completed scalar restriction. -/
theorem cbcFiniteSourceModel_preservesZeroMorphisms (n : ℕ) :
    (cbcFiniteReductionModule d U n ⋙ cbcFiniteSource d sq n).PreservesZeroMorphisms := by
  sorry

/-- Finite reduction followed by the finite target preserves zero morphisms.
Source: Stacks 03DI, 03EK, 099N
(blueprint: def-cbc-completed-finite-exchange-coordinates).
Proof: compose the zero-map equations of finite scalar extension, pullback,
open extension and scalar restriction. -/
theorem cbcFiniteTargetModel_preservesZeroMorphisms (n : ℕ) :
    (cbcFiniteReductionModule d U n ⋙ cbcFiniteTarget d sq n).PreservesZeroMorphisms := by
  sorry

/-- The evaluated source model preserves zero morphisms.
Source: Stacks 03DI, 03EK, 099N
(blueprint: def-cbc-completed-finite-exchange-coordinates).
Proof: reduction is additive levelwise, as are open extension and module pullback.
Evaluation preserves zero maps. Their composite therefore sends zero to zero. -/
theorem cbcSourceLevel_preservesZeroMorphisms (n : ℕ) :
    (completedReductionModuleTowerFunctor U d ⋙ cbcStrictOpenModule d j sq.isOpenImmersion ⋙
      completedTowerModulePullback g d ⋙
        (CategoryTheory.evaluation ℕᵒᵖ (pbcModules X' (pbcAdicCompletion X' d))).obj
          (op n)).PreservesZeroMorphisms := by
  sorry

/-- The evaluated target model preserves zero morphisms.
Source: Stacks 03DI, 03EK, 099N
(blueprint: def-cbc-completed-finite-exchange-coordinates).
Proof: each constituent sends zero morphisms to zero, including the evaluation.
Composing those equations in pullback-then-open order proves the assertion. -/
theorem cbcTargetLevel_preservesZeroMorphisms (n : ℕ) :
    (completedReductionModuleTowerFunctor U d ⋙ completedTowerModulePullback gU d ⋙
      cbcStrictOpenModule d j' sq.isOpenImmersion' ⋙
        (CategoryTheory.evaluation ℕᵒᵖ (pbcModules X' (pbcAdicCompletion X' d))).obj
          (op n)).PreservesZeroMorphisms := by
  sorry

/-- The ordinary finite-coordinate source comparison: first change the reduction
level's coordinates, then use the fixed scalar/open/pullback mates.
Source: Stacks 03DI, 099N (blueprint: def-cbc-completed-finite-exchange-coordinates). -/
def cbcSourceLevel (n : ℕ) :
    completedReductionModuleTowerFunctor U d ⋙ cbcStrictOpenModule d j sq.isOpenImmersion ⋙
        completedTowerModulePullback g d ⋙
          (CategoryTheory.evaluation ℕᵒᵖ (pbcModules X' (pbcAdicCompletion X' d))).obj (op n) ≅
      cbcFiniteReductionModule d U n ⋙ cbcFiniteSource d sq n :=
  Functor.isoWhiskerRight (cbcFiniteLevel d U n)
      (cbcOpenShriek d j sq.isOpenImmersion ⋙ completedModulePullback g d) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (cbcFiniteSourceRes d sq n)

/-- The analogous ordinary target comparison, with the identical finite coordinate change.
Source: Stacks 03DI, 099N (blueprint: def-cbc-completed-finite-exchange-coordinates). -/
def cbcTargetLevel (n : ℕ) :
    completedReductionModuleTowerFunctor U d ⋙ completedTowerModulePullback gU d ⋙
        cbcStrictOpenModule d j' sq.isOpenImmersion' ⋙
          (CategoryTheory.evaluation ℕᵒᵖ (pbcModules X' (pbcAdicCompletion X' d))).obj (op n) ≅
      cbcFiniteReductionModule d U n ⋙ cbcFiniteTarget d sq n :=
  Functor.isoWhiskerRight (cbcFiniteLevel d U n)
      (completedModulePullback gU d ⋙ cbcOpenShriek d j' sq.isOpenImmersion') ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (cbcFiniteTargetRes d sq n)

/-- The actual universal reduction counit on cochain representatives.
Source: Stacks 06XN (blueprint: def-cbc-completed-finite-exchange-coordinates). -/
def cbcReductionModelMap (T : Scheme.{u})
    (P : CochainComplex (pbcModules T (pbcAdicCompletion T d)) ℤ) :
    (completedReductionTower T d).obj (DerivedCategory.Q.obj P) ⟶
      DerivedCategory.Q.obj
        (((completedReductionModuleTowerFunctor T d).mapHomologicalComplex (.up ℤ)).obj P) :=
  Functor.leftDerivedCounitOnComplex (completedReductionModuleTowerFunctor T d)
    (completedReductionTower T d) (completedReductionTowerCounit d T) P

/-- Source comparison to its ordinary strict model, using only the universal counits.
Source: Stacks 06XN (blueprint: def-cbc-completed-finite-exchange-coordinates). -/
def cbcSourceModelMap (P : CochainComplex (pbcModules U (pbcAdicCompletion U d)) ℤ) :
    (completedReductionTower U d ⋙ cbcStrictOpen d j sq.isOpenImmersion ⋙
      completedTowerPullback g d).obj (DerivedCategory.Q.obj P) ⟶
    DerivedCategory.Q.obj
      (((completedTowerModulePullback g d).mapHomologicalComplex (.up ℤ)).obj
        (((cbcStrictOpenModule d j sq.isOpenImmersion).mapHomologicalComplex (.up ℤ)).obj
          (((completedReductionModuleTowerFunctor U d).mapHomologicalComplex (.up ℤ)).obj P))) :=
  (completedTowerPullback g d).map
    ((cbcStrictOpen d j sq.isOpenImmersion).map (cbcReductionModelMap d U P) ≫
      (cbcStrictOpenModule d j sq.isOpenImmersion).mapDerivedCategoryFactors.hom.app
        (((completedReductionModuleTowerFunctor U d).mapHomologicalComplex (.up ℤ)).obj P)) ≫
    completedTowerPullbackComplexCounit g d
      (((cbcStrictOpenModule d j sq.isOpenImmersion).mapHomologicalComplex (.up ℤ)).obj
        (((completedReductionModuleTowerFunctor U d).mapHomologicalComplex (.up ℤ)).obj P))

/-- Target comparison to the same ordinary strict model convention.
Source: Stacks 06XN (blueprint: def-cbc-completed-finite-exchange-coordinates). -/
def cbcTargetModelMap (P : CochainComplex (pbcModules U (pbcAdicCompletion U d)) ℤ) :
    (completedReductionTower U d ⋙ completedTowerPullback gU d ⋙
      cbcStrictOpen d j' sq.isOpenImmersion').obj (DerivedCategory.Q.obj P) ⟶
    DerivedCategory.Q.obj
      (((cbcStrictOpenModule d j' sq.isOpenImmersion').mapHomologicalComplex (.up ℤ)).obj
        (((completedTowerModulePullback gU d).mapHomologicalComplex (.up ℤ)).obj
          (((completedReductionModuleTowerFunctor U d).mapHomologicalComplex (.up ℤ)).obj P))) :=
  (cbcStrictOpen d j' sq.isOpenImmersion').map
    ((completedTowerPullback gU d).map (cbcReductionModelMap d U P) ≫
      completedTowerPullbackComplexCounit gU d
        (((completedReductionModuleTowerFunctor U d).mapHomologicalComplex (.up ℤ)).obj P)) ≫
    (cbcStrictOpenModule d j' sq.isOpenImmersion').mapDerivedCategoryFactors.hom.app
      (((completedTowerModulePullback gU d).mapHomologicalComplex (.up ℤ)).obj
        (((completedReductionModuleTowerFunctor U d).mapHomologicalComplex (.up ℤ)).obj P))

end AlgebraicGeometry.Scheme
