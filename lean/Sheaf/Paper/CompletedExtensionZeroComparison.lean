/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q03
-/
module

public import Sheaf.Paper.CompletedTowerPullback
public import Sheaf.Paper.IntrinsicCompletion
public import Sheaf.AlgebraicGeometry.OpenImmersionSquare
public import Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
public import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.Algebra.Category.ModuleCat.Ulift
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.CategoryTheory.Adjunction.Mates
import Sheaf.CategoryTheory.LocalizedModuleExactIndependent
import Sheaf.AlgebraicGeometry.ProEtaleExtensionZero
import Sheaf.CategoryTheory.RingedSliceExtensionTensor
import Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed
import Sheaf.AlgebraicGeometry.ProEtaleImmersionLimitPreservation
import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimit
import Sheaf.AlgebraicGeometry.ProEtaleConstantExact
import Sheaf.Paper.ConstantCompletionEquivalence
import Sheaf.Paper.ExactFunctorDerivedLimit
import WeilConjectures.Algebra.Homology.RoosComplex
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import WeilConjectures.CategoryTheory.Limits.TowerTransitionEndomorphism
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Mathlib.CategoryTheory.Abelian.FunctorCategory
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives

public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
/-! # Completed open-immersion base change

Source: blueprint order 1587; Stacks Tags 03DI, 09BP, 099N
(blueprint: lem-cbc-completed-extension-zero-comparison).
All extension functors below are the specified direct-sum presheaf followed by
module sheafification, transported along the ringed slice-site identification.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
variable {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A)


/-- Positive quotients retain the finiteness in the arithmetic datum, at size t+1.
Source: blueprint order 1587 (blueprint: lem-cbc-completed-extension-zero-comparison). -/
instance cbcQuotient_finite (n : ℕ) : Finite (A ⧸ d.ideal ^ (n + 1)) :=
  d.quotientFinite n

/-- Direct-image form of the recorded completed coefficient map, without assuming
that the structure map is invertible.
Source: Tag 099N (blueprint: lem-cbc-completed-extension-zero-comparison). -/
def cbcCompletedCoefficientDirectMap {X Y : Scheme.{t}} (g : X ⟶ Y) :
    completedReductionCoefficient Y d ⟶
      (proEtaleSheafDirectImage g CommRingCat.{t + 1}).obj
        (completedReductionCoefficient X d) :=
  ((proEtaleSheafAdjunction g CommRingCat.{t + 1}).homEquiv _ _)
    (completedCoefficientMap g d)

/-- Sectionwise direct image with the recorded completed scalar action.
Source: Tag 03D7 (blueprint: lem-cbc-completed-extension-zero-comparison). -/
def cbcCompletedModuleDirectImage {X Y : Scheme.{t}} (g : X ⟶ Y) :
    pbcModules X (pbcAdicCompletion X d) ⥤ pbcModules Y (pbcAdicCompletion Y d) :=
  SheafOfModules.pushforward.{t + 1} (F := proEtaleBaseChange g)
    (J := ProEt.topology Y) (K := ProEt.topology X)
    ⟨Functor.whiskerRight (cbcCompletedCoefficientDirectMap d g).hom
      (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})⟩

/-- The existing module pullback adjunction on the fixed small models. The explicit
continuity witness prevents inference from choosing an unrelated larger model.
Source: Tags 03D2, 03D7 (blueprint: lem-cbc-completed-extension-zero-comparison). -/
def cbcModelPullbackAdjunction {X Y : Scheme.{t}} (g : X ⟶ Y) :=
  letI := proEtaleModelBaseChange_isContinuous g
  SheafOfModules.pullbackPushforwardAdjunction.{t + 1}
    (F := proEtaleModelBaseChange g)
    (J := proEtaleModelTopology Y) (K := proEtaleModelTopology X)
    (proEtaleModelRingUnit g (pbcAdicCompletion Y d))

/-- The pullback adjunction is uniquely normalized by the model-site inverse-image
unit followed by the actual sheafified tensor section 1 tensor m.
Source: Tags 03D7, 03EK (blueprint: lem-cbc-completed-extension-zero-comparison).
Proof: use the model-site module adjunction followed by scalar extension, whose
unit is the specified pure tensor. Transport back leaves sections unchanged.
The tensor generators and sheafification determine the Hom bijection uniquely,
so the formula determines exactly one adjunction. No coefficient isomorphism is assumed. -/
theorem cbcModulePullbackAdjunction_exists {X Y : Scheme.{t}} (g : X ⟶ Y) :
    ∃! adj : completedModulePullback g d ⊣ cbcCompletedModuleDirectImage d g,
      ∀ (M : pbcModules Y (pbcAdicCompletion Y d)) (V : Y.ProEt)
        (x : M.val.obj (op V)),
        (adj.unit.app M).val.app (op V) x =
          pbcTensorSection (completedCoefficientMap g d)
            ((proEtaleModuleInverseImage g (pbcAdicCompletion Y d)).obj M)
            (op ((proEtaleBaseChange g).obj V)) 1
            (((cbcModelPullbackAdjunction d g).unit.app
                ((proEtaleModuleToModel
                  (reductionModuleRing Y (pbcAdicCompletion Y d))).obj M)).val.app
                    (op ((AsSmall.up : Y.ProEt ⥤ proEtaleSiteModel Y).obj V)) x) := by
  sorry

/-- The tensor-unit normalized adjunction for the recorded pullback construction.
Source: Tag 03D7 (blueprint: lem-cbc-completed-extension-zero-comparison). -/
def cbcModulePullbackAdjunction {X Y : Scheme.{t}} (g : X ⟶ Y) :=
  (cbcModulePullbackAdjunction_exists d g).exists.choose

/-- The recorded strict reduction, tower pullback and Rlim, as a composite functor.
Its object function is exactly completedPullbackObject.
Source: Tag 099N (blueprint: lem-cbc-completed-extension-zero-comparison). -/
abbrev cbcCompletedPullback {X Y : Scheme.{t}} (g : X ⟶ Y) :=
  completedReductionTower Y d ⋙ completedTowerPullback g d ⋙ completedTowerRlim d X

/-- Naturality of the recorded ordinary-to-completed pullback comparison.
Source: Tag 099N (blueprint: lem-cbc-completed-extension-zero-comparison).
Proof: the constant-tower/Rlim unit, the normalized constant-pullback comparison,
and the strict quotient augmentation are natural transformations. Functoriality
of Rlim and their three naturality identities give the displayed equality. -/
theorem cbcCompletedPullbackComparison_naturality {X Y : Scheme.{t}} (g : X ⟶ Y)
    {K L : DerivedCategory (pbcModules Y (pbcAdicCompletion Y d))} (f : K ⟶ L) :
    (completedOrdinaryPullback g d).map f ≫ completedPullbackComparison g d L =
      completedPullbackComparison g d K ≫ (cbcCompletedPullback d g).map f := by
  sorry

/-- The recorded completion-unit comparison with its naturality statement.
Source: Tag 099N (blueprint: lem-cbc-completed-extension-zero-comparison). -/
def cbcCompletedPullbackComparison {X Y : Scheme.{t}} (g : X ⟶ Y) :
    completedOrdinaryPullback g d ⟶ cbcCompletedPullback d g where
  app := completedPullbackComparison g d
  naturality _ _ f := cbcCompletedPullbackComparison_naturality d g f

/-- An open immersion is weakly etale.
Source: Tag 098K (blueprint: lem-cbc-completed-extension-zero-comparison).
Proof: an open immersion is etale, and etale morphisms are weakly etale. -/
theorem cbcOpenWeaklyEtale {U T : Scheme.{t}} (j : U ⟶ T)
    (_hj : IsOpenImmersion j) : WeaklyEtale j := by
  sorry

/-- Forget the ambient structure map in a pro-etale slice object.
Source: Tag 0951 (blueprint: lem-cbc-completed-extension-zero-comparison). -/
def cbcSliceFunctor (T : Scheme.{t}) (W : T.ProEt) : Over W ⥤ W.left.ProEt where
  obj V := MorphismProperty.Over.mk ⊤ V.hom.left
    ((ProEt.weaklyEtale_localization.{t, t + 1, t + 1} T W
      (CommRingCat.of (ULift.{t + 1} ℤ))).2.1 V)
  map f := MorphismProperty.Over.homMk f.left.left
    (congrArg (fun h ↦ h.left) f.w)

/-- The concrete localization functor is continuous.
Source: Tags 098K, 094T, 0951 (blueprint: lem-cbc-completed-extension-zero-comparison).
Proof: the functor keeps the underlying schemes and arrows. The pro-etale covering
condition is the same finite affine fpqc covering condition on those arrows;
therefore inverse images of covering sieves cover. This is exactly the site
identification in weaklyEtale_localization, with its concrete underlying maps. -/
@[instance] theorem cbcSliceFunctor_continuous (T : Scheme.{t}) (W : T.ProEt) :
    (cbcSliceFunctor T W).IsContinuous ((ProEt.topology T).over W)
      (ProEt.topology W.left) := by
  sorry

/-- The finite ring identification in the slice is fixed by local function sections.
Source: Tag 098K (blueprint: lem-cbc-completed-extension-zero-comparison).
Proof: localization keeps each underlying scheme, so its connected-component
functions agree literally. Their sheafification units induce this unique map.
Localization is an equivalence of sites, hence this map is an isomorphism. -/
theorem cbcFiniteSliceMap_exists (T : Scheme.{t}) (W : T.ProEt) (n : ℕ) :
    ∃! φ : ((reductionCoefficient T d n)).over W ⟶
        ((cbcSliceFunctor T W).sheafPushforwardContinuous CommRingCat.{t + 1}
          ((ProEt.topology T).over W) (ProEt.topology W.left)).obj
            ((reductionCoefficient W.left d n)),
      ∀ V : Over W,
        (toSheafify (ProEt.topology T)
          (AdicCoefficients.functionPresheaf T (A ⧸ d.ideal ^ (n + 1)))).app
            (op V.left) ≫ φ.hom.app (op V) =
        (toSheafify (ProEt.topology W.left)
          (AdicCoefficients.functionPresheaf W.left (A ⧸ d.ideal ^ (n + 1)))).app
            (op ((cbcSliceFunctor T W).obj V)) := by
  sorry

/-- The finite slice coefficient map with the specified function normalization.
Source: Tag 098K (blueprint: lem-cbc-completed-extension-zero-comparison). -/
def cbcFiniteSliceMap (T : Scheme.{t}) (W : T.ProEt) (n : ℕ) :=
  (cbcFiniteSliceMap_exists d T W n).exists.choose

/-- The completed coefficient identification is fixed by every finite projection.
Source: Tags 098K, 099N (blueprint: lem-cbc-completed-extension-zero-comparison).
Proof: localization commutes with limits since it keeps sections. The finite maps
commute with quotient maps since they identify the same functions. Take their
inverse limit; joint monicity of its projections proves uniqueness. -/
theorem cbcCompletedSliceMap_exists (T : Scheme.{t}) (W : T.ProEt) :
    ∃! φ : ((completedReductionCoefficient T d)).over W ⟶
        ((cbcSliceFunctor T W).sheafPushforwardContinuous CommRingCat.{t + 1}
          ((ProEt.topology T).over W) (ProEt.topology W.left)).obj
            ((completedReductionCoefficient W.left d)),
      ∀ n : ℕ, φ ≫
        ((cbcSliceFunctor T W).sheafPushforwardContinuous CommRingCat.{t + 1}
          ((ProEt.topology T).over W) (ProEt.topology W.left)).map
            ((completedReductionProjection W.left d n)) =
        ((ProEt.topology T).overPullback CommRingCat.{t + 1} W).map
          ((completedReductionProjection T d n)) ≫ cbcFiniteSliceMap d T W n := by
  sorry

/-- The completed ring map identifying the ringed slice site.
Source: Tag 098K (blueprint: lem-cbc-completed-extension-zero-comparison). -/
def cbcCompletedSliceMap (T : Scheme.{t}) (W : T.ProEt) :=
  (cbcCompletedSliceMap_exists d T W).exists.choose

/-- A module over the open's completed ring, viewed on the ambient ringed slice.
Source: Tag 03DI (blueprint: lem-cbc-completed-extension-zero-comparison). -/
def cbcModuleToSlice (T : Scheme.{t}) (W : T.ProEt) :
    (pbcModules W.left (pbcAdicCompletion W.left d)) ⥤ SheafOfModules.{t + 1}
      ((reductionModuleRing T (completedReductionCoefficient T d)).over W) :=
  SheafOfModules.pushforward.{t + 1} (F := cbcSliceFunctor T W)
    (J := (ProEt.topology T).over W) (K := ProEt.topology W.left)
    ((sheafCompose ((ProEt.topology T).over W) (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).map
      (cbcCompletedSliceMap d T W))

/-- The pro-etale object supplied by an open immersion.
Source: Tag 098K (blueprint: lem-cbc-completed-extension-zero-comparison). -/
def cbcOpenObject {U T : Scheme.{t}} (j : U ⟶ T) (hj : IsOpenImmersion j) : T.ProEt :=
  letI := hj
  MorphismProperty.Over.mk ⊤ j (inferInstance : WeaklyEtale j)

/-- Extension by zero is the recorded module direct-sum presheaf, then sheafification.
Source: Tag 03DI (blueprint: lem-cbc-completed-extension-zero-comparison). -/
def cbcOpenShriek {U T : Scheme.{t}} (j : U ⟶ T) (hj : IsOpenImmersion j) :
    (pbcModules U (pbcAdicCompletion U d)) ⥤ (pbcModules T (pbcAdicCompletion T d)) :=
  cbcModuleToSlice d T (cbcOpenObject j hj) ⋙
    SheafOfModules.extensionByZeroPresheaf.{t + 1}
      (reductionModuleRing T (completedReductionCoefficient T d)) (cbcOpenObject j hj) ⋙
    PresheafOfModules.sheafification.{t + 1}
      (𝟙 (reductionModuleRing T (completedReductionCoefficient T d)).obj)

/-- Extension by zero is additive.
Source: Tag 03DI (blueprint: lem-cbc-completed-extension-zero-comparison).
Proof: the slice transport keeps addition of maps; direct sums and module
sheafification are additive. Their composite is therefore additive. -/
@[instance] theorem cbcOpenShriek_additive {U T : Scheme.{t}}
    (j : U ⟶ T) (hj : IsOpenImmersion j) : (cbcOpenShriek d j hj).Additive := by
  sorry

/-- Extension by zero is exact, without any quasi-compactness assumption.
Source: Tag 03DJ (blueprint: lem-cbc-completed-extension-zero-comparison).
Proof: restriction to a slice is exact and its direct-sum/sheafification left
adjoint is exact. Ringed slice transport is an equivalence. The argument is
unchanged at distinct site object and Hom universes; equivalently transport to
AsSmall at t+1, apply the recorded localization theorem, and transport back. -/
@[instance] theorem cbcOpenShriek_finiteLimits {U T : Scheme.{t}}
    (j : U ⟶ T) (hj : IsOpenImmersion j) : PreservesFiniteLimits (cbcOpenShriek d j hj) := by
  sorry

/-- Extension by zero preserves finite colimits.
Source: Tag 03DI (blueprint: lem-cbc-completed-extension-zero-comparison).
Proof: it is left adjoint to restriction, via the direct-sum Hom bijection and
sheafification. Hence it preserves colimits, in particular finite colimits. -/
@[instance] theorem cbcOpenShriek_finiteColimits {U T : Scheme.{t}}
    (j : U ⟶ T) (hj : IsOpenImmersion j) : PreservesFiniteColimits (cbcOpenShriek d j hj) := by
  sorry

/-- The exact extension functor applied termwise and descended to the derived category.
Source: Tag 03DJ (blueprint: lem-cbc-completed-extension-zero-comparison). -/
def cbcDerivedOpenShriek {U T : Scheme.{t}} (j : U ⟶ T) (hj : IsOpenImmersion j) :
    DerivedCategory (pbcModules U (pbcAdicCompletion U d)) ⥤
      DerivedCategory (pbcModules T (pbcAdicCompletion T d)) :=
  (cbcOpenShriek d j hj).mapDerivedCategory

/-- Composition of a pro-etale arrow with the open immersion.
Source: Tag 098K (blueprint: lem-cbc-completed-extension-zero-comparison). -/
def cbcOpenSiteFunctor {U T : Scheme.{t}} (j : U ⟶ T) (hj : IsOpenImmersion j) :
    U.ProEt ⥤ T.ProEt :=
  letI := hj
  MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale j)

/-- Open-site composition is continuous.
Source: Tag 098K (blueprint: lem-cbc-completed-extension-zero-comparison).
Proof: its maps are unchanged scheme arrows and hence preserve the finite-affine
fpqc covering condition. This is the inverse side of slice-site localization. -/
@[instance] theorem cbcOpenSiteFunctor_continuous {U T : Scheme.{t}}
    (j : U ⟶ T) (hj : IsOpenImmersion j) :
    (cbcOpenSiteFunctor j hj).IsContinuous (ProEt.topology U) (ProEt.topology T) := by
  sorry

/-- The finite restriction coefficient map identifies the very same local functions.
Source: Tag 098K (blueprint: lem-cbc-completed-extension-zero-comparison).
Proof: the composition functor keeps the underlying scheme. Sheafify the identity
on functions on connected components. Localization commutes with sheafification;
the sheafification unit determines the resulting map uniquely. -/
theorem cbcFiniteRestrictionMap_exists {U T : Scheme.{t}}
    (j : U ⟶ T) (hj : IsOpenImmersion j) (n : ℕ) :
    ∃! φ : (reductionCoefficient U d n) ⟶
        ((cbcOpenSiteFunctor j hj).sheafPushforwardContinuous CommRingCat.{t + 1}
          (ProEt.topology U) (ProEt.topology T)).obj ((reductionCoefficient T d n)),
      ∀ V : U.ProEtᵒᵖ,
        (toSheafify (ProEt.topology U)
          (AdicCoefficients.functionPresheaf U (A ⧸ d.ideal ^ (n + 1)))).app V ≫
            φ.hom.app V =
        (toSheafify (ProEt.topology T)
          (AdicCoefficients.functionPresheaf T (A ⧸ d.ideal ^ (n + 1)))).app
            ((cbcOpenSiteFunctor j hj).op.obj V) := by
  sorry

/-- The finite restriction map fixed by local functions.
Source: Tag 098K (blueprint: lem-cbc-completed-extension-zero-comparison). -/
def cbcFiniteRestrictionMap {U T : Scheme.{t}}
    (j : U ⟶ T) (hj : IsOpenImmersion j) (n : ℕ) :=
  (cbcFiniteRestrictionMap_exists d j hj n).exists.choose

/-- The completed restriction map is fixed by its finite projections.
Source: Tags 098K, 099N (blueprint: lem-cbc-completed-extension-zero-comparison).
Proof: restriction computes sections and commutes with limits. The finite maps
are compatible with every quotient transition, so their limit is the uniquely
specified map. This is an isomorphism because all finite slice maps are. -/
theorem cbcCompletedRestrictionMap_exists {U T : Scheme.{t}}
    (j : U ⟶ T) (hj : IsOpenImmersion j) :
    ∃! φ : (completedReductionCoefficient U d) ⟶
        ((cbcOpenSiteFunctor j hj).sheafPushforwardContinuous CommRingCat.{t + 1}
          (ProEt.topology U) (ProEt.topology T)).obj ((completedReductionCoefficient T d)),
      ∀ n : ℕ, φ ≫
        ((cbcOpenSiteFunctor j hj).sheafPushforwardContinuous CommRingCat.{t + 1}
          (ProEt.topology U) (ProEt.topology T)).map ((completedReductionProjection T d n)) =
        (completedReductionProjection U d n) ≫ cbcFiniteRestrictionMap d j hj n := by
  sorry

/-- The canonical inverse of the open's completed coefficient identification.
Source: Tag 098K (blueprint: lem-cbc-completed-extension-zero-comparison). -/
def cbcCompletedRestrictionMap {U T : Scheme.{t}}
    (j : U ⟶ T) (hj : IsOpenImmersion j) :=
  (cbcCompletedRestrictionMap_exists d j hj).exists.choose

/-- Actual restriction of completed-ring modules to the open pro-etale site.
Source: Tag 03DI (blueprint: lem-cbc-completed-extension-zero-comparison). -/
def cbcOpenRestriction {U T : Scheme.{t}} (j : U ⟶ T) (hj : IsOpenImmersion j) :
    (pbcModules T (pbcAdicCompletion T d)) ⥤ (pbcModules U (pbcAdicCompletion U d)) :=
  SheafOfModules.pushforward.{t + 1} (F := cbcOpenSiteFunctor j hj)
    (J := ProEt.topology U) (K := ProEt.topology T)
    ((sheafCompose (ProEt.topology U) (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).map
      (cbcCompletedRestrictionMap d j hj))

/-- The slice object corresponding to a pro-etale object of the open.
Source: Tag 098K (blueprint: lem-cbc-completed-extension-zero-comparison). -/
def cbcOpenSliceObject {U T : Scheme.{t}} (j : U ⟶ T) (hj : IsOpenImmersion j)
    (V : U.ProEt) : Over (cbcOpenObject j hj) :=
  Over.mk (@id ((cbcOpenSiteFunctor j hj).obj V ⟶ cbcOpenObject j hj)
    (MorphismProperty.Over.homMk V.hom rfl))

open Classical in
/-- The extension/restriction adjunction is fixed by the direct-sum generator formula.
Source: Tag 03DI (blueprint: lem-cbc-completed-extension-zero-comparison).
Proof: the sheafification Hom equivalence identifies a map out of j!M with a
presheaf map out of its direct sum. Restricting this map to the summand indexed
by the structure arrow V to U gives exactly the displayed formula. Conversely,
apply a restriction map to each such summand and use the direct-sum universal
property. These operations are inverse, natural, and linear by the coefficient
identifications. The formula fixes the Hom equivalence, hence the adjunction. -/
theorem cbcOpenAdjunction_exists {U T : Scheme.{t}}
    (j : U ⟶ T) (hj : IsOpenImmersion j) :
    ∃! adj : cbcOpenShriek d j hj ⊣ cbcOpenRestriction d j hj,
      ∀ (M : (pbcModules U (pbcAdicCompletion U d))) (N : (pbcModules T (pbcAdicCompletion T d)))
        (α : (cbcOpenShriek d j hj).obj M ⟶ N) (V : U.ProEt)
        (x : M.val.obj (op V)),
        ((adj.homEquiv M N) α).val.app (op V) x =
          (PresheafOfModules.sheafificationHomEquiv.{t + 1}
            (𝟙 (reductionModuleRing T (completedReductionCoefficient T d)).obj) α).app
            (op ((cbcOpenSiteFunctor j hj).obj V))
              (DirectSum.of _ (cbcOpenSliceObject j hj V).hom x) := by
  sorry

/-- The generator-normalized extension/restriction adjunction.
Source: Tag 03DI (blueprint: lem-cbc-completed-extension-zero-comparison). -/
def cbcOpenAdjunction {U T : Scheme.{t}} (j : U ⟶ T) (hj : IsOpenImmersion j) :=
  (cbcOpenAdjunction_exists d j hj).exists.choose

variable {U' U X' X : Scheme.{t}} {gU : U' ⟶ U} {j' : U' ⟶ X'}
  {j : U ⟶ X} {g : X' ⟶ X} (sq : AlgebraicGeometry.OpenImmersionSquare gU j' j g)

/-- The right-adjoint exchange is uniquely fixed by restriction along the canonical
cartesian comparison of pro-etale objects, with its actual completed scalar action.
Source: blueprint order 1587, Step 7 (blueprint: lem-cbc-completed-extension-zero-comparison).
Proof: for V over U, the cartesian comparison from V times_U U' to V times_X X'
is an isomorphism. Restrict sections of M along it. The finite coefficient
projection equations show scalar compatibility, and pass to the completed limit.
Naturality is functoriality of restriction. Equality on every section proves uniqueness. -/
theorem cbcRightExchange_exists :
    ∃! γ : cbcCompletedModuleDirectImage d g ⋙ cbcOpenRestriction d j sq.isOpenImmersion ⟶
        cbcOpenRestriction d j' sq.isOpenImmersion' ⋙ cbcCompletedModuleDirectImage d gU,
      ∀ (M : (pbcModules X' (pbcAdicCompletion X' d))) (V : U.ProEtᵒᵖ)
        (x : ((cbcCompletedModuleDirectImage d g ⋙
          cbcOpenRestriction d j sq.isOpenImmersion).obj M).val.obj V),
        (γ.app M).val.app V x =
          M.val.map
            ((MorphismProperty.Over.pullbackMapComparison
              (cbcOpenWeaklyEtale j sq.isOpenImmersion)
              (cbcOpenWeaklyEtale j' sq.isOpenImmersion')
              sq.toCommSq).app V.unop).op x := by
  sorry

/-- The cartesian comparison on actual section modules.
Source: blueprint order 1587 (blueprint: lem-cbc-completed-extension-zero-comparison). -/
def cbcRightExchange := (cbcRightExchange_exists d sq).exists.choose

/-- The canonical underived inverse exchange is the adjoint conjugate of right exchange.
Source: blueprint order 1587 (blueprint: lem-cbc-completed-extension-zero-comparison). -/
def cbcUnderivedInverseExchange :
    completedModulePullback gU d ⋙ cbcOpenShriek d j' sq.isOpenImmersion' ⟶
      cbcOpenShriek d j sq.isOpenImmersion ⋙ completedModulePullback g d :=
  (conjugateEquiv
    ((cbcOpenAdjunction d j sq.isOpenImmersion).comp
      (cbcModulePullbackAdjunction d g))
    ((cbcModulePullbackAdjunction d gU).comp
      (cbcOpenAdjunction d j' sq.isOpenImmersion'))).symm (cbcRightExchange d sq)

/-- Ordinary open base change is invertible for the cartesian square.
Source: blueprint order 1587, Step 7 (blueprint: lem-cbc-completed-extension-zero-comparison).
Proof: right exchange restricts along the cartesian comparison isomorphism, hence
is invertible. Its adjoint conjugate is invertible. This is the usual finite
coefficient open base-change map, with completed coefficient scalar actions. -/
@[instance] theorem cbcUnderivedInverseExchange_isIso :
    IsIso (cbcUnderivedInverseExchange d sq) := by
  sorry

/-- The derived inverse exchange is fixed by the actual underived exchange on
K-flat representatives and the universal pullback counits.
Source: blueprint order 1587, Steps 2, 3, 7
(blueprint: lem-cbc-completed-extension-zero-comparison).
Proof: extension by zero is exact and commutes with tensor by restriction of the
other factor. Thus it preserves K-flat representatives; it also preserves flat
terms. On these representatives derive the underived adjoint mate termwise.
Both comparison maps in the equation are invertible. Resolve every object by
K-flat complexes, and descend along quasi-isomorphisms. Naturality and uniqueness
follow from the universal left-derived property and the displayed equation. -/
theorem cbcDerivedInverseExchange_exists :
    ∃! α : completedOrdinaryPullback gU d ⋙ cbcDerivedOpenShriek d j' sq.isOpenImmersion' ⟶
        cbcDerivedOpenShriek d j sq.isOpenImmersion ⋙ completedOrdinaryPullback g d,
      ∀ (P : CochainComplex ((pbcModules U (pbcAdicCompletion U d))) ℤ)
        (_hP : CochainComplex.IsKFlatIndependentCoefficients (R := pbcAdicCompletion U d) P),
        α.app (DerivedCategory.Q.obj P) ≫
          (completedOrdinaryPullback g d).map
            ((cbcOpenShriek d j sq.isOpenImmersion).mapDerivedCategoryFactors.hom.app P) ≫
          completedOrdinaryPullbackComplexCounit g d
            (((cbcOpenShriek d j sq.isOpenImmersion).mapHomologicalComplex (.up ℤ)).obj P) =
        (cbcDerivedOpenShriek d j' sq.isOpenImmersion').map
          (completedOrdinaryPullbackComplexCounit gU d P) ≫
          (cbcOpenShriek d j' sq.isOpenImmersion').mapDerivedCategoryFactors.hom.app
            (((completedModulePullback gU d).mapHomologicalComplex (.up ℤ)).obj P) ≫
          DerivedCategory.Q.map
            (((cbcUnderivedInverseExchange d sq).mapHomologicalComplex (.up ℤ)).app P) := by
  sorry

/-- The canonical derived inverse exchange.
Source: blueprint order 1587 (blueprint: lem-cbc-completed-extension-zero-comparison). -/
def cbcDerivedInverseExchange := (cbcDerivedInverseExchange_exists d sq).exists.choose

/-- The derived mate remains an isomorphism.
Source: blueprint order 1587, Step 7 (blueprint: lem-cbc-completed-extension-zero-comparison).
Proof: on each K-flat representative the normalized derived exchange is a
composition of invertible counits and the termwise underived base-change
isomorphism. Every derived object has such a representative; hence every
component is an isomorphism, so the natural transformation is an isomorphism. -/
@[instance] theorem cbcDerivedInverseExchange_isIso :
    IsIso (cbcDerivedInverseExchange d sq) := by
  sorry

/-- Ordinary derived exchange in the direction used by the completed comparison.
Source: blueprint order 1587 (blueprint: lem-cbc-completed-extension-zero-comparison). -/
def cbcOrdinaryExchange :
    cbcDerivedOpenShriek d j sq.isOpenImmersion ⋙ completedOrdinaryPullback g d ⟶
      completedOrdinaryPullback gU d ⋙ cbcDerivedOpenShriek d j' sq.isOpenImmersion' :=
  inv (cbcDerivedInverseExchange d sq)

/-- The intrinsic complete-object predicate, using any finite generating tuple of I.
Source: blueprint order 1587 (blueprint: lem-cbc-completed-extension-zero-comparison). -/
def cbcCompleteProperty (T : Scheme.{t}) (r : ℕ) (a : Fin r → A)
    (ha : Ideal.span (Set.range a) = d.ideal) :
    ObjectProperty (DerivedCategory ((pbcModules T (pbcAdicCompletion T d)))) :=
  fun K ↦ IsDerivedCompleteIntrinsic T d r a ha K
    (DerivedCategory.Q.objPreimage K) (DerivedCategory.Q.objObjPreimageIso K)

/-- Extension by zero along a quasi-compact open immersion preserves intrinsic
derived completeness. The completed base-change map is the unique natural map
compatible with ordinary base change and the specified completion units. It is
an isomorphism, and both sides are derived complete.

Source: blueprint order 1587, node lem-cbc-completed-extension-zero-comparison;
Stacks Tags 03DI, 09BP, 099N
(blueprint: lem-cbc-completed-extension-zero-comparison).

Proof plan: identify completed coefficients on the two ringed slice sites by
the projection-normalized localization maps. Exact extension by zero commutes
with tensor after restriction, preserving K-flat complexes and their strict
quotient reduction towers, including every transition. For a quasi-compact open,
recollement expresses j! as the kernel of j* to i*i^-1j*. Both direct images
preserve products, and closed inverse image preserves products on the pro-etale
site; thus j! preserves all products, including the empty one. Exact countable
products identify Rlim with the signed Roos fibre, naturally for maps of strict
towers. Applying j! to that fibre gives its canonical Rlim comparison, compatible
with structure maps. Apply this first to the finite free Koszul tower and its
unit: j!K is complete when K is. Finite coefficient base-change is the inverse
adjoint mate above; its local-section formulas commute with quotient transitions.
Apply functorial Rlim to those strict tower maps and use the j'! Rlim comparison.
This constructs the displayed completed map. It commutes with ordinary-to-completed
units by the quotient-unit normalization. Source and target are complete, so the
completion universal property proves uniqueness. The finite maps and the Rlim
comparison are isomorphisms; so is the completed map. Completeness of completed
pullback and the first assertion for j' give completeness of both sides. -/
theorem cbcCompletedExchange_exists [QuasiCompact j]
    (r : ℕ) (a : Fin r → A) (ha : Ideal.span (Set.range a) = d.ideal) :
    ∃! β : (cbcCompleteProperty d U r a ha).ι ⋙
        cbcDerivedOpenShriek d j sq.isOpenImmersion ⋙ cbcCompletedPullback d g ⟶
      (cbcCompleteProperty d U r a ha).ι ⋙ cbcCompletedPullback d gU ⋙
        cbcDerivedOpenShriek d j' sq.isOpenImmersion',
      ∀ K : (cbcCompleteProperty d U r a ha).FullSubcategory,
        (cbcCompletedPullbackComparison d g).app
            ((cbcDerivedOpenShriek d j sq.isOpenImmersion).obj K.obj) ≫ β.app K =
          (cbcOrdinaryExchange d sq).app K.obj ≫
            (cbcDerivedOpenShriek d j' sq.isOpenImmersion').map
              ((cbcCompletedPullbackComparison d gU).app K.obj) := by
  sorry

/-- The canonical completed base-change map, natural on the full complete subcategory.
It is fixed by the ordinary adjoint mate and the strict quotient completion units.
Source: blueprint order 1587 (blueprint: lem-cbc-completed-extension-zero-comparison). -/
def cbcCompletedExchange [QuasiCompact j]
    (r : ℕ) (a : Fin r → A) (ha : Ideal.span (Set.range a) = d.ideal) :=
  (cbcCompletedExchange_exists d sq r a ha).exists.choose

/-- Completed extension by zero commutes with pullback, naturally in complete K.
It preserves completeness and both sides of the canonical exchange are complete.
Source: blueprint order 1587; Tags 09BP, 099N
(blueprint: lem-cbc-completed-extension-zero-comparison).
Proof: exact extension by zero commutes with tensor after restricting the other
factor, hence with strict finite reduction including quotient transitions.
Quasi-compactness and ringed open/closed recollement give product preservation
by expressing extension by zero as the kernel of two product-preserving functors.
Exact countable products identify Rlim with the functorial signed Roos fibre;
therefore extension by zero commutes with that Rlim and its structure maps.
Apply this to the Koszul tower and its unit to obtain preservation of intrinsic
completeness. Apply it to the pulled strict quotient tower and the finite
coefficient adjoint-mate base-change isomorphisms to obtain a natural isomorphism.
Its quotient units agree with the specified ordinary-to-completed comparison,
so uniqueness in cbcCompletedExchange_exists identifies it with the displayed
canonical map. Completed pullback is complete; applying completeness preservation
to the base-changed quasi-compact open gives completeness of the second side. -/
theorem completedExtensionZeroComparison [QuasiCompact j]
    (r : ℕ) (a : Fin r → A) (ha : Ideal.span (Set.range a) = d.ideal) :
    IsIso (cbcCompletedExchange d sq r a ha) ∧
      (∀ K : (cbcCompleteProperty d U r a ha).FullSubcategory,
        cbcCompleteProperty d X r a ha
            ((cbcDerivedOpenShriek d j sq.isOpenImmersion).obj K.obj) ∧
          cbcCompleteProperty d X' r a ha
            ((cbcCompletedPullback d g).obj
              ((cbcDerivedOpenShriek d j sq.isOpenImmersion).obj K.obj)) ∧
          cbcCompleteProperty d X' r a ha
            ((cbcDerivedOpenShriek d j' sq.isOpenImmersion').obj
              ((cbcCompletedPullback d gU).obj K.obj))) := by
  sorry

end AlgebraicGeometry.Scheme
