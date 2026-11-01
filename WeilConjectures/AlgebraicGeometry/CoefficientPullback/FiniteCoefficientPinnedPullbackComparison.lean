/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.CoefficientPullback.FiniteCoefficientHeartPullback
public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteCoefficientHeartEncoding
public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteCoefficientHeartTensor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ModuleDerivedFunctorCompositorShifts
public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.CoefficientPullback.FiniteCoefficientPullbackEncoding
public import WeilConjectures.CategoryTheory.Adjunction.SixFunctors.FiniteCoefficientTensorPullbackEncoding
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperLowerStar
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
public import WeilConjectures.CategoryTheory.DerivedCategory.Shift.ExactFunctor

public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteCoefficientOperationEncoding
import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.CoefficientPullback.FiniteCoefficientHeartPullbackComposition
import WeilConjectures.CategoryTheory.InternalSectionTensorComparison
import WeilConjectures.CategoryTheory.Constant.ConstantScalarRestrictionTensorSupplement
import WeilConjectures.Algebra.Homology.RingIsomorphismTensorTransport
import WeilConjectures.AlgebraicGeometry.ModuleRingedComparison.ProEtaleSectionModuleFunctors
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
import WeilConjectures.CategoryTheory.Monoidal.Mod.Abelian
import WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian
import WeilConjectures.CategoryTheory.ModuleObjects.Symmetric
import WeilConjectures.CategoryTheory.ModuleObjects.ProEtaleCoefficients.ModuleEqualizerInternalHom
import WeilConjectures.CategoryTheory.Exact.ExactDerivedTensorSquare
import WeilConjectures.CategoryTheory.SixFunctors.Monoidal
import WeilConjectures.CategoryTheory.Derived.DerivedTensorRightExact
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Monoidal
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs

/-! # The specified finite-coefficient inverse-image comparison

Source: blueprint sec-smooth-purity, sk-prop-sp-purity-bc, opening finite-ring paragraph;
agent-written pinning of its coefficient comparison
(blueprint: lem-pur-finite-coefficient-pinned-pullback-comparison).

The comparison is the localization of the normalized heart mate, conjugated by the
canonical exact/total-derived comparisons. No existential pullback comparison is chosen.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.Functor
open scoped CategoryTheory.Obj TensorProduct

namespace AlgebraicGeometry.ProEtale.FiniteDiscreteOrdinary.CoefficientPullback

variable (A : Type u) [CommRing A] [Finite A]
  [TopologicalSpace A] [DiscreteTopology A] [IsTopologicalRing A]
variable (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj R] [IsCommMonObj R]

/-- Identification of the concrete section-action heart with the Encoding heart.
Source: the two Encoding normalization equations, clause (1)
(blueprint: lem-pur-finite-coefficient-pinned-pullback-comparison). -/
def pinnedHeartIdentification (e : Mon.mk R ≅ Mon.mk (coefficient A))
    (T : Scheme.{u}) (E : Encoding A T) :
    heart A R e T E ≅ coefficientHeartEncoding A e T E :=
  eqToIso (heart_eq A R e T E)

/-- The specified heart mate expressed using the Encoding heart functors.
Source: clause (1), transporting heartPull along the Encoding identifications
(blueprint: lem-pur-finite-coefficient-pinned-pullback-comparison). -/
def pinnedHeartPull (e : Mon.mk R ≅ Mon.mk (coefficient A))
    {X Y : Scheme.{u}} (f : X ⟶ Y) (EX : Encoding A X) (EY : Encoding A Y) :
    CondensedRing.upperStar R f ⋙ coefficientHeartEncoding A e X EX ≅
      coefficientHeartEncoding A e Y EY ⋙
        upperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) f :=
  isoWhiskerLeft _ (pinnedHeartIdentification A R e X EX).symm ≪≫
    heartPull A R e f EX EY ≪≫
    isoWhiskerRight (pinnedHeartIdentification A R e Y EY) _

/-- The canonical identification with the unchanged underlying additive sections.
Source: Encoding normalization, clause (2)
(blueprint: lem-pur-finite-coefficient-pinned-pullback-comparison). -/
def pinnedSectionsIso (e : Mon.mk R ≅ Mon.mk (coefficient A))
    (T : Scheme.{u}) (E : Encoding A T) :
    coefficientHeartEncoding A e T E ⋙ sheafCompose (Scheme.ProEt.topology T)
      (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} A)) Ab.{u + 1}) ≅
        Mod.forget (condensedRingObj R T) :=
  eqToIso (by
    unfold coefficientHeartEncoding
    rw [E.ordinary_functor, E.fixed_functor]
    rfl)

/-- Pure-pair normalization of a strong monoidal Encoding heart, on actual local sections.
The section identifications only expose the two Encoding normalization equations.
Source: clause (2), the section-tensor normalization
(blueprint: lem-pur-finite-coefficient-pinned-pullback-comparison). -/
def PinnedHeartNormalized (e : Mon.mk R ≅ Mon.mk (coefficient A))
    (T : Scheme.{u}) (E : Encoding A T)
    (m : (coefficientHeartEncoding A e T E).Monoidal) : Prop :=
  ∀ (M N : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj R T))
    (V : T.ProEtᵒᵖ) (x : M.X.obj.obj V) (y : N.X.obj.obj V),
    ((m.toLaxMonoidal.μ M N).hom.app V)
      (ConstantScalarRestriction.fixedPure (Scheme.ProEt.topology T) (ULift.{u + 1} A)
        ((coefficientHeartEncoding A e T E).obj M)
        ((coefficientHeartEncoding A e T E).obj N) V
        ((((pinnedSectionsIso A R e T E).inv.app M).hom.app V).hom x)
        ((((pinnedSectionsIso A R e T E).inv.app N).hom.app V).hom y)) =
      (((pinnedSectionsIso A R e T E).inv.app (M ⊗ N)).hom.app V).hom
        (InternalAbelianSheafModule.comparison_internalTmul (Scheme.ProEt.topology T)
          (condensedRingObj R T) M N V x y)

/-- Monoidality of the specified heart map for given strong structures on its vertices.
Source: clause (2), using the published geometric pullback structures
(blueprint: lem-pur-finite-coefficient-pinned-pullback-comparison). -/
def PinnedHeartMonoidal (e : Mon.mk R ≅ Mon.mk (coefficient A))
    {X Y : Scheme.{u}} (f : X ⟶ Y) (EX : Encoding A X) (EY : Encoding A Y)
    (mX : (coefficientHeartEncoding A e X EX).Monoidal)
    (mY : (coefficientHeartEncoding A e Y EY).Monoidal) : Prop :=
  letI := mX
  letI := mY
  letI : (CondensedRing.upperStar R f).Monoidal := CondensedRing.monoidal_upperStar R f
  letI : (upperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) f).Monoidal :=
    ProEtale.monoidal_upperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) f
  NatTrans.IsMonoidal (pinnedHeartPull A R e f EX EY).hom

/-- The canonical identification of the localized heart encoding with coefficientEncoding.
Source: clause (3), the termwise composite-functor comparison
(blueprint: lem-pur-finite-coefficient-pinned-pullback-comparison). -/
def pinnedHeartDerivedIso (e : Mon.mk R ≅ Mon.mk (coefficient A))
    (T : Scheme.{u}) (E : Encoding A T) :
    (coefficientHeartEncoding A e T E).mapDerivedCategory ≅ coefficientEncoding A e T E :=
  mapDerivedCategoryCompIso (Mod.comap (coefficientMap e.inv.hom T))
    (E.ordinary.functor ⋙ E.fixed.functor)

/-- The specified comparison: localize the heart mate and use the canonical comparisons
with the total derived inverse images on its two edges.
Source: clause (3), localization of heartPull
(blueprint: lem-pur-finite-coefficient-pinned-pullback-comparison). -/
def pinnedPullback (e : Mon.mk R ≅ Mon.mk (coefficient A))
    (E : ∀ T : Scheme.{u}, Encoding A T) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    pull R f ⋙ coefficientEncoding A e X (E X) ≅
      coefficientEncoding A e Y (E Y) ⋙ fixedPull A f :=
  isoWhiskerRight (CondensedRing.modulePullbackExactComparison R f) _ ≪≫
    isoWhiskerLeft _ (pinnedHeartDerivedIso A R e X (E X)).symm ≪≫
    mapDerivedCategorySquareIso (pinnedHeartPull A R e f (E X) (E Y)) ≪≫
    isoWhiskerRight (pinnedHeartDerivedIso A R e Y (E Y)) _ ≪≫
    isoWhiskerLeft _ (leftDerivedUpperStarIsoMapDerivedCategory
      (ModuleCat.{u + 1} (ULift.{u + 1} A)) f).symm

/-- The tensor comparison obtained from a given strong heart structure on K-flat
resolutions, transported along the canonical exact and coefficient-encoding comparisons.
Source: clause (3), derived tensor normalization
(blueprint: lem-pur-finite-coefficient-pinned-pullback-comparison). -/
def pinnedDerivedTensor (e : Mon.mk R ≅ Mon.mk (coefficient A))
    (T : Scheme.{u}) (E : Encoding A T)
    (m : (coefficientHeartEncoding A e T E).Monoidal) :
    (postcompose₂.obj (coefficientEncoding A e T E)).obj
      (CondensedRing.derivedTensor R T) ≅
    (((Functor.whiskeringLeft₂ _).obj (coefficientEncoding A e T E)).obj
      (coefficientEncoding A e T E)).obj
        (ProEtale.derivedTensor (ModuleCat.{u + 1} (ULift.{u + 1} A)) T) :=
  letI := m
  letI : (coefficientHeartEncoding A e T E).PreservesFlat :=
    Functor.preservesFlat_of_isEquivalence _
  let d : (coefficientHeartEncoding A e T E).leftDerivedFunctor ≅
      coefficientEncoding A e T E :=
    (coefficientHeartEncoding A e T E).leftDerivedFunctorIsoMapDerivedCategory ≪≫
      pinnedHeartDerivedIso A R e T E
  (postcompose₂.mapIso d.symm).app (CondensedRing.derivedTensor R T) ≪≫
    asIso (coefficientHeartEncoding A e T E).leftDerivedTensorComparison ≪≫
    ((((Functor.whiskeringLeft₂ _).obj
      (coefficientHeartEncoding A e T E).leftDerivedFunctor).mapIso d).app
        (ProEtale.derivedTensor (ModuleCat.{u + 1} (ULift.{u + 1} A)) T)) ≪≫
    (((Functor.whiskeringLeft₂ _).mapIso d).app (coefficientEncoding A e T E)).app
      (ProEtale.derivedTensor (ModuleCat.{u + 1} (ULift.{u + 1} A)) T)

/-- The integer-shift condition, with precisely termwise encoding shifts and the canonical
exact-comparison transport on the two total derived pullbacks.
Source: clause (4) and the specified module-derived shifts
(blueprint: lem-pur-finite-coefficient-pinned-pullback-comparison). -/
def PinnedPullbackCommShift (e : Mon.mk R ≅ Mon.mk (coefficient A))
    (E : ∀ T : Scheme.{u}, Encoding A T) {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop :=
  letI : (coefficientEncoding A e X (E X)).CommShift ℤ :=
    by unfold coefficientEncoding; infer_instance
  letI : (coefficientEncoding A e Y (E Y)).CommShift ℤ :=
    by unfold coefficientEncoding; infer_instance
  letI : (pull R f).CommShift ℤ := CondensedRing.modulePullbackDerivedCommShift R f
  letI : (fixedPull A f).CommShift ℤ := Functor.CommShift.ofIso
    (leftDerivedUpperStarIsoMapDerivedCategory
      (ModuleCat.{u + 1} (ULift.{u + 1} A)) f).symm ℤ
  NatTrans.CommShift (pinnedPullback A R e E f).hom ℤ

/-- Degree-zero comparison of the coefficient encoding, induced termwise.
Source: clause (4), exact-functor single-complex comparison
(blueprint: lem-pur-finite-coefficient-pinned-pullback-comparison). -/
def pinnedEncodingSingleIso (e : Mon.mk R ≅ Mon.mk (coefficient A))
    (T : Scheme.{u}) (E : Encoding A T) :
    DerivedCategory.singleFunctor _ 0 ⋙ coefficientEncoding A e T E ≅
      coefficientHeartEncoding A e T E ⋙ DerivedCategory.singleFunctor _ 0 :=
  isoWhiskerLeft _ (pinnedHeartDerivedIso A R e T E).symm ≪≫
    (coefficientHeartEncoding A e T E).mapDerivedCategorySingleFunctor 0

/-- The canonical degree-zero identification on the source of the specified comparison.
Source: clause (4), total/exact comparison and termwise single-complex identifications
(blueprint: lem-pur-finite-coefficient-pinned-pullback-comparison). -/
def pinnedSingleSourceIso (e : Mon.mk R ≅ Mon.mk (coefficient A))
    (E : ∀ T : Scheme.{u}, Encoding A T) {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj R Y)) :
    (coefficientEncoding A e X (E X)).obj
      ((pull R f).obj ((DerivedCategory.singleFunctor _ 0).obj M)) ≅
    (DerivedCategory.singleFunctor _ 0).obj
      ((coefficientHeartEncoding A e X (E X)).obj ((CondensedRing.upperStar R f).obj M)) :=
  (isoWhiskerRight (CondensedRing.modulePullbackExactComparison R f)
    (coefficientEncoding A e X (E X))).app _ ≪≫
    (coefficientEncoding A e X (E X)).mapIso
      (((CondensedRing.upperStar R f).mapDerivedCategorySingleFunctor 0).app M) ≪≫
    (pinnedEncodingSingleIso A R e X (E X)).app ((CondensedRing.upperStar R f).obj M)

/-- The canonical degree-zero identification on the target of the specified comparison.
Source: clause (4), exact ordinary pullback and termwise single-complex identifications
(blueprint: lem-pur-finite-coefficient-pinned-pullback-comparison). -/
def pinnedSingleTargetIso (e : Mon.mk R ≅ Mon.mk (coefficient A))
    (E : ∀ T : Scheme.{u}, Encoding A T) {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj R Y)) :
    (fixedPull A f).obj
      ((coefficientEncoding A e Y (E Y)).obj ((DerivedCategory.singleFunctor _ 0).obj M)) ≅
    (DerivedCategory.singleFunctor _ 0).obj
      ((upperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) f).obj
        ((coefficientHeartEncoding A e Y (E Y)).obj M)) :=
  (fixedPull A f).mapIso ((pinnedEncodingSingleIso A R e Y (E Y)).app M) ≪≫
    (leftDerivedUpperStarIsoMapDerivedCategory
      (ModuleCat.{u + 1} (ULift.{u + 1} A)) f).app _ ≪≫
    ((upperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) f).mapDerivedCategorySingleFunctor
      0).app ((coefficientHeartEncoding A e Y (E Y)).obj M)

end AlgebraicGeometry.ProEtale.FiniteDiscreteOrdinary.CoefficientPullback
