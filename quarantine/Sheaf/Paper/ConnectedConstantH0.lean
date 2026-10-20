/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NR
-/
module

public import Sheaf.Paper.CommonStageCompactWeilCohomology
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
public import Sheaf.Paper.PointReductionUnits
import Sheaf.CategoryTheory.Sites.RGammaDerivedLimit
import Sheaf.NumberTheory.Padics.AdicLimitFiniteModules
import Sheaf.Paper.ConstantTowerTransition
import Sheaf.Paper.FiniteMittagLeffler
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Mathlib.AlgebraicGeometry.Sites.ConstantSheaf
import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
import Sheaf.AlgebraicGeometry.ProEtaleModuleDirectImageLeftExact
import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
import Sheaf.Paper.CompletedIntegralConstantMapOfUniverses
import Sheaf.Paper.ConstantCoefficientScalarNormalization
import Sheaf.Paper.FiniteCoefficientPoint
import Sheaf.Paper.PointProEtaleSectionsExact
import Sheaf.Paper.SfCommonStageDirectImage
import Sheaf.Paper.SfRationalizationKaroubi

/-!
# Degree-zero constant cohomology on a connected scheme

Source: Bhatt--Scholze, Lemma 4.2.12, printed p. 30; Milne, Lectures on Etale
Cohomology, pp. 124 and 126; current blueprint, cohomological finiteness, Proof Step 7
(blueprint: lem-pod-connected-constant-h0).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory CategoryTheory.Limits Opposite SheafOfModules
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale
open scoped TensorProduct ChangeOfRings
namespace WeilConjectures

/-- The small-Hom field localization already used by rational coefficient cohomology.
Source: blueprint point coefficient categories and cohomological finiteness, Proof Step 7
(blueprint: lem-pod-connected-constant-h0). -/
noncomputable instance (priority := 2000) connectedH0FieldModuleDerived
    (F : Type v) [Field F] : HasDerivedCategory.{v} (ModuleCat.{v} F) :=
  HasDerivedCategory.ofIsGrothendieckAbelian _

/-- The small-Hom integral localization already used by integral coefficient cohomology.
Source: blueprint point coefficient categories and cohomological finiteness, Proof Step 7
(blueprint: lem-pod-connected-constant-h0). -/
noncomputable instance (priority := 2000) connectedH0IntegralModuleDerived
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] : HasDerivedCategory.{u + 1}
      (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E))) :=
  HasDerivedCategory.ofIsGrothendieckAbelian _

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (Y : Scheme.{u}) [Y.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of D.k))]
  [QuasiCompact (Y ↘ Spec (.of D.k))]


/-- The positive-level coefficient object, with the harmless predecessor cast removed.
Source: blueprint cohomological finiteness, Proof Step 7
(blueprint: lem-pod-connected-constant-h0). -/
def connectedFiniteCoefficientIso (n : ℕ) :
    finiteCohomologyCoefficient l E Y (n + 1) (by omega) ≅
      finiteConstantCoefficientObject l E Y n :=
  eqToIso (by simp [finiteCohomologyCoefficient])

/-- The H⁰ identification induced by the resolution augmentation and exact point sections.
Its target is the actual sections of the underived direct image of the regular sheaf.
Source: Stacks 05TD; blueprint cohomological finiteness, Proof Step 7
(blueprint: lem-pod-connected-constant-h0). -/
def connectedFiniteH0SectionsIso (n : ℕ) :
    finiteOrdinaryCohomology D l E Y (n + 1) (by omega)
        (finiteCohomologyCoefficient l E Y (n + 1) (by omega)) 0 ≅
      (pointFiniteSections D.k (Padic.coefficientExtensionRing l E (n + 1))).obj
        ((proEtaleConstantModuleDirectImage (Y ↘ Spec (.of D.k))
          (Padic.coefficientExtensionRing l E (n + 1))).obj
            (SheafOfModules.unit (integralCoefficientSheaf l E Y n))) := by
  letI :=
    (grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{u + 1, u, u + 1}
    (Scheme.ProEt.topology Y)
      (proEtaleConstantRing Y (Padic.coefficientExtensionRing l E (n + 1)))).1
  let F := proEtaleConstantModuleDirectImage (Y ↘ Spec (.of D.k))
    (Padic.coefficientExtensionRing l E (n + 1))
  let G := pointFiniteSections D.k (Padic.coefficientExtensionRing l E (n + 1))
  letI : PreservesFiniteLimits F :=
    (proEtaleConstantModuleDirectImage_additive_leftExact _ _).2
  exact (DerivedCategory.homologyFunctor _ 0).mapIso
      (G.mapDerivedCategory.{u + 2, u + 2}.mapIso
        (F.rightDerivedFunctor.mapIso (connectedFiniteCoefficientIso l E Y n))) ≪≫
    (G.mapDerivedCategoryHomologyFunctorIso.{_, _, _, _, u + 2, u + 2} 0).symm.app _ ≪≫
    G.mapIso (F.homologyRightDerivedFunctorObjSingleFunctorIso
      (SheafOfModules.unit (integralCoefficientSheaf l E Y n)) 0 ≪≫
        F.rightDerivedZeroIsoSelf.app _)

/-- The unit-section class: transport the ring section 1 through the augmentation H⁰ iso.
Source: Bhatt--Scholze 4.2.12; blueprint cohomological finiteness, Proof Step 7
(blueprint: lem-pod-connected-constant-h0). -/
def oneFinite (n : ℕ) :
    finiteOrdinaryCohomology D l E Y (n + 1)
      (by omega) (finiteCohomologyCoefficient l E Y (n + 1) (by omega)) 0 :=
  (connectedFiniteH0SectionsIso D l E Y n).inv
    (1 : (integralCoefficientSheaf l E Y n).obj.obj
      ((proEtaleBaseChange (Y ↘ Spec (.of D.k))).op.obj
        (op (Scheme.ProEt.mk (𝟙 (Spec (.of D.k)))))))

/-- The constant-section map, namely scalar multiplication by the actual unit-section class.
Source: Bhatt--Scholze 4.2.12; blueprint cohomological finiteness, Proof Step 7
(blueprint: lem-pod-connected-constant-h0). -/
def unitMap (n : ℕ) :
    ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1)) →ₗ[
      ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))]
    finiteOrdinaryCohomology D l E Y (n + 1)
      (by omega) (finiteCohomologyCoefficient l E Y (n + 1) (by omega)) 0 :=
  LinearMap.toSpanSingleton _ _ (oneFinite D l E Y n)

/-- The product used in precisely the Roos choice made by `integralImage`.
Source: blueprint derived direct image and cohomological finiteness, Proof Step 7
(blueprint: lem-pod-connected-constant-h0). -/
noncomputable instance connectedIntegralProduct :
    HasProduct (sfDirectImageTerm l E (Y ↘ Spec (.of D.k))
      (integralCohomologyCoefficient D l hl E Y).obj) := by
  letI : (Spec (.of D.k)).Over (Spec (.of D.k)) := ⟨𝟙 _⟩
  letI : (Y ↘ Spec (.of D.k)).IsOver (Spec (.of D.k)) := inferInstance
  exact (sfIntegralDirectImage_constructible D.k l (finiteFieldDatumPrimeUnit D l hl)
    E (Y ↘ Spec (.of D.k)) (integralCohomologyCoefficient D l hl E Y).obj
      (integralCohomologyCoefficient D l hl E Y).property).1.choose

/-- The specified Roos direct image underlying ordinary integral cohomology.
Source: blueprint ordinary cohomology and cohomological finiteness, Proof Step 7
(blueprint: lem-pod-connected-constant-h0). -/
def connectedIntegralImage : SfIntegralDirectImage l E (Y ↘ Spec (.of D.k))
    (integralCohomologyCoefficient D l hl E Y).obj := by
  letI : (Spec (.of D.k)).Over (Spec (.of D.k)) := ⟨𝟙 _⟩
  letI : (Y ↘ Spec (.of D.k)).IsOver (Spec (.of D.k)) := inferInstance
  exact (sfIntegralDirectImage_constructible D.k l (finiteFieldDatumPrimeUnit D l hl)
    E (Y ↘ Spec (.of D.k)) (integralCohomologyCoefficient D l hl E Y).obj
      (integralCohomologyCoefficient D l hl E Y).property).1.choose_spec.some

/-- Exact-localization transport of the recorded identity-on-sections square, retaining
ordinary cohomology's small-Hom integral localization and its finite localization.
Source: Stacks 07A6; blueprint cohomological finiteness, Proof Step 7
(blueprint: lem-pod-connected-constant-h0). -/
def connectedSectionsRestrictionIso (n : ℕ) :
    scalarReductionDerivedRestriction l E (Spec (.of D.k)) n ⋙
        pointFibreIntegralAmbient D l E ≅
      (pointFiniteSections D.k
        (Padic.coefficientExtensionRing l E (n + 1))).mapDerivedCategory.{u + 2, u + 2} ⋙
          (pointUnitIntegralRestriction l E n).mapDerivedCategory.{u + 2, u + 1} := by
  letI : (pointUnitIntegralRestriction l E n).Additive :=
    inferInstanceAs ((ModuleCat.restrictScalars.{u + 1, u + 1, u + 1}
      (pointReductionQuotient l E n)).Additive)
  letI : (pointFiniteSections D.k
      (Padic.coefficientExtensionRing l E (n + 1))).Additive :=
    pointFiniteSectionsAdditive _ _
  letI : (pointFiniteSections D.k (Padic.coefficientExtensionRing l E (n + 1)) ⋙
      pointUnitIntegralRestriction l E n).Additive := inferInstance
  letI : PreservesFiniteLimits
      (pointFiniteSections D.k (Padic.coefficientExtensionRing l E (n + 1)) ⋙
        pointUnitIntegralRestriction l E n) := comp_preservesFiniteLimits _ _
  letI : PreservesFiniteColimits
      (pointFiniteSections D.k (Padic.coefficientExtensionRing l E (n + 1)) ⋙
        pointUnitIntegralRestriction l E n) := comp_preservesFiniteColimits _ _
  letI : PreservesFiniteLimits
      (scalarReductionRestriction l E (Spec (.of D.k)) n ⋙ pointIntegralSections l E D.k) :=
    comp_preservesFiniteLimits _ _
  letI : PreservesFiniteColimits
      (scalarReductionRestriction l E (Spec (.of D.k)) n ⋙ pointIntegralSections l E D.k) :=
    comp_preservesFiniteColimits _ _
  exact (Functor.mapDerivedCategoryCompIso
    (scalarReductionRestriction l E (Spec (.of D.k)) n)
    (pointIntegralSections l E D.k)).symm ≪≫
      Functor.mapDerivedCategoryNatIso (pointUnitIntegralSectionsRestrictionIso D l E n) ≪≫
        Functor.mapDerivedCategoryCompIso
          (pointFiniteSections D.k (Padic.coefficientExtensionRing l E (n + 1)))
          (pointUnitIntegralRestriction l E n)

/-- Identify the nth restricted finite-image term with finite ordinary sections,
using the identity-on-sections restriction square and the actual finite reduction map.
Source: Stacks 07A6; blueprint cohomological finiteness, Proof Step 7
(blueprint: lem-pod-connected-constant-h0). -/
def connectedFiniteTowerIso (n : ℕ) :
    (pointFibreIntegralAmbient D l E).obj
        (sfDirectImageTerm l E (Y ↘ Spec (.of D.k))
          (integralCohomologyCoefficient D l hl E Y).obj n) ≅
      ((pointUnitIntegralRestriction l E n).mapDerivedCategory.{u + 2, u + 1}).obj
        (finiteOrdinarySections D l E Y (n + 1) (by omega)
          (finiteCohomologyCoefficient l E Y (n + 1) (by omega))) :=
  letI := ((integralConstantCoefficient_constructible l E Y D hl).2.2.2 n).1
  (connectedSectionsRestrictionIso D l E n).app _ ≪≫
    ((pointUnitIntegralRestriction l E n).mapDerivedCategory.{u + 2, u + 1}).mapIso
      ((pointFiniteSections D.k
        (Padic.coefficientExtensionRing l E (n + 1))).mapDerivedCategory.{u + 2, u + 2}.mapIso
          ((proEtaleConstantDerivedDirectImage (Y ↘ Spec (.of D.k))
            (Padic.coefficientExtensionRing l E (n + 1))).mapIso
              (asIso (constantCoefficientReductionMap l E Y n) ≪≫
                (connectedFiniteCoefficientIso l E Y n).symm)))

/-- The additive H⁰ identification of the restricted finite-image term.
Source: Stacks 07A6; blueprint cohomological finiteness, Proof Step 7
(blueprint: lem-pod-connected-constant-h0). -/
def connectedFiniteTowerH0Iso (n : ℕ) :
    (DerivedCategory.homologyFunctor.{u + 1} _ 0).obj
      ((pointFibreIntegralAmbient D l E).obj
        (sfDirectImageTerm l E (Y ↘ Spec (.of D.k))
          (integralCohomologyCoefficient D l hl E Y).obj n)) ≅
      (pointUnitIntegralRestriction l E n).obj
        (finiteOrdinaryCohomology D l E Y (n + 1) (by omega)
          (finiteCohomologyCoefficient l E Y (n + 1) (by omega)) 0) :=
  (DerivedCategory.homologyFunctor.{u + 1} _ 0).mapIso (connectedFiniteTowerIso D l hl E Y n) ≪≫
    (Functor.mapDerivedCategoryHomologyFunctorIso.{_, _, _, _, u + 2, u + 1}
      (pointUnitIntegralRestriction l E n) 0).symm.app _

/-- Coefficient reduction on H⁰, induced by `sfDirectImageTransition`.
Source: Stacks 0D6K; blueprint cohomological finiteness, Proof Step 7
(blueprint: lem-pod-connected-constant-h0). -/
def Q (n : ℕ) :
    (finiteOrdinaryCohomology D l E Y (n + 2)
      (by omega) (finiteCohomologyCoefficient l E Y (n + 2) (by omega)) 0) →+
    (finiteOrdinaryCohomology D l E Y (n + 1)
      (by omega) (finiteCohomologyCoefficient l E Y (n + 1) (by omega)) 0) :=
  (connectedFiniteTowerH0Iso D l hl E Y n).hom.hom.toAddMonoidHom.comp
    (((DerivedCategory.homologyFunctor.{u + 1} _ 0).map
      ((pointFibreIntegralAmbient D l E).map
        (sfDirectImageTransition l E (Y ↘ Spec (.of D.k))
          (integralCohomologyCoefficient D l hl E Y).obj n))).hom.toAddMonoidHom.comp
            (connectedFiniteTowerH0Iso D l hl E Y (n + 1)).inv.hom.toAddMonoidHom)

/-- The point fibre of the nth Roos projection, followed by finite-reduction comparison.
Source: Stacks 0D6K; blueprint cohomological finiteness, Proof Step 7
(blueprint: lem-pod-connected-constant-h0). -/
def P (n : ℕ) :
    integralOrdinaryCohomology D l hl E Y
      (integralCohomologyCoefficient D l hl E Y) 0 →+
    (finiteOrdinaryCohomology D l E Y (n + 1)
      (by omega) (finiteCohomologyCoefficient l E Y (n + 1) (by omega)) 0) :=
  (connectedFiniteTowerH0Iso D l hl E Y n).hom.hom.toAddMonoidHom.comp
    ((DerivedCategory.homologyFunctor.{u + 1} _ 0).map
      ((pointFibreIntegralAmbient D l E).map
        ((connectedIntegralImage D l hl E Y).projection ≫
          Pi.π (sfDirectImageTerm l E (Y ↘ Spec (.of D.k))
            (integralCohomologyCoefficient D l hl E Y).obj) n))).hom.toAddMonoidHom

/-- Compatible tuples under the actual coefficient reductions.
Source: Stacks 0D6K; blueprint cohomological finiteness, Proof Step 7
(blueprint: lem-pod-connected-constant-h0). -/
def connectedH0Tower :=
  Subtype (fun x : (∀ n : ℕ, finiteOrdinaryCohomology D l E Y (n + 1)
      (by omega) (finiteCohomologyCoefficient l E Y (n + 1) (by omega)) 0) ↦
    ∀ n : ℕ, Q D l hl E Y n (x (n + 1)) = x n)

/-- The actual projection maps are compatible with coefficient reduction.
Source: Stacks 0D6K; blueprint cohomological finiteness, Proof Step 7
(blueprint: lem-pod-connected-constant-h0).
Proof: successive projections of the Roos triangle have the prescribed transition.
Apply exact point sections and H⁰, then conjugate by the finite-reduction comparisons.
The adjacent conjugating isomorphisms cancel. -/
theorem connectedH0_projections_compatible (n : ℕ)
    (x : integralOrdinaryCohomology D l hl E Y
      (integralCohomologyCoefficient D l hl E Y) 0) :
    Q D l hl E Y n (P D l hl E Y (n + 1) x) = P D l hl E Y n x := by
  sorry

/-- The canonical projection-to-compatible-tuples map.
Source: Stacks 0D6K; blueprint cohomological finiteness, Proof Step 7
(blueprint: lem-pod-connected-constant-h0). -/
def limitTuple (x : integralOrdinaryCohomology D l hl E Y
      (integralCohomologyCoefficient D l hl E Y) 0) : connectedH0Tower D l hl E Y :=
  ⟨fun n ↦ P D l hl E Y n x, fun n ↦ connectedH0_projections_compatible D l hl E Y n x⟩

/-- The integral unit is uniquely specified by its finite unit-section classes.
Source: Milne pp. 124, 126; blueprint cohomological finiteness, Proof Step 7
(blueprint: lem-pod-connected-constant-h0).
Proof: finite coefficient reduction preserves unit sections by the augmentation and
coefficient-change square (`lem-pod-constant-tower-transition`). Thus the finite units
form a compatible tuple. Negative finite cohomology vanishes by left exactness.
The degree-zero Milnor sequence identifies integral H⁰ with the inverse limit, so this
tuple has a unique preimage. No finiteness of higher cohomology is used. -/
theorem connectedH0_integral_unit_existsUnique [ConnectedSpace Y] :
    ∃! x : integralOrdinaryCohomology D l hl E Y
        (integralCohomologyCoefficient D l hl E Y) 0,
      ∀ n : ℕ, P D l hl E Y n x = oneFinite D l E Y n := by
  sorry

/-- The integral unit class, determined uniquely by all its finite unit-section projections.
Source: Milne pp. 124, 126; blueprint cohomological finiteness, Proof Step 7
(blueprint: lem-pod-connected-constant-h0). -/
def oneIntegral [ConnectedSpace Y] :
    integralOrdinaryCohomology D l hl E Y
      (integralCohomologyCoefficient D l hl E Y) 0 :=
  (connectedH0_integral_unit_existsUnique D l hl E Y).exists.choose

/-- The recorded rational derived tensor comparison at the actual image of Y.
Source: blueprint point fibre, clause 3; cohomological finiteness, Proof Step 7
(blueprint: lem-pod-connected-constant-h0). -/
abbrev rationalTensorComparison :=
  pointRationalNormalization D l hl E
    (rationalImage D l hl E Y (rationalCohomologyCoefficient D l hl E Y))

/-- H⁰ of the canonical rational tensor comparison, with the standard exact tensor/H⁰
and coefficient-size identifications. Its source is E tensor integral H⁰, written with
ULift coefficients and then restricted along E ≃ ULift E; no cohomology is replaced.
Source: blueprint point fibre, clause 3; cohomological finiteness, Proof Step 7
(blueprint: lem-pod-connected-constant-h0). -/
def rationalH0TensorIso :
    (pointFibreCoefficientDown E).obj
      ((ModuleCat.extendScalars (pointIntegralToField l E)).obj
        (integralOrdinaryCohomology D l hl E Y
          (integralCohomologyCoefficient D l hl E Y) 0)) ≅
      (ModuleCat.uliftFunctor.{u + 1, u} E).obj
        (rationalOrdinaryCohomology D l hl E Y
          (rationalCohomologyCoefficient D l hl E Y) 0) :=
  (pointFibreCoefficientDown E).mapIso
      (Functor.mapDerivedCategoryHomologyFunctorIso.{_, _, _, _, u + 1, u + 1}
        (ModuleCat.extendScalars (pointIntegralToField l E)) 0 |>.app
          (integralOrdinarySections D l hl E Y
          (integralCohomologyCoefficient D l hl E Y)).obj) ≪≫
    (Functor.mapDerivedCategoryHomologyFunctorIso.{_, _, _, _, u + 1, u + 2}
      (pointFibreCoefficientDown E) 0).app _ ≪≫
    (DerivedCategory.homologyFunctor _ 0).mapIso
      ((pointFibreRationalDownIso D l E).app
        (integralImage D l hl E Y (integralCohomologyCoefficient D l hl E Y)).obj) ≪≫
    (DerivedCategory.homologyFunctor _ 0).mapIso (rationalTensorComparison D l hl E Y).symm ≪≫
    (Functor.mapDerivedCategoryHomologyFunctorIso.{_, _, _, _, u, u + 2}
      (ModuleCat.uliftFunctor.{u + 1, u} E) 0).symm.app _

/-- The E-linear H⁰ tensor map induced by `rationalTensorComparison`, after removing
only the carrier ULift of its target.
Source: blueprint point fibre, clause 3; cohomological finiteness, Proof Step 7
(blueprint: lem-pod-connected-constant-h0). -/
def rationalH0TensorMap :
    (pointFibreCoefficientDown E).obj
      ((ModuleCat.extendScalars (pointIntegralToField l E)).obj
        (integralOrdinaryCohomology D l hl E Y
          (integralCohomologyCoefficient D l hl E Y) 0)) →ₗ[E]
      rationalOrdinaryCohomology D l hl E Y
        (rationalCohomologyCoefficient D l hl E Y) 0 :=
  ULift.moduleEquiv.toLinearMap.comp (rationalH0TensorIso D l hl E Y).hom.hom

/-- The rational unit is the actual image of 1 tensor the integral unit.
The source orders the tensor factors oppositely; the tensor symmetry identifies them.
Source: blueprint cohomological finiteness, Proof Step 7
(blueprint: lem-pod-connected-constant-h0). -/
def oneRational [ConnectedSpace Y] :
    rationalOrdinaryCohomology D l hl E Y
      (rationalCohomologyCoefficient D l hl E Y) 0 :=
  rationalH0TensorMap D l hl E Y
    ((1 : ULift.{u + 1, u} E) ⊗ₜ[ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E),
      pointIntegralToField l E] oneIntegral D l hl E Y)

/-- Scalar multiplication by the rational unit class obtained from the actual tensor map.
Source: blueprint cohomological finiteness, Proof Step 7
(blueprint: lem-pod-connected-constant-h0). -/
def rationalScalarMap [ConnectedSpace Y] : E →ₗ[E]
    rationalOrdinaryCohomology D l hl E Y
      (rationalCohomologyCoefficient D l hl E Y) 0 :=
  LinearMap.toSpanSingleton _ _ (oneRational D l hl E Y)

/-- Constant cohomology with its specified unit, projection and tensor maps.
Source: Bhatt--Scholze 4.2.12; Milne pp. 124, 126; blueprint cohomological finiteness,
Proof Step 7 (blueprint: lem-pod-connected-constant-h0).
Proof: the augmentation identifies finite H⁰ with sections. The finite constant sheaf
is the sheaf of locally constant functions (Bhatt--Scholze 4.2.12), so nonempty
connectedness makes the constant-section map bijective. Coefficient naturality identifies
its reduction maps with quotient reduction and preserves 1. Exact sections at the point
commute with the derived limit (Stacks 0D6K); negative finite cohomology vanishes, so
Milnor gives bijectivity of the projection-to-tuples map. Completeness of O_E identifies
the coefficient inverse limit with O_E and the compatible finite units with its unit.
Finally exact fraction-field tensor commutes with H⁰; take H⁰ of the recorded rational
normalization at the actual integral image of Y. Its pure unit tensor is `oneRational`,
and scalar extension of the integral unit isomorphism proves the rational clause. -/
theorem connected_constant_h0 [IsSeparated (Y ↘ Spec (.of D.k))] [ConnectedSpace Y] :
    (∀ n, unitMap D l E Y n 1 = oneFinite D l E Y n) ∧
      (∀ n, Function.Bijective (unitMap D l E Y n)) ∧
      (∀ (n : ℕ) (x : integralOrdinaryCohomology D l hl E Y
          (integralCohomologyCoefficient D l hl E Y) 0),
        Q D l hl E Y n (P D l hl E Y (n + 1) x) = P D l hl E Y n x) ∧
      Function.Bijective (limitTuple D l hl E Y) ∧
      (∀ n, P D l hl E Y n (oneIntegral D l hl E Y) = oneFinite D l E Y n) ∧
      Function.Bijective (fun a : ULift.{u + 1, u}
        (Padic.coefficientExtensionIntegers l E) ↦ a • oneIntegral D l hl E Y) ∧
      Function.Bijective (rationalH0TensorMap D l hl E Y) ∧
      rationalH0TensorMap D l hl E Y
        ((1 : ULift.{u + 1, u} E) ⊗ₜ[ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E),
          pointIntegralToField l E] oneIntegral D l hl E Y) = oneRational D l hl E Y ∧
      rationalScalarMap D l hl E Y 1 = oneRational D l hl E Y ∧
      Function.Bijective (rationalScalarMap D l hl E Y) := by
  sorry

end WeilConjectures
