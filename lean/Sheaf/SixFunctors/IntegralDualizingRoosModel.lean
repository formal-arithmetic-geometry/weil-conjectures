/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Z6
-/
module

public import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
public import Sheaf.Paper.SfIntegralConstructible
public import Sheaf.Paper.SfDerivedComplete
public import Sheaf.Paper.NormalizedDVREffectivity
public import Sheaf.AlgebraicGeometry.CompactifiableOverField
public import Sheaf.AlgebraicGeometry.SfFiniteExceptionalInverseImage
public import Sheaf.Paper.FiniteTorAmplitude
public import Sheaf.AlgebraicGeometry.ProEtaleTorAmplitude
public import Sheaf.Paper.IntrinsicFiniteTorsionConstructibility
public import Sheaf.Paper.CompletedIntegralConstantMapOfUniverses
public import Sheaf.Paper.CompactSupportReductionTower
public import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitOfUniverses
public import Sheaf.Paper.CoefficientDuality
public import Sheaf.Paper.IntegralRationalQbarCompactSupport
public import Sheaf.Paper.FiniteCoefficientPoint
public import Sheaf.Paper.DirectImagesConstructible
public import WeilConjectures.Mathlib.Topology.KrullDimension

public import Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses
public import Sheaf.SixFunctors.FiniteDualizing

/-! # Strict Roos realization of the finite dualizing tower

The unchanged integral mapping-complex, compact-support, and limit constructions
are recorded here so that the finite bounds and mapping-limit steps can use the
same objects independently of the assembly theorem.

Source: current blueprint prop-coef-integral-dualizing, inverse-limit assertion
(blueprint: lem-coef-integral-dualizing-roos-model).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open SheafOfModules
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The published sheafification instance with both universes specified.
Source: blueprint order 1455, ordinary coefficient sheaves
(blueprint: prop-coef-integral-dualizing). -/
instance integralDualizingRingSheafify (Y : Scheme.{u}) :
    HasSheafify (ProEt.topology Y) CommRingCat.{u + 1} :=
  integralCoefficientRingSheafify.{u, u} Y

/-- The coefficient ring in the section universe, with only a carrier lift.
Source: blueprint order 2145, D(R) (blueprint: prop-coef-integral-dualizing). -/
abbrev integralDualizingCoefficients := ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E)

/-- The actual constant scalar map to sections of the completion.
Source: blueprint order 2145, global derived mapping complexes
(blueprint: prop-coef-integral-dualizing). -/
def integralDualizingScalar (Y : Scheme.{u}) (U : Y.ProEtᵒᵖ) :
    integralDualizingCoefficients l E →+*
      (completedIntegralCoefficientSheafUnrestricted l E Y).obj.obj U :=
  (((integralConstantToCompletionOfUniverses.{u, u} l E Y).hom.app U).hom).comp
    (((forget₂ CommRingCat.{u + 1} RingCat.{u + 1}).map
      ((toSheafify (D := CommRingCat.{u + 1}) (ProEt.topology Y)
        ((Functor.const Y.ProEtᵒᵖ).obj
          (CommRingCat.of (integralDualizingCoefficients l E)))).app U)).hom)

/-- Ordinary global sections with their actual R action, evaluated at the final object.
Source: blueprint order 2145, global derived mapping complexes
(blueprint: prop-coef-integral-dualizing). -/
def integralDualizingSections (Y : Scheme.{u}) :
    scalarReductionSource l E Y ⥤ ModuleCat.{u + 1} (integralDualizingCoefficients l E) :=
  SheafOfModules.evaluation _ (op (ProEt.mk (𝟙 Y))) ⋙
    ModuleCat.restrictScalars (integralDualizingScalar l E Y (op (ProEt.mk (𝟙 Y))))

/-- Evaluation and scalar restriction are additive, with the existing module structures.
Source: blueprint order 2145 (blueprint: prop-coef-integral-dualizing). -/
instance integralDualizingSections_additive (Y : Scheme.{u}) :
    (integralDualizingSections l E Y).Additive :=
  inferInstanceAs (SheafOfModules.forget _ ⋙
    PresheafOfModules.evaluation _ (op (ProEt.mk (𝟙 Y))) ⋙
    ModuleCat.restrictScalars (integralDualizingScalar l E Y (op (ProEt.mk (𝟙 Y))))).Additive

/-- Derived sections computed on the published K-injective replacements.
Source: blueprint order 2145, global derived mapping complexes
(blueprint: prop-coef-integral-dualizing). -/
def integralDualizingDerivedSections (Y : Scheme.{u}) :
    DerivedCategory (scalarReductionSource l E Y) ⥤
      DerivedCategory.{u + 1} (ModuleCat.{u + 1} (integralDualizingCoefficients l E)) :=
  letI := (grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{u + 1, u, u}
    (ProEt.topology Y) (completedIntegralCommRingSheafUnrestricted l E Y)).1
  (integralDualizingSections l E Y).rightDerivedFunctor

/-- Global derived Hom is RΓ of the recorded internal derived Hom.
Source: blueprint order 2145, definition of RHom_X
(blueprint: prop-coef-integral-dualizing). -/
def integralDualizingGlobalHom (Y : Scheme.{u})
    (M : DerivedCategory (scalarReductionSource l E Y)) :
    (sfIntegralConstructibleCategory l E Y)ᵒᵖ ⥤
      DerivedCategory.{u + 1} (ModuleCat.{u + 1} (integralDualizingCoefficients l E)) :=
  (sfIntegralConstructible l E Y).ι.op ⋙
    (Functor.curry.obj (derivedInternalHomOfUniverses.{u + 1, u, u}
      (ProEt.topology Y) (completedIntegralCommRingSheafUnrestricted l E Y))).flip.obj M ⋙
      integralDualizingDerivedSections l E Y

/-- Total right derived inverse limit on strict completed-coefficient towers.
The chosen functor has the right-derived universal property, so is unique up to the
unique comparison compatible with its derived unit. Its data is not an arbitrary cone.
Source: blueprint order 2145 and Stacks 0940--0941
(blueprint: prop-coef-integral-dualizing). -/
def integralDualizingLimit (Y : Scheme.{u}) :
    DerivedCategory (ℕᵒᵖ ⥤ scalarReductionSource l E Y) ⥤
      DerivedCategory (scalarReductionSource l E Y) :=
  (ringedStrictTowerHomotopyLimitOfUniverses.{u + 2, u + 1, u, u}
    (ProEt.topology Y) (completedIntegralCoefficientSheafUnrestricted l E Y)
    (completedIntegralCoefficient_mul_commUnrestricted l E Y)).choose

variable (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
  (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]

/-- The compactification supplied by Nagata over the given field.
Source: blueprint order 2145, a:X→s (blueprint: prop-coef-integral-dualizing). -/
def integralDualizingCompactification : Compactification (X ↘ Spec (.of D.k)) :=
  letI := hasCompactification_of_finiteType_over_field D.k X (Spec (.of D.k))
    (X ↘ Spec (.of D.k))
  HasCompactification.compactification (X ↘ Spec (.of D.k))

/-- The published coherent compact-support reduction functor, including all transitions
and all derived morphisms. Its evaluation and transition characterizations determine its
coherent tower up to isomorphism. Only normalized scalar structures from that construction
are used to extract the functor.
Source: blueprint order 2145 and Bhatt--Scholze 6.7.6
(blueprint: prop-coef-integral-dualizing). -/
def integralDualizingCompactTower :
    DerivedCategory (scalarReductionSource l E X) ⥤
      DerivedCategory (ℕᵒᵖ ⥤ scalarReductionSource l E (Spec (.of D.k))) := by
  let h := exists_compactSupportReductionTower l E D.k X (Spec (.of D.k))
    (X ↘ Spec (.of D.k)) (finiteFieldDatumPrimeUnit D l hl)
      (integralDualizingCompactification D X)
  letI := h.choose
  letI := h.choose_spec.choose
  exact h.choose_spec.choose_spec.2.2.choose

/-- Integral compact support followed by coefficient-point sections, with its map action.
Source: blueprint order 2145, C=Γ(s,Ra_!K)
(blueprint: prop-coef-integral-dualizing). -/
def integralDualizingCompactSections : sfIntegralConstructibleCategory l E X ⥤
    DerivedCategory.{u + 1} (ModuleCat.{u + 1} (integralDualizingCoefficients l E)) :=
  (sfIntegralConstructible l E X).ι ⋙ integralDualizingCompactTower l E D hl X ⋙
    integralDualizingLimit l E (Spec (.of D.k)) ⋙
      integralDualizingDerivedSections l E (Spec (.of D.k))

/-- A Roos limit presentation of the coherent normalized tower, with the actual counit
reductions and their compatibility with every quotient transition. This is a predicate on
real objects and maps, using the published countable products and effectivity comparisons.
Source: blueprint order 2145, first display and transition paragraph
(blueprint: prop-coef-integral-dualizing). -/
def IntegralDualizingLimitPresentation (T : NormalizedDVRTower l E X D hl)
    (M : DerivedCategory (scalarReductionSource l E X)) : Prop :=
  letI : HasCountableProducts (completedIntegralDerivedCategory l E X D hl) :=
    integralOperationsDerivedCountableProducts l E X
  ∃ (p : M ⟶ ∏ᶜ fun n : ℕ ↦ (normalizedDVRTowerEvaluation l E X D hl n).obj T.tower)
    (δ : (∏ᶜ fun n : ℕ ↦ (normalizedDVRTowerEvaluation l E X D hl n).obj T.tower) ⟶
      M⟦(1 : ℤ)⟧),
    IsDerivedLimitTriangle
      (fun n : ℕ ↦ (normalizedDVRTowerTransition l E X D hl n.le_succ).app T.tower)
        M p δ ∧
    (∀ n : ℕ, IsIso (normalizedDVRCounitComparison l E X D hl T M p n)) ∧
    ∀ (m n : ℕ) (h : n ≤ m),
      normalizedDVRCounitComparison l E X D hl T M p m ≫ T.tau h =
        normalizedDVRReductionTransition l E X D hl h M ≫
          (normalizedDVRRes l E X h).map
            (normalizedDVRCounitComparison l E X D hl T M p n)

/-- A strict normalized realization of the finite dualizing objects, together with
its Roos triangle for the published total derived inverse limit.

Source: current blueprint prop-coef-integral-dualizing, first proof paragraph,
its inverse-limit assertion and compatibility with lem-coef-finite-dualizing;
Stacks Tags 0940 and 0941 (blueprint: lem-coef-integral-dualizing-roos-model).

Proof: use the counit-defined finite comparisons and their unit and cocycle identities.
Their scalar adjuncts give the semilinear transitions. Choose a representative at level
one, then recursively represent each next transition by a roof whose backward arrow is
a quasi-isomorphism, retaining its forward chain map. Compose these chain maps for all
longer transitions and restrict to completed coefficients. This gives one strict tower,
its evaluation isomorphisms, and the required normalized DVR datum; normalization follows
from invertibility of each finite comparison by the scalar adjunction and Yoneda.
Resolve this strict tower by a functorial K-injective tower. The total derived limit
comes with the Roos triangle of its evaluated tower. Uniqueness of derived evaluation,
compatible with its localization comparison, identifies this evaluation with
normalizedDVRTowerEvaluation, including every transition. Transport its product and
triangle along that identification to obtain the displayed p and delta. This is the
same inverse-limit realization used in the current blueprint's reduction formula;
no constructibility or duality conclusion is asserted here. -/
theorem integralDualizing_roos_model (D : FiniteFieldDatum.{u})
    (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))] :
    ∃ (T : NormalizedDVRTower l E X D hl)
      (e : ∀ n : ℕ, T.M n ≅ integralDualizingFiniteTerm l E D X n),
      (∀ {m n : ℕ} (h : n ≤ m),
        T.tau h ≫ (normalizedDVRRes l E X h).map (e n).hom =
          (e m).hom ≫
            (Adjunction.ofIsRightAdjoint (normalizedDVRRes l E X h)).homEquiv _ _
              (integralDualizingFiniteComparison l E D X hl h)) ∧
      (letI : HasCountableProducts (completedIntegralDerivedCategory l E X D hl) :=
        integralOperationsDerivedCountableProducts l E X
       ∃ (p : (integralDualizingLimit l E X).obj T.tower ⟶
          ∏ᶜ fun n : ℕ ↦ (normalizedDVRTowerEvaluation l E X D hl n).obj T.tower)
         (δ : (∏ᶜ fun n : ℕ ↦
          (normalizedDVRTowerEvaluation l E X D hl n).obj T.tower) ⟶
          ((integralDualizingLimit l E X).obj T.tower)⟦(1 : ℤ)⟧),
         IsDerivedLimitTriangle
           (fun n : ℕ ↦ (normalizedDVRTowerTransition l E X D hl n.le_succ).app T.tower)
           ((integralDualizingLimit l E X).obj T.tower) p δ) := by sorry

end WeilConjectures
