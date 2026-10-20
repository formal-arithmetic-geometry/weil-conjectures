/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q96
-/
module

public import Sheaf.Paper.SfIntegralConstructible
public import Sheaf.AlgebraicGeometry.ProEtaleCohomologicalSupport
public import Sheaf.Paper.IntrinsicFiniteTorsionConstructibility
public import Sheaf.Paper.SfDerivedComplete
public import Sheaf.Paper.SfRationalizationKaroubi
public import Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients
public import Sheaf.Paper.SfDerivedDirectImage
public import Sheaf.AlgebraicGeometry.ProEtaleConstantDerivedDirectImage
public import Sheaf.Paper.SfIntegralReductionTower
public import Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Sheaf.AlgebraicGeometry.OrdinaryDerivedOpenClosedAdjunctions
import Sheaf.AlgebraicGeometry.ProEtaleClosedEssentialImage
import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
import Sheaf.AlgebraicGeometry.ProEtaleIntrinsicClosedAmbient
import Sheaf.AlgebraicGeometry.ProfiniteCoefficientInverseImage
import Sheaf.AlgebraicGeometry.SfIntrinsicCompactSupport
import Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition
import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
import Sheaf.Paper.AdicCoefficientDatum
import Sheaf.Paper.CompletedCoefficientPushforwardComparison
import Sheaf.Paper.CompletedDirectImageLimits
import Sheaf.Paper.ConstantCompletionEquivalence
import Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients
import Sheaf.Paper.FiniteDirectImageComposition
import Sheaf.Paper.FiniteFreeCompletedScalarComparison
import Sheaf.Paper.PbcRoosTriangle
import Sheaf.Paper.PbcScalarExtension
import Sheaf.Paper.QcqsCompactSupportRealization
import Sheaf.Paper.SfCommonStageDirectImage
import Sheaf.Paper.SfIntegralConstructibleLinear
import Sheaf.Paper.SfIntegralDirectImageConstructible
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ClosedUpperShriek
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.ClosedImmersion
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.ClosedImmersion

/-!
# Closed direct image is fully faithful at every coefficient stage

Source: Weil blueprint, sec-smooth-purity/sk-prop-sf-closed-unit,
prop-sf-closed-unit-all-stages, order 1861
(blueprint: prop-sf-closed-unit-all-stages).

The conclusion includes existence of the restricted functors. The comparison squares
identify their object and morphism maps with the recorded ambient direct images and
with scalar localization. At algebraically closed coefficients the comparison is on
every finite-field inclusion, with the scalar cocycle and change-of-stage equations,
hence on every common-stage representative.
No direct-image functor is an unconstrained hypothesis.
-/

@[expose] public section
set_option autoImplicit false

universe u v

open CategoryTheory AlgebraicGeometry

namespace WeilConjectures

/-- A presentation of the restrictions of the specified direct image at a fixed
finite coefficient extension. The finite and integral squares are comparisons with
the recorded ambient functors, not merely assertions of their source and target.
The rational square and localized linearity specify scalar localization of the
integral restriction, including its action on every tensor Hom group. Presentations
are allowed up to natural isomorphism, as are the derived functors themselves.

Source: Weil blueprint, order 1861, finite, integral and rational stages
(blueprint: prop-sf-closed-unit-all-stages). -/
structure ClosedDirectImageCoefficientStages
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {Z X : Scheme.{u}} (i : Z ⟶ X) where
  /-- The finite-level restriction, at every positive exponent. -/
  finiteStar : ∀ (n : ℕ) (hn : 1 ≤ n),
    (Scheme.intrinsicFiniteTorsionConstructible l E n hn Z).FullSubcategory ⥤
      (Scheme.intrinsicFiniteTorsionConstructible l E n hn X).FullSubcategory
  /-- The finite functor is the restriction of the actual derived image along i. -/
  finiteComparison : ∀ (n : ℕ) (hn : 1 ≤ n),
    finiteStar n hn ⋙ (Scheme.intrinsicFiniteTorsionConstructible l E n hn X).ι ≅
      (Scheme.intrinsicFiniteTorsionConstructible l E n hn Z).ι ⋙
        Scheme.proEtaleConstantDerivedDirectImage i (Padic.coefficientExtensionRing l E n)
  /-- The integral restriction. -/
  integralStar : sfIntegralConstructibleCategory l E Z ⥤ sfIntegralConstructibleCategory l E X
  /-- Its ambient realization is the specified completed-coefficient derived image. -/
  integralComparison : integralStar ⋙ (sfIntegralConstructible l E X).ι ≅
    (sfIntegralConstructible l E Z).ι ⋙ sfCompletedDerivedDirectImage l E i
  /-- The raw rationalization of the integral restriction. -/
  rationalStar : sfRationalConstructibleCategory l E Z ⥤ sfRationalConstructibleCategory l E X
  /-- Additivity is needed to specify the action on arbitrary sums of pure tensors. -/
  rationalAdditive : rationalStar.Additive
  /-- The scalar factor is fixed, so a scalar-twisting functor is not allowed. -/
  rationalLinear : rationalStar.Linear
    (Localization.Away (Padic.coefficientExtensionUniformizer l E))
  /-- On integral generators the rational functor is precisely the integral image. -/
  rationalComparison : sfRationalConstructibleLocalization l E Z ⋙ rationalStar ≅
    integralStar ⋙ sfRationalConstructibleLocalization l E X

/-- Compatible presentations of the actual direct image at every coefficient field
and on the common-stage category. Each inclusion comparison is natural in every
finite-stage morphism. The scalar cocycle and the inclusion coherence fix its
compatibility with all canonical changes of stage.
Source: Weil blueprint, order 1861, algebraically closed stage
(blueprint: prop-sf-closed-unit-all-stages). -/
structure ClosedDirectImageStages
    (l : ℕ) [Fact l.Prime]
    (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    {Z X : Scheme.{u}} (i : Z ⟶ X) where
  /-- Restrictions of the actual ambient direct images, with their scalar localization. -/
  coefficient : ∀ (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E], ClosedDirectImageCoefficientStages l E i
  /-- The direct-image comparisons with the recorded finite scalar transitions. -/
  scalarComparison : ∀ {E L : AlgebraicallyClosedCoefficients.Index l Ω} (h : E ≤ L),
    (coefficient (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E)).rationalStar ⋙
        (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω X).T h ≅
      (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω Z).T h ⋙
        (coefficient (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L)).rationalStar
  /-- Pasting successive extensions agrees with their direct comparison. -/
  scalarCoherence : ∀ {E L M : AlgebraicallyClosedCoefficients.Index l Ω}
    (h : E ≤ L) (h' : L ≤ M)
    (K : GeneralAlgebraicallyClosedCoefficients.Stage l Ω Z E),
    ((GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω X).T h').map
        ((scalarComparison h).hom.app K) ≫
      (scalarComparison h').hom.app
        (((GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω Z).T h).obj K) ≫
      (coefficient (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω M)).rationalStar.map
        (((GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω Z).assoc h h').hom.app K) =
      ((GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω X).assoc h h').hom.app
          ((coefficient (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E)).rationalStar.obj
            K) ≫
        (scalarComparison (h.trans h')).hom.app K
  /-- The common-stage realization. -/
  algebraicallyClosedStar : generalAlgebraicallyClosedConstructibleCategory l Ω Z ⥤
    generalAlgebraicallyClosedConstructibleCategory l Ω X
  /-- On each finite-field inclusion this is the rationalized direct image along i. -/
  inclusionComparison : ∀ E : AlgebraicallyClosedCoefficients.Index l Ω,
    GeneralAlgebraicallyClosedCoefficients.inclusion (l := l) (Ω := Ω) (Y := Z) E ⋙
        algebraicallyClosedStar ≅
      (coefficient (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E)).rationalStar ⋙
        GeneralAlgebraicallyClosedCoefficients.inclusion (l := l) (Ω := Ω) (Y := X) E
  /-- The inclusion comparisons respect the canonical change-of-stage arrows. -/
  inclusionCoherence : ∀ {E L : AlgebraicallyClosedCoefficients.Index l Ω} (h : E ≤ L)
    (K : GeneralAlgebraicallyClosedCoefficients.Stage l Ω Z E),
    algebraicallyClosedStar.map
        (((GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω Z).transIso h).hom.app K) ≫
      (inclusionComparison E).hom.app K =
      (inclusionComparison L).hom.app
          (((GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω Z).T h).obj K) ≫
        (GeneralAlgebraicallyClosedCoefficients.inclusion (l := l) (Ω := Ω) (Y := X) L).map
          ((scalarComparison h).inv.app K) ≫
        ((GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω X).transIso h).hom.app
          ((coefficient (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E)).rationalStar.obj
            K)


/-- The actual closed direct images admit fully faithful restrictions at all four
stages. Existence of the comparison squares includes preservation of the relevant
constructible categories. At the algebraically closed stage the comparison is a
natural isomorphism on every finite coefficient stage, compatible with the
scalar comparisons and the canonical change-of-stage arrows.
The finite ambient right adjoint exists and its unit is invertible on every object,
without a boundedness or constructibility assumption. For each restricted functor,
the unit is invertible for every right adjoint whenever one exists.

Source: Weil blueprint, sec-smooth-purity/sk-prop-sf-closed-unit, order 1861
(blueprint: prop-sf-closed-unit-all-stages).

Proof (all assertions postponed at stage 2):
1. Finite type over a field makes X and Z Noetherian. Their complementary open
immersion is quasi-compact. A closed immersion is proper; its identity/open,
closed/proper compactification identifies Ri_! with Ri_* at every stage.
2. The open--closed recollement counit i^* Ri_* to id is invertible. Thus finite
ambient Ri_* is fully faithful. Closed direct image is exact. Extend a finite
constructible stratification of Z by the zero sheaf on its open complement; this
proves preservation and supplies finiteStar and finiteComparison.
3. Identify the completed-coefficient image with the strict finite-image tower
using the projection-normalized comparison. Integral constructibility and the
actual reduction comparisons give its integral restriction and integralComparison.
Apply Hom to the source and image Roos triangles. Scalar-extension/restriction
adjunction identifies the maps into finite terms with finite direct image on Hom.
The product maps are bijective. Exact five-term rows then give the integral Hom
bijection, transported through the natural completed/tower comparison.
4. Tensor the integral Hom map and its inverse with E. This gives the additive,
localized-linear rational restriction and rationalComparison; no Karoubi envelope
is introduced.
5. Use the canonical finite scalar-extension comparisons for direct image. Their
coherence lets the rational restrictions descend to the existing common-stage
category and gives the displayed inclusion comparisons, scalarCoherence and
inclusionCoherence. These equations identify the image of a representative with
the finite-stage direct image conjugated by the specified scalar comparisons.
At each common finite
field the Hom map is bijective. Apply its inverse to a representative; coherence
and injectivity make this independent of the chosen common field. Thus the
algebraically closed image is fully faithful.
6. For each right adjoint, postcomposition with its unit corresponds under the
adjunction to the fully faithful direct image on Hom. Yoneda makes the unit an
isomorphism, with no Full or Faithful premise. Finite ambient closed support gives
the right adjoint and the same unit assertion for all ambient objects, as in
prop-sf-closed-immersion-unit. -/
theorem closedUnitAllStages
    (k : Type u) [Field k]
    (l : ℕ) [Fact l.Prime] (hℓ : IsUnit (l : k))
    (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    {Z X : Scheme.{u}} [Z.Over (Spec (.of k))] [X.Over (Spec (.of k))]
    [IsSeparated (Z ↘ Spec (.of k))] [LocallyOfFiniteType (Z ↘ Spec (.of k))]
    [QuasiCompact (Z ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))]
    (i : Z ⟶ X) [i.IsOver (Spec (.of k))] [IsClosedImmersion i] :
    Nonempty (ClosedDirectImageStages l Ω i) ∧
    ∀ S : ClosedDirectImageStages l Ω i,
      (∀ (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E],
        (∀ (n : ℕ) (hn : 1 ≤ n),
          ((S.coefficient E).finiteStar n hn).Full ∧
            ((S.coefficient E).finiteStar n hn).Faithful) ∧
        ((S.coefficient E).integralStar.Full ∧
          (S.coefficient E).integralStar.Faithful) ∧
        ((S.coefficient E).rationalStar.Full ∧
          (S.coefficient E).rationalStar.Faithful) ∧
        (∀ (n : ℕ) (hn : 1 ≤ n)
          (G : (Scheme.intrinsicFiniteTorsionConstructible l E n hn X).FullSubcategory ⥤
            (Scheme.intrinsicFiniteTorsionConstructible l E n hn Z).FullSubcategory)
          (adj : (S.coefficient E).finiteStar n hn ⊣ G), ∀ Q, IsIso (adj.unit.app Q)) ∧
        (∀ (G : sfIntegralConstructibleCategory l E X ⥤
            sfIntegralConstructibleCategory l E Z)
          (adj : (S.coefficient E).integralStar ⊣ G), ∀ Q, IsIso (adj.unit.app Q)) ∧
        (∀ (G : sfRationalConstructibleCategory l E X ⥤
            sfRationalConstructibleCategory l E Z)
          (adj : (S.coefficient E).rationalStar ⊣ G), ∀ Q, IsIso (adj.unit.app Q)) ∧
        (∀ (n : ℕ) (_hn : 1 ≤ n),
          ∃ G : Scheme.proEtaleDerivedCategory X (Padic.coefficientExtensionRing l E n) ⥤
              Scheme.proEtaleDerivedCategory Z (Padic.coefficientExtensionRing l E n),
          ∃ adj : Scheme.proEtaleConstantDerivedDirectImage i
              (Padic.coefficientExtensionRing l E n) ⊣ G,
            ∀ Q, IsIso (adj.unit.app Q))) ∧
      (S.algebraicallyClosedStar.Full ∧ S.algebraicallyClosedStar.Faithful) ∧
      (∀ (G : generalAlgebraicallyClosedConstructibleCategory l Ω X ⥤
          generalAlgebraicallyClosedConstructibleCategory l Ω Z)
        (adj : S.algebraicallyClosedStar ⊣ G), ∀ Q, IsIso (adj.unit.app Q)) := by
  sorry

end WeilConjectures
