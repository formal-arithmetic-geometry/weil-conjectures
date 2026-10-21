/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NU
-/
module

public import Sheaf.Paper.LisseIntegralSmallCoefficients
public import Sheaf.Paper.CurveWeilMiddleExtension
public import Sheaf.Paper.CompletedCoefficientPresentationTransport
public import Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients
public import Sheaf.Paper.SfRationalizationKaroubi
public import Sheaf.Paper.FiniteCoefficientPoint

/-! # Completed realization of a lisse integral system

Source: Bhatt--Scholze, Propositions 6.8.4(1),(4), 6.8.14(2), Remark 6.8.15;
Weil II (1.1.1) b)--d)
(blueprint: def-a1-lisse-integral-completed-realization).

The realization is an actual inverse limit on the pro-etale site, placed in degree
zero. Coefficient presentation is changed by the recorded exact normalized transport.
Rationalization and inclusion retain the displayed finite coefficient stage. The
point cohomology uses the recorded integral fibre, with its canonical coefficient action.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (Ω : Type (u + 1)) [Field Ω]
  [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]

/-- Inverse limit of the finite-level pro-etale images of the normalized integral
system. The identity direct image in the existing level functor supplies only the
canonical site/coefficient conversion; no curve or immersion hypothesis is required.
Source: BS 6.8.4(1),(4)
(blueprint: def-a1-lisse-integral-completed-realization). -/
def lisseIntegralCompletedRealization (X : Scheme.{u}) [IsNoetherian X] [X.IsSeparated]
    [∀ x : X, Invertible (l : X.residueField x)]
    (E : Padic.FiniteCoefficientFields l Ω) :
    LisseIntegralSheaf l E.val X ⥤
      DerivedCategory (scalarReductionSource l (pbcFiniteField.{u} l Ω E) X) :=
  ObjectProperty.ι _ ⋙
    (Functor.whiskeringRight _ _ _).obj (middleExtensionLevelFunctor l Ω E (𝟙 X)) ⋙
    lim ⋙ DerivedCategory.singleFunctor _ 0 ⋙
      (purCoefficientModel l (pbcFiniteField.{u} l Ω E) X).functor

/-- Integral localization followed by inclusion at the specified finite coefficient
field. Membership in the constructible integral category is supplied as a proof of
that predicate on the actual realized object, not as a choice of new object data.
Source: BS 6.8.14(2), 6.8.15; Weil II (1.1.1) d)
(blueprint: def-a1-lisse-integral-completed-realization). -/
def lisseIntegralCommonStage (X : Scheme.{u}) (E : Padic.FiniteCoefficientFields l Ω)
    (K : sfIntegralConstructibleCategory l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E) X) :=
  (GeneralAlgebraicallyClosedCoefficients.inclusion (l := l) (Ω := Ω) (Y := X) E).obj
    ((sfRationalConstructibleLocalization l _ X).obj K)

/-- The point normalization used by ordinary and compact cohomology. This is the
recorded integral fibre followed by homology and the inverse ULift coefficient
identification; every underlying section and linear map is retained.
Source: blueprint def-weil-finite-coefficient-point, clause 2
(blueprint: def-a1-lisse-integral-completed-realization). -/
def lisseIntegralPointCohomology (D : FiniteFieldDatum.{u})
    (E : Padic.FiniteCoefficientFields l Ω) (i : ℤ) :
    DerivedCategory (scalarReductionSource l (pbcFiniteField.{u} l Ω E)
      (Spec (.of D.k))) ⥤
      ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l (pbcFiniteField.{u} l Ω E)) :=
  letI : IsGrothendieckAbelian.{u + 1}
      (ModuleCat.{u + 1}
        (ULift.{u + 1, u}
          (Padic.coefficientExtensionIntegers l (pbcFiniteField.{u} l Ω E)))) :=
    inferInstance
  letI : HasDerivedCategory.{u + 1}
      (ModuleCat.{u + 1}
        (ULift.{u + 1, u}
          (Padic.coefficientExtensionIntegers l (pbcFiniteField.{u} l Ω E)))) :=
    HasDerivedCategory.ofIsGrothendieckAbelian _
  (pointFibreIntegralAmbient D l (pbcFiniteField.{u} l Ω E)) ⋙
    DerivedCategory.homologyFunctor.{u + 1}
      (ModuleCat.{u + 1}
        (ULift.{u + 1, u}
          (Padic.coefficientExtensionIntegers l (pbcFiniteField.{u} l Ω E)))) i ⋙
    ModuleCat.restrictScalars.{u + 1, u, u + 1}
      (ULift.ringEquiv :
        ULift.{u + 1, u}
          (Padic.coefficientExtensionIntegers l (pbcFiniteField.{u} l Ω E)) ≃+*
            Padic.coefficientExtensionIntegers l (pbcFiniteField.{u} l Ω E)).symm.toRingHom

end WeilConjectures
