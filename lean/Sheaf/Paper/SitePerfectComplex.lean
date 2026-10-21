/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q33
-/
module

public import Sheaf.Paper.StrictPerfectCoefficientPackageOfUniverses
public import Sheaf.Paper.CompletedIntegralCoefficients
public import Sheaf.Paper.IntegralDerivedOperations
public import Sheaf.Paper.AlgebraicallyClosedCoefficients
public import Sheaf.Paper.SfRationalizationKaroubi
public import Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients

/-!
# Perfect complexes on the coefficient site

Source: Weil conjectures blueprint, `sec-smooth-purity/sk-prop-sf-pf-reduction`,
order 1881 (blueprint: def-weil-site-perfect-complex).

## Main definitions

- `IsFiniteCoefficientSitePerfect`
- `IsIntegralCoefficientSitePerfect`
- `IsRationalCoefficientSitePerfect`
- `IsAlgebraicallyClosedCoefficientSitePerfect`
-/

@[expose] public section

set_option autoImplicit false

universe d t u v

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

open CategoryTheory CategoryTheory.Limits

namespace WeilConjectures

/-- Abelian sheafification on the actual pro-etale slice, at the coefficient size.
Source: Stacks Tag 03DA (blueprint: def-weil-site-perfect-complex). -/
noncomputable instance sitePerfectOverAbSheafify (Y : AlgebraicGeometry.Scheme.{t})
    (U : Y.ProEt) :
    HasSheafify ((AlgebraicGeometry.Scheme.ProEt.topology Y).over U)
      AddCommGrpCat.{max u (t + 1)} :=
  letI : EssentiallySmall.{max u (t + 1)} (Over U) := essentiallySmallSelf _
  hasSheafifyEssentiallySmallSite _ _

/-- The locally bijective criterion on that same small model of the slice.
Source: Stacks Tag 03DA (blueprint: def-weil-site-perfect-complex). -/
noncomputable instance sitePerfectOverAbLocallyBijective (Y : AlgebraicGeometry.Scheme.{t})
    (U : Y.ProEt) :
    ((AlgebraicGeometry.Scheme.ProEt.topology Y).over U).WEqualsLocallyBijective
      AddCommGrpCat.{max u (t + 1)} :=
  letI : EssentiallySmall.{max u (t + 1)} (Over U) := essentiallySmallSelf _
  GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall _

/-- Site-perfectness at the finite coefficient stage uses an actual covering sieve
and bounded finite-projective models of module sheaves on its members. The exponent
is `n + 1`, so every positive finite level is included.
Source: Weil blueprint, order 1881 (blueprint: def-weil-site-perfect-complex). -/
noncomputable def IsFiniteCoefficientSitePerfect (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (Y : AlgebraicGeometry.Scheme.{t}) (n : ℕ)
    (K : @DerivedCategory (SheafOfModules.{max u (t + 1)}
      (integralCoefficientSheaf l E Y n)) _ _ (HasDerivedCategory.standard _)) : Prop :=
  letI := integralCoefficientAbSheafify.{t, u} Y
  letI := integralCoefficientAbLocallyBijective.{t, u} Y
  letI := HasDerivedCategory.standard (SheafOfModules.{max u (t + 1)}
    (integralCoefficientSheaf l E Y n))
  @SheafOfModules.IsPerfectOnRingedSiteOfUniverses.{t + 1, t, max u (t + 1)}
    _ _ _ (integralCoefficientAbSheafify.{t, u} Y)
    (fun U ↦ sitePerfectOverAbSheafify.{t, u} Y U)
    (fun U ↦ sitePerfectOverAbLocallyBijective.{t, u} Y U)
    (integralCoefficientAbLocallyBijective.{t, u} Y)
    (integralCoefficientCommRingSheaf l E Y n) (HasDerivedCategory.standard _) K

/-- Site-perfectness at the integral stage uses the completed coefficient sheaf,
with the same covering and bounded-retract condition as at finite level.
Source: Weil blueprint, order 1881 (blueprint: def-weil-site-perfect-complex). -/
noncomputable def IsIntegralCoefficientSitePerfect
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (Y : AlgebraicGeometry.Scheme.{t})
    (K : @DerivedCategory (SheafOfModules.{max u (t + 1)}
      (completedIntegralCoefficientSheafUnrestricted l E Y)) _ _
      (HasDerivedCategory.standard _)) : Prop :=
  letI := integralCoefficientAbSheafify.{t, u} Y
  letI := integralCoefficientAbLocallyBijective.{t, u} Y
  letI := HasDerivedCategory.standard (SheafOfModules.{max u (t + 1)}
    (completedIntegralCoefficientSheafUnrestricted l E Y))
  @SheafOfModules.IsPerfectOnRingedSiteOfUniverses.{t + 1, t, max u (t + 1)}
    _ _ _ (integralCoefficientAbSheafify.{t, u} Y)
    (fun U ↦ sitePerfectOverAbSheafify.{t, u} Y U)
    (fun U ↦ sitePerfectOverAbLocallyBijective.{t, u} Y U)
    (integralCoefficientAbLocallyBijective.{t, u} Y)
    (completedIntegralCommRingSheafUnrestricted l E Y) (HasDerivedCategory.standard _) K

/-- The ambient raw scalar localization, used to compare bounded local models.
Only morphisms are localized; its objects remain actual integral derived objects.
Source: blueprint orders 1460 and 1881 (blueprint: def-weil-site-perfect-complex). -/
noncomputable abbrev sitePerfectRationalAmbient (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (Y : AlgebraicGeometry.Scheme.{u}) :=
  ScalarLocalization (Padic.coefficientExtensionIntegers l E)
    (DerivedCategory (integralTowerModules l E Y))
    (Padic.coefficientExtensionUniformizer l E)

/-- A module term splits from a finite sum of the unit after scalar localization.
The splitting is required in the raw localized category, and need not lift integrally.
Source: blueprint order 1881 (blueprint: def-weil-site-perfect-complex). -/
noncomputable def IsRationalFiniteProjectiveTerm (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (Y : AlgebraicGeometry.Scheme.{u}) (M : integralTowerModules l E Y) : Prop :=
  ∃ m : ℕ,
    ∃ i : (ScalarLocalization.mk
        ((DerivedCategory.singleFunctor (integralTowerModules l E Y) 0).obj M) :
        sitePerfectRationalAmbient l E Y) ⟶
      ScalarLocalization.mk ((DerivedCategory.singleFunctor (integralTowerModules l E Y) 0).obj
        (∏ᶜ fun _ : Fin m ↦
          SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted l E Y))),
    ∃ p : ScalarLocalization.mk ((DerivedCategory.singleFunctor (integralTowerModules l E Y) 0).obj
        (∏ᶜ fun _ : Fin m ↦
          SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted l E Y))) ⟶
      (ScalarLocalization.mk
        ((DerivedCategory.singleFunctor (integralTowerModules l E Y) 0).obj M) :
        sitePerfectRationalAmbient l E Y),
    i ≫ p = 𝟙 _

/-- Rational site-perfectness: an actual site cover and bounded local complexes with
finite-free retractions after inverting the uniformizer. A rational bounded complex
can be represented this way by clearing its finitely many differential denominators;
the termwise retractions are still taken after localization.
The datum D and ell different from its characteristic are the conventions of the
recorded rational coefficient category (blueprint order 1460).
Source: blueprint order 1881 (blueprint: def-weil-site-perfect-complex). -/
noncomputable def IsRationalCoefficientSitePerfect
    (D : FiniteFieldDatum.{d}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (Y : AlgebraicGeometry.Scheme.{u})
    (K : rationalConstructibleCategory D l hl E Y) : Prop :=
  ∀ V : Y.ProEt, ∃ S : Sieve V, S ∈ AlgebraicGeometry.Scheme.ProEt.topology Y V ∧
    ∀ (U : Y.ProEt) (f : U ⟶ V), S f →
      ∃ F : CochainComplex (integralTowerModules l E U.left) ℤ,
        (∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (F.X n)) ∧
        (∀ n : ℤ, IsRationalFiniteProjectiveTerm l E U.left (F.X n)) ∧
        Nonempty ((ScalarLocalization.mk
          ((integralDerivedPullback l E U.hom).obj K.obj.obj) :
            sitePerfectRationalAmbient l E U.left) ≅
          ScalarLocalization.mk (DerivedCategory.Q.obj F))

/-- Common-stage site-perfectness is descent from some finite coefficient field,
up to isomorphism in the actual pair category. No closure under formal retracts is used.
Source: blueprint order 1881 (blueprint: def-weil-site-perfect-complex). -/
noncomputable def IsAlgebraicallyClosedCoefficientSitePerfect
    (D : FiniteFieldDatum.{d}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω]
    [IsAlgClosure ℚ_[l] Ω] (Y : AlgebraicGeometry.Scheme.{u})
    (K : algebraicallyClosedConstructibleCategory D l hl Ω Y) : Prop :=
  ∃ E : AlgebraicallyClosedCoefficients.Index l Ω,
    ∃ P : AlgebraicallyClosedCoefficients.Stage D l hl Ω Y E,
      IsRationalCoefficientSitePerfect D l hl
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E) Y P ∧
      Nonempty (K ≅ (AlgebraicallyClosedCoefficients.inclusion
        (D := D) (l := l) (hl := hl) (Ω := Ω) (Y := Y) E).obj P)

set_option backward.isDefEq.respectTransparency false in
/-- A covering on every pro-etale slice supplies a bounded complex whose terms
split from finite sums of the coefficient unit in the raw scalar localization.
Source: Weil blueprint, order 1881 (blueprint: def-weil-site-perfect-complex).
This is the recorded rational local-model predicate with the intrinsic category
as its domain; neither integral lifts of the term splittings nor integral
perfectness are required. -/
noncomputable def IsSfRationalCoefficientSitePerfect (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (Y : AlgebraicGeometry.Scheme.{u}) (K : sfRationalConstructibleCategory l E Y) : Prop :=
  ∀ V : Y.ProEt, ∃ S : Sieve V, S ∈ AlgebraicGeometry.Scheme.ProEt.topology Y V ∧
    ∀ (U : Y.ProEt) (f : U ⟶ V), S f →
      ∃ F : CochainComplex (integralTowerModules l E U.left) ℤ,
        (∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (F.X n)) ∧
        (∀ n : ℤ, IsRationalFiniteProjectiveTerm l E U.left (F.X n)) ∧
        Nonempty ((ScalarLocalization.mk
          ((integralDerivedPullback l E U.hom).obj K.obj.obj) :
            sitePerfectRationalAmbient l E U.left) ≅
          ScalarLocalization.mk (DerivedCategory.Q.obj F))

/-- Site-perfectness in the intrinsic common-stage category means descent, up to
isomorphism in that pair category, from a site-perfect intrinsic rational stage.
This is the same finite-stage condition as the legacy common-stage predicate above;
the finite-stage objects use the intrinsic categories of the six-functor datum.
Source: blueprint order 1881, algebraically closed paragraph
(blueprint: def-weil-site-perfect-complex). -/
noncomputable def IsGeneralAlgebraicallyClosedCoefficientSitePerfect
    (l : ℕ) [Fact l.Prime]
    (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    (Y : AlgebraicGeometry.Scheme.{u})
    (K : generalAlgebraicallyClosedConstructibleCategory l Ω Y) : Prop :=
  ∃ E : AlgebraicallyClosedCoefficients.Index l Ω,
    ∃ P : GeneralAlgebraicallyClosedCoefficients.Stage l Ω Y E,
      IsSfRationalCoefficientSitePerfect l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E) Y P ∧
      Nonempty (K ≅ (GeneralAlgebraicallyClosedCoefficients.inclusion
        (l := l) (Ω := Ω) (Y := Y) E).obj P)

end WeilConjectures
