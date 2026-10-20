/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NP
-/
module
public import Sheaf.Paper.OrdinaryCompactCohomology
public import Sheaf.Paper.CompactSupportCoefficientAction
public import Sheaf.Paper.SfDerivedDirectImage
public import Sheaf.AlgebraicGeometry.ProEtaleConstantDerivedDirectImage
public import Sheaf.Paper.SfIntegralReductionTower
public import Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
import WeilConjectures.Compactification.Refinement
public import WeilConjectures.Compactification.RefinementCategory
import Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZero
import Sheaf.Paper.ProEtaleConstructibleOrigin
import Sheaf.AlgebraicGeometry.CompactSupportRestrictionOfScalars
import Sheaf.AlgebraicGeometry.SfIntrinsicCompactSupport
import Sheaf.Paper.CommonStageCompactWeilCohomology
import Sheaf.Paper.CompactificationCoherence
import Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients
import Sheaf.Paper.QcqsCompactSupportRealization
import Sheaf.Paper.SfCommonStageDirectImage
import Sheaf.Paper.SfRationalizationKaroubi
import Sheaf.SecSmoothPurity.IntrinsicCompactSupportRestriction
/-!
# Proper coincidence of compact-support and ordinary cohomology

Source: literature/blueprint/main-20261015/blueprint/sec-zeta-weil/sk-input-weights/
prop-weil-proper-compact-coincidence.md (blueprint: prop-weil-proper-compact-coincidence).

## Main statements

* `WeilConjectures.properCompactPointOver`: the identity structure morphism on the point.
* `WeilConjectures.properCompactCoincidence`: proper comparison for all four coefficients.
-/
@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
open AlgebraicallyClosedCoefficients (Coefficient)

/-- The point has its identity structure morphism over the fixed geometric field.
Source: blueprint structure morphism a_Y and its point s = Spec k
(blueprint: prop-weil-proper-compact-coincidence). -/
instance properCompactPointOver (D : FiniteFieldDatum.{u}) :
    (Spec (CommRingCat.of D.k)).Over (Spec (CommRingCat.of D.k)) :=
  ⟨𝟙 _⟩

/-- For a proper structure morphism over the geometric field of the finite-field
datum, compact-support and ordinary direct images agree for finite, integral,
rational, and algebraically closed coefficients. Their sections and cohomology
objects are consequently isomorphic for every bounded constructible input.
For rational and algebraically closed coefficients the ordinary functor is
represented by the compact-support formula at the identity compactification;
the algebraically closed clause holds for every normalized coefficient action at
`c` and at the identity compactification, not only for some choice of them;
the image clauses also compare with the recorded ordinary tower values.

Source: literature/blueprint/main-20261015/blueprint/sec-zeta-weil/sk-input-weights/
prop-weil-proper-compact-coincidence.proof.md (blueprint: prop-weil-proper-compact-coincidence).
Proof: (1) Use the finite-field and coefficient data of
`def-weil-ordinary-compact-cohomology`; properness of the structure morphism is
`def-weil-proper-morphism`.  The identity compactification is supplied by
`def-weil-compactifications-refinements`.  For its identity open immersion,
`def-weil-extension-by-zero` identifies extension by zero with the identity,
so `def-compact-support-direct-image-detailed` gives the finite-level direct-image
isomorphism.  The etale-origin and compactification-coherence clauses are those
of `lem-sf-proetale-constructible-origin` and
`prop-compactification-coherence-detailed`.
(2) For integral coefficients, `def-weil-integral-rational-qbar-compact-support`
and `def-weil-derived-direct-image` give the two towers.  Their terms and
transition maps agree by `lem-sf-compact-support-restriction-of-scalars`, since
the identity extension is literally the identity.
(3) Localization through `def-weil-rationalization-karoubi` preserves the
comparison, and `def-weil-algebraically-closed-coefficients` transports it to
common finite stages, yielding the rational and algebraically closed clauses.
(4) Applying the geometric-point fibre and degreewise cohomology in
`def-weil-ordinary-compact-cohomology` gives each displayed cohomology
isomorphism, naturally in the input and in the degree.
-/
theorem properCompactCoincidence
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    (E₀ : Padic.FiniteCoefficientFields l Ω) (Y : Scheme.{u})
    [Y.Over (Spec (CommRingCat.of D.k))]
    [IsProper (Y ↘ Spec (CommRingCat.of D.k))]
    (c : Compactification (Y ↘ Spec (CommRingCat.of D.k)))
    (n : ℕ) (hn : 1 ≤ n) :
    Nonempty ((intrinsicFiniteTorsionConstructible l (Coefficient.{u} l Ω E₀)
        n hn Y).ι ⋙ @sfIntrinsicCompactSupport Y (Spec (CommRingCat.of D.k))
          (Y ↘ Spec (CommRingCat.of D.k)) c
          (Padic.coefficientExtensionRing l (Coefficient.{u} l Ω E₀) n)
          _ (Padic.finite_coefficientExtensionRing l (Coefficient.{u} l Ω E₀) n hn) ≅
      (intrinsicFiniteTorsionConstructible l (Coefficient.{u} l Ω E₀) n hn Y).ι ⋙
        proEtaleConstantDerivedDirectImage (Y ↘ Spec (CommRingCat.of D.k))
          (Padic.coefficientExtensionRing l (Coefficient.{u} l Ω E₀) n)) ∧
    Nonempty (sfCompactSupportFiniteIntegralFunctor l D.k (finiteFieldDatumPrimeUnit D l hl)
        c (Coefficient.{u} l Ω E₀) ⋙
          (sfIntegralConstructible l (Coefficient.{u} l Ω E₀) (Spec (.of D.k))).ι ≅
      (sfIntegralConstructible l (Coefficient.{u} l Ω E₀) Y).ι ⋙
        sfCompletedDerivedDirectImage l (Coefficient.{u} l Ω E₀) (Y ↘ Spec (.of D.k))) ∧
    Nonempty (sfCompactSupportFiniteFunctor l D.k (finiteFieldDatumPrimeUnit D l hl)
        c (Coefficient.{u} l Ω E₀) ≅
      sfCompactSupportFiniteFunctor l D.k (finiteFieldDatumPrimeUnit D l hl)
        (Compactification.ofIsProper (Y ↘ Spec (.of D.k))) (Coefficient.{u} l Ω E₀)) ∧
    (∀ S : SfCompactSupportCoefficientAction l D.k (finiteFieldDatumPrimeUnit D l hl) Ω c,
      ∀ S₀ : SfCompactSupportCoefficientAction l D.k (finiteFieldDatumPrimeUnit D l hl) Ω
          (Compactification.ofIsProper (Y ↘ Spec (.of D.k))),
        Nonempty (S.system.functor ≅ S₀.system.functor)) ∧
    (∀ K : (intrinsicFiniteTorsionConstructible l (Coefficient.{u} l Ω E₀) n hn
        Y).FullSubcategory,
      Nonempty (finiteCompactSections D l (Coefficient.{u} l Ω E₀) Y c n hn K.obj ≅
        finiteOrdinarySections D l (Coefficient.{u} l Ω E₀) Y n hn K.obj) ∧
      ∀ i : ℤ, Nonempty (finiteCompactCohomology D l
        (Coefficient.{u} l Ω E₀) Y c n hn K.obj i ≅
          finiteOrdinaryCohomology D l (Coefficient.{u} l Ω E₀) Y n hn K.obj i)) ∧
    (∀ K : sfIntegralConstructibleCategory l (Coefficient.{u} l Ω E₀) Y,
      Nonempty (sfIntegralCompactSupportValue l (Coefficient.{u} l Ω E₀) D.k
        (finiteFieldDatumPrimeUnit D l hl) c K ≅
          integralImage D l hl (Coefficient.{u} l Ω E₀) Y K) ∧
      Nonempty (integralCompactSections D l hl (Coefficient.{u} l Ω E₀) Y c K ≅
        integralOrdinarySections D l hl (Coefficient.{u} l Ω E₀) Y K) ∧
      ∀ i : ℤ, Nonempty (integralCompactCohomology D l hl (Coefficient.{u} l Ω E₀)
        Y c K i ≅ integralOrdinaryCohomology D l hl (Coefficient.{u} l Ω E₀) Y K i)) ∧
    (∀ K : sfRationalConstructibleCategory l (Coefficient.{u} l Ω E₀) Y,
      Nonempty (sfRationalCompactSupportValue l (Coefficient.{u} l Ω E₀) D.k
        (finiteFieldDatumPrimeUnit D l hl) c K.obj ≅
          rationalImage D l hl (Coefficient.{u} l Ω E₀) Y K) ∧
      Nonempty (rationalCompactSections D l hl (Coefficient.{u} l Ω E₀) Y c K ≅
        rationalOrdinarySections D l hl (Coefficient.{u} l Ω E₀) Y K) ∧
      ∀ i : ℤ, Nonempty (rationalCompactCohomology D l hl (Coefficient.{u} l Ω E₀)
        Y c K i ≅ rationalOrdinaryCohomology D l hl (Coefficient.{u} l Ω E₀) Y K i)) ∧
    (∀ K : generalAlgebraicallyClosedConstructibleCategory l Ω Y,
      Nonempty (sfQbarCompactSupportValue l D.k (finiteFieldDatumPrimeUnit D l hl)
        Ω c K.stage K.obj.obj ≅ qbarImage D l hl Y Ω K) ∧
      Nonempty (qbarCompactSections D l hl Y Ω c K ≅ qbarOrdinarySections D l hl Y Ω K) ∧
      ∀ i : ℤ, Nonempty (qbarCompactCohomology D l hl Y Ω c K i ≅
        qbarOrdinaryCohomology D l hl Y Ω K i)) := by
  sorry

end WeilConjectures
