/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q30
-/
module

public import Sheaf.Paper.CompletedIntegralConstantMapOfUniverses
public import Sheaf.Paper.IntegralReductionTowerUnrestricted
public import Sheaf.Paper.IntegralConstructibleLinear
public import Sheaf.Paper.IntegralDerivedOperationsOnSlices
public import Sheaf.CategoryTheory.ScalarLocalization
public import Sheaf.NumberTheory.Padics.IntegersLocalizationUniformizer
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
public import Sheaf.CategoryTheory.RingedDerivedRestrictionGeneral
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Sheaf.CategoryTheory.LocalizedModuleExactForSystems

/-!
# Finite-cover scalar localization gives uniform power torsion

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors/
  sk-prop-sf-dualizable-biduality/_section.md, proof paragraph “Choose locally a
  bounded complex” and the extracted finite-cover uniform-power argument
  (blueprint: lem-sf-rational-local-global-power-torsion).

The local scalar-localization hypothesis is stated in the slice category of the
small pro-etale site.  Cohomology is expressed by the derived homology functor;
its image of the canonical scalar endomorphism is the stated scalar action on
the cohomology sheaf.
-/

@[expose] public section
set_option autoImplicit false
set_option warn.sorry false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe t u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

namespace WeilConjectures

/-- Abelian sheafification on the small pro-etale site, in a coefficient size containing
the site (`max u (t + 1)`). Source: Stacks Tag 03DA
(blueprint: lem-sf-rational-local-global-power-torsion). -/
noncomputable instance sfRationalSiteHasSheafify (X : AlgebraicGeometry.Scheme.{t}) :
    HasSheafify (AlgebraicGeometry.Scheme.ProEt.topology X)
      AddCommGrpCat.{max u (t + 1)} :=
  letI : EssentiallySmall.{max u (t + 1)} X.ProEt := essentiallySmallSelf _
  hasSheafifyEssentiallySmallSite _ _

/-- The locally bijective sheafification criterion on the small pro-etale site.
Source: Stacks Tag 03DA (blueprint: lem-sf-rational-local-global-power-torsion). -/
noncomputable instance sfRationalSiteLocallyBijective (X : AlgebraicGeometry.Scheme.{t}) :
    (AlgebraicGeometry.Scheme.ProEt.topology X).WEqualsLocallyBijective
      AddCommGrpCat.{max u (t + 1)} :=
  letI : EssentiallySmall.{max u (t + 1)} X.ProEt := essentiallySmallSelf _
  GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall _

/-- Abelian sheafification on a pro-etale slice, in a coefficient size containing the
site (`max u (t + 1)`), so the scheme and coefficient universes stay independent.
Source: Stacks Tag 03DA (blueprint: lem-sf-rational-local-global-power-torsion). -/
noncomputable instance sfRationalSliceHasSheafify
    (X : AlgebraicGeometry.Scheme.{t}) (U : AlgebraicGeometry.Scheme.ProEt X) :
    HasSheafify ((AlgebraicGeometry.Scheme.ProEt.topology X).over U)
      AddCommGrpCat.{max u (t + 1)} :=
  letI : EssentiallySmall.{max u (t + 1)} (Over U) := essentiallySmallSelf _
  hasSheafifyEssentiallySmallSite _ _

/-- The locally bijective sheafification criterion on a pro-etale slice, in the same
coefficient size. Source: Stacks Tag 03DA
(blueprint: lem-sf-rational-local-global-power-torsion). -/
noncomputable instance sfRationalSliceLocallyBijective
    (X : AlgebraicGeometry.Scheme.{t}) (U : AlgebraicGeometry.Scheme.ProEt X) :
    ((AlgebraicGeometry.Scheme.ProEt.topology X).over U).WEqualsLocallyBijective
      AddCommGrpCat.{max u (t + 1)} :=
  letI : EssentiallySmall.{max u (t + 1)} (Over U) := essentiallySmallSelf _
  GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall _

/-- Slice restriction of completed-coefficient modules is additive; first component of
the recorded exactness theorem. Source: Stacks Section 03DH
(blueprint: lem-sf-rational-local-global-power-torsion). -/
noncomputable instance sfRationalOverAdditive
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (X : AlgebraicGeometry.Scheme.{t}) (U : AlgebraicGeometry.Scheme.ProEt X) :
    (SheafOfModules.overFunctor.{max u (t + 1)}
      (completedIntegralCoefficientSheafUnrestricted l E X) U).Additive :=
  (ringedOverFunctor_exactGeneral _ U).1

/-- Slice restriction preserves finite limits; second component of the recorded
exactness theorem. Source: Stacks Section 03DH
(blueprint: lem-sf-rational-local-global-power-torsion). -/
noncomputable instance sfRationalOverFiniteLimits
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (X : AlgebraicGeometry.Scheme.{t}) (U : AlgebraicGeometry.Scheme.ProEt X) :
    PreservesFiniteLimits (SheafOfModules.overFunctor.{max u (t + 1)}
      (completedIntegralCoefficientSheafUnrestricted l E X) U) :=
  (ringedOverFunctor_exactGeneral _ U).2.1

/-- Slice restriction preserves finite colimits; third component of the recorded
exactness theorem. Source: Stacks Section 03DH
(blueprint: lem-sf-rational-local-global-power-torsion). -/
noncomputable instance sfRationalOverFiniteColimits
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (X : AlgebraicGeometry.Scheme.{t}) (U : AlgebraicGeometry.Scheme.ProEt X) :
    PreservesFiniteColimits (SheafOfModules.overFunctor.{max u (t + 1)}
      (completedIntegralCoefficientSheafUnrestricted l E X) U) :=
  (ringedOverFunctor_exactGeneral _ U).2.2

/-- The standard derived localization of modules on a slice. Source: Stacks Tag 05RU
(blueprint: lem-sf-rational-local-global-power-torsion). -/
noncomputable instance sfRationalSliceHasDerivedCategory
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (X : AlgebraicGeometry.Scheme.{t}) (U : AlgebraicGeometry.Scheme.ProEt X) :
    HasDerivedCategory
      (SheafOfModules.{max u (t + 1)}
        ((completedIntegralCoefficientSheafUnrestricted l E X).over U)) :=
  HasDerivedCategory.standard _

/-- A finite pro-etale cover on which an object becomes zero after inverting the
uniformizer has one uniformizer power annihilating every cohomology sheaf.

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors/
`sk-prop-sf-dualizable-biduality/_section.md`, proof paragraph “Choose locally a
bounded complex” and the extracted finite-cover uniform-power argument
(blueprint: lem-sf-rational-local-global-power-torsion).

Proof.  For each member of the finite cover choose a local annihilating power and
then take their maximum; for an empty cover use exponent zero.  Exact restriction
to a slice identifies the cohomology of the restricted object with the restriction
of the global cohomology and carries the scalar endomorphism to the same scalar
endomorphism.  Thus the chosen maximum annihilates each cohomology sheaf after
restriction.  Apply the cover-local isomorphism criterion to the map from the
zero sheaf to the image of this scalar endomorphism.  The restrictions are
isomorphisms, so the image is globally zero, uniformly in the cohomological
degree.  The same argument applies to the empty covering case.  The hypothesis that
`l` is invertible on `X` is the node's standing assumption; the argument does not use it.

The global and slice linear structures are explicit instance arguments; the intended
ones are the canonical constant-section actions (for the global category,
`integralCoefficientLinear` when the scheme and coefficient universes agree).  Since
`l` is a unit times a power of the uniformizer and every linear structure restricts to
the integer action, the hypothesis and the conclusion are equivalent to the
corresponding `l`-power statements, so the statement says the same for every choice.
The scheme lives in universe `t` and the coefficients in `u`, independently.
This statement was checked and delivered by group Q151 on 2026-10-18.
-/
theorem sfRationalLocalGlobalPowerTorsion
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E]
    (X : AlgebraicGeometry.Scheme.{t})
    (_hl : ∀ x : X, IsUnit (l : X.presheaf.stalk x))
    (C : DerivedCategory (integralTowerModules l E X))
    (n : ℕ)
    (U : Fin n → AlgebraicGeometry.Scheme.ProEt X)
    (hU : (AlgebraicGeometry.Scheme.ProEt.topology X).CoversTop U)
    [Linear (Padic.coefficientExtensionIntegers l E)
      (DerivedCategory (integralTowerModules l E X))]
    [∀ j : Fin n,
      Linear (Padic.coefficientExtensionIntegers l E)
        (DerivedCategory
          (SheafOfModules.{max u (t + 1)}
            ((completedIntegralCoefficientSheafUnrestricted l E X).over (U j))))]
    (hzero : ∀ j : Fin n,
      IsZero
        ((ScalarLocalization.localization
          (Padic.coefficientExtensionIntegers l E)
          (DerivedCategory
            (SheafOfModules.{max u (t + 1)}
              ((completedIntegralCoefficientSheafUnrestricted l E X).over (U j))))
          (Padic.coefficientExtensionUniformizer l E)).obj
          ((SheafOfModules.overFunctor.{max u (t + 1)}
            (completedIntegralCoefficientSheafUnrestricted l E X)
            (U j)).mapDerivedCategory.obj C))) :
    ∃ N : ℕ, ∀ d : ℤ,
      (DerivedCategory.homologyFunctor (integralTowerModules l E X) d).map
        ((Padic.coefficientExtensionUniformizer l E) ^ N • 𝟙 C) = 0 := by
  sorry

end WeilConjectures
