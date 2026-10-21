/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q80
-/
module

public import Sheaf.Paper.AdicCoefficientDatum
public import Sheaf.Paper.IntegralUniformCoefficient
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HomModule
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.CategoryTheory.Triangulated.Basic
import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
import Sheaf.Algebra.Homology.KFlat
import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
import Sheaf.Paper.CompletedConstantSheafReduction
import Sheaf.Paper.ConstantModuleSectionProperties
import Sheaf.Paper.SfCommonStageWeilCohomology
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import Sheaf.Algebra.Homology.KFlatIndependentCoefficients

/-!
# Uniformizer cone comparison and uniform reduction bound

Source: literature/stacks-project/sites-modules.tex, Tags 093J and 093M; derived.tex Tag 05RS
(blueprint: lem-cbc-finite-extension-reduction-cone-bound).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite

namespace AlgebraicGeometry.Scheme

/-- The completed finite-extension module category is abelian by the standard sheaf-of-modules
instance. Source: Stacks Project, Modules on Sites, Tag 093J (blueprint:
lem-cbc-finite-extension-reduction-cone-bound). -/
noncomputable instance finiteExtensionCompletedModulesAbelian
    (l : ℕ) [Fact l.Prime] (E : Type (u + 1)) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (T : Scheme.{u}) :
    Abelian (pbcModules T (pbcAdicCompletion T (pbcPadicCoefficientDatum l E))) :=
  SheafOfModules.instAbelian _

/--
Source: literature/stacks-project/sites-modules.tex, Tags 093J and 093M; derived.tex Tag 05RS
(blueprint: lem-cbc-finite-extension-reduction-cone-bound).

For the completed coefficient datum of a finite extension, reduction modulo every positive
power of the uniformizer is the cone of uniformizer multiplication.  The same distinguished
triangle is natural in the derived module, and the long exact homology sequence gives the
uniform interval `[a - 1, b]` from an interval `[a, b]` for the original object.
-/
theorem finiteExtensionReductionConeBound
    (l : ℕ) [Fact l.Prime] (E : Type (u + 1)) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (T : Scheme.{u})
    (M : PbcCompletedDerived T (pbcPadicCoefficientDatum l E)) (a b : ℤ) (hab : a ≤ b)
    (hM : ∀ q : ℤ, q < a ∨ b < q →
      IsZero ((DerivedCategory.homologyFunctor
        (pbcModules T (pbcAdicCompletion T (pbcPadicCoefficientDatum l E))) q).obj M)) :
    ∀ n : ℕ, 1 ≤ n →
      ∃ (β : 𝟭 (PbcCompletedDerived T (pbcPadicCoefficientDatum l E)) ⟶
          (pbcCompletedReduction T (pbcPadicCoefficientDatum l E) (n - 1) ⋙
            pbcDerivedRestrict (pbcAdicProjection T (pbcPadicCoefficientDatum l E) (n - 1))))
        (γ : (pbcCompletedReduction T (pbcPadicCoefficientDatum l E) (n - 1) ⋙
              pbcDerivedRestrict
                (pbcAdicProjection T (pbcPadicCoefficientDatum l E) (n - 1))) ⟶
          𝟭 (PbcCompletedDerived T (pbcPadicCoefficientDatum l E)) ⋙ shiftFunctor
            (PbcCompletedDerived T (pbcPadicCoefficientDatum l E)) (1 : ℤ)),
        (∀ N : PbcCompletedDerived T (pbcPadicCoefficientDatum l E),
          Triangle.mk
              ((Padic.coefficientExtensionUniformizer l E) ^ n • 𝟙 N)
              (β.app N) (γ.app N) ∈
            distTriang (PbcCompletedDerived T (pbcPadicCoefficientDatum l E))) ∧
        (∀ q : ℤ, q < a - 1 ∨ b < q →
          IsZero ((DerivedCategory.homologyFunctor
            (pbcModules T (pbcAdicCompletion T (pbcPadicCoefficientDatum l E))) q).obj
            ((pbcCompletedReduction T (pbcPadicCoefficientDatum l E) (n - 1) ⋙
              pbcDerivedRestrict
                (pbcAdicProjection T (pbcPadicCoefficientDatum l E) (n - 1))).obj M))) := by
  sorry

end AlgebraicGeometry.Scheme
