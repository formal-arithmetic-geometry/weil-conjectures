/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.IntegralQuotient.IntegralQuotientCoefficients
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.ProfiniteFiniteConstantLocalModel
public import WeilConjectures.AlgebraicGeometry.Cohomological.CohomologicalDimension
public import WeilConjectures.CategoryTheory.Integral.IntegralStratumHomFormula
public import WeilConjectures.CategoryTheory.Integral.IntegralStratumFiniteCdReductionsHeartData
public import WeilConjectures.CategoryTheory.Integral.IntegralStratumFiniteCdReductionsSectionsFromData

/-! Heart-level section bound for the continuous integral coefficient.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj

attribute [local instance 20000] HasDerivedCategory.ofIsGrothendieckAbelian

namespace CategoryTheory

/-- Heart-level dual-torsion section bound for the continuous integral coefficient.
Source: Stacks Tags 08JJ and 099Y.

The hypothesis `hD` pins `D` to `stratumModuleDual _ S L = RHom(L[0], A[0])`; the
statement is false for an arbitrary object `D` (take `D = A[0]⟦10⟧` and `F` the
constant sheaf `A/ℓ` on a nonempty `S`: then `H^{-10}` is `H^0(S, A/ℓ) ≠ 0`). -/
theorem integralStratumFiniteCdReductions_heart_bound
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (S : Scheme.{u}) [IsNoetherian S]
    (L : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1})
      (condensedRingObj (IntegralQuotient.integral l E) S))
    (hL : HasFiniteConstantLocalModel (IntegralQuotient.integral l E) S L)
    (D : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1})
      (condensedRingObj (IntegralQuotient.integral l E) S)))
    (hD : D = stratumModuleDual (IntegralQuotient.integral l E) S L)
    (s : ℕ) (hs : cohomologicalDimension l (Fact.out : l.Prime) S ≤ s)
    (F : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1})
      (condensedRingObj (IntegralQuotient.integral l E) S))
    (hF : IsClassicalAbelian F.X ∧
      IsEllPowerTorsionLocal l (Fact.out : l.Prime) F.X) :
    ∀ i : ℤ, i < 0 ∨ (s : ℤ) + 1 < i →
      IsZero ((DerivedCategory.homologyFunctor Ab.{u + 1} i).obj
        ((stratumModuleDerivedSections (IntegralQuotient.integral l E) S).obj
          (((derivedTensor (IntegralQuotient.integral l E) S).obj D).obj
            ((DerivedCategory.singleFunctor _ 0).obj F)))) := by
  subst D
  obtain ⟨hTor, hcoh⟩ := integralStratumFiniteCdReductions_heart_data
    l E S L hL F hF
  exact integralStratumFiniteCdReductions_sections_from_data
    l E S _ s hs F hTor hcoh

end CategoryTheory
