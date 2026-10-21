/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q95
-/
module

public import Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree

/-! # Lisse integral models in the common-stage coefficient category

Source: Deligne, Weil II (1.1.1) b)--d); Bhatt--Scholze, Definition 6.8.3 and
Proposition 6.8.4(1),(4) (blueprint: def-a1-common-stage-lisse-lattice).

The condition retains the actual completed integral module, its degree-zero realization,
and its image under the recorded rationalization and common-stage inclusion.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace WeilConjectures

/-- The common-stage object admits an integral lisse lattice realizing
its carrier. The lattice is a finite locally free module over the completed coefficient
sheaf, placed in degree zero. Its integral constructibility is retained, and the
isomorphism is in the recorded common-stage category. No Frobenius-stable lattice is
required. Rank zero and ranks varying on connected components are allowed.
Source: Weil II (1.1.1) b)--d); Bhatt--Scholze, Definition 6.8.3 and
Proposition 6.8.4(1),(4) (blueprint: def-a1-common-stage-lisse-lattice). -/
def HasCommonStageLisseLattice (l : ℕ) [Fact l.Prime]
    (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    (X : Scheme.{u}) (K : generalAlgebraicallyClosedConstructibleCategory l Ω X) : Prop :=
  ∃ (E : AlgebraicallyClosedCoefficients.Index l Ω)
    (M : sfIntegralConstructibleCategory l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E) X)
    (N : scalarReductionSource l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E) X),
    SheafOfModules.IsFiniteLocallyFree N ∧
      Nonempty (M.obj ≅ (DerivedCategory.singleFunctor _ 0).obj N) ∧
      Nonempty (K ≅ (GeneralAlgebraicallyClosedCoefficients.inclusion E).obj
        ((sfRationalConstructibleLocalization l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E) X).obj M))

end WeilConjectures
