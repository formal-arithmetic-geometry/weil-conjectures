/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q02
-/
module

public import Sheaf.Paper.AdicCoefficientDatum
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimitProducts

import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
/-!
# Sequential derived inverse limits of completed-coefficient towers

Source: blueprint order 1240; Stacks Tag 07KC
(blueprint: def-weil-pbc-derived-inverse-limit).
This records an object and a distinguished Roos triangle; it selects neither a limit
object nor an inverse-limit functor. The index n : ℕ denotes the positive level n+1.

## Main definitions

- `AlgebraicGeometry.Scheme.CompletedDerivedInverseLimit`:
  the recorded construction or statement of this node.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe t
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

/-- An object with the specified distinguished Roos triangle is a sequential derived
inverse limit. The product is in the completed-coefficient derived category; exact
countable products and Tag 07KC compute it by termwise products of representatives.
No object or functor is chosen by this definition.
Source: blueprint order 1240 (blueprint: def-weil-pbc-derived-inverse-limit). -/
structure CompletedDerivedInverseLimit (T : Scheme.{t}) {A : Type (t + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) (M : DerivedCategory (reductionTowerCategory T
      (reductionModuleRing T (completedReductionCoefficient T d))))
    [HasProduct (completedTowerDerivedSequence T d M)] where
  obj : reductionDerivedCategory T (completedReductionCoefficient T d)
  p : obj ⟶ ∏ᶜ (completedTowerDerivedSequence T d M)
  δ : ∏ᶜ (completedTowerDerivedSequence T d M) ⟶ obj⟦(1 : ℤ)⟧
  distinguished : IsDerivedLimitTriangle (completedTowerDerivedStep T d M) obj p δ

end AlgebraicGeometry.Scheme
