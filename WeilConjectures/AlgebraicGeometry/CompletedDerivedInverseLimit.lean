/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AdicCoefficientDatumSupplement
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.AlgebraicGeometry.ProEtaleCountableProductsExact
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.CategoryTheory.RingedSiteModules
import WeilConjectures.AlgebraicGeometry.CompletedIntegralCoefficientsSupplement
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.CategoryTheory.Limits.Shapes.Countable
import WeilConjectures.AlgebraicGeometry.ProEtaleAffineWeaklyContractibleCover
import WeilConjectures.AlgebraicGeometry.ProEtaleAffineContractibleExtension
import WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
import WeilConjectures.AlgebraicGeometry.ProEtaleWeaklyContractibleEvaluationColimitsSupplement
import Mathlib.CategoryTheory.Sites.CompatibleSheafification
import Mathlib.CategoryTheory.Limits.Types.Products
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.CategoryTheory.Sites.Abelian
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
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
