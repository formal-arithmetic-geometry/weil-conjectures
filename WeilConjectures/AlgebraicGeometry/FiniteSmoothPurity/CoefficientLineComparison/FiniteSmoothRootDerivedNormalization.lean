/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteSmoothCoefficientArrows
public import WeilConjectures.CategoryTheory.Exact.ExactDegreeZeroAdjoint
import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.ScalarSingleAdjointInsertion

/-! # Exact degree-zero normalization of the root comparison

Source: smooth-purity reduction compatibilities (3), root-line normalization.
(blueprint: lem-pur-finite-smooth-root-derived-normalization).
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace AlgebraicGeometry.Etale.FiniteSmoothPurity
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
attribute [local instance 10000] SheafExactDegreeZero.scalarWeakSheafify
attribute [local irreducible] Functor.leftAdjoint Functor.rightAdjoint
  Functor.mapDerivedCategory
set_option linter.auxLemma false in
attribute [local instance 100000] DerivedCategoryModule._proof_1 DerivedCategoryModule._proof_2

end AlgebraicGeometry.Etale.FiniteSmoothPurity

namespace AlgebraicGeometry.Etale.FiniteSmoothPurity

/-- Generator-normalized derived root comparisons are exact degree-zero insertion transposes.
Source: Stacks 06YY; the record's derived normalization and adjunction naturality.
(blueprint: lem-pur-finite-smooth-root-derived-normalization).
Proof: move the single image of the sheaf comparison through the derived adjunction
Hom equivalence. Naturality of the exact restriction/single comparison identifies the
result with the single image of the ordinary adjunct. The record's defining
normalization gives the claimed equality. -/
theorem CoefficientLineComparison.derived_eq_scalarInsertion
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    {phi : A →+* B} {N M : ℕ} {hA : (N : A) = 0} {hB : (M : B) = 0}
    {T : Scheme.{u}} (e : CoefficientLineComparison phi N M hA hB T) :
    e.derivedIso.hom = SheafExactDegreeZero.scalarAdjointInsertion T.smallEtaleTopology phi
      ((ProEtale.etaleSheafExtendScalarsAdjunction phi T).homEquiv _ _ e.sheafIso.hom) := by
  exact e.derived_normalization.trans (scalarSingleMap_eq_scalarInsertion phi T _ _ e.sheafIso.hom)

end AlgebraicGeometry.Etale.FiniteSmoothPurity
