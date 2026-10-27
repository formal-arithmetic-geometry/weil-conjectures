/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E8
-/
module

public import Sheaf.Paper.FiniteFreeHomLocalCalculation

/-! # Finite-free evaluation under coefficient change

Source: thm-coef-finite-hom, proof paragraphs 2–3.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
set_option Elab.async false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Functor
namespace WeilConjectures
attribute [local implicit_reducible] finiteHomEtaleCategory
attribute [local instance] lisseHomModuleDerivedCategory
attribute [local irreducible] _root_.DerivedCategory instCategoryDerivedCategory
attribute [local irreducible] Functor.rightAdjoint Functor.leftAdjoint
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor Functor.mapDerivedCategory
  Etale.upperStar Etale.lowerStar _root_.DerivedCategory.monoidalClosed
  ProEtale.pbcFixedScalarExtension Etale.derivedTensor
  Padic.coefficientExtensionAbsoluteValue Padic.coefficientExtensionIntegers
  Padic.coefficientExtensionUniformizer Padic.coefficientExtensionIdeal
  coefficientBaseChangeHom finiteHomEtaleData finiteHomEtaleClosed finiteHomEtaleTensor

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
  [FiniteDimensional (Padic l) E]

/-- The canonical comparison is the identity in finite-free evaluation coordinates.
Source: thm-coef-finite-hom, local finite-free calculation
(blueprint: lem-coef-etale-finite-free-hom-local-identity).

Proof: finite-free evaluation identifies internal Hom with the finite product of copies
of its second input. Scalar extension preserves finite products because it is additive.
A bounded flat complex is K-flat, so its scalar representative map is invertible.
The same computation with the reduced basis identifies the target coordinates.
To check the square, compose with every product projection and transpose through the
closed adjunction. Normalization of the tensor comparison and unit identifies both
maps with scalar extension of evaluation on that basis vector. The empty product
case is the zero object and requires no vector. -/
theorem etaleFiniteFreeHomLocalIdentity (T : Scheme.{u}) {n m : ℕ} (h : m ≤ n)
    (K N : finiteHomEtale l E T n) :
    ∃ v : LisseHomComparisonType
      (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1)))
      (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (m + 1)))
      (finiteHomQuotient l E h) T K N,
      HEq v (etaleFiniteHomCanonical l E T h K N) ∧
      LisseHomLocalFreeCalculationRing _ _ (finiteHomQuotient l E h) T K N v := by
  sorry

end WeilConjectures
