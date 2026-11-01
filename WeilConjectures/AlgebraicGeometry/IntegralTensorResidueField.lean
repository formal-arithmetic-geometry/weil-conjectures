/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.AlgebraicGeometry.AdicCompletion.DerivedCompletionSupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Field.Defs
import WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import Mathlib.LinearAlgebra.TensorProduct.Vanishing
import Mathlib.RingTheory.TensorProduct.DirectLimitFG
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.Algebra.Category.Ring.Adjunctions
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.RingTheory.Flat.EquationalCriterion
import Mathlib.LinearAlgebra.Basis.VectorSpace
import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteDiscreteCondensedRing

/-!
# Bounded constructible tensor over the first residue field

Source: literature/blueprint/latest/blueprint/part-six-operations/sec-constructibility-upper-shriek/
sec-ladic-summary/sec-i-heart/sk-lem-int-tensor/det-lem-int-tensor-product.proof.md,
“The stratum”, from “Every F_E,S-module is flat” through the truncation argument
(blueprint: lem-sfb-integral-tensor-residue-field).
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- Bounded constructible complexes over the pulled-back continuous condensed first
residue field are closed under the ordinary derived tensor over that residue field.

Source: det-lem-int-tensor-product.proof.md, “The stratum”, final argument.
(blueprint: lem-sfb-integral-tensor-residue-field).

Proof: the finite discrete residue ring is the finite field F_E; its continuous
condensed realization pulled to S is the constant field sheaf. Every module sheaf
over a constant field is flat: tensor is sheafification of sectionwise tensor over
the field, and both operations are exact. Consequently derived tensor is exact in
each variable with the usual sum of cohomological bounds. For constructible sheaves
F and G, intersect their finite locally closed stratifications and refine their
trivializing covers by fibre products. On each chart, finitely presented field
modules are finite free, so their models F_E^r and F_E^s tensor to F_E^(r*s).
Thus the tensor is constructible. The bounded truncation triangles, successively in
both variables, and triangulatedness of constructible cohomology extend this result
to bounded complexes. Empty strata and rank zero give zero tensor; no nonzero rank,
nonempty scheme, constant global rank or characteristic assumption is needed. -/
theorem integralTensorResidueField
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (S : Scheme.{u}) [IsNoetherian S]
    (M N : AdicCompletion.FiniteDerived l E S 0)
    (hM : constantModelBoundedConstructible (DerivedNakayama.quotientRing l E 1) S M)
    (hN : constantModelBoundedConstructible (DerivedNakayama.quotientRing l E 1) S N) :
    constantModelBoundedConstructible (DerivedNakayama.quotientRing l E 1) S (M ⊗ N) := by
  sorry

end AlgebraicGeometry.ProEtale
