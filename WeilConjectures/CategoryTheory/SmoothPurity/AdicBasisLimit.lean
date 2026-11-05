/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Ideal.Quotient.PowTransition
public import Mathlib.LinearAlgebra.Basis.Defs
import WeilConjectures.CategoryTheory.Constant.ConstantSpecifiedBasis
import Mathlib.CategoryTheory.Functor.OfSequence
import Mathlib.Algebra.Category.ModuleCat.Products
import Mathlib.RingTheory.TensorProduct.Quotient
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification

/-!
# Finite bases of completed constant quotient sheaves

Source: Bhatt--Scholze, Lemma 6.8.2(1), pp. 58--59, for the inverse-limit model.
The finite-basis and cofinal-filtration refinement is the agent argument in the DAG
(blueprint: lem-pur-adic-basis-limit).

Levels of the inverse sequence are numbered by n : ℕ and have exponent n+1.
Finite products in module sheaves are the finite direct sums in the statement.
The displayed sums characterize the quotient basis maps and the completed map,
including their columns, without a choice of an unrelated isomorphism.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe uC vC r

open CategoryTheory CategoryTheory.Limits Opposite
open scoped BigOperators

namespace CategoryTheory

variable {C : Type uC} [Category.{vC} C] (J : GrothendieckTopology C)

variable {A B : Type r} [CommRing A] [CommRing B] [Algebra A B]

variable {A B : Type (max uC vC r)} [CommRing A] [CommRing B] [Algebra A B]

end CategoryTheory
