/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.Algebra.Homology.HomologySequenceLemmas
import Mathlib.LinearAlgebra.TensorProduct.RightExactness

/-! # Principal quotient preserves quasi-isomorphisms on regular complexes

Source: Stacks Project, Derived Categories, Tag 05RT; steps 4--7 of the original plan.
(blueprint: lem-pod-principal-quotient-quasi-iso) -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped ChangeOfRings TensorProduct

namespace CochainComplex.PrincipalQuotient
variable {R A : Type u} [CommRing R] [CommRing A] (f : R →+* A) (t : R)
  (hf : Function.Surjective f) (hk : ∀ x : R, f x = 0 ↔ ∃ y : R, t * y = x)

include hf

include hk

end CochainComplex.PrincipalQuotient
