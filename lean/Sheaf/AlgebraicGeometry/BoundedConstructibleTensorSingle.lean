/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B2
-/
module

public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FinitenessCoefficient
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor



/-! # BoundedConstructibleTensorSingle

The remaining local tensor calculation on constructible sheaves in degree zero.
-/

@[expose] public section

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

universe u

open scoped CategoryTheory.Obj
open CategoryTheory Limits MonoidalCategory Opposite

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ]
  [IsCommMonObj Λ] {k : Type u} [Field k]
variable (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom]
  [QuasiCompact X.hom] [IsSeparated X.hom]

/-- The tensor calculation for two constructible sheaves in degree zero.

Source: Bhatt--Scholze, Definition 6.8.10 and Proposition 6.8.11(3);
blueprint `lem-sfb-dc-tensor-preserves`, steps 1--9. The finite-type scheme is noetherian.
Refine the finite constructible stratifications of F and G and then their local presentation
covers. The field local-triviality theorems make the restrictions finite free, so their
derived tensor is finite free in degree zero. For integral coefficients, the integral
constant-model comparison expresses the scalar modules as finite sums of free and cyclic
DVR modules. Resolve each cyclic module by multiplication by its uniformizer power between
two free modules. The resulting tensor has cohomology only in degrees -1 and 0, each a finite
sum of cyclic modules. Exact inverse image commutes with these computations. Finite-stratum
vanishing detection gives the global bounds, while the same covers exhibit local finite
presentations for the remaining homology. This proves bounded constructibility. The zero
module, rank zero and empty strata give zero complexes throughout.
(blueprint: lem-sfb-dc-tensor-single) -/
theorem boundedConstructible_tensor_single
    {ℓ : ℕ} [IsEllAdicFinitenessCoefficient ℓ Λ] [Fact (ringChar k ≠ ℓ)]
    (F G : Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
      (condensedRingObj Λ X.left))
    (hF : IsConstructibleModuleObject (condensedRingObj Λ X.left) F)
    (hG : IsConstructibleModuleObject (condensedRingObj Λ X.left) G) :
    boundedConstructible (condensedRingObj Λ X.left)
      ((DerivedCategory.singleFunctor _ 0).obj F ⊗
        (DerivedCategory.singleFunctor _ 0).obj G) := by
  sorry


end AlgebraicGeometry.ProEtale.CondensedRing
