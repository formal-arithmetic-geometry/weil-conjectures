/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T1
-/
module

public import Sheaf.Paper.PQFCohomology
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.CategoryTheory.Limits.Shapes.Products
import Sheaf.AlgebraicGeometry.OpenModuleCohomologyDirectedColimit
import Sheaf.AlgebraicGeometry.SchemeModulesEnoughInjectives
import Sheaf.CategoryTheory.DeltaFunctor
import Sheaf.CategoryTheory.RightDerivedUniversalDeltaFunctor

/-! # Cohomology commutes with direct sums on qcqs schemes

Source: Stacks Project, Cohomology, Tag 01FF, applied as in Tag 09J7
(blueprint: lem-weil-pbc-qcqs-cohomology-direct-sum).
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme

open Classical in
/-- On a quasi-compact quasi-separated scheme, the canonical linear map from the direct sum
of the cohomology modules to the cohomology of a coproduct is bijective, hence an isomorphism.
Its restriction to summand `i` is the map on cohomology induced by `ι i`.
In particular, take `I = ℕ` and the family of nonnegative graded pieces of a quasi-coherent
 graded module; no quasi-coherence hypothesis is needed for the general assertion.

Source: Stacks Project, Cohomology, Tag 01FF, and its direct-sum application in Tag 09J7
(blueprint: lem-weil-pbc-qcqs-cohomology-direct-sum).

Proof:
1. By lem-weil-pbc-qcqs-scheme-spectral and def-weil-spectral-space, the underlying space
has a basis of compact opens closed under intersection, and the whole space is compact.
Thus lem-weil-pbc-qs-scheme-cohomology-directed-colimit applies at the whole space.
2. Finite partial sums are biproducts in the abelian module-sheaf category. Their inclusions
form a directed system indexed by finite subsets of I; the given coproduct is its colimit
by lem-weil-pbc-scheme-modules-coproduct-finite-subsums, including the empty partial sum.
3. By pqf-def-cohomology and lem-weil-pbc-right-derived-universal-delta-functor, H^p is
additive (def-weil-pbc-delta-functor, def-weil-pbc-additive-functor). Applying it to the
finite biproduct identities identifies each finite partial cohomology sum with H^p of
that finite partial sheaf sum.
4. Every algebraic direct-sum element has finite support (def-weil-pbc-direct-sum-modules).
Functoriality identifies its image under the canonical map with the image of the
corresponding finite partial cohomology class in the cohomology of the full coproduct.
5. Directed-colimit cohomology gives a finite-stage representative of every target class;
step 3 then gives a finite-support preimage, proving surjectivity.
6. A finite-support class mapping to zero becomes zero at a larger finite stage by the
same directed-colimit theorem. Step 3 is injective at that stage, so the original class
was zero. The canonical map is linear and bijective, hence an isomorphism.
7. The graded assertion is the specialization I = ℕ of this same assertion. -/
theorem moduleCohomology_directSum_bijective (X : Scheme.{u})
    [CompactSpace X] [QuasiSeparatedSpace X] (I : Type v)
    (F : I → SheafOfModules.{u} (moduleRings X.toRingedSpace))
    (S : SheafOfModules.{u} (moduleRings X.toRingedSpace)) (ι : ∀ i : I, F i ⟶ S)
    (_hS : IsColimit (Cofan.mk S ι)) (p : ℕ) :
    Function.Bijective
      (DirectSum.toModule ((moduleRings X.toRingedSpace).obj.obj (op ⊤)) I
        ((RingedSpace.moduleCohomology X.toRingedSpace p).obj S)
        (fun i ↦ ((RingedSpace.moduleCohomology X.toRingedSpace p).map (ι i)).hom)) := by
  sorry

end AlgebraicGeometry.Scheme
