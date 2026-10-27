/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M9
-/
module

public import Sheaf.Paper.IntegralMatrixModelData

/-! # Simultaneous finite matrix models for integral local reductions

Source: Stacks 093J, 093M, 06YQ, 06YY, 07A6.
(blueprint: lem-sp-integral-local-model-finite-matrix-reduction).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe r t w
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale
namespace IntegralMatrix

variable (l : ℕ) [Fact l.Prime] (E : Type r) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
variable {C : Type r} [SmallCategory C] (J : GrothendieckTopology C)
variable [hD : ∀ (D : Type (r + 1)) [Category.{r} D] [Abelian D],
  HasDerivedCategory.{w} D]

/-- Homology of a derived object whose restriction is the given constant matrix cone.
The comparison input is a derived isomorphism, with no resolution, finiteness,
local-model condition or transition data assumed.

Source: Stacks 093J, 03DH, 08JB and 0115; original matrix-reduction node, steps 6 and 8
(blueprint: lem-sp-integral-matrix-cohomology).

Proof: the cone of a map between degree-zero modules has kernel in degree -1,
cokernel in degree 0, and zero homology elsewhere, including for zero ranks.
Exact constant realization preserves these kernels and cokernels. Exact slice
restriction commutes with homology. The homology factorization through the derived
localization and the localization comparison for slice restriction therefore
identify the restriction of H^i(K) with H^i of the local matrix cone via the supplied
isomorphism. This gives the two asserted constant-module isomorphisms and the zero
objects in all remaining degrees. The last two assertions follow by applying the
same exact-restriction comparison to the two homology isomorphisms.
-/
theorem matrix_cohomology (U : C) {a b : ℕ}
    (d : Matrix (Fin b) (Fin a) (Scalars l E)) (n : ℕ)
    (K : DerivedCategory (Modules J (coefficient l E J n)))
    (e : (overDerived J (coefficient l E J n) U).obj K ≅
      localMatrixObject l E J U d n) :
    Nonempty ((((DerivedCategory.homologyFunctor _ (-1)).obj K).over U) ≅
      (((constantAtLevel l E J n).obj
        (ModuleCat.of (Residues l E n) (scalarKernel l E d n))).over U)) ∧
    Nonempty ((((DerivedCategory.homologyFunctor _ 0).obj K).over U) ≅
      (((constantAtLevel l E J n).obj
        (ModuleCat.of (Residues l E n) (scalarCokernel l E d n))).over U)) ∧
    (∀ i : ℤ, i ≠ -1 → i ≠ 0 →
      IsZero (((DerivedCategory.homologyFunctor _ i).obj K).over U)) ∧
    Nonempty (((DerivedCategory.homologyFunctor _ (-1)).obj
      ((overDerived J (coefficient l E J n) U).obj K)) ≅
      (((constantAtLevel l E J n).obj
        (ModuleCat.of (Residues l E n) (scalarKernel l E d n))).over U)) ∧
    Nonempty (((DerivedCategory.homologyFunctor _ 0).obj
      ((overDerived J (coefficient l E J n) U).obj K)) ≅
      (((constantAtLevel l E J n).obj
        (ModuleCat.of (Residues l E n) (scalarCokernel l E d n))).over U)) := by sorry

end IntegralMatrix
end AlgebraicGeometry.ProEtale
