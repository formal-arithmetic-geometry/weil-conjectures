/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FinitePositiveReduction.FiniteReductionPositiveLineComparison
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixDefinitions

/-! # The actual finite quotient as scalar-six coefficient data

Source: finite-reduction proof Step 2, the actual quotient coefficient morphism.
(blueprint: def-pur-finite-reduction-coefficient-data).
The existing twistFiniteRing quotient is bundled without changing its map.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Functor CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.CondensedRing.FinitePurityReduction

variable (ell : ℕ) [Fact ell.Prime]
variable (E : Type u) [Field E] [Algebra (Padic ell) E]
  [FiniteDimensional (Padic ell) E]

/-- The existing discrete condensed finite quotient. Source: coefficient conventions
(blueprint: def-pur-finite-reduction-coefficient-data). -/
abbrev coefficient (n : ℕ) : ScalarSixRing.{u} := ⟨twistFiniteRing ell E n⟩

/-- Multiplication on the bundled quotient. Source: coefficient conventions, Step 2
(blueprint: def-pur-finite-reduction-coefficient-data). -/
instance coefficientMon (n : ℕ) : MonObj (coefficient ell E n).X :=
  (coefficient ell E n).mon

/-- Commutativity on the bundled quotient. Source: coefficient conventions, Step 2
(blueprint: def-pur-finite-reduction-coefficient-data). -/
instance coefficientComm (n : ℕ) : IsCommMonObj (coefficient ell E n).X :=
  (coefficient ell E n).comm

/-- Bundle the actual quotient, without changing its underlying ring map.
Source: finite-reduction Step 2 (blueprint: def-pur-finite-reduction-coefficient-data). -/
def quotient (m n : ℕ) (hmn : m ≤ n) :
    coefficient ell E n ⟶ coefficient ell E m :=
  CommMon.homMk (Mon.ofHom (FinitePositiveReduction.quotient ell E m n hmn))

end AlgebraicGeometry.ProEtale.CondensedRing.FinitePurityReduction
