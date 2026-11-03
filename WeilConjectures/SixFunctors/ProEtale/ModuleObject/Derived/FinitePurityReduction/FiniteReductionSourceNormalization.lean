/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.FinitePurityReduction.FiniteReductionSourceData

/-! # Unique root-normalized finite-reduction source comparison

Source: finite-reduction proof Step 2, compatible primitive-root coordinates.
(blueprint: lem-pur-finite-reduction-source-normalization).
The coefficient bundle is imported, not reconstructed here.
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

/-- Existence and uniqueness of the chart-normalized twisted-source comparison.
Source: Step 2 (blueprint: lem-pur-finite-reduction-source-normalization).
Proof: choose a primitive ell^(n+1) root over the algebraically closed base and
its ell^(n-m) power. The chart conjugate defines an isomorphism. Changing the
primitive root multiplies both charts by corresponding scalar units, which
commute with the scalar-linear pullback mate. Thus every compatible pair gives
the same conjugate. Evaluating the normalization at the chosen pair proves
uniqueness; empty schemes and d=0 follow from the unit charts. -/
theorem sourceComparison_existsUnique (m n : ℕ) (hmn : m ≤ n)
    (D : WeilConjectures.FiniteFieldDatum.{u}) (hEll : ell ≠ D.p)
    {X Y : Over (Spec (.of D.k))} (f : X ⟶ Y) (d : ℕ)
    (K : DerivedCategory (ModuleRingedComparison.internalModules
      (coefficient ell E n).X Y.left)) :
    ∃! e : (scalarSixChange (quotient ell E m n hmn) X.left).obj
      (((coefficientFiniteTwistFunctor ell E X.left n (d : ℤ)).obj
        ((scalarSixPull (coefficient ell E n) f.left).obj K)) ⟦2 * (d : ℤ)⟧) ≅
      (((coefficientFiniteTwistFunctor ell E X.left m (d : ℤ)).obj
        ((scalarSixPull (coefficient ell E m) f.left).obj
          ((scalarSixChange (quotient ell E m n hmn) Y.left).obj K))) ⟦2 * (d : ℤ)⟧),
      SourceNormalized ell E m n hmn f d K e := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing.FinitePurityReduction
