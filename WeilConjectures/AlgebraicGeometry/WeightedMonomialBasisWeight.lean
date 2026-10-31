/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.HilbertPluckerPGLLinearization
public import WeilConjectures.AlgebraicGeometry.UniformProjectiveFibreVanishing
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.Order.ConditionallyCompleteLattice.Basic

/-! # Weighted monomial bases and their minimum weight

Source: Morrison, arXiv:0810.2340, Section 2.2, Proposition 1, printed pp.6--7.
(blueprint: def-sfb-weighted-monomial-basis-weight)
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.BoundedHilbertWeight

/-- The actual degree-m module cohomology, with its structural k-vector-space action.
Source: Morrison §2.2 (blueprint: def-sfb-weighted-monomial-basis-weight). -/
abbrev sections (k : Type u) [Field k] (n : ℕ) {X : Scheme.{u}}
    (i : X ⟶ ℙ(HilbertPlucker.Coordinates.{u} n; Spec (.of k))) (m : ℕ) :=
  UniformProjectiveFibreVanishing.cohomology k
    (i ≫ (ℙ(HilbertPlucker.Coordinates n; Spec (.of k)) ↘ Spec (.of k)))
    ((Scheme.Modules.tensorPullback i).obj
      (ProjectiveSpace.twist (HilbertPlucker.Coordinates n) (Spec (.of k)) (m : ℤ))) 0

/-- Linear forms on the specified ambient projective space.
Source: Morrison §2.2 (blueprint: def-sfb-weighted-monomial-basis-weight). -/
abbrev LinearForms (k : Type u) [Field k] (n : ℕ) :=
  MvPolynomial.homogeneousSubmodule (HilbertPlucker.Coordinates.{u} n) k 1

/-- The increasing weighted flag associated to a basis and nonnegative integral weights.
Natural-number weights encode exactly the integral weights with 0 ≤ w_i.
Source: Morrison §2.2 (blueprint: def-sfb-weighted-monomial-basis-weight). -/
def flag {k : Type u} [Field k] {n : ℕ}
    (b : Module.Basis (HilbertPlucker.Coordinates.{u} n) k (LinearForms k n))
    (w : HilbertPlucker.Coordinates.{u} n → ℕ) (s : ℕ) : Submodule k (LinearForms k n) :=
  Submodule.span k {v | ∃ j, w j ≤ s ∧ b j = v}

/-- The degree-m monomial in the chosen linear forms. Homogeneous projection is an
explicit construction and fixes this product of m degree-one factors.
Source: Morrison §2.2 (blueprint: def-sfb-weighted-monomial-basis-weight). -/
def monomial {k : Type u} [Field k] {n : ℕ}
    (b : Module.Basis (HilbertPlucker.Coordinates.{u} n) k (LinearForms k n))
    (m : ℕ) (e : RelativeProjectiveSpace.monomials.{u} (n + 1) m) :
    MvPolynomial.homogeneousSubmodule (HilbertPlucker.Coordinates.{u} n) k m :=
  ⟨MvPolynomial.homogeneousComponent m
    (∏ j : HilbertPlucker.Coordinates.{u} n, (b j).val ^ e.down.val j.down),
    MvPolynomial.homogeneousComponent_mem _ _⟩

/-- A finite set of monomials whose restrictions are linearly independent and span H⁰.
This is the basis condition, including a zero-dimensional target and the empty basis.
Source: Morrison §2.2 (blueprint: def-sfb-weighted-monomial-basis-weight). -/
def IsMonomialBasis {k : Type u} [Field k] {n : ℕ} {X : Scheme.{u}}
    {i : X ⟶ ℙ(HilbertPlucker.Coordinates.{u} n; Spec (.of k))} {m : ℕ}
    (ρ : ModuleCat.of k
      (MvPolynomial.homogeneousSubmodule (HilbertPlucker.Coordinates.{u} n) k m) ⟶
      sections k n i m)
    (b : Module.Basis (HilbertPlucker.Coordinates.{u} n) k (LinearForms k n))
    (S : Finset (RelativeProjectiveSpace.monomials.{u} (n + 1) m)) : Prop :=
  LinearIndependent k (fun e : S ↦ ρ (monomial b m e.val)) ∧
    Submodule.span k (Set.range (fun e : S ↦ ρ (monomial b m e.val))) = ⊤

/-- Total weight of a finite monomial set, summing exponent times linear-form weight.
Source: Morrison §2.2 (blueprint: def-sfb-weighted-monomial-basis-weight). -/
def totalWeight {n m : ℕ} (w : HilbertPlucker.Coordinates.{u} n → ℕ)
    (S : Finset (RelativeProjectiveSpace.monomials.{u} (n + 1) m)) : ℕ :=
  ∑ e ∈ S, ∑ j : HilbertPlucker.Coordinates.{u} n, w j * e.down.val j.down

/-- Minimum monomial-basis weight. The infimum on ℕ is total even in low degrees
where no monomial basis exists; the theorem asserts attainment in its stated range.
Source: Morrison §2.2 (blueprint: def-sfb-weighted-monomial-basis-weight). -/
def weight {k : Type u} [Field k] {n : ℕ} {X : Scheme.{u}}
    {i : X ⟶ ℙ(HilbertPlucker.Coordinates.{u} n; Spec (.of k))} {m : ℕ}
    (ρ : ModuleCat.of k
      (MvPolynomial.homogeneousSubmodule (HilbertPlucker.Coordinates.{u} n) k m) ⟶
      sections k n i m)
    (b : Module.Basis (HilbertPlucker.Coordinates.{u} n) k (LinearForms k n))
    (w : HilbertPlucker.Coordinates.{u} n → ℕ) : ℕ :=
  sInf {v | ∃ S, IsMonomialBasis ρ b S ∧ totalWeight w S = v}

end AlgebraicGeometry.BoundedHilbertWeight
