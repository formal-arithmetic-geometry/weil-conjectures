/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
public import WeilConjectures.CategoryTheory.DerivedCategory.Perfect
public import WeilConjectures.Algebra.Category.ModuleCat.DerivedBaseChange
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.DerivedCategory.Linear
public import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.Algebra.Homology.ShortComplex.Linear
import WeilConjectures.Algebra.Homology.MinimalMatrixComplex
import WeilConjectures.Algebra.Homology.MatrixComplexTower
import WeilConjectures.NumberTheory.Padics.IntegersProfiniteTower
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
import Mathlib.RingTheory.Ideal.Quotient.Index
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.Algebra.Ring.Pi
import Mathlib.Topology.Homeomorph.Defs
import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Topology.Compactness.Compact
import WeilConjectures.NumberTheory.Padics.IntegersCosetBasis
import Mathlib.Topology.Bases
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.NumberTheory.Padics.ProperSpace
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvr
import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Localization.FractionRing
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrCore
import Mathlib.Analysis.Normed.Algebra.Ultra
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Algebra.Valued.LocallyCompact
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorization
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorizationUnique
import WeilConjectures.Mathlib.RingTheory.OrderOfVanishing.Noetherian

/-!
# Perfect complexes over the integral coefficient tower

Source: Weil conjectures blueprint, `sk-lem-integral-scalar-towers`, statement (1), (2)
(blueprint: sk-lem-integral-scalar-towers).

Positive levels are indexed by `n : ℕ`, with level `n` meaning exponent `n + 1`.
The isomorphisms of (1) are expressed by their adjoint universal arrows. For a bounded
finite free complex, ordinary quotient reduction computes derived scalar extension.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits

namespace Padic

/-- The ordinary quotient complex by a power of a scalar, constructed as a cokernel.
Cokernels of complexes of modules are computed degreewise, so this is the termwise quotient.
Source: blueprint `sk-lem-integral-scalar-towers`, statement (2)
(blueprint: sk-lem-integral-scalar-towers). -/
def scalarQuotient {A : Type u} [CommRing A]
    (t : A) (Q : CochainComplex (ModuleCat.{u} A) ℤ) (n : ℕ) :
    CochainComplex (ModuleCat.{u} A) ℤ :=
  cokernel (t ^ n • 𝟙 Q)

/-- The actual quotient transition, induced by the identity on the integral complex.
Source: blueprint `sk-lem-integral-scalar-towers`, statement (2)
(blueprint: sk-lem-integral-scalar-towers). -/
def scalarQuotientTransition {A : Type u} [CommRing A]
    (t : A) (Q : CochainComplex (ModuleCat.{u} A) ℤ)
    (m n : ℕ) (h : n ≤ m) : scalarQuotient t Q m ⟶ scalarQuotient t Q n :=
  cokernel.desc (t ^ m • 𝟙 Q) (cokernel.π (t ^ n • 𝟙 Q)) (by
    rw [← Nat.sub_add_cancel h, pow_add, mul_smul, Linear.smul_comp,
      cokernel.condition, smul_zero])

section Coefficients

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  [HasDerivedCategory.{v} (ModuleCat.{u} (coefficientExtensionIntegers l E))]
  [∀ n : ℕ, HasDerivedCategory.{v} (ModuleCat.{u} (coefficientExtensionRing l E n))]

end Coefficients

end Padic
