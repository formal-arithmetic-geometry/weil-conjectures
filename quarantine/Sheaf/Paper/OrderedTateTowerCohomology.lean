/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group X8
-/
module

public import Sheaf.Paper.SmoothPurityTowerGammaData
public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite

/-! # Cohomology of ordered shifted Tate towers

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/
sk-prop-sp-composition/sk-prop-sp-composition-factors.proof.md, (1), tower paragraph.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry.Scheme WeilConjectures
namespace AlgebraicGeometry.ProEtale.SpCompositionFactors

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (b : SpTowerShriek.Base l E)

/-- Cohomology of an ordered shifted Tate tower, including its finite local rank.
Source: composition-factors proof (1), tower paragraph, concentration argument
(blueprint: lem-sp-ordered-tate-tower-cohomology).

Proof: the first Tate line is locally free of rank one by twist-sheaf-locally-free.
Write ell as a unit times the a-th power of a uniformizer and evaluate at a(n+1)
to obtain the ell^(n+1) coefficient quotient, with no unramified assumption. Its
positive tensor powers are locally free of rank one, as is the coefficient unit
at power zero. Such lines are flat: on their trivializing covers their tensor
functors are the identity. Exactness of tower tensor with these lines follows
levelwise from coefficient-towers-abelian. Induct on orderedLine. The coefficient
unit is in degree zero; each tensor with the shifted degree-one line shifts the
sole nonzero cohomology degree down by two. Exact evaluation commutes with this
homology and identifies its value with the corresponding finite Tate power.
This gives local rank one. Vanishing is asserted in the ambient tower category:
all its evaluations vanish, so the cohomology system is zero componentwise.
On the empty scheme the local rank condition is vacuous and all systems vanish.
The argument concerns coefficient lines only and uses no normalized-input
assumption. -/
theorem ordered_tate_tower_cohomology (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))] [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))]
    (w : SpChartAdmissibility.Twists l E X) (r : ℕ) :
    (∀ i : ℤ, i ≠ -2 * (r : ℤ) →
      IsZero ((DerivedCategory.homologyFunctor (SpTowerShriek.S l E X) i).obj
        (SpTowerGamma.orderedLine l E b X w r))) ∧
    ∀ n : ℕ, ((SpTowerShriek.ev l E X n).obj
      ((DerivedCategory.homologyFunctor (SpTowerShriek.S l E X) (-2 * (r : ℤ))).obj
        (SpTowerGamma.orderedLine l E b X w r))).IsFiniteLocallyFreeOfRank 1 := by sorry

end AlgebraicGeometry.ProEtale.SpCompositionFactors
