/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SmoothPurityTowerGamma

/-! # Bounds for tensoring with an evaluated ordered Tate line

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/
sk-prop-sp-tower-geometric/sk-prop-sp-tower-geometric-gamma.proof.md, (3).
The natural level n denotes the positive exponent n+1.
(blueprint: lem-sp-ordered-line-level-bounds).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genInjectivity false
set_option genSizeOfSpec false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry.Scheme WeilConjectures

namespace AlgebraicGeometry.ProEtale.SpPurityReduction

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  [b : SpTowerShriek.Base l E]

/-- Tensor with the finite evaluation of the ordered d-fold positive Tate line
shifted by two preserves constructible cohomology and subtracts 2d from each Tor
endpoint. The input is any finite-coefficient derived object; no morphism or
strict-tower lift of that object is involved.

Source: gamma proof (3), the twist part of the uniform-domain calculation;
prop-weil-twist-preserves and Stacks Tag 08FZ.
(blueprint: lem-sp-ordered-line-level-bounds).

Proof: evaluate the ordered line recursively, using the actual tensor-evaluation
comparison in b.calculus. At d=0, the evaluated tower unit is the coefficient
unit, so tensor is the identity. At a successor, evaluation of the new factor
commutes with its shift and its degree-zero inclusion. The comparison w.level
identifies it with the positive ell-power Tate line. This line is locally free
of rank one: write ell as a unit times a positive power of the uniformizer and
apply the finite Tate-line trivializations in prop-weil-twist-preserves over the
resulting quotient ring. Tensoring by this degree-zero line is exact and locally
the identity, hence preserves constructible cohomology and every specified Tor
interval. For each degree-zero test module, associativity computes the test
tensor with the shifted line, and H^i(C[2]) = H^(i+2)(C) subtracts two from both
endpoints. Induction gives subtraction by 2d. Transport along the evaluation
and associativity isomorphisms throughout. Only this one coefficient level is
used. The argument includes d=0, n=0, equal endpoints and the zero object.
-/
theorem ordered_line_level_bounds
    (D : FiniteFieldDatum.{u}) [CharP D.k D.p] (hne : l ≠ D.p)
    (T : Scheme.{u}) [IsNoetherian T] [T.Over (Spec (.of D.k))]
    [IsSeparated (T ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (T ↘ Spec (.of D.k))] [QuasiCompact (T ↘ Spec (.of D.k))]
    (w : SpChartAdmissibility.Twists l E T) (d n : ℕ)
    (M : proEtaleDerivedCategory T (SpTowerShriek.R l E n))
    (hM : spFiniteConstructibleTor T (SpTowerShriek.R l E n) M)
    (a z : ℤ)
    (hTor : HasProEtaleTorAmplitude T (SpTowerShriek.R l E n) M a z) :
    let N := ((b.calculus T).levelClosed n).tensor.obj
      (M, (SpTowerShriek.Ev l E T n).obj (SpTowerGamma.orderedLine l E b T w d))
    (∀ i : ℤ, IsConstructibleProEtaleModuleSheaf T (SpTowerShriek.R l E n)
      ((DerivedCategory.homologyFunctor
        (proEtaleRingModules T (proEtaleConstantRing T (SpTowerShriek.R l E n))) i).obj N)) ∧
      HasProEtaleTorAmplitude T (SpTowerShriek.R l E n) N
        (a - 2 * d) (z - 2 * d) := by sorry

end AlgebraicGeometry.ProEtale.SpPurityReduction

attribute [instance high] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
