/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.IntegralDirectImageTower.IntegralDirectImageTowerData

/-! # Current reduction and total inverse limit

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-smooth-purity/sec-sp-grp-ladic-summary/sec-towers-and-integral-coefficients/
sk-lem-sp-tower/_section.md, statement paragraphs 1--2
(blueprint: sk-lem-sp-tower).
The source is the ordinary derived category over the pulled-back condensed ring.
The limit and its normalized adjunction are the existing construction-only interface.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.ProEtale.IntegralDirectImageTower
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- Reduction is left adjoint to the total derived restricted inverse limit, with
its canonical completion unit; on Noetherian schemes this same adjunction is an
 equivalence on the specified full subcategories.
Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-smooth-purity/sec-sp-grp-ladic-summary/sec-towers-and-integral-coefficients/
sk-lem-sp-tower/_section.md, statement and proof (six DAG proof steps)
(blueprint: sk-lem-sp-tower).
Proof: transpose the actual quotient tensor maps to the restricted limit
projections. The tensor-generator normalization identifies the unit with completion.
For Noetherian T, the condensed integral criterion and exact products make the
unit invertible on bounded constructible complexes. The normalized quotient-error
triangle and finite-tail Roos contraction identify every counit evaluation with
an isomorphism. Uniformizer cofinality, the Roos interval and the integral criterion
put the total limit in Dbc. Evaluations detect isomorphisms, so the actual unit
and counit give the equivalence of these two full subcategories. -/
theorem current_integral_tower_adjunction (s : Presentation l E) (T : Scheme.{u}) :
    ∃ L : Limit l E s T,
      ∀ [IsNoetherian T],
      (∀ M : Constructible l E T,
        spNormalizedConstructibleTorTowers l E T (s.towers T)
          ((red l E s T).obj M.obj) ∧
        IsIso ((redLimitAdjunction l E s T L).unit.app M.obj)) ∧
      (∀ C : (spNormalizedConstructibleTorTowers l E T (s.towers T)).FullSubcategory,
        constantModelBoundedConstructible (spIntegralCondensed l E) T
          ((lim l E s T L).obj C.obj) ∧
        IsIso ((redLimitAdjunction l E s T L).counit.app C.obj)) := by
  sorry

end AlgebraicGeometry.ProEtale.IntegralDirectImageTower
