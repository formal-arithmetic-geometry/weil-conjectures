/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CurrentIntegralData

/-! # Single-morphism integral realization

Source: latest blueprint, sec-smooth-purity, composition-comparisons, integral clause.
(blueprint: lem-sp-current-composition-integral-edge).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.ProEtale.CompositionComparisons
open IntegralDirectImageTower NormalizedIntegralAdjunction

/-- One normalized integral realization of a supplied smooth tower adjunction over k.
Source: latest blueprint, composition-comparisons proof, final paragraph; normalized
reduction equivalence and integral-direct-image identification.
(blueprint: lem-sp-current-composition-integral-edge).

Proof in words:
1. Finite type over the field makes X and Y Noetherian; p != l makes l invertible.
The integral criterion makes the section images of the constructible inputs complete.
The specified reduction towers are normalized and constructible with common Tor bounds.
2. Take the normalized scalar geometry and total restricted limits from the direct-image
construction. Its canonical whole-tower comparison for c is the proper/open mate;
restricting it gives leftComparison with the required left_normalization equation.
Its constructibility clause is supportClosed.
3. Compare the supplied tower right adjoint with the geometrically constructed one by
uniqueness of right adjoints to the same compact-support functor. The transition formulas
for the finite exceptional coefficient mates show that it preserves normalized inputs.
The common finite cohomological/Tor bounds and tower reconstruction give closedness of
Rlim G red. These assertions are invariant under the right-adjoint comparison.
4. The reduction/limit counit is invertible on these normalized G red values. Restrict it
to obtain rightComparison, whose underlying component is exactly the specified counit.
5. The two constructible reductions are fully faithful by the normalized equivalence
and the coefficient-model comparison. Restrict the supplied tower adjunction through
leftComparison and rightComparison. The formulas for a restricted adjunction give
unit_reduction and counit_reduction, and finish all fields of IntegralEdge. -/
theorem integralEdge
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (hpl : p ≠ l)
    {X Y : Scheme.{u}}
    [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))] [LocallyOfFiniteType (Y ↘ Spec (.of k))]
    [QuasiCompact (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
    (d : ℕ) [SmoothOfRelativeDimension d f]
    (s : Presentation l E)
    (c : Compactification f)
    (hF : ∀ M : Towers l E s X,
      spConstructibleTorTowers l E Y (s.towers Y)
        ((towerShriek l E s c).obj M.obj))
    (G : Towers l E s Y ⥤ Towers l E s X)
    (a : towerSupport l E s c hF ⊣ G) :
    Nonempty (IntegralEdge l E s c hF G a) := by
  sorry

end AlgebraicGeometry.ProEtale.CompositionComparisons
