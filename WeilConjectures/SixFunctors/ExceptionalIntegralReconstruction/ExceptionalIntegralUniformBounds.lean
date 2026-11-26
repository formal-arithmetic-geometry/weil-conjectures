/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ExceptionalIntegralReconstruction.ExceptionalIntegralReconstructionInterfaces

/-!
# Uniform bounds for exceptional integral systems

The images of normalized systems under the exceptional operations have common finite
cohomological and Tor intervals.

## Implementation details

At each coefficient exponent, the evaluated outputs are identified with the intrinsic finite
compact-support and exceptional inverse-image functors, via the coordinate evaluation comparison,
the proper/open finite evaluation and the site comparisons. The uniform exceptional constants are
chosen before varying the exponent, and endpoints are enlarged by minima and maxima. No absolute
separatedness of `X` or `Y` and no flatness of coefficient quotients is used.

## References

* [Zheng, Propositions 2.23, 2.29, 3.16 and 5.24]
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [local semireducible] AlgebraicGeometry.exceptionalProSystemDerived
  AlgebraicGeometry.exceptionalProLevelDerived AlgebraicGeometry.strictEtaleLevelDerived

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.ExceptionalIntegralReconstruction

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The images of normalized systems under `s.left` and `s.exceptional` satisfy
`LevelBounds`: they have common finite cohomological and Tor intervals. -/
theorem exceptionalIntegralUniformBounds
    (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    {X Y : Scheme.{u}} {f : X ⟶ Y}
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    [f.IsOver (Spec (.of D.k))] [IsSeparated f] [LocallyOfFiniteType f]
    [QuasiCompact f] (c : Compactification f) (s : Systems l E c) :
    (∀ N, normalized l E X N →
      IntegralSystemRealization.LevelBounds l E Y ((s.left l E c).obj N)) ∧
    (∀ N, normalized l E Y N →
      IntegralSystemRealization.LevelBounds l E X ((s.exceptional l E c).obj N)) := by sorry

end WeilConjectures.ExceptionalIntegralReconstruction
