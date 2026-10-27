/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T4
-/
module

public import Sheaf.Paper.FiniteClopenExceptionalRestriction
public import Sheaf.Paper.CompleteResidueLineInverse
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-! # The residue line of a normalized smooth component

Source: blueprint thm-pur-cohomological-smoothness, first paragraph.
(blueprint: lem-pur-smooth-clopen-residue-line).
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures.PurityFiniteSetting

variable (P : PurityFiniteSetting.{u})
    (E : Type u) [Field E] [Algebra (Padic P.coefficients.l) E]
    [FiniteDimensional (Padic P.coefficients.l) E]
    (X Y : Over (Spec (.of P.field.k)))
    [LocallyOfFiniteType (X.left ↘ Spec (.of P.field.k))]
    [QuasiCompact (X.left ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y.left ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y.left ↘ Spec (.of P.field.k))]
    (g : X.left ⟶ Y.left) [g.IsOver (Spec (.of P.field.k))]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]

/-- The first reduction of the actual integral exceptional unit is a shifted etale line.

Source: blueprint thm-pur-cohomological-smoothness, first paragraph; the first step
of lem-pur-smooth-clopen-component-inverse.
(blueprint: lem-pur-smooth-clopen-residue-line).

Proof: compare R.integralI with the normalized integral exceptional functor for
c.precomp j.left by the counit-preserving uniqueness of right adjoints to the same
integral compact-support functor. Apply its actual reduction-system comparison to
the integral coefficient unit. The normalized reduction of the unit is the finite
coefficient unit, and reduction of this exceptional image is the intrinsic finite
exceptional image of that unit. This comparison uses the canonical reduction system
of the integral exceptional construction, not an arbitrary tower having its limit.
The finite exceptional adjunction comparison and the etale/pro-etale comparison unit
identify the latter with the intrinsic realization of the ordinary etale dualizing
complex. Smooth tensor duality writes that complex as L[2d], with L etale locally
free of rank one. Exact intrinsic comparison commutes with the degree-zero embedding
and shifts. Compose these isomorphisms and transport the etale local line condition.
No basis of L is chosen. Finite type over the fixed field supplies Noetherianity
and invertibility of the coefficient prime; the empty scheme and d=0 are included. -/
theorem smooth_clopen_residue_line
    (Xi : Over (Spec (.of P.field.k)))
    [LocallyOfFiniteType (Xi.left ↘ Spec (.of P.field.k))]
    [QuasiCompact (Xi.left ↘ Spec (.of P.field.k))]
    (c : Compactification g) (j : Xi ⟶ X)
    [IsOpenImmersion j.left] [IsClosedImmersion j.left]
    (R : ClopenExceptionalCoefficientComparison P E X Y Xi g c j)
    (d : ℕ) [SmoothOfRelativeDimension d (j.left ≫ g)] :
    let U : sfIntegralConstructibleCategory P.coefficients.l E Y.left :=
      ⟨integralConstantCoefficientObject P.coefficients.l E Y.left,
        (integralConstantCoefficient_constructible P.coefficients.l E Y.left
          P.field P.coefficients.different).2.1⟩
    ∃ L : Sheaf Xi.left.smallEtaleTopology
        (ModuleCat.{u + 1} (ULift.{u + 1, u}
          (Padic.coefficientExtensionRing P.coefficients.l E 1))),
      completeResidueEtaleLine Xi.left (Padic.coefficientExtensionRing P.coefficients.l E 1) L ∧
      Nonempty ((scalarReductionDerivedExtension P.coefficients.l E Xi.left 0).obj
          (R.integralI.obj U).obj ≅
        ((DerivedCategory.singleFunctor _ 0).obj
          ((completeResidueEtalePullback P.coefficients.l E Xi.left 0).obj L))⟦2 * (d : ℤ)⟧) := by
  sorry

end WeilConjectures.PurityFiniteSetting
