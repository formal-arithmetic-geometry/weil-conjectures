/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.LowerShriek
public import WeilConjectures.WeilSheaf.TateTwist

/-! # Vanishing outside the native smooth dualizing degree

This is the geometric vanishing input used to obtain the two canonical t-structure bounds.
-/

@[expose] public section
set_option autoImplicit false

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.WeilComplex

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)] {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]

/-- The native exceptional constant object has no cohomology outside degree `-2d`.

Source: current blueprint, `cor-pur-adic-and-rational-smooth-dualizing-complexes`,
smooth specialization, and `cor-coef-verdier-weil-equivariance`.
(blueprint: lem-sf-weil-smooth-dualizing-concentration)

Proof: base change the structure morphism to the algebraic closure and apply the
counit-normalized native exceptional-forgetting comparison.  The coefficient-stage
smooth purity theorem identifies the resulting ordinary exceptional object with the
constant Tate line shifted by `2d`; exact conservative forgetting transports its
vanishing in every other degree back to the native Weil category.  Frobenius
compatibility is only used to transport the comparison, so no identification of the
surviving Weil sheaf is needed here.
-/
theorem smooth_dualizing_homology_vanishing
    (J : WeilComplex k₀ l (Spec (CommRingCat.of k₀)) ⥤ WeilComplex k₀ l X)
    (adj : derivedLowerShriek k₀ l (X ↘ Spec (CommRingCat.of k₀)) ⊣ J)
    (d : ℕ) [SmoothOfRelativeDimension d (X ↘ Spec (CommRingCat.of k₀))] :
    ∀ i : ℤ, i ≠ -2 * (d : ℤ) →
      IsZero ((homologySheaf i).obj
        (J.obj (WeilSheaf.toComplex.obj
          (WeilSheaf.adicConstant k₀ l (Spec (CommRingCat.of k₀)))))) := by
  sorry

end AlgebraicGeometry.WeilComplex
