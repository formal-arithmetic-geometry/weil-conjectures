/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace
public import WeilConjectures.EtaleCohomology.Purity.Smooth.DiagonalOrientation
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion

/-!
# The finite orientation of an open immersion

Let `j : U ⟶ X` be a quasi-compact separated open immersion, smooth of relative dimension `0`,
and `Λ` a finite coefficient ring with invertible exponent and a normalized Kummer class. The
orientation `Rj^! Λ_X ≅ Λ_U(0)[0]` of the diagonal argument
(`AlgebraicGeometry.Etale.dualizingComplexTwistShiftIso`, blueprint
`thm-pur-diagonal-dualizing-object`) is expected to be the canonical identification
`Rj^! Λ_X ≅ j^* Λ_X ≅ Λ_U ≅ Λ_U(0)[0]`
(`AlgebraicGeometry.Etale.dualizingComplexTwistShiftIso_of_isOpenImmersion`, `sorry`ed): for `j`
the diagonal `U ⟶ U ×_X U` is an isomorphism, the base change map of the dualizing complexes is
the canonical one, and the fundamental class of an isomorphism in codimension `0` is `1`
(the class restricting to the trivial frame classes). This is the finite step of
`ProEtale.CondensedRing.isIntegralSmoothOrientation_integralOpenImmersionOrientation`
(blueprint `det-sp-trace-basic`, part 3: for étale `f` the orientation is the identity).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Etale

open Scheme

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] [HasKummerClass Λ]
  [HasKummerClass.IsNormalized Λ] {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
  [SmoothOfRelativeDimension 0 j] [HasCompactification j] [IsSeparated j] [QuasiCompact j]
  [HasInvertibleExponent Λ U]

/-- Blueprint `det-sp-trace-basic`, part 3, for an open immersion: **the diagonal orientation of
an open immersion `j` is the canonical identification**
`Rj^! Λ_X ≅ D(j^*) Λ_X ≅ Lj^* Λ_X ≅ Λ_U ≅ Λ_U(0)[0]`. -/
theorem dualizingComplexTwistShiftIso_of_isOpenImmersion {k : Type u} [Field k]
    (aX : X ⟶ Spec (.of k)) [IsSeparated aX] [LocallyOfFiniteType aX] :
    dualizingComplexTwistShiftIso Λ j 0 aX =
      (rightDerivedUpperShriekIsoOfIsOpenImmersion Λ j).app _ ≪≫
        (leftDerivedUpperStarIsoMapDerivedCategory _ j).symm.app _ ≪≫
        leftDerivedUpperStarConstantComplexIso Λ j ≪≫ (twistShiftZeroIso Λ U rfl _).symm :=
  sorry

end AlgebraicGeometry.Etale
