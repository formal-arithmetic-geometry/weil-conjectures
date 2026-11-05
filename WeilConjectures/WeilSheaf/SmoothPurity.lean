/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.PurityTensorMap
public import WeilConjectures.WeilSheaf.LowerShriek
public import WeilConjectures.WeilSheaf.TateTwist
public import WeilConjectures.WeilSheaf.TateTwistNativeTensor
public import WeilConjectures.WeilSheaf.UpperShriek
public import WeilConjectures.WeilSheaf.UpperShriekGeometric
public import WeilConjectures.WeilSheaf.UpperShriekUnitTensorMap
public import WeilConjectures.WeilSheaf.UpperStarConstant
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.IsoAlgebraComp
import WeilConjectures.TraceFormula.PurityDevissage
import WeilConjectures.WeilSheaf.SmoothPurityMapOfOrientation
import WeilConjectures.WeilSheaf.SmoothPurityNativeTateDescent
import WeilConjectures.WeilSheaf.SmoothPurityOrientationOfTateEncoding

/-!
# Smooth purity for Weil complexes

For a smooth separated morphism `f : X ⟶ Y` of pure relative dimension `d` of `k₀`-schemes of
finite type, the exceptional inverse image of Weil complexes is the twisted shifted pullback,
`Rf^! ≅ f^*(d)[2d]`. Since `Rf^!` is characterized as the right adjoint of the direct image with
compact support `Rf₀!` (`def-weil-exceptional-inverse-image`), this is the statement that
`f^*(d)[2d]` is right adjoint to `Rf₀!`
(`AlgebraicGeometry.WeilComplex.nonempty_derivedLowerShriek_adjunction_of_smooth`, the Weil stage
`Λ = ℚ̄_ℓ` of `sk-thm-purity-transport`).

## Proof

`Rf₀!` has a right adjoint `Rf^!`
(`AlgebraicGeometry.WeilComplex.isLeftAdjoint_derivedLowerShriek`), so it suffices to show
`f^*(d)[2d] ≅ Rf^!`. Forgetting the Weil structure, the underlying complex of `Rf^! L` on the
geometric fibre `X̄` is `Rf̄^!` of that of `L`
(`WeilComplex.nonempty_adicSheafDerivedEquivCondensedMod_forget_obj_iso_upperShriek`).
Through this identification, the purity map `γ_{f,L} : f^* L(d)[2d] ⟶ Rf^! L` of Weil complexes
is the geometric purity map `f̄^* L̄ ⊗ Rf̄^! ℚ̄_ℓ ⟶ Rf̄^! L̄`
(`AlgebraicGeometry.WeilComplex.exists_natTrans_forget_eq_upperShriekUnitTensorMap`),
which is an isomorphism by smooth purity over `k̄`
(`AlgebraicGeometry.ProEtale.CondensedRing.isIso_upperShriekUnitTensorMap_of_smooth`). Forgetting
the Weil structure reflects isomorphisms
(`CategoryTheory.Endofunctor.IsoAlgebra.isIso_of_isIso_forget_mapDerivedCategory_map`), so `γ_f`
is an isomorphism.

As in the blueprint (`def-pur-smooth-purity-map`), `γ_f` is the composite
`f^* L(d)[2d] ≅ f^* L ⊗ ℚ̄_ℓ(d)[2d] ≅ f^* L ⊗ Rf^! ℚ̄_ℓ ⟶ Rf^! L` of
- the identification of the Tate twist with a tensor product
  (`AlgebraicGeometry.WeilComplex.nonempty_nativeConstructibleTensor_iso_tateTwist_comp_shift`);
- the inverse of the Weil orientation `Rf^! ℚ̄_ℓ ≅ ℚ̄_ℓ(d)[2d]`
  (`AlgebraicGeometry.WeilComplex.nonempty_upperShriek_obj_adicConstant_iso_of_smooth`);
- the co-projection map of Weil complexes, which lies over the geometric one
  (`AlgebraicGeometry.WeilComplex.exists_coprojection_forget_eq_upperShriekUnitTensorMap`).

## Unfinished

The identification of the Tate twist with a tensor product is proved, and so is the
Frobenius-equivariant orientation
(`AlgebraicGeometry.WeilComplex.exists_forget_upperShriek_adicConstant_iso_comm_derivedStrIso`,
`thm-pur-weil-equivariance-of-purity-and-trace`), from the native Tate encoding (A3) and the
invertibility of the exceptional unit base change along `k₀ ⟶ k̄₀` (A1', by Verdier duality).
The remaining input of `γ_f` rests on a statement with `sorry`:
- the co-projection map needs the compatibility of forgetting the Weil structure with the native
  tensor product, the projection formula and the counit of `Rf₀! ⊣ Rf^!`. The Weil projection
  formula is known to exist, through the proper projection formula
  `AlgebraicGeometry.WeilComplex.nonempty_rightDerivedLowerStar_nativeDerivedTensor_iso`.

The absolute dualizing-complex theorem and the trivial-line Thom theorem use a separate route:
`WeilConjectures.WeilSheaf.SmoothPurityAbsolute` descends the finite-base dualizing object and
identifies its Tate datum, and `WeilConjectures.WeilSheaf.SmoothPurityThomFromTate` applies the
compact projection formula. Their users in `VerdierDual` and `FourierInversion.OtherSections`
therefore do not invoke the unfinished relative orientation above. The declaration-level check
in `WeilConjectures.WeilSheaf.SmoothPurityDependencyAudit` verifies this separation.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

namespace WeilComplex

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))]
  (f : X ⟶ Y) [f.IsOver (Spec (CommRingCat.of k₀))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))] [QuasiSeparated (Y ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]

section Geometric

open ProEtale MonoidalCategory

variable [IsSeparated (Y ↘ Spec (CommRingCat.of k₀))]
  [IsSeparated (X ↘ Spec (CommRingCat.of k₀))] [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
  [HasUpperShriek k₀ l f]

end Geometric

end WeilComplex

end AlgebraicGeometry
