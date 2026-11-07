/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Submission.WeilConjectures.TraceFormula.PurityTensorMap
public import Submission.WeilConjectures.WeilSheaf.LowerShriek
public import Submission.WeilConjectures.WeilSheaf.TateTwist
public import Submission.WeilConjectures.WeilSheaf.TateTwistNativeTensor
public import Submission.WeilConjectures.WeilSheaf.UpperShriek
public import Submission.WeilConjectures.WeilSheaf.UpperShriekGeometric
public import Submission.WeilConjectures.WeilSheaf.UpperShriekUnitTensorMap
public import Submission.WeilConjectures.WeilSheaf.UpperStarConstant
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.IsoAlgebraComp
import Submission.WeilConjectures.TraceFormula.PurityDevissage
import Submission.WeilConjectures.WeilSheaf.SmoothPurityMapOfOrientation
import Submission.WeilConjectures.WeilSheaf.SmoothPurityNativeTateDescent
import Submission.WeilConjectures.WeilSheaf.SmoothPurityOrientationOfTateEncoding

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

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

/-- **Frobenius equivariance of the orientation of a smooth morphism** (blueprint:
`thm-pur-weil-equivariance-of-purity-and-trace`, the purity square at `K = ℚ̄_ℓ`): for a smooth
separated morphism `f : X ⟶ Y` of pure relative dimension `d`, there is an isomorphism
`Rf̄^! ℚ̄_ℓ ≅ ℚ̄_ℓ(d)[2d]` of the underlying complexes on the geometric fibre `X̄` which commutes
with the Frobenius structures `Fr_X^* (-) ≅ (-)` of the two Weil complexes
(`CategoryTheory.Endofunctor.IsoAlgebra.derivedStrIso`).

Mathematically, this is the canonical orientation. Under the identification of the underlying
complex of `Rf^! ℚ̄_ℓ` with `Rf̄^! ℚ̄_ℓ`
(`WeilComplex.nonempty_adicSheafDerivedEquivCondensedMod_forget_obj_iso_upperShriek`), the
Frobenius structure of `Rf^! ℚ̄_ℓ` is the exceptional datum
`Fr_X^* Rf̄^! ℚ̄_ℓ ⟶ Rf̄^! Fr_Y^* ℚ̄_ℓ ≅ Rf̄^! ℚ̄_ℓ` of the cartesian Frobenius square. The
canonical orientation is compatible with base change along this square
(`thm-pur-smooth-base-change-coherence`), so it carries the exceptional datum to the Tate datum
(`def-pur-tate-datum`), which is the Frobenius structure of `ℚ̄_ℓ(d)[2d]`. Equivalently,
geometric Frobenius acts on `R^{2d} f̄_! ℚ̄_ℓ` by `q^d` through the trace.

Proof: the native Tate encoding `α` (A3,
`AlgebraicGeometry.WeilSheaf.purity_nonempty_toCondensedTateDescentIso`: the Tate twist sheaf is
the descent of the finite-base root-defined Tate sheaf) and the invertibility of the exceptional
base change map at the unit along `k₀ ⟶ k̄₀` for every smooth `f` (A1',
`ProEtale.CondensedRing.isIso_smoothUnitBaseChange_descendedShriekGeometricExchange`,
by Verdier duality) produce the orientation as an isomorphism of native Weil complexes
(`exists_forget_upperShriek_adicConstant_iso_comm_derivedStrIso_of_tateEncoding`), so it
commutes with the Frobenius structures. -/
theorem exists_forget_upperShriek_adicConstant_iso_comm_derivedStrIso (d : ℕ)
    [SmoothOfRelativeDimension d f] :
    ∃ g : forget.obj ((upperShriek f).obj
        (WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k₀ l Y))) ≅
      forget.obj (((tateTwist k₀ l X d).obj
        (WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k₀ l X)))⟦(2 * d : ℤ)⟧),
      (Endofunctor.IsoAlgebra.derivedStrIso _).hom.app
          ((upperShriek f).obj (WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k₀ l Y))).obj ≫
          g.hom =
        (WeilSheaf.frobeniusPullback k₀ l X).mapDerivedCategory.map g.hom ≫
          (Endofunctor.IsoAlgebra.derivedStrIso _).hom.app (((tateTwist k₀ l X d).obj
            (WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k₀ l X)))⟦(2 * d : ℤ)⟧).obj := by
  obtain ⟨α⟩ := WeilSheaf.purity_nonempty_toCondensedTateDescentIso k₀ l X d
  exact exists_forget_upperShriek_adicConstant_iso_comm_derivedStrIso_of_tateEncoding f d α

/-- **The Weil orientation of a smooth morphism** (blueprint:
`cor-pur-adic-and-rational-smooth-dualizing-complexes`, at the coefficient stage `ℚ̄_ℓ` with Weil
structures): for a smooth separated morphism `f : X ⟶ Y` of pure relative dimension `d`, the
relative dualizing complex `Rf^! ℚ̄_ℓ` is isomorphic to `ℚ̄_ℓ(d)[2d]` as a Weil complex.

On the geometric fibre this is the smooth purity isomorphism `Rf̄^! ℚ̄_ℓ ≅ ℚ̄_ℓ(d)[2d]`
(`AlgebraicGeometry.ProEtale.CondensedRing.smoothPurityIso`). The content is that the orientation
commutes with the Frobenius structures, as in the finite-coefficient statement over `Spec k₀`
`AlgebraicGeometry.Etale.exists_iso_dualizingComplex_isWeilMorphism`
(`AlgebraicGeometry.WeilComplex.exists_forget_upperShriek_adicConstant_iso_comm_derivedStrIso`).
A Frobenius-equivariant isomorphism of underlying complexes lifts to an isomorphism of Weil
complexes (`CategoryTheory.Endofunctor.IsoAlgebra.nonempty_iso_of_forget_mapDerivedCategory_iso`).

`AlgebraicGeometry.WeilComplex.nonempty_rightAdjoint_obj_adicConstant_iso_of_smooth` is the same
statement for an arbitrary right adjoint of `Rf₀!`, deduced from smooth purity. -/
theorem nonempty_upperShriek_obj_adicConstant_iso_of_smooth (d : ℕ)
    [SmoothOfRelativeDimension d f] :
    Nonempty ((upperShriek f).obj (WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k₀ l Y)) ≅
      ((tateTwist k₀ l X d).obj
        (WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k₀ l X)))⟦(2 * d : ℤ)⟧) := by
  obtain ⟨g, hg⟩ :=
    exists_forget_upperShriek_adicConstant_iso_comm_derivedStrIso (k₀ := k₀) (l := l) f d
  obtain ⟨e⟩ := Endofunctor.IsoAlgebra.nonempty_iso_of_forget_mapDerivedCategory_iso _ g hg
  exact ⟨ObjectProperty.isoMk _ e⟩

end Geometric

end WeilComplex

end AlgebraicGeometry
