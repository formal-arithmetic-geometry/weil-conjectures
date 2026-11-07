/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Submission.WeilConjectures.CategoryTheory.Adjunction.MateCoprojection
public import Submission.WeilConjectures.TraceFormula.PurityTensorMap
public import Submission.WeilConjectures.WeilSheaf.Native.NativeCompactProjectionFormula
public import Submission.WeilConjectures.WeilSheaf.UpperShriek
public import Submission.WeilConjectures.WeilSheaf.UpperShriekGeometric

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-!
# The co-projection map of the exceptional inverse image of Weil complexes

For a separated morphism of finite type `f : X ⟶ Y` of separated `k₀`-schemes of finite type
and a Weil complex `L` on `Y`, the co-projection map
`f^* L ⊗ Rf^! ℚ̄_ℓ ⟶ Rf^! L` of Weil complexes is natural in `L` and lies over the geometric
co-projection map `f̄^* L̄ ⊗ Rf̄^! ℚ̄_ℓ ⟶ Rf̄^! L̄`
(`AlgebraicGeometry.ProEtale.CondensedRing.upperShriekUnitTensorMap`) on the geometric fibres
(`AlgebraicGeometry.WeilComplex.exists_coprojection_forget_eq_upperShriekUnitTensorMap`).
The tensor product is the native derived tensor product of Weil complexes
(`AlgebraicGeometry.WeilComplex.nativeConstructibleTensor`).

## Construction

The map is the adjoint under `Rf₀! ⊣ Rf^!` of
`Rf₀!(f^* L ⊗ Rf^! ℚ̄_ℓ) ≅ Rf₀!(Rf^! ℚ̄_ℓ ⊗ f^* L) ≅ Rf₀! Rf^! ℚ̄_ℓ ⊗ L ⟶ ℚ̄_ℓ ⊗ L ≅ L`, built
from the symmetry of the native tensor product, a projection formula for `Rf₀!` and the counit.
Forgetting the Weil structure
(`AlgebraicGeometry.WeilComplex.geometricFiberBoundedConstructibleFunctor`) carries it to the
geometric map by a formal argument on adjunctions
(`CategoryTheory.Adjunction.exists_natTrans_map_comp_eq_homEquiv_coprojection`). The input is a
natural isomorphism `Rf̄_! ∘ For ≅ For ∘ Rf₀!` whose mate `For ∘ Rf^! ⟶ Rf̄^! ∘ For` is invertible
and which carries a projection formula for Weil complexes to the geometric projection formula.

## Unfinished

This input is stated with `sorry`
(`AlgebraicGeometry.WeilComplex.exists_lowerShriek_forget_iso_projection`). The library has no
natural comparison of `For ∘ Rf₀!` with the condensed `Rf̄_!`
(`CondensedRing.boundedConstructibleLowerShriek`): only an objectwise identification of the right
adjoints exists
(`WeilComplex.nonempty_adicSheafDerivedEquivCondensedMod_forget_obj_iso_upperShriek`), and the
comparison of forgetting with the native tensor product
(`ProEtaleWeilSheaf.nativeGeometricForget_tensorComparison`) and the Weil projection formula
(`WeilComplex.nonempty_nativeCompactProjectionLeft_iso`) are only `Nonempty` statements.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry.WeilComplex

open ProEtale

attribute [local instance] CondensedRing.boundedConstructibleBraiding

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

section Native

variable (k₀ l) (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]
  [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]

open scoped CategoryTheory.Obj in
/-- The underlying bounded constructible complex on the geometric fibre `X̄`, in the condensed
model, of a Weil complex on `X`, as a functor
(`AlgebraicGeometry.WeilComplex.geometricFiberBoundedConstructibleObj`). -/
noncomputable def geometricFiberBoundedConstructibleFunctor :
    WeilComplex k₀ l X ⥤ BoundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj l)
      (Over.mk (X ↘ Spec (CommRingCat.of k₀)).geometricFiberToAlgebraicClosure).left) :=
  ObjectProperty.lift _ (forget ⋙ (adicSheafDerivedEquivCondensedMod l _).functor)
    (fun L ↦ (geometricFiberBoundedConstructibleObj L).property)

/-- The native tensor product of Weil complexes is symmetric. -/
theorem nonempty_nativeConstructibleTensor_iso_swap :
    Nonempty (nativeConstructibleTensor k₀ l X ≅
      CategoryTheory.Prod.swap _ _ ⋙ nativeConstructibleTensor k₀ l X) := by
  let := (ProEtaleWeilSheaf.nativeDerivedClosedComparison k₀ l X).weilClosed.monoidal
  let := (ProEtaleWeilSheaf.nativeDerivedClosedComparison k₀ l X).weilSymmetry
  exact ⟨NatIso.ofComponents (fun A ↦ ObjectProperty.isoMk _ (β_ A.1.obj A.2.obj))
    (fun {A B} g ↦ ObjectProperty.hom_ext _ (BraidedCategory.braiding_naturality g.1.hom g.2.hom))⟩

/-- The constant Weil complex `ℚ̄_ℓ` is a left unit for the native tensor product of Weil
complexes. -/
theorem nonempty_nativeConstructibleTensor_adicConstant_iso :
    Nonempty (CategoryTheory.Prod.sectR (WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k₀ l X))
      _ ⋙ nativeConstructibleTensor k₀ l X ≅ 𝟭 _) := by
  let := (ProEtaleWeilSheaf.nativeDerivedClosedComparison k₀ l X).weilClosed.monoidal
  exact ⟨NatIso.ofComponents (fun A ↦ ObjectProperty.isoMk _
    (whiskerRightIso (ProEtaleWeilSheaf.nativeDerivedClosedComparison k₀ l X).weilUnit.symm A.obj ≪≫
      λ_ A.obj))
    (fun {A B} g ↦ ObjectProperty.hom_ext _ (by
      change (𝟙 _ ⊗ₘ g.hom) ≫
          ((ProEtaleWeilSheaf.nativeDerivedClosedComparison k₀ l X).weilUnit.inv ▷ B.obj ≫
            (λ_ B.obj).hom) =
        ((ProEtaleWeilSheaf.nativeDerivedClosedComparison k₀ l X).weilUnit.inv ▷ A.obj ≫
          (λ_ A.obj).hom) ≫ g.hom
      rw [id_tensorHom, whisker_exchange_assoc, leftUnitor_naturality, Category.assoc]))⟩

set_option synthInstance.maxHeartbeats 400000 in
-- the monoidal structure of the derived category of condensed modules is found slowly
set_option backward.isDefEq.respectTransparency false in
-- `Mod.monoidalClosed` needs `IsCommMonObj (condensedRingObj _ _)` up to instance unfolding
open scoped CategoryTheory.Obj in
/-- The underlying bounded constructible complex of the constant Weil complex `ℚ̄_ℓ` is the
unit `ℚ̄_ℓ` on the geometric fibre. -/
noncomputable def geometricFiberBoundedConstructibleFunctorObjAdicConstantIso :
    (geometricFiberBoundedConstructibleFunctor k₀ l X).obj
        (WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k₀ l X)) ≅ 𝟙_ _ :=
  ObjectProperty.isoMk _
    ((adicSheafDerivedEquivCondensedMod l _).functor.mapIso
        (((Endofunctor.IsoAlgebra.forget _).mapDerivedCategorySingleFunctor 0).app _) ≪≫
      ((adicSheafEquivCondensedMod l _).functor.mapDerivedCategorySingleFunctor 0).app _ ≪≫
      (_root_.DerivedCategory.singleFunctor _ 0).mapIso (adicSheafEquivCondensedModUnitIso l _) ≪≫
      _root_.DerivedCategory.singleFunctorObjUnitIso _)

end Native
section Coprojection

variable {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))]
  (f : X ⟶ Y) [f.IsOver (Spec (CommRingCat.of k₀))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))] [QuasiSeparated (Y ↘ Spec (CommRingCat.of k₀))]
  [IsSeparated (Y ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [IsSeparated (X ↘ Spec (CommRingCat.of k₀))] [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
  [HasUpperShriek k₀ l f]

end Coprojection

end AlgebraicGeometry.WeilComplex
