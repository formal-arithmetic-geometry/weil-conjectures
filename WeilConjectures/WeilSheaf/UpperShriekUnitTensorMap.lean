/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.MateCoprojection
public import WeilConjectures.TraceFormula.PurityTensorMap
public import WeilConjectures.WeilSheaf.Native.NativeCompactProjectionFormula
public import WeilConjectures.WeilSheaf.UpperShriek
public import WeilConjectures.WeilSheaf.UpperShriekGeometric
public import WeilConjectures.WeilSheaf.Native.Projection.CompactProjectionFinal

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

The comparison is constructed from the canonical proper projection map and the open
projection map. Their forget squares and invertible exceptional mates paste along the chosen
compactification. Compatibility of the geometric projection with change of compactification
then gives the comparison for the geometric category's chosen compact direct image.
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

/-- **Forgetting the Weil structure commutes with `Rf₀!`, compatibly with `Rf^!` and the
projection formulas.** For a separated morphism of finite type `f : X ⟶ Y` of separated
`k₀`-schemes of finite type, write `For` for the underlying bounded constructible complex on the
geometric fibre (`AlgebraicGeometry.WeilComplex.geometricFiberBoundedConstructibleFunctor`).
There is a natural isomorphism `β : Rf̄_! ∘ For ≅ For ∘ Rf₀!` such that
- its mate `For ∘ Rf^! ⟶ Rf̄^! ∘ For` under `Rf₀! ⊣ Rf^!` and `Rf̄_! ⊣ Rf̄^!` is invertible;
- for natural identifications `τ` of `For` of the native tensor product with the tensor product
  of `Dᵇc`, `γ : For ∘ f^* ≅ f̄^* ∘ For`, and a projection formula
  `e : Rf₀! M ⊗ T ≅ Rf₀!(M ⊗ f^* T)` of Weil complexes, `For(e)` is the geometric projection
  formula `Rf̄_! M̄ ⊗ T̄ ⟶ Rf̄_!(M̄ ⊗ f̄^* T̄)`
  (`ProEtale.CondensedRing.boundedConstructibleExceptionalProjectionMorphism`).

This is the compatibility of the Weil six operations with the geometric ones of
`fix-prop-projection-formula` and `def-weil-exceptional-inverse-image` (blueprint) used by
`thm-pur-weil-equivariance-of-purity-and-trace`. -/
theorem exists_lowerShriek_forget_iso_projection :
    ∃ β : geometricFiberBoundedConstructibleFunctor k₀ l X ⋙
          CondensedRing.boundedConstructibleLowerShriek l (geometricFiberHom (k₀ := k₀) f) ≅
        derivedLowerShriek k₀ l f ⋙ geometricFiberBoundedConstructibleFunctor k₀ l Y,
      (∀ L, IsIso ((mateEquiv (derivedLowerShriekUpperShriekAdjunction f)
        (CondensedRing.boundedConstructibleUpperShriekAdjunction l
          (geometricFiberHom (k₀ := k₀) f)) (TwoSquare.mk _ _ _ _ β.hom)).natTrans.app L)) ∧
      ∃ (τX : nativeConstructibleTensor k₀ l X ⋙ geometricFiberBoundedConstructibleFunctor k₀ l X ≅
          (geometricFiberBoundedConstructibleFunctor k₀ l X).prod
            (geometricFiberBoundedConstructibleFunctor k₀ l X) ⋙ tensor _)
        (τY : nativeConstructibleTensor k₀ l Y ⋙ geometricFiberBoundedConstructibleFunctor k₀ l Y ≅
          (geometricFiberBoundedConstructibleFunctor k₀ l Y).prod
            (geometricFiberBoundedConstructibleFunctor k₀ l Y) ⋙ tensor _)
        (γ : upperStar f ⋙ geometricFiberBoundedConstructibleFunctor k₀ l X ≅
          geometricFiberBoundedConstructibleFunctor k₀ l Y ⋙
            CondensedRing.boundedConstructibleUpperStar _ l (geometricFiberHom (k₀ := k₀) f))
        (e : nativeCompactProjectionLeft k₀ l f ≅ nativeCompactProjectionRight k₀ l f),
        ∀ M T, (geometricFiberBoundedConstructibleFunctor k₀ l Y).map (e.hom.app (M, T)) ≫
            β.inv.app _ ≫
            (CondensedRing.boundedConstructibleLowerShriek l (geometricFiberHom (k₀ := k₀) f)).map
              (τX.hom.app (M, (upperStar f).obj T) ≫
                (geometricFiberBoundedConstructibleFunctor k₀ l X).obj M ◁ γ.hom.app T) =
          τY.hom.app ((derivedLowerShriek k₀ l f).obj M, T) ≫
            β.inv.app M ▷ (geometricFiberBoundedConstructibleFunctor k₀ l Y).obj T ≫
            CondensedRing.boundedConstructibleExceptionalProjectionMorphism l
              (geometricFiberHom (k₀ := k₀) f) _ _ := by
  refine ⟨projectionCompactForgetIso k₀ l f, ?_,
    compactProjectionForgetTensorIso k₀ l X, compactProjectionForgetTensorIso k₀ l Y,
    projectionCompactPullForgetIso k₀ l f, projectionCompactIso k₀ l f, ?_⟩
  · have := isIso_mateEquiv_projectionCompactForgetIso k₀ l f
      (derivedLowerShriekUpperShriekAdjunction f)
    intro L
    infer_instance
  · exact projectionCompact_forget_square k₀ l f

set_option maxHeartbeats 1000000 in
-- elaborating the instantiation of the abstract transport lemma is slow
/-- **The co-projection map of Weil complexes lies over the geometric one.** This is a helper for
`thm-pur-weil-equivariance-of-purity-and-trace`, not a blueprint node: it concerns the map
`φ_{f,K} : Lf^* K ⊗ ω_f ⟶ Rf^! K` of `pur9-cs-def-phi`, at the coefficient stage `ℚ̄_ℓ`. For a
separated morphism of finite type `f : X ⟶ Y` of separated `k₀`-schemes of finite type, there is
a morphism of Weil complexes `f^* L ⊗ Rf^! ℚ̄_ℓ ⟶ Rf^! L`, natural in `L`, which on the geometric
fibre `X̄` is the geometric co-projection map `f̄^* L̄ ⊗ Rf̄^! ℚ̄_ℓ ⟶ Rf̄^! L̄`
(`AlgebraicGeometry.ProEtale.CondensedRing.upperShriekUnitTensorMap`), up to isomorphisms `ψ_L`
of the sources and `φ_L` of the targets.

The isomorphism `φ_L` is the identification of the underlying complex of `Rf^! L` with
`Rf̄^! L̄` (`WeilComplex.nonempty_adicSheafDerivedEquivCondensedMod_forget_obj_iso_upperShriek`),
and `ψ_L` is the comparison of pullback and tensor product with forgetting the Weil structure,
together with `φ` at `ℚ̄_ℓ`; here both are only required to exist. -/
theorem exists_coprojection_forget_eq_upperShriekUnitTensorMap :
    ∃ π : upperStar f ⋙ (𝟭 (WeilComplex k₀ l X)).prod' ((Functor.const _).obj
          ((upperShriek f).obj (WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k₀ l Y)))) ⋙
          nativeConstructibleTensor k₀ l X ⟶
        upperShriek f,
      ∀ L : WeilComplex k₀ l Y,
        ∃ (φ : (adicSheafDerivedEquivCondensedMod l
            (X ↘ Spec (CommRingCat.of k₀)).geometricFiber).functor.obj
              (forget.obj ((upperShriek f).obj L)) ≅
          ((CondensedRing.boundedConstructibleUpperShriek l (geometricFiberHom (k₀ := k₀) f)).obj
            (geometricFiberBoundedConstructibleObj L)).obj)
          (ψ : (adicSheafDerivedEquivCondensedMod l
            (X ↘ Spec (CommRingCat.of k₀)).geometricFiber).functor.obj
              (forget.obj ((upperStar f ⋙ (𝟭 (WeilComplex k₀ l X)).prod' ((Functor.const _).obj
                ((upperShriek f).obj (WeilSheaf.toComplex.obj
                  (WeilSheaf.adicConstant k₀ l Y)))) ⋙
                nativeConstructibleTensor k₀ l X).obj L)) ≅
          ((CondensedRing.boundedConstructibleUpperStar _ l (geometricFiberHom (k₀ := k₀) f)).obj
              (geometricFiberBoundedConstructibleObj L) ⊗
            (CondensedRing.boundedConstructibleUpperShriek l
              (geometricFiberHom (k₀ := k₀) f)).obj (𝟙_ _)).obj),
        (adicSheafDerivedEquivCondensedMod l _).functor.map (forget.map (π.app L)) ≫ φ.hom =
          ψ.hom ≫ (ObjectProperty.ι _).map (CondensedRing.upperShriekUnitTensorMap l
            (geometricFiberHom (k₀ := k₀) f) (geometricFiberBoundedConstructibleObj L)) := by
  obtain ⟨β, hβ, τX, τY, γ, e, he⟩ := exists_lowerShriek_forget_iso_projection (k₀ := k₀) (l := l) f
  obtain ⟨b⟩ := nonempty_nativeConstructibleTensor_iso_swap k₀ l X
  obtain ⟨u⟩ := nonempty_nativeConstructibleTensor_adicConstant_iso k₀ l Y
  have := hβ
  obtain ⟨π, hπ⟩ := Adjunction.exists_natTrans_map_comp_eq_homEquiv_coprojection
    (derivedLowerShriekUpperShriekAdjunction f)
    (CondensedRing.boundedConstructibleUpperShriekAdjunction l (geometricFiberHom (k₀ := k₀) f))
    (nativeConstructibleTensor k₀ l X) (nativeConstructibleTensor k₀ l Y) (upperStar f)
    (CondensedRing.boundedConstructibleUpperStar _ l (geometricFiberHom (k₀ := k₀) f)) β τX τY γ e
    (CondensedRing.boundedConstructibleExceptionalProjectionMorphism l
      (geometricFiberHom (k₀ := k₀) f))
    (fun g K ↦ CondensedRing.boundedConstructibleExceptionalProjectionMorphism_natural_left l _ g K)
    he b _ u (geometricFiberBoundedConstructibleFunctorObjAdicConstantIso k₀ l Y)
  refine ⟨π, fun L ↦ ?_⟩
  obtain ⟨φ, ψ, h⟩ := hπ L
  refine ⟨(ObjectProperty.ι _).mapIso φ, (ObjectProperty.ι _).mapIso ψ, ?_⟩
  have h' := congrArg (ObjectProperty.ι _).map h
  rw [Functor.map_comp, Functor.map_comp] at h'
  exact h'

end Coprojection

end AlgebraicGeometry.WeilComplex
