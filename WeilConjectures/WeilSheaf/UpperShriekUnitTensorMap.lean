/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.MateCoprojection
public import WeilConjectures.CategoryTheory.Adjunction.ProjectionPasting
public import WeilConjectures.WeilSheaf.GeometricFiber.LowerShriek
public import WeilConjectures.WeilSheaf.GeometricFiber.OpenProjection
public import WeilConjectures.WeilSheaf.GeometricFiber.ProperProjection
public import WeilConjectures.TraceFormula.PurityTensorMap
public import WeilConjectures.WeilSheaf.Native.NativeCompactProjectionFormula
public import WeilConjectures.WeilSheaf.UpperShriek
public import WeilConjectures.WeilSheaf.UpperShriekGeometric

import WeilConjectures.Tactic.ExactModProofs

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

This input (`AlgebraicGeometry.WeilComplex.exists_lowerShriek_forget_iso_projection`) is pasted
from the compactification `Rf₀! = Rg_* ∘ i_!` defining `Rf₀!`
(`CategoryTheory.Functor.map_projectionIsoOfComp_hom_app`,
`CategoryTheory.Functor.isIso_mateEquiv_forgetCompIsoOfComp_app`): the comparisons for the open
immersion `i` (`AlgebraicGeometry.WeilComplex.exists_extensionByZero_forget_iso_projection`) and
for the proper `g` (`AlgebraicGeometry.WeilComplex.exists_derivedLowerStar_forget_iso_projection`),
and the identification of `ī_! ⋙ Rḡ_*` with `Rf̄_!` together with its projection morphisms
(`AlgebraicGeometry.WeilComplex.geometricFiberLowerShriekIso_hom_app_whiskerRight_comp`).
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

set_option maxHeartbeats 4000000 in
-- elaborating the pasted comparisons of the derived functors is slow
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
  let c := nativeProjectionCompactification k₀ f
  have : IsLocallyNoetherian Y :=
    LocallyOfFiniteType.isLocallyNoetherian (Y ↘ Spec (CommRingCat.of k₀))
  have : CompactSpace Y :=
    QuasiCompact.compactSpace_of_compactSpace (Y ↘ Spec (CommRingCat.of k₀))
  have : IsLocallyNoetherian c.Z := LocallyOfFiniteType.isLocallyNoetherian c.g
  have : CompactSpace c.Z := QuasiCompact.compactSpace_of_compactSpace c.g
  have : IsNoetherian c.Z := ⟨⟩
  have : TopologicalSpace.NoetherianSpace X := c.i.isOpenEmbedding.isInducing.noetherianSpace
  have : QuasiCompact c.i := inferInstance
  have := isLeftAdjoint_derivedLowerStar_of_isProper (k₀ := k₀) (l := l) c.g
  obtain ⟨βI, hβI, γi, eI, hI⟩ := exists_extensionByZero_forget_iso_projection (k₀ := k₀) (l := l) f
  obtain ⟨βG, hβG, γg, eG, hG⟩ := exists_derivedLowerStar_forget_iso_projection (k₀ := k₀) (l := l) f
  -- `Rf₀! = Rg_* ∘ i_!` and `f^* = i^* ∘ g^*`
  let ℓ : derivedLowerShriek k₀ l f ≅ extensionByZero c.i ⋙ derivedLowerStar c.g :=
    NatIso.ofComponents (fun K ↦ Iso.refl _) (fun φ ↦ by
      rw [Iso.refl_hom, Iso.refl_hom, Category.comp_id, Category.id_comp]
      rfl)
  let pc : upperStar c.g ⋙ upperStar c.i ≅ upperStar (k₀ := k₀) (l := l) f :=
    (upperStarCompIso c.i c.g).symm ≪≫ upperStarCongrIso c.comm.symm
  -- the geometric `Rf̄_! ≅ ī_! ⋙ Rḡ_*`
  let θ := geometricFiberLowerShriekIso k₀ l f
  refine ⟨Functor.isoWhiskerLeft _ θ.symm ≪≫ Functor.forgetCompIsoOfComp ℓ βI βG, fun L ↦ ?_,
    geometricFiberBoundedConstructibleFunctorTensorIso k₀ l X,
    geometricFiberBoundedConstructibleFunctorTensorIso k₀ l Y,
    Functor.forgetPullIsoOfComp pc γi γg (geometricFiberUpperStarCompIso k₀ l f),
    Functor.projectionIsoOfComp ℓ pc eI eG, fun M T ↦ ?_⟩
  · have hβ : TwoSquare.mk _ _ _ _
        (Functor.isoWhiskerLeft (geometricFiberBoundedConstructibleFunctor k₀ l X) θ.symm ≪≫
          Functor.forgetCompIsoOfComp ℓ βI βG).hom =
        (TwoSquare.mk _ _ _ _ (Functor.forgetCompIsoOfComp ℓ βI βG).hom).whiskerRight θ.inv := by
      ext K
      simp [TwoSquare.whiskerRight]
    have hm := Functor.isIso_mateEquiv_forgetCompIsoOfComp_app ℓ βI βG
      (extensionByZeroUpperStarAdjunction c.i) (Adjunction.ofIsLeftAdjoint (derivedLowerStar c.g))
      (derivedLowerShriekUpperShriekAdjunction f)
      (CondensedRing.boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction _ l
        (geometricFiberHom (k₀ := k₀) c.i))
      (Adjunction.ofIsLeftAdjoint (CondensedRing.boundedConstructibleLowerStar l
        (geometricFiberHom (k₀ := k₀) c.g))) hβI (fun L ↦ hβG _ _ L) L
    rw [hβ, mateEquiv_conjugateEquiv_vcomp _
      ((CondensedRing.boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction _ l
        (geometricFiberHom (k₀ := k₀) c.i)).comp
        (Adjunction.ofIsLeftAdjoint (CondensedRing.boundedConstructibleLowerStar l
          (geometricFiberHom (k₀ := k₀) c.g))))]
    dsimp only [TwoSquare.whiskerBottom]
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app]
    infer_instance
  · have hA := Functor.map_projectionIsoOfComp_hom_app ℓ pc eI eG
      (geometricFiberBoundedConstructibleFunctorTensorIso k₀ l X)
      (geometricFiberBoundedConstructibleFunctorTensorIso k₀ l c.Z)
      (geometricFiberBoundedConstructibleFunctorTensorIso k₀ l Y) βI βG γi γg
      (geometricFiberUpperStarCompIso k₀ l f)
      (fun A B ↦ (CondensedRing.boundedConstructibleUpperStarLowerStarAdjunction l
        (geometricFiberHom (k₀ := k₀) c.g)).projectionMorphism A B)
      (fun φ B ↦ (CondensedRing.boundedConstructibleUpperStarLowerStarAdjunction l
        (geometricFiberHom (k₀ := k₀) c.g)).projectionMorphism_natural_left φ B)
      (fun K N ↦ inv ((CondensedRing.boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction
        _ l (geometricFiberHom (k₀ := k₀) c.i)).projectionComparison K N))
      (fun K _ _ h ↦ (CondensedRing.boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction
        _ l (geometricFiberHom (k₀ := k₀) c.i)).inv_projectionComparison_natural_right K h)
      hG hI M T
    have hΘ := geometricFiberLowerShriekIso_hom_app_whiskerRight_comp (k₀ := k₀) (l := l) f
      ((geometricFiberBoundedConstructibleFunctor k₀ l X).obj M)
      ((geometricFiberBoundedConstructibleFunctor k₀ l Y).obj T)
    simp only [Iso.trans_inv, Functor.isoWhiskerLeft_inv, NatTrans.comp_app,
      Functor.whiskerLeft_app, Iso.symm_inv, Category.assoc, comp_whiskerRight] at hA ⊢
    rw [hΘ, ← θ.hom.naturality]
    simp only [Functor.comp_map, Functor.comp_obj] at hA ⊢
    have hA' := (reassoc_of% hA) (θ.hom.app ((geometricFiberBoundedConstructibleFunctor k₀ l X).obj M ⊗
      (CondensedRing.boundedConstructibleUpperStar _ l (geometricFiberHom (k₀ := k₀) f)).obj
        ((geometricFiberBoundedConstructibleFunctor k₀ l Y).obj T)))
    simp only [Functor.map_comp, Category.assoc] at hA' ⊢
    exact_mod_proofs hA'

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
