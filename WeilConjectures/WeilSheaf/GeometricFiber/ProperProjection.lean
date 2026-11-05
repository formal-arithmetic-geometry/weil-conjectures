/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.GeometricFiber.Forget
public import WeilConjectures.WeilSheaf.GeometricFiber.ProperProjectionAmbient
public import WeilConjectures.WeilSheaf.Native.Projection.ProperProjectionIso
public import WeilConjectures.WeilSheaf.UpperShriek
public import WeilConjectures.PoincareDuality.ProjectionFormulaOpenImmersion

/-!
# Forgetting the Weil structure commutes with the proper direct image

Let `X ⟶[i] Z ⟶[g] Y` be the compactification of `f : X ⟶ Y` defining the direct image with
compact support of Weil complexes, and `ḡ` the base change of the proper morphism `g` to the
geometric fibres. Forgetting the Weil structures (`For`,
`AlgebraicGeometry.WeilComplex.geometricFiberBoundedConstructibleFunctor`) commutes with the
direct images: `For ∘ Rḡ_* ≅ Rg_* ∘ For`, the mate `For ∘ Rg^! ⟶ Rḡ^! ∘ For` of this
isomorphism is invertible, and `For` carries the proper projection formula of Weil complexes
to the projection morphism of `Lḡ^* ⊣ Rḡ_*` on bounded constructible complexes
(`AlgebraicGeometry.WeilComplex.exists_derivedLowerStar_forget_iso_projection`).
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry.WeilComplex

open ProEtale

attribute [local instance] Compactification.over

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

variable {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [Y.Over (Spec (CommRingCat.of k₀))]
  [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
  [IsSeparated (Y ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]
  (f : X ⟶ Y) [f.IsOver (Spec (CommRingCat.of k₀))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]

set_option maxHeartbeats 2000000 in
-- the derived categories of condensed modules are slow to elaborate
set_option synthInstance.maxHeartbeats 400000 in
-- the monoidal structure of the derived category of condensed modules is found slowly
/-- **Forgetting the Weil structure commutes with the proper direct image, compatibly with the
exceptional inverse images and the projection formulas.** For the compactification
`X ⟶[i] Z ⟶[g] Y` defining `Rf₀!`, there is a natural isomorphism
`β : Rḡ_* ∘ For ≅ For ∘ Rg_*` such that
- its mate `For ∘ Rg^! ⟶ Rḡ^! ∘ For` is invertible, for every right adjoint `Rg^!` of `Rg_*` on
  Weil complexes;
- for some natural isomorphism `γ : For ∘ g^* ≅ ḡ^* ∘ For` and some projection formula
  `e : Rg_* A ⊗ T ≅ Rg_*(A ⊗ g^* T)` of Weil complexes, `For(e)` is the projection morphism
  `Rḡ_* Ā ⊗ T̄ ⟶ Rḡ_*(Ā ⊗ ḡ^* T̄)` of `ḡ^* ⊣ Rḡ_*`, up to `β`, `γ` and the tensor comparisons
  `AlgebraicGeometry.WeilComplex.geometricFiberBoundedConstructibleFunctorTensorIso`. -/
theorem exists_derivedLowerStar_forget_iso_projection :
    ∃ β : geometricFiberBoundedConstructibleFunctor k₀ l (nativeProjectionCompactification k₀ f).Z ⋙
          CondensedRing.boundedConstructibleLowerStar l
            (geometricFiberHom (k₀ := k₀) (nativeProjectionCompactification k₀ f).g) ≅
        derivedLowerStar (nativeProjectionCompactification k₀ f).g ⋙
          geometricFiberBoundedConstructibleFunctor k₀ l Y,
      (∀ {R : WeilComplex k₀ l Y ⥤ WeilComplex k₀ l (nativeProjectionCompactification k₀ f).Z}
        {R' : _ ⥤ _} (adj' : CondensedRing.boundedConstructibleLowerStar l
          (geometricFiberHom (k₀ := k₀) (nativeProjectionCompactification k₀ f).g) ⊣ R')
        (adj : derivedLowerStar (nativeProjectionCompactification k₀ f).g ⊣ R)
        (L : WeilComplex k₀ l Y),
        IsIso ((mateEquiv adj adj' (TwoSquare.mk _ _ _ _ β.hom)).natTrans.app L)) ∧
      ∃ (γ : upperStar (nativeProjectionCompactification k₀ f).g ⋙
            geometricFiberBoundedConstructibleFunctor k₀ l (nativeProjectionCompactification k₀ f).Z ≅
          geometricFiberBoundedConstructibleFunctor k₀ l Y ⋙
            CondensedRing.boundedConstructibleUpperStar _ l
              (geometricFiberHom (k₀ := k₀) (nativeProjectionCompactification k₀ f).g))
        (e : (derivedLowerStar (nativeProjectionCompactification k₀ f).g).prod (𝟭 _) ⋙
            nativeConstructibleTensor k₀ l Y ≅
          (𝟭 _).prod (upperStar (nativeProjectionCompactification k₀ f).g) ⋙
            nativeConstructibleTensor k₀ l (nativeProjectionCompactification k₀ f).Z ⋙
              derivedLowerStar (nativeProjectionCompactification k₀ f).g),
        ∀ A T, (geometricFiberBoundedConstructibleFunctor k₀ l Y).map (e.hom.app (A, T)) ≫
            β.inv.app _ ≫
            (CondensedRing.boundedConstructibleLowerStar l
              (geometricFiberHom (k₀ := k₀) (nativeProjectionCompactification k₀ f).g)).map
              ((geometricFiberBoundedConstructibleFunctorTensorIso k₀ l
                  (nativeProjectionCompactification k₀ f).Z).hom.app
                  (A, (upperStar (nativeProjectionCompactification k₀ f).g).obj T) ≫
                (geometricFiberBoundedConstructibleFunctor k₀ l
                  (nativeProjectionCompactification k₀ f).Z).obj A ◁ γ.hom.app T) =
          (geometricFiberBoundedConstructibleFunctorTensorIso k₀ l Y).hom.app
              ((derivedLowerStar (nativeProjectionCompactification k₀ f).g).obj A, T) ≫
            β.inv.app A ▷ (geometricFiberBoundedConstructibleFunctor k₀ l Y).obj T ≫
            (CondensedRing.boundedConstructibleUpperStarLowerStarAdjunction l
              (geometricFiberHom (k₀ := k₀) (nativeProjectionCompactification k₀ f).g)).projectionMorphism
              ((geometricFiberBoundedConstructibleFunctor k₀ l
                (nativeProjectionCompactification k₀ f).Z).obj A)
              ((geometricFiberBoundedConstructibleFunctor k₀ l Y).obj T) := by
  have : IsProper (nativeProjectionCompactification k₀ f).g :=
    (nativeProjectionCompactification k₀ f).isProper
  refine ⟨geometricFiberBoundedConstructibleFunctorLowerStarIso _,
    fun adj' adj L ↦
      isIso_mateEquiv_geometricFiberBoundedConstructibleFunctorLowerStarIso _ adj' adj L,
    geometricFiberBoundedConstructibleFunctorUpperStarIso _,
    derivedLowerStarNativeConstructibleTensorIso _, fun A T ↦ ?_⟩
  -- compare the two sides on the ambient derived categories
  apply (ObjectProperty.fullyFaithfulι _).map_injective
  simp only [Functor.map_comp]
  rw [ι_map_geometricFiberBoundedConstructibleFunctor_map,
    ι_map_derivedLowerStarNativeConstructibleTensorIso_hom_app,
    ι_map_geometricFiberBoundedConstructibleFunctorLowerStarIso_inv_app]
  simp only [ι_map_boundedConstructibleLowerStar_geometricFiberHom_map,
    ι_map_geometricFiberBoundedConstructibleFunctorTensorIso_hom_app,
    boundedConstructible_ι_map_whiskerRight,
    ι_map_geometricFiberBoundedConstructibleFunctorLowerStarIso_inv_app,
    ι_map_boundedConstructibleProjectionMorphism_geometricFiberHom]
  -- the remaining comparisons, with the geometric fibres written uniformly
  have hCT := ι_map_geometricFiberBoundedConstructibleFunctorTensorIso_hom_app _ A
    ((upperStar (nativeProjectionCompactification k₀ f).g).obj T)
  have hW := boundedConstructible_ι_map_whiskerLeft' _
    ((geometricFiberBoundedConstructibleFunctor k₀ l _).obj A)
    ((geometricFiberBoundedConstructibleFunctorUpperStarIso
      (nativeProjectionCompactification k₀ f).g).hom.app T)
  have hγ := ι_map_geometricFiberBoundedConstructibleFunctorUpperStarIso_hom_app
    (nativeProjectionCompactification k₀ f).g T
  dsimp only [Over.mk_left] at hCT hW hγ ⊢
  simp only [hCT, hW, hγ]
  exact forget_map_projection_eq _ A T

end AlgebraicGeometry.WeilComplex
