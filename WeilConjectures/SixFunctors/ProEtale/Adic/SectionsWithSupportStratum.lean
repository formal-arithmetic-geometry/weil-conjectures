/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Monoidal.Mod.TensorLeftFree
public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseInternalHom
public import WeilConjectures.SixFunctors.ProEtale.Adic.SectionsWithSupport

/-!
# Morphisms out of an extension by zero from a stratum

Let `i : Z ⟶ X` be a closed immersion with quasi-compact open complement `j`, `u : S ⟶ Z` an open
immersion, `a = i ∘ u`, so that `a_! = i_* u_!`, and `L` a lisse (finite locally free) sheaf of
`ℚ̄_ℓ,S`-modules. Blueprint `det-lem-formal-closed-support-stratum-hom` computes
`Hom(a_! L, K[q])` for `K ∈ D(X_proét, ℚ̄_ℓ)`:
```
Hom_X(i_* u_! L, K[q]) ≅ Hom_Z(u_! L, RΓ_Z K[q]) ≅ Hom_S(L, u^* RΓ_Z K[q])
  ≅ Hom_S(ℚ̄_ℓ,S, 𝓗om(L, u^* RΓ_Z K)[q]) = H^q(S, 𝓗om(L, u^* RΓ_Z K)),
```
(`AlgebraicGeometry.ProEtale.homEquivStratum`). The three steps are the adjunctions
`i_* ⊣ RΓ_Z` (`AlgebraicGeometry.ProEtale.adicDerivedSectionsWithSupportAdjunction`),
`u_! ⊣ u^*` and `L ⊗ - ⊣ 𝓗om(L, -)`; the last two are adjunctions of exact functors, `L` being
flat (`AlgebraicGeometry.ProEtale.IsAdicLisseSheaf.preservesFiniteLimits_tensorLeft`) and
`𝓗om(L, -)` exact (`AlgebraicGeometry.ProEtale.IsAdicLisseSheaf.preservesFiniteColimits_ihom`),
so they pass to the derived categories levelwise, and `L ⊗ ℚ̄_ℓ,S ≅ L`. For `L` lisse,
`𝓗om(L, -)` is `L^∨ ⊗ -` of the blueprint.
-/

@[expose] public section

universe u

open CategoryTheory Limits Pretriangulated

namespace AlgebraicGeometry

open Scheme

namespace ProEtale

variable {l : ℕ} [Fact l.Prime]

section Flat

variable {X : Scheme.{u}}

instance (F : AdicSheaf l X) : (Mod.tensorLeft F).Additive :=
  (Mod.ihomAdjunction F).left_adjoint_additive

instance (F : AdicSheaf l X) : PreservesFiniteLimits (AdicSheaf.ihom F) :=
  have := (Mod.ihomAdjunction F).rightAdjoint_preservesLimits
  inferInstance


/-- **Tensoring with a lisse sheaf preserves monomorphisms**: after pullback along a member `g`
of a pro-étale cover trivialising `F`, it becomes tensoring with `ℚ̄_ℓⁿ`. -/
theorem IsAdicLisseSheaf.mono_tensorLeft_map {F : AdicSheaf l X} (hF : IsAdicLisseSheaf F)
    {M N : AdicSheaf l X} (f : M ⟶ N) [Mono f] : Mono ((Mod.tensorLeft F).map f) := by
  obtain ⟨R, hR, hRF⟩ := hF
  obtain ⟨ι, V, g, rfl⟩ := R.exists_eq_ofArrows
  have (i : ι) : WeaklyEtale (g i) :=
    Scheme.proetalePrecoverage_le_precoverage_weaklyEtale _ hR (.mk i)
  refine Preadditive.mono_of_isZero_kernel _
    (AdicSheaf.isZero_of_isZero_upperStar g hR fun i ↦ ?_)
  obtain ⟨n, ⟨e⟩⟩ := hRF (g i) (.mk i)
  have : Mono ((g i)^*ᵃ[l].map ((Mod.tensorLeft F).map f)) := by
    have key := NatIso.naturality_2 (adicUpperStarTensorLeftIso l (g i) F) f
    change Mono ((Mod.tensorLeft F ⋙ (g i)^*ᵃ[l]).map f)
    rw [← key]
    have h1 : Mono ((g i)^*ᵃ[l].map f) := Functor.map_mono _ f
    have := Mod.mono_tensorLeft_map_of_iso_biproduct e ((g i)^*ᵃ[l].map f)
    exact mono_comp' (IsIso.mono_of_iso ((adicUpperStarTensorLeftIso l (g i) F).app M).hom)
      (mono_comp' this (IsIso.mono_of_iso ((adicUpperStarTensorLeftIso l (g i) F).app N).inv))
  exact (isZero_kernel_of_mono ((g i)^*ᵃ[l].map ((Mod.tensorLeft F).map f))).of_iso
    (PreservesKernel.iso (g i)^*ᵃ[l] _)

/-- **Tensoring with a lisse sheaf is exact**: it is right exact as a left adjoint, and it
preserves monomorphisms (`AlgebraicGeometry.ProEtale.IsAdicLisseSheaf.mono_tensorLeft_map`). -/
theorem IsAdicLisseSheaf.preservesFiniteLimits_tensorLeft {F : AdicSheaf l X}
    (hF : IsAdicLisseSheaf F) : PreservesFiniteLimits (Mod.tensorLeft F) := by
  have := (Mod.ihomAdjunction F).leftAdjoint_preservesColimits
  have : (Mod.tensorLeft F).PreservesMonomorphisms := ⟨fun f _ ↦ hF.mono_tensorLeft_map f⟩
  have := Functor.preservesHomology_of_preservesMonos_and_cokernels (Mod.tensorLeft F)
  exact Functor.preservesFiniteLimits_of_preservesHomology _

/-- Tensoring with a lisse sheaf is exact. -/
instance {F : AdicSheaf l X} [h : Fact (IsAdicLisseSheaf F)] :
    PreservesFiniteLimits (Mod.tensorLeft F) :=
  h.out.preservesFiniteLimits_tensorLeft

/-- The internal hom out of a lisse sheaf is exact. -/
instance {F : AdicSheaf l X} [h : Fact (IsAdicLisseSheaf F)] :
    PreservesFiniteColimits (AdicSheaf.ihom F) :=
  h.out.preservesFiniteColimits_ihom

instance (F : AdicSheaf l X) : PreservesFiniteColimits (Mod.tensorLeft F) :=
  have := (Mod.ihomAdjunction F).leftAdjoint_preservesColimits
  inferInstance

/-- The derived adjunction `L ⊗ - ⊣ 𝓗om(L, -)` for a lisse sheaf `L`, both functors being
exact. -/
noncomputable def derivedTensorLeftIhomAdjunction (F : AdicSheaf l X)
    [Fact (IsAdicLisseSheaf F)] :
    (Mod.tensorLeft F).mapDerivedCategory ⊣ (AdicSheaf.ihom F).mapDerivedCategory :=
  (Mod.ihomAdjunction F).mapDerivedCategoryRightDerivedAdjunction.ofNatIsoRight
    (AdicSheaf.ihom F).rightDerivedFunctorIsoMapDerivedCategory

end Flat

variable {Z U X S : Scheme.{u}}
  (i : Z ⟶ X) [IsClosedImmersion i] (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
  (hij : IsCompl (Set.range i.base) (Set.range j.base)) (v : S ⟶ Z) [IsOpenImmersion v]
  (L : AdicSheaf l S) [Fact (IsAdicLisseSheaf L)]

/-- The derived adjunction `u_! ⊣ u^*` along an open immersion `u`, both functors being exact. -/
noncomputable def adicDerivedOpenImmersionLowerShriekAdjunction :
    ((v)_!ᵃ[l]).mapDerivedCategory ⊣ ((v)^*ᵃ[l]).mapDerivedCategory :=
  have := (adicOpenImmersionLowerShriekAdjunction l v).leftAdjoint_preservesColimits
  (adicOpenImmersionLowerShriekAdjunction l
    v).mapDerivedCategoryRightDerivedAdjunction.ofNatIsoRight
    ((v)^*ᵃ[l]).rightDerivedFunctorIsoMapDerivedCategory

/-- The object `L` of `D(S_proét, ℚ̄_ℓ)` placed in degree `0` is `L ⊗ ℚ̄_ℓ,S`. -/
noncomputable def singleIsoMapDerivedCategoryTensorLeftSingleRegular :
    (DerivedCategory.singleFunctor (AdicSheaf l S) 0).obj L ≅
      (Mod.tensorLeft L).mapDerivedCategory.obj
        ((DerivedCategory.singleFunctor (AdicSheaf l S) 0).obj
          (Mod.regular (adicConstantSheaf l S))) :=
  (DerivedCategory.singleFunctor (AdicSheaf l S) 0).mapIso
      (Mod.tensorLeftObjRegularIso L).symm ≪≫
    ((Mod.tensorLeft L).mapDerivedCategorySingleFunctor 0).symm.app _

variable [PreservesFiniteColimits (i)_*ᵃ[l]]

/-- Blueprint `det-lem-formal-closed-support-stratum-hom`: **morphisms out of an extension by zero
from a stratum.** For a closed immersion `i : Z ⟶ X` with quasi-compact open complement `j`, an
open immersion `u : S ⟶ Z`, a lisse sheaf `L` of `ℚ̄_ℓ,S`-modules, `K ∈ D(X_proét, ℚ̄_ℓ)` and
`q ∈ ℤ`,
```
Hom(i_* u_! L, K[q]) ≅ Hom(ℚ̄_ℓ,S, 𝓗om(L, u^* RΓ_Z K)[q]) = H^q(S, 𝓗om(L, u^* RΓ_Z K)),
```
through `i_* ⊣ RΓ_Z`, `u_! ⊣ u^*` and `L ⊗ - ⊣ 𝓗om(L, -)`. Here `a_! = i_* u_!` for
`a = i ∘ u`, and `𝓗om(L, -) ≅ L^∨ ⊗ -` as `L` is lisse. -/
noncomputable def homEquivStratum (K : DerivedCategory (AdicSheaf l X)) (q : ℤ) :
    (((i)_*ᵃ[l]).mapDerivedCategory.obj (((v)_!ᵃ[l]).mapDerivedCategory.obj
        ((DerivedCategory.singleFunctor (AdicSheaf l S) 0).obj L)) ⟶ K⟦q⟧) ≃
      ((DerivedCategory.singleFunctor (AdicSheaf l S) 0).obj
          (Mod.regular (adicConstantSheaf l S)) ⟶
        ((AdicSheaf.ihom L).mapDerivedCategory.obj (((v)^*ᵃ[l]).mapDerivedCategory.obj
          ((adicSectionsWithSupport l i j hij).rightDerivedFunctor.obj K)))⟦q⟧) :=
  ((adicDerivedSectionsWithSupportAdjunction l i j hij).homEquiv _ _).trans <|
    (Iso.homCongr (Iso.refl _)
      (((adicSectionsWithSupport l i j hij).rightDerivedFunctor.commShiftIso q).app K)).trans <|
    ((adicDerivedOpenImmersionLowerShriekAdjunction v).homEquiv _ _).trans <|
    (Iso.homCongr (singleIsoMapDerivedCategoryTensorLeftSingleRegular L)
      ((((v)^*ᵃ[l]).mapDerivedCategory.commShiftIso q).app _)).trans <|
    ((derivedTensorLeftIhomAdjunction L).homEquiv _ _).trans <|
    Iso.homCongr (Iso.refl _) (((AdicSheaf.ihom L).mapDerivedCategory.commShiftIso q).app _)

end ProEtale

end AlgebraicGeometry
