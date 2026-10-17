/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Adjunction
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Monoidal
public import WeilConjectures.CategoryTheory.Sites.ConstantSheafMonoidal
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Point.ConstantSheaf
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.FiniteCoefficients.Defs

/-!
# Constant complexes, the constant-tensor comparison and the Künneth morphism

For a commutative ring `Λ` (in the blueprint `Λ = 𝒪_E/ϖⁿ` or a finite field `𝔽_{ℓ^r}`) and a
scheme `W`, the constant complex functor `c_W : D(Mod_Λ) ⥤ D(W_ét, Λ)` is left adjoint to the
derived sections `RΓ_W` (`AlgebraicGeometry.Etale.constantComplexAdjunction`), and comes with a
monoidal comparison `c_W(M ⊗ᴸ N) ⟶ c_W M ⊗ᴸ c_W N`
(`AlgebraicGeometry.Etale.constantComplexTensorComparison`), the derived comonoidal structure of
the exact monoidal constant sheaf functor. With these we define

- `AlgebraicGeometry.Etale.constantProjectionMap` (`pur7710-def-constant-projection`):
  `RΓ_W K ⊗ᴸ M ⟶ RΓ_W (K ⊗ᴸ c_W M)`;
- `AlgebraicGeometry.Etale.globalSectionsKunnethMap` (`pur7710-def-kunneth-map`) and
  `AlgebraicGeometry.Etale.globalSectionsKunnethMapFiniteField`
  (`pur7710-def-kunneth-map-field`): `RΓ_X K ⊗ᴸ RΓ_Y L ⟶ RΓ_Z (K ⊠ᴸ L)`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- The constant sheaf functor on étale sheaves of `Λ`-modules preserves flat objects: the stalk
of `M_W` at every geometric point is `M`. -/
instance preservesFlat_constantSheaf (W : Scheme.{u}) :
    (constantSheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)).PreservesFlat where
  flat_obj {M} hM := (flat_iff_forall_flat_sheafFiber_obj _).2 fun s ↦
    ObjectProperty.prop_of_iso _
      ((pointSmallEtale s).ulift.{u + 1}.sheafFiberConstantSheafIso M).symm hM

/-- The adjunction `c_W ⊣ RΓ_W` between constant complexes and derived sections (blueprint
`pur7710-lem-constant-adjunction`): the derived adjunction of `constantSheaf ⊣ Γ`, the total
left derived functor of the exact constant sheaf functor being identified with the levelwise
functor. -/
noncomputable def constantComplexAdjunction (W : Scheme.{u}) :
    constantComplexFunctor Λ W ⊣ rightDerivedGlobalSectionsModule Λ W :=
  (constantSheafΓAdj W.smallEtaleTopology (ModuleCat.{u + 1} Λ)).derivedAdjunction.ofNatIsoLeft
    (constantSheaf W.smallEtaleTopology
      (ModuleCat.{u + 1} Λ)).leftDerivedFunctorIsoMapDerivedCategory

/-- The monoidal comparison `c_W(M ⊗ᴸ N) ⟶ c_W M ⊗ᴸ c_W N` of constant complexes (blueprint
`pur7710-lem-constant-monoidal`): the derived comonoidal structure
`CategoryTheory.Functor.leftDerivedTensorComparison` of the exact monoidal constant sheaf
functor, transported along `L(constantSheaf) ≅ D(constantSheaf)`. It is an isomorphism. -/
noncomputable def constantComplexTensorComparison (W : Scheme.{u})
    (M N : DerivedCategory (ModuleCat.{u + 1} Λ)) :
    (constantComplexFunctor Λ W).obj (M ⊗ N) ⟶
      ((-⊗ᴸ-(W)[ModuleCat.{u + 1} Λ]).obj ((constantComplexFunctor Λ W).obj M)).obj
        ((constantComplexFunctor Λ W).obj N) :=
  let F := constantSheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)
  let e := F.leftDerivedFunctorIsoMapDerivedCategory
  e.inv.app (M ⊗ N) ≫ (F.leftDerivedTensorComparison.app M).app N ≫
    (e.hom.app M ⊗ₘ e.hom.app N)

/-- Blueprint `pur7710-def-constant-projection`: the constant-tensor comparison.

For a scheme `W`, `K ∈ D(W_ét, Λ)` and `M ∈ D(Mod_Λ)`, the morphism
`P_{W,K,M} : RΓ_W K ⊗ᴸ M ⟶ RΓ_W (K ⊗ᴸ c_W M)` corresponding under `c_W ⊣ RΓ_W`
(`AlgebraicGeometry.Etale.constantComplexAdjunction`) to the composite
`c_W(RΓ_W K ⊗ᴸ M) ⟶ c_W RΓ_W K ⊗ᴸ c_W M ⟶ K ⊗ᴸ c_W M` of the monoidal comparison
(`AlgebraicGeometry.Etale.constantComplexTensorComparison`) and of `ε_K ⊗ 1`. -/
noncomputable def constantProjectionMap (W : Scheme.{u})
    (K : DerivedCategory (Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (M : DerivedCategory (ModuleCat.{u + 1} Λ)) :
    (rightDerivedGlobalSectionsModule Λ W).obj K ⊗ M ⟶
      (rightDerivedGlobalSectionsModule Λ W).obj
        (((-⊗ᴸ-(W)[ModuleCat.{u + 1} Λ]).obj K).obj ((constantComplexFunctor Λ W).obj M)) :=
  (constantComplexAdjunction Λ W).homEquiv _ _
    (constantComplexTensorComparison Λ W _ M ≫
      ((-⊗ᴸ-(W)[ModuleCat.{u + 1} Λ]).map ((constantComplexAdjunction Λ W).counit.app K)).app _)

/-- Blueprint `pur7710-def-kunneth-map`: the ordinary Künneth morphism at finite level.

For schemes `X`, `Y` over `S` (in the blueprint `S = Spec k`), `Z = X ×_S Y` with projections
`p_X`, `p_Y`, and `K ∈ D(X_ét, Λ)`, `L ∈ D(Y_ét, Λ)`, the morphism
`Kun_{K,L} : RΓ_X K ⊗ᴸ RΓ_Y L ⟶ RΓ_Z (K ⊠ᴸ L)` corresponding under `c_Z ⊣ RΓ_Z` to the composite
```
c_Z(RΓ_X K ⊗ᴸ RΓ_Y L) ⟶ c_Z RΓ_X K ⊗ᴸ c_Z RΓ_Y L
  ≅ Lp_X^* c_X RΓ_X K ⊗ᴸ Lp_Y^* c_Y RΓ_Y L ⟶ Lp_X^* K ⊗ᴸ Lp_Y^* L
```
of the monoidal comparison of `c_Z`, of the identifications `Lp^* c ≅ c`
(`AlgebraicGeometry.Etale.constantFunctorCompLeftDerivedUpperStarIso`) and of
`Lp_X^* ε_K ⊗ Lp_Y^* ε_L`. -/
noncomputable def globalSectionsKunnethMap {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (L : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (rightDerivedGlobalSectionsModule Λ X).obj K ⊗ (rightDerivedGlobalSectionsModule Λ Y).obj L ⟶
      (rightDerivedGlobalSectionsModule Λ (pullback f g)).obj (exteriorProduct Λ f g K L) :=
  (constantComplexAdjunction Λ (pullback f g)).homEquiv _ _
    (constantComplexTensorComparison Λ (pullback f g) _ _ ≫
      (((constantFunctorCompLeftDerivedUpperStarIso Λ (pullback.fst f g)).inv.app _ ≫
          L((pullback.fst f g)^*[ModuleCat.{u + 1} Λ]).map
            ((constantComplexAdjunction Λ X).counit.app K)) ⊗ₘ
        ((constantFunctorCompLeftDerivedUpperStarIso Λ (pullback.snd f g)).inv.app _ ≫
          L((pullback.snd f g)^*[ModuleCat.{u + 1} Λ]).map
            ((constantComplexAdjunction Λ Y).counit.app L))))

/-- Blueprint `pur7710-def-kunneth-map-field`: the ordinary Künneth morphism with finite-field
coefficients `F = 𝔽_{ℓ^r}`: the construction of
`AlgebraicGeometry.Etale.globalSectionsKunnethMap` with `F` in place of `Λ`,
`RΓ_X K ⊗ᴸ_F RΓ_Y L ⟶ RΓ_Z (K ⊠ᴸ_F L)`. -/
noncomputable abbrev globalSectionsKunnethMapFiniteField (F : Type (u + 1)) [Field F] [Finite F]
    {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (K : DerivedCategoryFiniteField F X) (L : DerivedCategoryFiniteField F Y) :
    (rightDerivedGlobalSectionsFiniteField F X).obj K ⊗
        (rightDerivedGlobalSectionsFiniteField F Y).obj L ⟶
      (rightDerivedGlobalSectionsFiniteField F (pullback f g)).obj
        (exteriorProductFiniteField F f g K L) :=
  globalSectionsKunnethMap F f g K L

end Etale

end AlgebraicGeometry
