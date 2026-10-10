/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import WeilConjectures.SixFunctors.ProEtale.Adic.OpenImmersion
public import WeilConjectures.SixFunctors.ProEtale.BaseChange.WeaklyEtale

/-!
# Open base change for the pushforward of `ℓ`-adic sheaves

Let

```
U' --j'--> Z'
|          |
g'         g''
v          v
U  --j-->  Z
```

be a cartesian square of schemes with `j` and `j'` weakly étale. The base change map
`j^* g''_* ⟶ g'_* j'^*` of sheaves of `ℚ̄_ℓ`-modules
(`AlgebraicGeometry.ProEtale.isIso_baseChangeMap_of_isPullback`) lifts to sheaves of modules over
the constant `ℓ`-adic sheaves (`AlgebraicGeometry.ProEtale.adicBaseChangeMap`), where it is again
an isomorphism, the forgetful functor reflecting isomorphisms. For `j` an open immersion the
pullbacks along `j` and `j'` have exact left adjoints, the extensions by zero, so they preserve
K-injective complexes, and the base change isomorphism derives:
`j^* ∘ Rg''_* ≅ Rg'_* ∘ j'^*` (`AlgebraicGeometry.ProEtale.adicDerivedBaseChangeIso`). In
particular the higher direct images commute with restriction to an open subscheme.
-/

@[expose] public section

universe u

open CategoryTheory Category Limits Opposite

namespace AlgebraicGeometry.ProEtale

variable (l : ℕ) [Fact l.Prime]

variable {U' U Z' Z : Scheme.{u}} {g' : U' ⟶ U} {j' : U' ⟶ Z'} {j : U ⟶ Z} {g'' : Z' ⟶ Z}

/-- The square isomorphism `j'_* ⋙ g''_* ≅ g'_* ⋙ j_*` of pushforwards of `ℓ`-adic sheaves
attached to a commutative square `g' ≫ j = j' ≫ g''`. -/
noncomputable def adicSquareLowerStarIso (sq : CommSq g' j' j g'') :
    (j')_*ᵃ[l] ⋙ (g'')_*ᵃ[l] ≅ (g')_*ᵃ[l] ⋙ (j)_*ᵃ[l] :=
  adicLowerStarComp l j' g'' ≪≫ adicLowerStarCongr l sq.w.symm ≪≫
    (adicLowerStarComp l g' j).symm

variable [WeaklyEtale j] [WeaklyEtale j']

/-- **The base change map** `g''_* ⋙ j^* ⟶ j'^* ⋙ g'_*` of `ℓ`-adic sheaves, for a commutative
square with `j` and `j'` weakly étale: the mate of
`AlgebraicGeometry.ProEtale.adicSquareLowerStarIso` along `j'^* ⊣ j'_*` and `j^* ⊣ j_*`. -/
noncomputable def adicBaseChangeMap (sq : CommSq g' j' j g'') :
    (g'')_*ᵃ[l] ⋙ (j)^*ᵃ[l] ⟶ (j')^*ᵃ[l] ⋙ (g')_*ᵃ[l] :=
  ((mateEquiv (adicUpperStarLowerStarAdjunction l j')
    (adicUpperStarLowerStarAdjunction l j)).symm
    (TwoSquare.mk _ _ _ _ (adicSquareLowerStarIso l sq).hom)).natTrans

set_option maxHeartbeats 1600000 in
-- The kernel needs time to unfold the module structures of the lifted functors.
omit [WeaklyEtale j] [WeaklyEtale j'] in
/-- The underlying map of sheaves of `ℚ̄_ℓ`-modules of the base change map of `ℓ`-adic sheaves is
the base change map of the underlying sheaves. -/
lemma adicBaseChangeMap_app_hom (sq : CommSq g' j' j g'') (M : AdicSheaf l Z') :
    ((adicBaseChangeMap l sq).app M).hom =
      (ProEtale.baseChangeMap (WeilCoefficients.{u} l) sq).app M.X := by
  simp only [adicBaseChangeMap, ProEtale.baseChangeMap, mateEquiv, Equiv.coe_fn_symm_mk,
    NatTrans.comp_app, Functor.comp_obj, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Functor.leftUnitor_inv_app,
    Functor.rightUnitor_hom_app, Functor.id_obj, comp_id, id_comp, Mod.comp_hom', Mod.id_hom',
    Functor.comp_map,
    adicUpperStar_map_hom, adicLowerStar_map_hom, adicUpperStarLowerStarAdjunction,
    Adjunction.modAdjunction_unit_app_hom, Adjunction.modAdjunction_counit_app_hom,
    adicSquareLowerStarIso, ProEtale.squareLowerStarIso, Iso.trans_hom, Iso.symm_hom,
    adicLowerStarComp_hom_app_hom, adicLowerStarComp_inv_app_hom, adicLowerStarCongr_hom_app_hom]
  rfl

/-- **Weakly étale base change for `ℓ`-adic sheaves**: for a cartesian square the base change
map is an isomorphism. -/
instance isIso_adicBaseChangeMap_of_isPullback (hsq : IsPullback g' j' j g'') :
    IsIso (adicBaseChangeMap l hsq.toCommSq) := by
  have := ProEtale.isIso_baseChangeMap_of_isPullback (WeilCoefficients.{u} l) hsq
  have (M : AdicSheaf l Z') : IsIso ((adicBaseChangeMap l hsq.toCommSq).app M) := by
    have : IsIso ((Mod.forget _).map ((adicBaseChangeMap l hsq.toCommSq).app M)) := by
      change IsIso ((adicBaseChangeMap l hsq.toCommSq).app M).hom
      rw [adicBaseChangeMap_app_hom]
      infer_instance
    exact isIso_of_reflects_iso _ (Mod.forget _)
  exact NatIso.isIso_of_isIso_app _

section Derived

variable [IsOpenImmersion j] [IsOpenImmersion j']

instance : (j')^*ᵃ[l].PreservesKInjectiveComplexes :=
  (adicOpenImmersionLowerShriekAdjunction l j').preservesKInjectiveComplexes

/-- **Open base change for the derived pushforward of `ℓ`-adic sheaves**: for a cartesian square
with `j` (hence `j'`) an open immersion, `j^* ∘ Rg''_* ≅ Rg'_* ∘ j'^*`.

```
D(Z') --Rg''_*--> D(Z)
  |                 |
 j'^*             j^*
  v                 v
D(U') --Rg'_*---> D(U)
```
-/
noncomputable def adicDerivedBaseChangeIso (hsq : IsPullback g' j' j g'') :
    (g'')_*ᵃ[l].rightDerivedFunctor ⋙ (j)^*ᵃ[l].mapDerivedCategory ≅
      (j')^*ᵃ[l].mapDerivedCategory ⋙ (g')_*ᵃ[l].rightDerivedFunctor :=
  have := isIso_adicBaseChangeMap_of_isPullback l hsq
  (Functor.rightDerivedFunctorCompMapDerivedCategoryIso (g'')_*ᵃ[l] (j)^*ᵃ[l]).symm ≪≫
    Functor.rightDerivedFunctorNatIso (asIso (adicBaseChangeMap l hsq.toCommSq)) ≪≫
    Functor.rightDerivedFunctorCompIso (j')^*ᵃ[l] (g')_*ᵃ[l] ≪≫
    Functor.isoWhiskerRight (j')^*ᵃ[l].rightDerivedFunctorIsoMapDerivedCategory
      (g')_*ᵃ[l].rightDerivedFunctor

end Derived

end AlgebraicGeometry.ProEtale
