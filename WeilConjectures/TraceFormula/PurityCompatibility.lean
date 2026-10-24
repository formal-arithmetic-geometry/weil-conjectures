/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.KunnethVerdier

/-!

# Cohomological smoothness and the exceptional Künneth map of a smooth projection

For a smooth morphism `f : X ⟶ Y` of separated `k`-schemes of finite type, cohomological
smoothness (blueprint `sk-prop-cohsm`) provides two canonical isomorphisms on the bounded
constructible derived categories `Dᵇc(-)⟦ℚ̲̄_ℓ⟧`:

* (G11) the *tensor map* `θ_{f,N} : Lf^* N ⊗ᴸ Rf^! ℚ̄_ℓ ⟶ Rf^! N`
  (`ProEtale.CondensedRing.boundedConstructibleUpperShriekTensorMap`), the exceptional adjoint of
  the inverse projection formula followed by the counit of `Rf_! ⊣ Rf^!`;
* (G12) the *exceptional base change map* `Lg'^* Rf^! N ⟶ Rf'^! Lg^* N` of a cartesian square
  (`ProEtale.CondensedRing.boundedConstructibleUpperShriekBaseChangeMap`), the exceptional
  adjoint of the inverse compact-support base change followed by `Lg^*` of the counit.

From them we deduce the only input from smooth purity used by the Künneth–Verdier theorem
(`ProEtale.CondensedRing.isIso_kunnethVerdierMap`, blueprint `thm-trf-kunneth-verdier`): for `Y`
smooth over `k`, the exceptional Künneth map `α : M ⊠ ω_Y ⟶ Rp_X^! M` of the projection
`p_X : X ⨯ Y ⟶ X` is an isomorphism (`ProEtale.CondensedRing.isIso_exceptionalKunnethMap_of_smooth`,
the smooth step of the proof of blueprint `prop-trf-exceptional-kunneth`). Indeed `α` is (G11) for
`p_X` at `M` after `M ⊠ (G12)` for the base change of `a_Y` along `a_X`
(`ProEtale.CondensedRing.exceptionalKunnethMap_eq`).

## Sorried input (blueprint `sk-prop-cohsm`, smooth purity)

- `ProEtale.CondensedRing.isIso_boundedConstructibleUpperShriekTensorMap`: (G11).
- `ProEtale.CondensedRing.isIso_boundedConstructibleUpperShriekBaseChangeMap`: (G12).

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

attribute [local instance] boundedConstructibleBraiding

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

section TensorMap

variable {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]

/-- The *tensor map* `θ_{f,N} : Lf^* N ⊗ᴸ Rf^! ℚ̄_ℓ ⟶ Rf^! N` (blueprint `sk-prop-cohsm`,
Complement, map (G11)): the exceptional adjoint of
```
Rf_! (Lf^* N ⊗ Rf^! ℚ̄_ℓ) ≅ Rf_! (Rf^! ℚ̄_ℓ ⊗ Lf^* N) ≅ Rf_! Rf^! ℚ̄_ℓ ⊗ N --ε ⊗ 1--> ℚ̄_ℓ ⊗ N ≅ N,
```
the tensor symmetry, the inverse of the projection formula, the counit of `Rf_! ⊣ Rf^!` and the
left unitor. The blueprint writes the tensor factors in the other order. -/
noncomputable def boundedConstructibleUpperShriekTensorMap (f : X ⟶ Y)
    (N : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleUpperStar _ ℓ f).obj N ⊗
        (boundedConstructibleUpperShriek _ ℓ f).obj (𝟙_ _) ⟶
      (boundedConstructibleUpperShriek _ ℓ f).obj N :=
  (boundedConstructibleUpperShriekAdjunction _ ℓ f).homEquiv _ _
    ((boundedConstructibleLowerShriek _ ℓ f).map (β_ _ _).hom ≫
      inv (((boundedConstructibleExceptionalProjection _ ℓ f).app
        ((boundedConstructibleUpperShriek _ ℓ f).obj (𝟙_ _))).app N) ≫
      ((boundedConstructibleUpperShriekAdjunction _ ℓ f).counit.app (𝟙_ _) ▷ N) ≫ (λ_ N).hom)

/-- Blueprint `sk-prop-cohsm` (G11): **the tensor formula of a smooth morphism**. For `f` smooth,
the tensor map `θ_{f,N} : Lf^* N ⊗ᴸ Rf^! ℚ̄_ℓ ⟶ Rf^! N` is an isomorphism for every bounded
constructible `N` (SGA 4, Exposé XVIII, Théorème 3.2.5). -/
theorem isIso_boundedConstructibleUpperShriekTensorMap (f : X ⟶ Y) [Smooth f.left]
    (N : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    IsIso (boundedConstructibleUpperShriekTensorMap ℓ f N) :=
  sorry

end TensorMap

section BaseChangeMap

attribute [local instance] isIso_boundedConstructibleLowerShriekBaseChange_padicAlgCl

variable {X Y X' Y' : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom] [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
  [IsSeparated X'.hom] [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]
  {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}

/-- The *exceptional base change map* `Lg'^* Rf^! N ⟶ Rf'^! Lg^* N` of a cartesian square
`g' ≫ f = f' ≫ g` (blueprint `sk-prop-cohsm`, Complement, map (G12)): the exceptional adjoint of
```
Rf'_! Lg'^* Rf^! N ≅ Lg^* Rf_! Rf^! N --Lg^* ε--> Lg^* N,
```
the inverse of compact-support base change followed by `Lg^*` of the counit of `Rf_! ⊣ Rf^!`. -/
noncomputable def boundedConstructibleUpperShriekBaseChangeMap (sq : IsPullback g' f' f g)
    (N : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleUpperStar _ ℓ g').obj ((boundedConstructibleUpperShriek _ ℓ f).obj N) ⟶
      (boundedConstructibleUpperShriek _ ℓ f').obj ((boundedConstructibleUpperStar _ ℓ g).obj N) :=
  (boundedConstructibleUpperShriekAdjunction _ ℓ f').homEquiv _ _
    ((asIso (boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ sq)).inv.app
        ((boundedConstructibleUpperShriek _ ℓ f).obj N) ≫
      (boundedConstructibleUpperStar _ ℓ g).map
        ((boundedConstructibleUpperShriekAdjunction _ ℓ f).counit.app N))

/-- Blueprint `sk-prop-cohsm` (G12): **exceptional base change along a smooth morphism**. For `f`
smooth and a cartesian square `g' ≫ f = f' ≫ g`, the exceptional base change map
`Lg'^* Rf^! N ⟶ Rf'^! Lg^* N` is an isomorphism for every bounded constructible `N` (SGA 4,
Exposé XVIII, Théorème 3.2.5 and 2.9 (Var 4)). The compatibility of (G12) with (G11) asserted by
the blueprint is not needed here. -/
theorem isIso_boundedConstructibleUpperShriekBaseChangeMap [Smooth f.left]
    (sq : IsPullback g' f' f g) (N : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    IsIso (boundedConstructibleUpperShriekBaseChangeMap ℓ sq N) :=
  sorry

end BaseChangeMap

section Kunneth

variable {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]

/-- The inverse of the projection formula is natural in its first variable. -/
private lemma lowerShriek_map_whiskerRight_comp_inv_exceptionalProjection
    {Z : Over (Spec (.of k))} [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]
    [IsSeparated Z.hom] (f : Z ⟶ X) {K K' : Dᵇc(Z.left)⟦Profinite.padicAlgClRingObj ℓ⟧}
    (φ : K ⟶ K') (B : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleLowerShriek _ ℓ f).map (φ ▷ (boundedConstructibleUpperStar _ ℓ f).obj B) ≫
        inv (((boundedConstructibleExceptionalProjection _ ℓ f).app K').app B) =
      inv (((boundedConstructibleExceptionalProjection _ ℓ f).app K).app B) ≫
        ((boundedConstructibleLowerShriek _ ℓ f).map φ ▷ B) := by
  rw [IsIso.comp_inv_eq, Category.assoc, IsIso.eq_inv_comp]
  exact (boundedConstructibleExceptionalProjectionMorphism_natural_left _ ℓ f φ B).symm

/-- The adjoint of `adj.homEquiv x ≫ G.map e` is `x ≫ e`. -/
private lemma map_homEquiv_comp_map_comp_counit {𝒞 𝒟 : Type*} [Category* 𝒞] [Category* 𝒟]
    {F : 𝒞 ⥤ 𝒟} {G : 𝒟 ⥤ 𝒞} (adj : F ⊣ G) {A : 𝒞} {B B' : 𝒟} (x : F.obj A ⟶ B)
    (e : B ⟶ B') :
    F.map (adj.homEquiv _ _ x ≫ G.map e) ≫ adj.counit.app B' = x ≫ e := by
  rw [← adj.homEquiv_naturality_right]
  exact (adj.homEquiv_counit _ _ _).symm.trans ((adj.homEquiv _ _).symm_apply_apply _)

/-- The computation behind `exceptionalKunnethMap_eq`, for abstract functors and morphisms: an
exceptional adjoint of the shape of `exceptionalKunnethAdjoint` factors through the transpose of
`y : W ⟶ R 𝟙`, as soon as the adjoint of `y` is the composite `b ≫ c ≫ e`. -/
private lemma homEquiv_eq_whiskerLeft_comp_homEquiv {𝒞 𝒟 : Type*} [Category* 𝒞] [Category* 𝒟]
    [MonoidalCategory 𝒞] [BraidedCategory 𝒞] [MonoidalCategory 𝒟] {L : 𝒞 ⥤ 𝒟} {R : 𝒟 ⥤ 𝒞}
    (adj : L ⊣ R) (A : 𝒞) (M : 𝒟) {W : 𝒞} (y : W ⟶ R.obj (𝟙_ 𝒟))
    (ipf : ∀ K : 𝒞, L.obj (K ⊗ A) ⟶ L.obj K ⊗ M)
    (hpf : L.map (y ▷ A) ≫ ipf (R.obj (𝟙_ 𝒟)) = ipf W ≫ (L.map y ▷ M))
    {T₁ T₂ : 𝒟} (b : L.obj W ⟶ T₁) (c : T₁ ⟶ T₂) (e : T₂ ⟶ 𝟙_ 𝒟)
    (hy : L.map y ≫ adj.counit.app (𝟙_ 𝒟) = b ≫ c ≫ e) :
    adj.homEquiv _ _ (L.map (β_ A W).hom ≫ ipf W ≫ (b ▷ M) ≫ (c ▷ M) ≫ (e ▷ M) ≫ (λ_ M).hom) =
      A ◁ y ≫ adj.homEquiv _ _ (L.map (β_ A (R.obj (𝟙_ 𝒟))).hom ≫ ipf (R.obj (𝟙_ 𝒟)) ≫
        (adj.counit.app (𝟙_ 𝒟) ▷ M) ≫ (λ_ M).hom) := by
  rw [← adj.homEquiv_naturality_left, ← L.map_comp_assoc,
    BraidedCategory.braiding_naturality_right, L.map_comp_assoc, reassoc_of% hpf,
    ← comp_whiskerRight_assoc (L.map y), hy]
  simp only [comp_whiskerRight, Category.assoc]

/-- **The exceptional Künneth map of `p_X` through cohomological smoothness**: the exceptional
Künneth map `α : Lp_X^* M ⊗ Lp_Y^* ω_Y ⟶ Rp_X^! M` is the exceptional base change map (G12)
`Lp_Y^* Ra_Y^! ℚ̄_ℓ ⟶ Rp_X^! La_X^* ℚ̄_ℓ ≅ Rp_X^! ℚ̄_ℓ` of the product square, tensored with
`Lp_X^* M`, followed by the tensor map (G11) `Lp_X^* M ⊗ Rp_X^! ℚ̄_ℓ ⟶ Rp_X^! M` of `p_X`. -/
lemma exceptionalKunnethMap_eq (M : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    exceptionalKunnethMap ℓ (Y := Y) M =
      (boundedConstructibleUpperStar _ ℓ (prod.fst : X ⨯ Y ⟶ X)).obj M ◁
          (boundedConstructibleUpperShriekBaseChangeMap ℓ (isPullback_prod_toPoint X Y) (𝟙_ _) ≫
            (boundedConstructibleUpperShriek _ ℓ (prod.fst : X ⨯ Y ⟶ X)).map
              (Functor.Monoidal.εIso (boundedConstructibleUpperStar _ ℓ (toPoint X))).inv) ≫
        boundedConstructibleUpperShriekTensorMap ℓ (prod.fst : X ⨯ Y ⟶ X) M :=
  homEquiv_eq_whiskerLeft_comp_homEquiv
    (boundedConstructibleUpperShriekAdjunction _ ℓ (prod.fst : X ⨯ Y ⟶ X))
    ((boundedConstructibleUpperStar _ ℓ (prod.fst : X ⨯ Y ⟶ X)).obj M) M _
    (fun K ↦ inv (((boundedConstructibleExceptionalProjection _ ℓ (prod.fst : X ⨯ Y ⟶ X)).app
      K).app M))
    (lowerShriek_map_whiskerRight_comp_inv_exceptionalProjection ℓ _ _ M) _ _ _
    ((map_homEquiv_comp_map_comp_counit _ _ _).trans (Category.assoc _ _ _))

/-- **Purity for a smooth projection** (the smooth step of the proof of blueprint
`prop-trf-exceptional-kunneth`): for `Y` smooth over `k`, the exceptional Künneth map
`α : M ⊠ ω_Y ⟶ Rp_X^! M` of the projection `p_X : X ⨯ Y ⟶ X` is an isomorphism for every bounded
constructible `M` on `X`. By `exceptionalKunnethMap_eq` it is (G11) for the smooth morphism `p_X`
after `M ⊠ (G12)` for the smooth morphism `a_Y` (blueprint `sk-prop-cohsm`). -/
theorem isIso_exceptionalKunnethMap_of_smooth [Smooth Y.hom]
    (M : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    IsIso (exceptionalKunnethMap ℓ (Y := Y) M) := by
  have : Smooth (toPoint Y).left := inferInstanceAs (Smooth Y.hom)
  have : Smooth (prod.fst : X ⨯ Y ⟶ X).left :=
    MorphismProperty.of_isPullback (isPullback_prod_left X Y).flip inferInstance
  have := isIso_boundedConstructibleUpperShriekBaseChangeMap ℓ (isPullback_prod_toPoint X Y) (𝟙_ _)
  have := isIso_boundedConstructibleUpperShriekTensorMap ℓ (prod.fst : X ⨯ Y ⟶ X) M
  rw [exceptionalKunnethMap_eq]
  infer_instance

end Kunneth

end AlgebraicGeometry.ProEtale.CondensedRing
