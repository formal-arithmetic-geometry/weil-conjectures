/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.CoefficientChangeExchange
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.RelativeMap

/-!
# Coefficient comparisons and the composition law of `Rf_!`

Let `ρ : Λ →+* Λ'` be a morphism of finite coefficient rings. For composable `f : X ⟶ Y` and
`g : Y ⟶ S` admitting compactifications, with `f ≫ g = h` quasi-compact and `Y`, `S`
quasi-compact, the composition isomorphism `R(h)_! ≅ Rf_! ⋙ Rg_!`
(`AlgebraicGeometry.Etale.rightDerivedLowerShriekCompIsoOfEq`) is compatible with the
coefficient comparisons `Res ⋙ Rf_! ≅ Rf_! ⋙ Res`
(`AlgebraicGeometry.Etale.derivedRestrictScalarsCompRightDerivedLowerShriekIso`), in the sense of
`AlgebraicGeometry.Etale.CoeffCompatible`
(`AlgebraicGeometry.Etale.coeffCompatible_rightDerivedLowerShriekCompIsoOfEq`).

The composition isomorphism is assembled from the comparison of compactifications, which is
handled by `AlgebraicGeometry.Etale.coeffCompatible_rightDerivedLowerShriekOfCompactificationIso`,
and the isomorphism `AlgebraicGeometry.Etale.rightDerivedLowerShriekOfCompactificationCompIso`
on compatible compactifications. The latter is built from associators, whiskerings and three
kinds of building blocks, whose compatibility is proved here:

- the composition of extensions by zero
  (`AlgebraicGeometry.Etale.coeffCompatible_mapDerivedCategoryOpenImmersionLowerShriekComp`),
  reduced to sheaves and then, through the units of `j_! ⊣ j^*`, to the compatibility of the
  composition of pullbacks (`AlgebraicGeometry.Etale.CoeffCompatible.of_unit_comp`);
- the exchange `Rg'_* ⋙ Dj_! ⟶ Dj'_! ⋙ Rg''_*` of an extension by zero with a direct image
  (`AlgebraicGeometry.Etale.coeffCompatible_openImmersionLowerShriekLowerStarExchange`), a mate
  of the base change isomorphism of the extension by zero;
- the composition of derived direct images
  (`AlgebraicGeometry.Etale.coeffCompatible_rightDerivedLowerStarComp`), a conjugate of the
  composition of pullbacks.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

open Scheme

section UnitComp

variable {A₁ A₂ A₃ B₁ B₂ B₃ : Type*} [Category A₁] [Category A₂] [Category A₃] [Category B₁]
  [Category B₂] [Category B₃]
  {L₁ : A₂ ⥤ A₁} {R₁ : A₁ ⥤ A₂} {L₂ : A₃ ⥤ A₂} {R₂ : A₂ ⥤ A₃} {L : A₃ ⥤ A₁} {R : A₁ ⥤ A₃}
  {M₁ : B₂ ⥤ B₁} {S₁ : B₁ ⥤ B₂} {M₂ : B₃ ⥤ B₂} {S₂ : B₂ ⥤ B₃} {M : B₃ ⥤ B₁} {S : B₁ ⥤ B₃}
  {r₁ : B₁ ⥤ A₁} {r₂ : B₂ ⥤ A₂} {r₃ : B₃ ⥤ A₃}

/-- **Compatibility of an isomorphism of composite left adjoints, through units.** Let
`L ⊣ R`, `L₁ ⊣ R₁`, `L₂ ⊣ R₂` and `M ⊣ S`, `M₁ ⊣ S₁`, `M₂ ⊣ S₂` be adjunctions related by
restriction functors `r` through comparisons `τ` of the left adjoints and `σ` of the right
adjoints, compatible with the units (`hu`, `hu₁`, `hu₂`). Let `eL : L ⟶ L₂ ⋙ L₁` and
`eM : M ⟶ M₂ ⋙ M₁` correspond, under the units, to `eR : R₁ ⋙ R₂ ⟶ R` and
`eS : S₁ ⋙ S₂ ⟶ S`. If `eR` and `eS` are compatible with the comparisons `σ`, then `eL` and `eM`
are compatible with the comparisons `τ`. -/
lemma CoeffCompatible.of_unit_comp (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) (a : L ⊣ R) (b₁ : M₁ ⊣ S₁)
    (b₂ : M₂ ⊣ S₂) (b : M ⊣ S) (τ₁ : r₂ ⋙ L₁ ≅ M₁ ⋙ r₁) (σ₁ : r₁ ⋙ R₁ ≅ S₁ ⋙ r₂)
    (τ₂ : r₃ ⋙ L₂ ≅ M₂ ⋙ r₂) (σ₂ : r₂ ⋙ R₂ ≅ S₂ ⋙ r₃) (τ : r₃ ⋙ L ≅ M ⋙ r₁)
    (σ : r₁ ⋙ R ≅ S ⋙ r₃)
    (hu₁ : ∀ N, a₁.unit.app (r₂.obj N) ≫ R₁.map (τ₁.hom.app N) ≫ σ₁.hom.app (M₁.obj N) =
      r₂.map (b₁.unit.app N))
    (hu₂ : ∀ N, a₂.unit.app (r₃.obj N) ≫ R₂.map (τ₂.hom.app N) ≫ σ₂.hom.app (M₂.obj N) =
      r₃.map (b₂.unit.app N))
    (hu : ∀ N, a.unit.app (r₃.obj N) ≫ R.map (τ.hom.app N) ≫ σ.hom.app (M.obj N) =
      r₃.map (b.unit.app N))
    (eL : L ⟶ L₂ ⋙ L₁) (eM : M ⟶ M₂ ⋙ M₁) (eR : R₁ ⋙ R₂ ⟶ R) (eS : S₁ ⋙ S₂ ⟶ S)
    (hL : ∀ c, a.unit.app c ≫ R.map (eL.app c) = (a₂.comp a₁).unit.app c ≫ eR.app _)
    (hM : ∀ c, b.unit.app c ≫ S.map (eM.app c) = (b₂.comp b₁).unit.app c ≫ eS.app _)
    (hR : ∀ X, R₂.map (σ₁.hom.app X) ≫ σ₂.hom.app (S₁.obj X) ≫ r₃.map (eS.app X) =
      eR.app (r₁.obj X) ≫ σ.hom.app X) :
    CoeffCompatible τ (pasteTwoSquaresIso τ₂ τ₁) eL eM := by
  intro N
  apply (a.homEquiv _ _).injective
  rw [← cancel_mono (σ.hom.app (M₁.obj (M₂.obj N))), pasteTwoSquaresIso_hom_app,
    Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  have n₁ := σ.hom.naturality (eM.app N)
  have n₂ := σ₂.hom.naturality (b₁.unit.app (M₂.obj N))
  have n₃ := eR.naturality (L₁.map (τ₂.hom.app N) ≫ τ₁.hom.app (M₂.obj N))
  have n₄ := congrArg R₂.map (a₁.unit.naturality (τ₂.hom.app N))
  have k := congrArg r₃.map (hM N)
  have k₁ := congrArg R₂.map (hu₁ (M₂.obj N))
  have k₂ := hR (M₁.obj (M₂.obj N))
  have l := hL (r₃.obj N)
  simp only [Functor.comp_obj, Functor.comp_map, Functor.id_obj, Functor.id_map,
    Adjunction.comp_unit_app, Functor.map_comp, Category.assoc] at n₁ n₂ n₃ n₄ k k₁ l
  simp only [Functor.map_comp, Category.assoc]
  rw [n₁, reassoc_of% (hu N), k, ← hu₂, Category.assoc, Category.assoc, ← reassoc_of% n₂,
    ← reassoc_of% k₁, k₂, reassoc_of% l, ← reassoc_of% n₃, reassoc_of% n₄]

end UnitComp

variable {Λ Λ' : Type (u + 1)} [CommRing Λ] [CommRing Λ'] (ρ : Λ →+* Λ')

section OpenImmersion

variable {V U X : Scheme.{u}} (j' : V ⟶ U) (j : U ⟶ X) [IsOpenImmersion j'] [IsOpenImmersion j]

/-- The composition isomorphism `(j' ≫ j)_! ≅ j'_! ⋙ j_!` of extensions by zero corresponds,
under the units of the adjunctions `j_! ⊣ j^*`, to the inverse of the composition isomorphism
`(j' ≫ j)^* ≅ j^* ⋙ j'^*` of pullbacks. -/
lemma unit_app_comp_map_openImmersionLowerShriekComp_hom_app (A : Type*) [Category.{u + 1} A]
    [Abelian A] [IsGrothendieckAbelian.{u + 1} A] [HasSmallSiteSheafify A]
    (F : Sheaf V.smallEtaleTopology A) :
    (openImmersionLowerShriekUpperStarAdjunction A (j' ≫ j)).unit.app F ≫
      (j' ≫ j)^*[A].map ((openImmersionLowerShriekComp A j' j).hom.app F) =
    ((openImmersionLowerShriekUpperStarAdjunction A j').comp
        (openImmersionLowerShriekUpperStarAdjunction A j)).unit.app F ≫
      (upperStarComp A j' j).inv.app _ := by
  rw [openImmersionLowerShriekComp, Adjunction.unit_leftAdjointUniq_hom_app,
    ← Adjunction.homEquiv_id, Adjunction.homEquiv_ofNatIsoRight_apply, Adjunction.homEquiv_id]
  rfl

/-- The composition isomorphism `(j' ≫ j)_! ≅ j'_! ⋙ j_!` of extensions by zero of étale sheaves is
compatible with the comparisons `AlgebraicGeometry.Etale.openImmersionLowerShriekRestrictScalarsIso`
of restriction of scalars with the extensions by zero. -/
lemma coeffCompatible_openImmersionLowerShriekComp :
    CoeffCompatible (openImmersionLowerShriekRestrictScalarsIso ρ (j' ≫ j))
      (pasteTwoSquaresIso (openImmersionLowerShriekRestrictScalarsIso ρ j')
        (openImmersionLowerShriekRestrictScalarsIso ρ j))
      (openImmersionLowerShriekComp (ModuleCat.{u + 1} Λ) j' j).hom
      (openImmersionLowerShriekComp (ModuleCat.{u + 1} Λ') j' j).hom :=
  CoeffCompatible.of_unit_comp (openImmersionLowerShriekUpperStarAdjunction _ j)
    (openImmersionLowerShriekUpperStarAdjunction _ j')
    (openImmersionLowerShriekUpperStarAdjunction _ (j' ≫ j))
    (openImmersionLowerShriekUpperStarAdjunction _ j)
    (openImmersionLowerShriekUpperStarAdjunction _ j')
    (openImmersionLowerShriekUpperStarAdjunction _ (j' ≫ j))
    (openImmersionLowerShriekRestrictScalarsIso ρ j) (upperStarRestrictScalarsIso ρ j)
    (openImmersionLowerShriekRestrictScalarsIso ρ j') (upperStarRestrictScalarsIso ρ j')
    (openImmersionLowerShriekRestrictScalarsIso ρ (j' ≫ j))
    (upperStarRestrictScalarsIso ρ (j' ≫ j))
    (openImmersionLowerShriekUpperStarAdjunction_unit_app_comp_upperStarMap ρ j)
    (openImmersionLowerShriekUpperStarAdjunction_unit_app_comp_upperStarMap ρ j')
    (openImmersionLowerShriekUpperStarAdjunction_unit_app_comp_upperStarMap ρ (j' ≫ j))
    _ _ (upperStarComp _ j' j).inv (upperStarComp _ j' j).inv
    (unit_app_comp_map_openImmersionLowerShriekComp_hom_app j' j _)
    (unit_app_comp_map_openImmersionLowerShriekComp_hom_app j' j _) fun G ↦ by
      rw [← cancel_epi ((upperStarComp (ModuleCat.{u + 1} Λ) j' j).hom.app
        ((Sheaf.restrictScalars X.smallEtaleTopology ρ).obj G)), Iso.hom_inv_id_app_assoc,
        ← reassoc_of% (upperStarRestrictScalarsIso_hom_app_comp_upperStarComp ρ j' j _ rfl G),
        ← Functor.map_comp, Iso.hom_inv_id_app, CategoryTheory.Functor.map_id, Category.comp_id]

/-- The composition isomorphism `D((j' ≫ j)_!) ≅ D(j'_!) ⋙ D(j_!)` of derived extensions by
zero is compatible with the coefficient comparisons
`AlgebraicGeometry.Etale.derivedRestrictScalarsCompOpenImmersionLowerShriekIso`. -/
lemma coeffCompatible_mapDerivedCategoryOpenImmersionLowerShriekComp :
    CoeffCompatible (derivedRestrictScalarsCompOpenImmersionLowerShriekIso ρ (j' ≫ j))
      (pasteTwoSquaresIso (derivedRestrictScalarsCompOpenImmersionLowerShriekIso ρ j')
        (derivedRestrictScalarsCompOpenImmersionLowerShriekIso ρ j))
      (mapDerivedCategoryOpenImmersionLowerShriekComp (ModuleCat.{u + 1} Λ) j' j).hom
      (mapDerivedCategoryOpenImmersionLowerShriekComp (ModuleCat.{u + 1} Λ') j' j).hom :=
  (CoeffCompatible.mapDerivedCategoryNatIso
    (coeffCompatible_openImmersionLowerShriekComp ρ j' j)).comp
    (CoeffCompatible.mapDerivedCategoryCompIso _ _)

/-- The isomorphism `D(j'_!) ⋙ D(j_!) ≅ D(a_!)` for `j' ≫ j = a`, the inverse of the composition
isomorphism followed by the identification along `j' ≫ j = a`, is compatible with the
coefficient comparisons. -/
lemma coeffCompatible_mapDerivedCategoryOpenImmersionLowerShriekComp_symm_trans_congr
    {a : V ⟶ X} [IsOpenImmersion a] (h : j' ≫ j = a) :
    CoeffCompatible
      (pasteTwoSquaresIso (derivedRestrictScalarsCompOpenImmersionLowerShriekIso ρ j')
        (derivedRestrictScalarsCompOpenImmersionLowerShriekIso ρ j))
      (derivedRestrictScalarsCompOpenImmersionLowerShriekIso ρ a)
      ((mapDerivedCategoryOpenImmersionLowerShriekComp (ModuleCat.{u + 1} Λ) j' j).symm ≪≫
        mapDerivedCategoryOpenImmersionLowerShriekCongr _ h).hom
      ((mapDerivedCategoryOpenImmersionLowerShriekComp (ModuleCat.{u + 1} Λ') j' j).symm ≪≫
        mapDerivedCategoryOpenImmersionLowerShriekCongr _ h).hom := by
  subst h
  intro K
  simpa [mapDerivedCategoryOpenImmersionLowerShriekCongr] using
    (coeffCompatible_mapDerivedCategoryOpenImmersionLowerShriekComp ρ j' j).inv K

end OpenImmersion

/-- The exchange map `Rg'_* ⋙ Dj_! ⟶ Dj'_! ⋙ Rg''_*` of an extension by zero with a derived
direct image (`AlgebraicGeometry.Etale.openImmersionLowerShriekLowerStarExchange`), for a
cartesian square `g' ≫ j = j' ≫ g''` with `j`, `j'` open immersions, is compatible with the
coefficient comparisons of the derived direct images and of the derived extensions by zero.
It is the mate of the inverse of the base change isomorphism of the extension by zero, which is
compatible with the coefficient comparisons, and the comparisons of the derived direct images
are mates of those of the pullbacks. -/
lemma coeffCompatible_openImmersionLowerShriekLowerStarExchange {U' U Z' Z : Scheme.{u}}
    {g' : U' ⟶ U} {j' : U' ⟶ Z'} {j : U ⟶ Z} {g'' : Z' ⟶ Z} [IsOpenImmersion j]
    [IsOpenImmersion j'] (hsq : IsPullback g' j' j g'') (d' d'' : ℕ)
    (hd' : ∀ (F : Sheaf U'.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℕ), d' < q →
      IsZero ((((g')_*[ModuleCat.{u + 1} Λ]).rightDerived q).obj F))
    (hd'' : ∀ (F : Sheaf Z'.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℕ), d'' < q →
      IsZero ((((g'')_*[ModuleCat.{u + 1} Λ]).rightDerived q).obj F)) :
    CoeffCompatible
      (pasteTwoSquaresIso (derivedRestrictScalarsCompRightDerivedLowerStarIso ρ g' d' hd')
        (derivedRestrictScalarsCompOpenImmersionLowerShriekIso ρ j))
      (pasteTwoSquaresIso (derivedRestrictScalarsCompOpenImmersionLowerShriekIso ρ j')
        (derivedRestrictScalarsCompRightDerivedLowerStarIso ρ g'' d'' hd''))
      (openImmersionLowerShriekLowerStarExchange (ModuleCat.{u + 1} Λ) hsq)
      (openImmersionLowerShriekLowerStarExchange (ModuleCat.{u + 1} Λ') hsq) := by
  have hbc : CoeffCompatible
      (pasteTwoSquaresIso (Functor.mapDerivedCategorySquareIso (upperStarRestrictScalarsIso ρ g'))
        (derivedRestrictScalarsCompOpenImmersionLowerShriekIso ρ j'))
      (pasteTwoSquaresIso (derivedRestrictScalarsCompOpenImmersionLowerShriekIso ρ j)
        (Functor.mapDerivedCategorySquareIso (upperStarRestrictScalarsIso ρ g'')))
      (mapDerivedCategoryOpenImmersionLowerShriekBaseChangeIso _ hsq).hom
      (mapDerivedCategoryOpenImmersionLowerShriekBaseChangeIso _ hsq).hom := fun K ↦ by
    rw [pasteTwoSquaresIso_hom_app, pasteTwoSquaresIso_hom_app, Category.assoc]
    have := isIso_openImmersionLowerShriekBaseChangeMap (ModuleCat.{u + 1} Λ) hsq
    have := isIso_openImmersionLowerShriekBaseChangeMap (ModuleCat.{u + 1} Λ') hsq
    exact mapDerivedCategorySquareIso_hom_app_comp_of_comm _ _ _ _
      (asIso (openImmersionLowerShriekBaseChangeMap (ModuleCat.{u + 1} Λ') hsq.toCommSq))
      (asIso (openImmersionLowerShriekBaseChangeMap (ModuleCat.{u + 1} Λ) hsq.toCommSq))
      (openImmersionLowerShriekBaseChangeMap_app_restrictScalars ρ hsq.toCommSq) K
  intro K
  rw [pasteTwoSquaresIso_hom_app, pasteTwoSquaresIso_hom_app, Category.assoc]
  exact Adjunction.mateEquiv_restrict (mapDerivedUpperStarLowerStarAdjunction _ g')
    (mapDerivedUpperStarLowerStarAdjunction _ g'') (mapDerivedUpperStarLowerStarAdjunction _ g')
    (mapDerivedUpperStarLowerStarAdjunction _ g'')
    (mapDerivedCategoryOpenImmersionLowerShriekBaseChangeIso _ hsq).inv
    (mapDerivedCategoryOpenImmersionLowerShriekBaseChangeIso _ hsq).inv
    (Functor.mapDerivedCategorySquareIso (upperStarRestrictScalarsIso ρ g'))
    (derivedRestrictScalarsCompRightDerivedLowerStarIso ρ g' d' hd')
    (Functor.mapDerivedCategorySquareIso (upperStarRestrictScalarsIso ρ g''))
    (derivedRestrictScalarsCompRightDerivedLowerStarIso ρ g'' d'' hd'')
    (derivedRestrictScalarsCompOpenImmersionLowerShriekIso ρ j)
    (derivedRestrictScalarsCompOpenImmersionLowerShriekIso ρ j')
    (mateEquiv_mapDerivedUpperStarLowerStarAdjunction_restrictScalars ρ g' d' hd')
    (mateEquiv_mapDerivedUpperStarLowerStarAdjunction_restrictScalars ρ g'' d'' hd'')
    (fun N ↦ by simpa only [pasteTwoSquaresIso_hom_app, Category.assoc] using hbc.inv N) K

/-- The composition isomorphism `Rg₁_* ⋙ Rg₂_* ≅ R(g₁ ≫ g₂)_*` of derived direct images
(`AlgebraicGeometry.Etale.rightDerivedLowerStarComp`) is compatible with the coefficient
comparisons `AlgebraicGeometry.Etale.derivedRestrictScalarsCompRightDerivedLowerStarIso`, for
any bounds on the higher direct images. It is the conjugate of the composition isomorphism of
the pullbacks, which is compatible with the coefficient comparisons. -/
lemma coeffCompatible_rightDerivedLowerStarComp {T S U : Scheme.{u}} (g₁ : T ⟶ S) (g₂ : S ⟶ U)
    (d₁ d₂ d₁₂ : ℕ)
    (hd₁ : ∀ (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℕ), d₁ < q →
      IsZero ((((g₁)_*[ModuleCat.{u + 1} Λ]).rightDerived q).obj F))
    (hd₂ : ∀ (F : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℕ), d₂ < q →
      IsZero ((((g₂)_*[ModuleCat.{u + 1} Λ]).rightDerived q).obj F))
    (hd₁₂ : ∀ (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℕ), d₁₂ < q →
      IsZero ((((g₁ ≫ g₂)_*[ModuleCat.{u + 1} Λ]).rightDerived q).obj F)) :
    CoeffCompatible
      (pasteTwoSquaresIso (derivedRestrictScalarsCompRightDerivedLowerStarIso ρ g₁ d₁ hd₁)
        (derivedRestrictScalarsCompRightDerivedLowerStarIso ρ g₂ d₂ hd₂))
      (derivedRestrictScalarsCompRightDerivedLowerStarIso ρ (g₁ ≫ g₂) d₁₂ hd₁₂)
      (rightDerivedLowerStarComp (ModuleCat.{u + 1} Λ) g₁ g₂).hom
      (rightDerivedLowerStarComp (ModuleCat.{u + 1} Λ') g₁ g₂).hom := fun M ↦ by
  rw [pasteTwoSquaresIso_hom_app, Category.assoc]
  exact Adjunction.conjugateEquiv_comp_restrict
    (mapDerivedUpperStarLowerStarAdjunction _ g₁)
    (mapDerivedUpperStarLowerStarAdjunction _ g₂)
    (mapDerivedUpperStarLowerStarAdjunction _ (g₁ ≫ g₂))
    (mapDerivedUpperStarLowerStarAdjunction _ g₁)
    (mapDerivedUpperStarLowerStarAdjunction _ g₂)
    (mapDerivedUpperStarLowerStarAdjunction _ (g₁ ≫ g₂))
    (Functor.mapDerivedCategorySquareIso (upperStarRestrictScalarsIso ρ g₁))
    (derivedRestrictScalarsCompRightDerivedLowerStarIso ρ g₁ d₁ hd₁)
    (Functor.mapDerivedCategorySquareIso (upperStarRestrictScalarsIso ρ g₂))
    (derivedRestrictScalarsCompRightDerivedLowerStarIso ρ g₂ d₂ hd₂)
    (Functor.mapDerivedCategorySquareIso (upperStarRestrictScalarsIso ρ (g₁ ≫ g₂)))
    (derivedRestrictScalarsCompRightDerivedLowerStarIso ρ (g₁ ≫ g₂) d₁₂ hd₁₂)
    (mateEquiv_mapDerivedUpperStarLowerStarAdjunction_restrictScalars ρ g₁ d₁ hd₁)
    (mateEquiv_mapDerivedUpperStarLowerStarAdjunction_restrictScalars ρ g₂ d₂ hd₂)
    (mateEquiv_mapDerivedUpperStarLowerStarAdjunction_restrictScalars ρ (g₁ ≫ g₂) d₁₂ hd₁₂) _ _
    (Functor.mapDerivedCategorySquareIso_hom_app_comp (upperStarRestrictScalarsIso ρ g₂)
      (upperStarRestrictScalarsIso ρ g₁) (upperStarRestrictScalarsIso ρ (g₁ ≫ g₂))
      (upperStarComp _ g₁ g₂) (upperStarComp _ g₁ g₂)
      (upperStarRestrictScalarsIso_hom_app_comp_upperStarComp ρ g₁ g₂ _ rfl))
    M

variable [Finite Λ] [Finite Λ']

section CompactificationComp

variable {X Y S : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ S}

/-- The isomorphism `Rf_!(e.restrict) ⋙ Rg_!(d) ≅ R(f ≫ g)_!(d.comp e)`
(`AlgebraicGeometry.Etale.rightDerivedLowerShriekOfCompactificationCompIso`) is compatible
with the coefficient comparisons of the derived lower shrieks, written as pastings of the
comparisons of the extensions by zero and of the derived direct images, for arbitrary bounds on
the higher direct images. -/
lemma coeffCompatible_rightDerivedLowerShriekOfCompactificationCompIso_hom
    (d : Compactification g) (e : Compactification (f ≫ d.i)) (n₁ n₂ n₃ n₄ : ℕ)
    (h₁ : ∀ (F : Sheaf e.restrict.Z.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℕ), n₁ < q →
      IsZero ((((e.restrict.g)_*[ModuleCat.{u + 1} Λ]).rightDerived q).obj F))
    (h₂ : ∀ (F : Sheaf d.Z.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℕ), n₂ < q →
      IsZero ((((d.g)_*[ModuleCat.{u + 1} Λ]).rightDerived q).obj F))
    (h₃ : ∀ (F : Sheaf e.Z.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℕ), n₃ < q →
      IsZero ((((e.g)_*[ModuleCat.{u + 1} Λ]).rightDerived q).obj F))
    (h₄ : ∀ (F : Sheaf e.Z.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℕ), n₄ < q →
      IsZero ((((e.g ≫ d.g)_*[ModuleCat.{u + 1} Λ]).rightDerived q).obj F)) :
    CoeffCompatible
      (pasteTwoSquaresIso
        (pasteTwoSquaresIso (derivedRestrictScalarsCompOpenImmersionLowerShriekIso ρ e.restrict.i)
          (derivedRestrictScalarsCompRightDerivedLowerStarIso ρ e.restrict.g n₁ h₁))
        (pasteTwoSquaresIso (derivedRestrictScalarsCompOpenImmersionLowerShriekIso ρ d.i)
          (derivedRestrictScalarsCompRightDerivedLowerStarIso ρ d.g n₂ h₂)))
      (pasteTwoSquaresIso (derivedRestrictScalarsCompOpenImmersionLowerShriekIso ρ e.i)
        (derivedRestrictScalarsCompRightDerivedLowerStarIso ρ (e.g ≫ d.g) n₄ h₄))
      (rightDerivedLowerShriekOfCompactificationCompIso Λ d e).hom
      (rightDerivedLowerShriekOfCompactificationCompIso Λ' d e).hom :=
  (CoeffCompatible.associator_hom _ _ _).comp
    ((CoeffCompatible.whiskerLeft _
      ((CoeffCompatible.associator_inv _ _ _).comp
      ((CoeffCompatible.whiskerRight _ (coeffCompatible_openImmersionLowerShriekLowerStarExchange
        ρ e.isPullback_restrict n₁ n₃ h₁ h₃)).comp
      ((CoeffCompatible.associator_hom _ _ _).comp
      (CoeffCompatible.whiskerLeft _
        (coeffCompatible_rightDerivedLowerStarComp ρ e.g d.g n₃ n₂ n₄ h₃ h₂ h₄)))))).comp
    ((CoeffCompatible.associator_inv _ _ _).comp
    (CoeffCompatible.whiskerRight _
      (coeffCompatible_mapDerivedCategoryOpenImmersionLowerShriekComp_symm_trans_congr ρ _ _
        e.restrict_i_fst))))

/-- The isomorphism `Rf_!(e.restrict) ⋙ Rg_!(d) ≅ R(f ≫ g)_!(d.comp e)`
(`AlgebraicGeometry.Etale.rightDerivedLowerShriekOfCompactificationCompIso`) is compatible
with the coefficient comparisons
`AlgebraicGeometry.Etale.compactificationRestrictScalarsIso`, over quasi-compact bases. -/
lemma coeffCompatible_rightDerivedLowerShriekOfCompactificationCompIso [CompactSpace Y]
    [CompactSpace S] (d : Compactification g) (e : Compactification (f ≫ d.i)) :
    CoeffCompatible
      (pasteTwoSquaresIso (compactificationRestrictScalarsIso ρ e.restrict)
        (compactificationRestrictScalarsIso ρ d))
      (compactificationRestrictScalarsIso ρ (d.comp e))
      (rightDerivedLowerShriekOfCompactificationCompIso Λ d e).hom
      (rightDerivedLowerShriekOfCompactificationCompIso Λ' d e).hom := by
  have : CompactSpace d.Z := QuasiCompact.compactSpace_of_compactSpace d.g
  obtain ⟨n₃, h₃⟩ :=
    exists_isZero_rightDerived_lowerStar_of_isProper_of_compactSpace Λ isAddTorsion_of_finite e.g
  exact coeffCompatible_rightDerivedLowerShriekOfCompactificationCompIso_hom ρ d e _ _ n₃ _ _ _ h₃ _

end CompactificationComp

/-- **The composition law for `Rf_!` is compatible with the coefficient comparisons**: for a
morphism of finite coefficient rings `ρ : Λ →+* Λ'` and `f ≫ g = h` with `h` quasi-compact and
`Y`, `S` quasi-compact, the composition isomorphisms `R(h)_! ≅ Rf_! ⋙ Rg_!` over `Λ` and over
`Λ'` are related by the coefficient comparisons
`AlgebraicGeometry.Etale.derivedRestrictScalarsCompRightDerivedLowerShriekIso` of `Rh_!` and of
`Rf_! ⋙ Rg_!`. -/
theorem coeffCompatible_rightDerivedLowerShriekCompIsoOfEq {X Y S : Scheme.{u}} (f : X ⟶ Y)
    (g : Y ⟶ S) (h : X ⟶ S) (w : f ≫ g = h) [HasCompactification f] [HasCompactification g]
    [HasCompactification h] [QuasiCompact h] [CompactSpace Y] [CompactSpace S] :
    CoeffCompatible (derivedRestrictScalarsCompRightDerivedLowerShriekIso ρ h)
      (pasteTwoSquaresIso (derivedRestrictScalarsCompRightDerivedLowerShriekIso ρ f)
        (derivedRestrictScalarsCompRightDerivedLowerShriekIso ρ g))
      (rightDerivedLowerShriekCompIsoOfEq Λ f g h w).hom
      (rightDerivedLowerShriekCompIsoOfEq Λ' f g h w).hom := by
  subst w
  have : QuasiCompact f := .of_comp f g
  have h₀ : CoeffCompatible (derivedRestrictScalarsCompRightDerivedLowerShriekIso ρ (f ≫ g))
      (derivedRestrictScalarsCompRightDerivedLowerShriekIso ρ (f ≫ g))
      (eqToIso (rfl : R(f ≫ g)_![ModuleCat.{u + 1} Λ] = _)).hom
      (eqToIso (rfl : R(f ≫ g)_![ModuleCat.{u + 1} Λ'] = _)).hom := fun K ↦ by simp
  have h₁ := (coeffCompatible_rightDerivedLowerShriekOfCompactificationIso ρ
    ((HasCompactification.compactification g).comp
      ((HasCompactification.compactification (f ≫ g)).ofComp
        (HasCompactification.compactification g)))
    (HasCompactification.compactification (f ≫ g))).inv
  have h₂ := (coeffCompatible_rightDerivedLowerShriekOfCompactificationCompIso ρ
    (HasCompactification.compactification g)
    ((HasCompactification.compactification (f ≫ g)).ofComp
      (HasCompactification.compactification g))).inv
  have h₃ := CoeffCompatible.whiskerRight
    (compactificationRestrictScalarsIso ρ (HasCompactification.compactification g))
    (coeffCompatible_rightDerivedLowerShriekOfCompactificationIso ρ
      ((HasCompactification.compactification (f ≫ g)).ofComp
        (HasCompactification.compactification g)).restrict
      (HasCompactification.compactification f))
  exact h₀.comp (h₁.comp (h₂.comp h₃))

end AlgebraicGeometry.Etale
