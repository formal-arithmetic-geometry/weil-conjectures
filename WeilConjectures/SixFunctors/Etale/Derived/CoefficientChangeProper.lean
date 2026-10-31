/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.CoefficientChangeExchange
public import WeilConjectures.SixFunctors.Etale.Derived.Identity
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekToLowerStar

/-!
# Coefficient comparisons for proper morphisms and the identity

Let `ρ : Λ →+* Λ'` be a morphism of commutative rings, `Λ` finite. We show that the
identifications `Rf_! ≅ Rf_*` for a proper `f` over a quasi-compact base and `R(𝟙 X)_! ≅ 𝟭` are
compatible (`AlgebraicGeometry.Etale.CoeffCompatible`) with the coefficient comparisons
`Res ⋙ Rf_! ≅ Rf_! ⋙ Res` and `Res ⋙ Rf_* ≅ Rf_* ⋙ Res` along restriction of scalars.

The ingredients are compatibilities of the building blocks of these identifications:

- the derived comparison `D(j_!) ⟶ Rj_*` of an open immersion `j`, the transpose under
  `D(j^*) ⊣ Rj_*` of the inverse of the unit of `D(j_!) ⊣ D(j^*)`
  (`AlgebraicGeometry.Etale.coeffCompatible_derivedOpenImmersionLowerShriekToLowerStar`, from the
  abstract `AlgebraicGeometry.Etale.CoeffCompatible.whiskerLeft_unit_comp_inv_unit`);
- the composition isomorphism `Rg₁_* ⋙ Rg₂_* ≅ R(g₁ ≫ g₂)_*`, a conjugate of the composition
  isomorphism of pullbacks (`AlgebraicGeometry.Etale.coeffCompatible_rightDerivedLowerStarComp`);
- the isomorphism `R(𝟙 X)_* ≅ 𝟭`, the conjugate of `D((𝟙 X)^*) ≅ 𝟭`
  (`AlgebraicGeometry.Etale.conjugateIsoEquiv_mapDerivedUpperStarLowerStarAdjunction_id`), with
  the abstract stability of compatibility under conjugation
  (`AlgebraicGeometry.Etale.CoeffCompatible.conjugateEquiv`).

In each case the coefficient comparison of the derived direct image is the mate of that of the
pullback
(`AlgebraicGeometry.Etale.mateEquiv_mapDerivedUpperStarLowerStarAdjunction_restrictScalars`),
which reduces the statements to compatibilities of pullbacks and extensions by zero.

## Main statements

- `AlgebraicGeometry.Etale.coeffCompatible_rightDerivedLowerShriekIsoRightDerivedLowerStar`
- `AlgebraicGeometry.Etale.coeffCompatible_rightDerivedLowerShriekIdIso`
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

open Scheme

section Abstract

variable {A A' B B' : Type*} [Category A] [Category A'] [Category B] [Category B']
  {rA : A' ⥤ A} {rB : B' ⥤ B}

/-- If the comparison `σ` of right adjoints is the mate of the comparison `τ` of left adjoints,
then the restriction of the unit of the primed adjunction is computed by the unit of the
unprimed one. -/
lemma _root_.CategoryTheory.Adjunction.map_unit_app_of_mateEquiv {G : A ⥤ B} {R : B ⥤ A}
    {G' : A' ⥤ B'} {R' : B' ⥤ A'}
    (b : G ⊣ R) (b' : G' ⊣ R') (τ : rA ⋙ G ≅ G' ⋙ rB) (σ : rB ⋙ R ≅ R' ⋙ rA)
    (h : mateEquiv b' b τ.hom = σ.inv) (c : A') :
    rA.map (b'.unit.app c) =
      b.unit.app (rA.obj c) ≫ R.map (τ.hom.app c) ≫ σ.hom.app (G'.obj c) := by
  have := unit_mateEquiv b' b τ.hom c
  rw [h] at this
  simp only [Functor.comp_obj, Functor.id_obj] at this
  rw [← reassoc_of% this]
  simp

/-- Let `L ⊣ G ⊣ R` and `L' ⊣ G' ⊣ R'` be adjoint triples whose first units are isomorphisms,
related by restriction functors through comparisons `ιL`, `τG`, `σR`, where `σR` is the mate of
`τG` and the comparisons are compatible with the units of `L ⊣ G` and `L' ⊣ G'`. Then the
comparison maps `L ⟶ R` and `L' ⟶ R'`, transposes of the inverses of the units, are compatible
with the comparisons `ιL` and `σR`. -/
lemma CoeffCompatible.whiskerLeft_unit_comp_inv_unit {L : B ⥤ A} {G : A ⥤ B} {R : B ⥤ A}
    {L' : B' ⥤ A'} {G' : A' ⥤ B'} {R' : B' ⥤ A'} (a : L ⊣ G) (b : G ⊣ R) (a' : L' ⊣ G')
    (b' : G' ⊣ R') [IsIso a.unit] [IsIso a'.unit] (ιL : rB ⋙ L ≅ L' ⋙ rA)
    (τG : rA ⋙ G ≅ G' ⋙ rB) (σR : rB ⋙ R ≅ R' ⋙ rA) (hb : mateEquiv b' b τG.hom = σR.inv)
    (ha : ∀ K, a.unit.app (rB.obj K) ≫ G.map (ιL.hom.app K) ≫ τG.hom.app (L'.obj K) =
      rB.map (a'.unit.app K)) :
    CoeffCompatible ιL σR
      (Functor.whiskerLeft L b.unit ≫ (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight (CategoryTheory.inv a.unit) R)
      (Functor.whiskerLeft L' b'.unit ≫ (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight (CategoryTheory.inv a'.unit) R') := by
  intro K
  have hi : G.map (ιL.hom.app K) ≫ τG.hom.app (L'.obj K) ≫
      rB.map (CategoryTheory.inv (a'.unit.app K)) = CategoryTheory.inv (a.unit.app (rB.obj K)) := by
    rw [← cancel_epi (a.unit.app (rB.obj K)), IsIso.hom_inv_id, reassoc_of% (ha K),
      ← Functor.map_comp, IsIso.hom_inv_id, rB.map_id]
    rfl
  have hn₁ := b.unit.naturality (ιL.hom.app K)
  have hn₂ := σR.hom.naturality (CategoryTheory.inv (a'.unit.app K))
  simp only [Functor.comp_obj, Functor.comp_map, Functor.id_obj, Functor.id_map] at hn₁ hn₂
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_inv_app, Category.id_comp, NatIso.isIso_inv_app, Functor.map_comp,
    Category.assoc, Adjunction.map_unit_app_of_mateEquiv b b' τG σR hb]
  rw [reassoc_of% hn₁, ← hn₂, ← hi]
  simp only [Functor.map_comp, Category.assoc]

end Abstract

variable {Λ Λ' : Type (u + 1)} [CommRing Λ] [CommRing Λ'] (ρ : Λ →+* Λ')

/-- The coefficient comparison of the derived direct image does not depend on the chosen bound
for the higher direct images. -/
lemma derivedRestrictScalarsCompRightDerivedLowerStarIso_congr {X Y : Scheme.{u}} (f : X ⟶ Y)
    (d₁ d₂ : ℕ)
    (hd₁ : ∀ (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℕ), d₁ < q →
      IsZero ((((f)_*[ModuleCat.{u + 1} Λ]).rightDerived q).obj F))
    (hd₂ : ∀ (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℕ), d₂ < q →
      IsZero ((((f)_*[ModuleCat.{u + 1} Λ]).rightDerived q).obj F)) :
    derivedRestrictScalarsCompRightDerivedLowerStarIso ρ f d₁ hd₁ =
      derivedRestrictScalarsCompRightDerivedLowerStarIso ρ f d₂ hd₂ :=
  rfl

/-- The isomorphism `D(F₁) ⋙ D(F₂) ≅ D(G₁) ⋙ D(G₂)` induced by the inverse of a square is the
inverse of the induced isomorphism. -/
lemma _root_.CategoryTheory.Functor.mapDerivedCategorySquareIso_symm_hom {C₁ C₂ D₁ D₂ : Type*}
    [Category C₁] [Category C₂]
    [Category D₁] [Category D₂] [Abelian C₁] [Abelian C₂] [Abelian D₁] [Abelian D₂]
    [HasDerivedCategory C₁] [HasDerivedCategory C₂] [HasDerivedCategory D₁]
    [HasDerivedCategory D₂] {F₁ : C₁ ⥤ C₂} {F₂ : C₂ ⥤ D₂} {G₁ : C₁ ⥤ D₁} {G₂ : D₁ ⥤ D₂}
    [F₁.Additive] [PreservesFiniteLimits F₁] [PreservesFiniteColimits F₁]
    [F₂.Additive] [PreservesFiniteLimits F₂] [PreservesFiniteColimits F₂]
    [G₁.Additive] [PreservesFiniteLimits G₁] [PreservesFiniteColimits G₁]
    [G₂.Additive] [PreservesFiniteLimits G₂] [PreservesFiniteColimits G₂]
    (e : F₁ ⋙ F₂ ≅ G₁ ⋙ G₂) :
    (Functor.mapDerivedCategorySquareIso e.symm).hom =
      (Functor.mapDerivedCategorySquareIso e).inv := by
  simp only [Functor.mapDerivedCategorySquareIso, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom,
    Iso.symm_inv, Functor.mapDerivedCategoryNatIso_symm, Category.assoc]

section OpenImmersion

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- The coefficient comparisons of `D(j_!)` and `D(j^*)` are compatible with the units of the
derived adjunctions `D(j_!) ⊣ D(j^*)` over `Λ` and over `Λ'`. -/
lemma derivedOpenImmersionLowerShriekUpperStarAdjunction_unit_app_restrictScalars
    (K : DerivedCategory (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ'))) :
    (derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) j).unit.app
        ((Sheaf.derivedRestrictScalars U.smallEtaleTopology ρ).obj K) ≫
      D((j)^*[ModuleCat.{u + 1} Λ]).map
        ((derivedRestrictScalarsCompOpenImmersionLowerShriekIso ρ j).hom.app K) ≫
      (Functor.mapDerivedCategorySquareIso (upperStarRestrictScalarsIso ρ j)).hom.app
        (D((j)_!open[ModuleCat.{u + 1} Λ']).obj K) =
    (Sheaf.derivedRestrictScalars U.smallEtaleTopology ρ).map
      ((derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ') j).unit.app
        K) := by
  have h := Adjunction.mapDerivedCategoryAdjunction_mate
    (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ') j)
    (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) j)
    (upperStarRestrictScalarsIso ρ j).symm (openImmersionLowerShriekRestrictScalarsIso ρ j)
    (fun G ↦ by
      rw [Iso.symm_hom, ← openImmersionLowerShriekUpperStarAdjunction_unit_app_comp_upperStarMap,
        Category.assoc, Category.assoc, Iso.hom_inv_id_app]
      exact (Category.comp_id _).symm) K
  rw [Functor.mapDerivedCategorySquareIso_symm_hom] at h
  rw [← Category.assoc]
  erw [h]
  rw [Category.assoc, Iso.inv_hom_id_app]
  exact Category.comp_id _

/-- **The comparison `D(j_!) ⟶ Rj_*` is compatible with restriction of scalars** along an open
immersion `j`, through the coefficient comparisons of `D(j_!)` and `Rj_*`. -/
lemma coeffCompatible_derivedOpenImmersionLowerShriekToLowerStar (d : ℕ)
    (hd : ∀ (F : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℕ), d < q →
      IsZero ((((j)_*[ModuleCat.{u + 1} Λ]).rightDerived q).obj F)) :
    CoeffCompatible (derivedRestrictScalarsCompOpenImmersionLowerShriekIso ρ j)
      (derivedRestrictScalarsCompRightDerivedLowerStarIso ρ j d hd)
      (derivedOpenImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} Λ) j)
      (derivedOpenImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} Λ') j) :=
  CoeffCompatible.whiskerLeft_unit_comp_inv_unit
    (derivedOpenImmersionLowerShriekUpperStarAdjunction _ j)
    (mapDerivedUpperStarLowerStarAdjunction _ j)
    (derivedOpenImmersionLowerShriekUpperStarAdjunction _ j)
    (mapDerivedUpperStarLowerStarAdjunction _ j) _
    (Functor.mapDerivedCategorySquareIso (upperStarRestrictScalarsIso ρ j)) _
    (mateEquiv_mapDerivedUpperStarLowerStarAdjunction_restrictScalars ρ j d hd)
    (derivedOpenImmersionLowerShriekUpperStarAdjunction_unit_app_restrictScalars ρ j)

end OpenImmersion

/-- The composition isomorphism of derived direct images is the conjugate of the composition
isomorphism of the pullbacks. -/
lemma rightDerivedLowerStarComp_hom_eq {T S V : Scheme.{u}} (A : Type*) [Category.{u + 1} A]
    [Abelian A] [IsGrothendieckAbelian.{u + 1} A] (g₁ : T ⟶ S) (g₂ : S ⟶ V) :
    (rightDerivedLowerStarComp A g₁ g₂).hom =
      conjugateEquiv ((mapDerivedUpperStarLowerStarAdjunction A g₂).comp
          (mapDerivedUpperStarLowerStarAdjunction A g₁))
        (mapDerivedUpperStarLowerStarAdjunction A (g₁ ≫ g₂))
        (Functor.mapDerivedCategoryTriangleIso (upperStarComp A g₁ g₂ (g₁ ≫ g₂) rfl)).hom :=
  rfl

/-- The composition isomorphism `Rg₁_* ⋙ Rg₂_* ≅ R(g₁ ≫ g₂)_*` is compatible with the coefficient
comparisons of the derived direct images. -/
lemma coeffCompatible_rightDerivedLowerStarComp {T S V : Scheme.{u}} (g₁ : T ⟶ S) (g₂ : S ⟶ V)
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
      (rightDerivedLowerStarComp (ModuleCat.{u + 1} Λ') g₁ g₂).hom := by
  intro M
  rw [pasteTwoSquaresIso_hom_app, Category.assoc, rightDerivedLowerStarComp_hom_eq,
    rightDerivedLowerStarComp_hom_eq]
  exact Adjunction.conjugateEquiv_comp_restrict
    (mapDerivedUpperStarLowerStarAdjunction _ g₁) (mapDerivedUpperStarLowerStarAdjunction _ g₂)
    (mapDerivedUpperStarLowerStarAdjunction _ (g₁ ≫ g₂))
    (mapDerivedUpperStarLowerStarAdjunction _ g₁) (mapDerivedUpperStarLowerStarAdjunction _ g₂)
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

/-- The isomorphism `Rg₁_* ≅ Rg₂_*` induced by an equality `g₁ = g₂` is compatible with the
coefficient comparisons of the derived direct images. -/
lemma coeffCompatible_rightDerivedLowerStarCongr {X Y : Scheme.{u}} {g₁ g₂ : X ⟶ Y}
    (h : g₁ = g₂) (d₁ d₂ : ℕ)
    (hd₁ : ∀ (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℕ), d₁ < q →
      IsZero ((((g₁)_*[ModuleCat.{u + 1} Λ]).rightDerived q).obj F))
    (hd₂ : ∀ (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℕ), d₂ < q →
      IsZero ((((g₂)_*[ModuleCat.{u + 1} Λ]).rightDerived q).obj F)) :
    CoeffCompatible (derivedRestrictScalarsCompRightDerivedLowerStarIso ρ g₁ d₁ hd₁)
      (derivedRestrictScalarsCompRightDerivedLowerStarIso ρ g₂ d₂ hd₂)
      (rightDerivedLowerStarCongr (ModuleCat.{u + 1} Λ) h).hom
      (rightDerivedLowerStarCongr (ModuleCat.{u + 1} Λ') h).hom := by
  subst h
  intro K
  rw [derivedRestrictScalarsCompRightDerivedLowerStarIso_congr ρ g₁ d₁ d₂ hd₁ hd₂]
  simp

section Conjugate

variable {A A' B B' : Type*} [Category A] [Category A'] [Category B] [Category B']
  {rA : A' ⥤ A} {rB : B' ⥤ B}

/-- **Conjugates and coefficient comparisons.** Let `L₁ ⊣ R₁`, `L₂ ⊣ R₂` and their primed
versions be related by restriction functors through comparisons `τ` of the left adjoints and
`σ` of the right adjoints, each `σ` being the mate of the corresponding `τ`. If `α : L₂ ⟶ L₁`
and `α' : L₂' ⟶ L₁'` are compatible with the comparisons of the left adjoints, then their
conjugates `R₁ ⟶ R₂` and `R₁' ⟶ R₂'` are compatible with the comparisons of the right
adjoints. -/
lemma CoeffCompatible.conjugateEquiv {L₁ L₂ : B ⥤ A} {R₁ R₂ : A ⥤ B} {L₁' L₂' : B' ⥤ A'}
    {R₁' R₂' : A' ⥤ B'} (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) (a₁' : L₁' ⊣ R₁') (a₂' : L₂' ⊣ R₂')
    (τ₁ : rB ⋙ L₁ ≅ L₁' ⋙ rA) (σ₁ : rA ⋙ R₁ ≅ R₁' ⋙ rB) (τ₂ : rB ⋙ L₂ ≅ L₂' ⋙ rA)
    (σ₂ : rA ⋙ R₂ ≅ R₂' ⋙ rB) (h₁ : mateEquiv a₁' a₁ τ₁.hom = σ₁.inv)
    (h₂ : mateEquiv a₂' a₂ τ₂.hom = σ₂.inv) {α : L₂ ⟶ L₁} {α' : L₂' ⟶ L₁'}
    (h : CoeffCompatible τ₂ τ₁ α α') :
    CoeffCompatible σ₁ σ₂ (CategoryTheory.conjugateEquiv a₁ a₂ α)
      (CategoryTheory.conjugateEquiv a₁' a₂' α') := by
  intro X
  rw [← cancel_mono (σ₂.inv.app X)]
  simp only [Category.assoc, Iso.hom_inv_id_app, Functor.comp_obj, Category.comp_id]
  apply (a₂.homEquiv _ _).symm.injective
  have k₂ : L₂.map (σ₂.inv.app X) ≫ a₂.counit.app (rA.obj X) =
      τ₂.hom.app (R₂'.obj X) ≫ rA.map (a₂'.counit.app X) := by
    rw [← Adjunction.map_hom_app_comp_counit_of_mateEquiv a₂ a₂' τ₂ σ₂ h₂ X,
      ← L₂.map_comp_assoc, Iso.inv_hom_id_app]
    erw [L₂.map_id, Category.id_comp]
  have k₁ := Adjunction.map_hom_app_comp_counit_of_mateEquiv a₁ a₁' τ₁ σ₁ h₁ X
  have c := conjugateEquiv_counit a₁ a₂ α (rA.obj X)
  have c' := conjugateEquiv_counit a₁' a₂' α' X
  have n₁ := τ₂.hom.naturality ((CategoryTheory.conjugateEquiv a₁' a₂' α').app X)
  have n₂ := α.naturality (σ₁.hom.app X)
  have e := h (R₁'.obj X)
  simp only [Functor.comp_obj, Functor.comp_map] at n₁ n₂ e
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc, k₂]
  rw [reassoc_of% n₁, ← rA.map_comp, c', rA.map_comp, reassoc_of% e, reassoc_of% n₂, k₁, c]

/-- The unitors `r ⋙ 𝟭 ≅ 𝟭 ⋙ r` are mates for the identity adjunctions. -/
lemma _root_.CategoryTheory.mateEquiv_id_rightUnitor_trans_leftUnitor_symm (r : A' ⥤ A) :
    mateEquiv (Adjunction.id (C := A')) (Adjunction.id (C := A))
        (Functor.rightUnitor r ≪≫ (Functor.leftUnitor r).symm).hom =
      (Functor.rightUnitor r ≪≫ (Functor.leftUnitor r).symm).inv := by
  ext K
  simp [mateEquiv_apply]

end Conjugate

/-- The identifications `D(𝟭) ≅ 𝟭` of the functor induced by the identity on derived categories
are compatible with the functors induced by an exact functor `r`. -/
lemma CoeffCompatible.mapDerivedCategoryIdIso {C C' : Type*} [Category C] [Category C']
    [Abelian C] [Abelian C'] [HasDerivedCategory C] [HasDerivedCategory C'] (r : C' ⥤ C)
    [r.Additive] [PreservesFiniteLimits r] [PreservesFiniteColimits r] :
    CoeffCompatible
      (Functor.mapDerivedCategorySquareIso (Functor.rightUnitor r ≪≫ (Functor.leftUnitor r).symm))
      (Functor.rightUnitor _ ≪≫ (Functor.leftUnitor _).symm)
      (Functor.mapDerivedCategoryIdIso C).hom (Functor.mapDerivedCategoryIdIso C').hom := by
  intro K
  have hr : Functor.rightUnitor r ≪≫ (Functor.leftUnitor r).symm = Iso.refl (r ⋙ 𝟭 C) := by
    ext
    simp
  have h₁ := congr_app (Functor.mapDerivedCategoryCompIso_comp_id r) K
  have h₂ := congr_app (Functor.mapDerivedCategoryCompIso_id_comp r) K
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    NatTrans.id_app] at h₁ h₂
  rw [hr]
  simp only [Functor.mapDerivedCategorySquareIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.mapDerivedCategoryNatIso_refl, NatTrans.id_app, Category.assoc]
  erw [Category.id_comp, h₂]
  rw [← cancel_epi ((Functor.mapDerivedCategoryCompIso r (𝟭 C)).hom.app K),
    Iso.hom_inv_id_app_assoc]
  erw [reassoc_of% h₁]
  simp

/-- The identification `D((𝟙 X)^*) ≅ 𝟭` is compatible with the coefficient comparisons. -/
lemma coeffCompatible_mapDerivedCategoryUpperStarIdIso (X : Scheme.{u}) :
    CoeffCompatible (Functor.mapDerivedCategorySquareIso (upperStarRestrictScalarsIso ρ (𝟙 X)))
      (Functor.rightUnitor _ ≪≫ (Functor.leftUnitor _).symm)
      (Functor.mapDerivedCategoryNatIso (upperStarId (ModuleCat.{u + 1} Λ) X) ≪≫
        Functor.mapDerivedCategoryIdIso _).hom
      (Functor.mapDerivedCategoryNatIso (upperStarId (ModuleCat.{u + 1} Λ') X) ≪≫
        Functor.mapDerivedCategoryIdIso _).hom := by
  have hs : CoeffCompatible (upperStarRestrictScalarsIso ρ (𝟙 X))
      (Functor.rightUnitor _ ≪≫ (Functor.leftUnitor _).symm)
      (upperStarId (ModuleCat.{u + 1} Λ) X).hom (upperStarId (ModuleCat.{u + 1} Λ') X).hom := by
    intro G
    simpa using congr_app (upperStarRestrictScalarsIso_id_hom ρ X) G
  exact (CoeffCompatible.mapDerivedCategoryNatIso hs).comp
    (CoeffCompatible.mapDerivedCategoryIdIso (Sheaf.restrictScalars X.smallEtaleTopology ρ))

section IdentityConjugate

universe vC vD wC wD

attribute [local irreducible] Adjunction.mapDerivedCategoryAdjunction

/-- The levelwise derived adjunction of the identity adjunction is the identity adjunction,
transported along `D(𝟭) ≅ 𝟭`. -/
lemma _root_.CategoryTheory.Adjunction.mapDerivedCategoryAdjunction_id {C : Type*}
    [Category.{vC} C] [Abelian C]
    [IsGrothendieckAbelian.{vC} C] [HasDerivedCategory.{wC} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [SymmetricCategory C] [MonoidalClosed C]
    [Abelian.HasFunctorialFlatResolution C] :
    (Adjunction.id (C := C)).mapDerivedCategoryAdjunction =
      ((Adjunction.id (C := DerivedCategory C)).ofNatIsoLeft
        (Functor.mapDerivedCategoryIdIso C).symm).ofNatIsoRight
        (Functor.mapDerivedCategoryIdIso C).symm := by
  apply Adjunction.ext
  refine Localization.natTrans_ext DerivedCategory.Qh (HomotopyCategory.quasiIso C (.up ℤ))
    fun K ↦ ?_
  simp only [Adjunction.ofNatIsoRight_unit, Adjunction.ofNatIsoLeft_unit,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Iso.symm_hom]
  simp only [Adjunction.id_unit, NatTrans.id_app, Functor.id_map, Category.id_comp]
  rw [← cancel_mono ((𝟭 C).mapDerivedCategory.map
    ((𝟭 C).mapDerivedCategoryFactorsh.hom.app K) ≫
      (𝟭 C).mapDerivedCategoryFactorsh.hom.app
        (((𝟭 C).mapHomotopyCategory (.up ℤ)).obj K))]
  simp only [Category.assoc]
  erw [(Adjunction.id (C := C)).mapDerivedCategoryAdjunction_unit_app_fac K]
  have hn := (Functor.mapDerivedCategoryIdIso C).inv.naturality
    ((𝟭 C).mapDerivedCategoryFactorsh.hom.app K)
  dsimp only [Functor.id_map] at hn
  rw [← reassoc_of% hn, ← Functor.mapDerivedCategoryIdIso_hom_app_Qh_obj,
    Iso.inv_hom_id_app_assoc, ← Functor.mapDerivedCategoryIdIso_hom_app_Qh_obj,
    Iso.inv_hom_id_app, Adjunction.mapHomotopyCategory_id_unit_app]
  have hi (K' : HomotopyCategory C (.up ℤ)) :
      (Functor.mapHomotopyCategoryIdIso C (.up ℤ)).inv.app K' = 𝟙 K' := by
    apply (cancel_mono ((Functor.mapHomotopyCategoryIdIso C (.up ℤ)).hom.app K')).mp
    erw [Iso.inv_hom_id_app, Functor.mapHomotopyCategoryIdIso_hom_app_eq_id, Category.id_comp]
    rfl
  erw [hi]
  repeat erw [CategoryTheory.Functor.map_id, Category.comp_id]
  exact DerivedCategory.Qh.map_id K

/-- For an adjunction `a` of exact functors, the transformations induced on derived categories
by isomorphisms `e : L₁ ≅ L₂` and `r : R₂ ≅ R₁` compatible with the units of `a` and `b` are
compatible with the units of the levelwise derived adjunctions. -/
lemma _root_.CategoryTheory.Adjunction.mapDerivedCategoryAdjunction_unit_comp_whiskerRight
    {C : Type*} {D : Type*} [Category.{vC} C] [Category.{vD} D] [Abelian C] [Abelian D]
    [IsGrothendieckAbelian.{vC} C] [IsGrothendieckAbelian.{vD} D]
    [HasDerivedCategory.{wC} C] [HasDerivedCategory.{wD} D]
    [MonoidalCategory C] [MonoidalPreadditive C] [SymmetricCategory C] [MonoidalClosed C]
    [MonoidalCategory D] [MonoidalPreadditive D] [SymmetricCategory D] [MonoidalClosed D]
    [Abelian.HasFunctorialFlatResolution C] [Abelian.HasFunctorialFlatResolution D]
    {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C}
    [L₁.Additive] [R₁.Additive] [L₂.Additive] [R₂.Additive]
    [PreservesFiniteLimits L₁] [PreservesFiniteColimits L₁]
    [PreservesFiniteLimits R₁] [PreservesFiniteColimits R₁]
    [PreservesFiniteLimits L₂] [PreservesFiniteColimits L₂]
    [PreservesFiniteLimits R₂] [PreservesFiniteColimits R₂]
    (a : L₁ ⊣ R₁) (b : L₂ ⊣ R₂) (e : L₁ ≅ L₂) (r : R₂ ≅ R₁)
    (h : ∀ K, a.unit.app K ≫ R₁.map (e.hom.app K) = b.unit.app K ≫ r.hom.app (L₂.obj K)) :
    a.mapDerivedCategoryAdjunction.unit ≫
        Functor.whiskerRight (Functor.mapDerivedCategoryNatIso e).hom R₁.mapDerivedCategory =
      b.mapDerivedCategoryAdjunction.unit ≫
        Functor.whiskerLeft L₂.mapDerivedCategory (Functor.mapDerivedCategoryNatIso r).hom := by
  refine Localization.natTrans_ext DerivedCategory.Qh (HomotopyCategory.quasiIso C (.up ℤ))
    fun K ↦ ?_
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app]
  rw [← cancel_mono (R₁.mapDerivedCategory.map (L₂.mapDerivedCategoryFactorsh.hom.app K) ≫
    R₁.mapDerivedCategoryFactorsh.hom.app ((L₂.mapHomotopyCategory (.up ℤ)).obj K))]
  simp only [Category.assoc]
  have he := Functor.mapDerivedCategoryNatIso_fach e K
  slice_lhs 2 3 =>
    rw [← Functor.map_comp, he, Functor.map_comp]
  have hNR := R₁.mapDerivedCategoryFactorsh.hom.naturality
    ((NatTrans.mapHomotopyCategory e.hom (.up ℤ)).app K)
  simp only [Functor.comp_map] at hNR
  simp only [Category.assoc]
  erw [hNR]
  erw [reassoc_of% (a.mapDerivedCategoryAdjunction_unit_app_fac K)]
  have hN := (Functor.mapDerivedCategoryNatIso r).hom.naturality
    (L₂.mapDerivedCategoryFactorsh.hom.app K)
  erw [← reassoc_of% hN]
  erw [Functor.mapDerivedCategoryNatIso_fach r]
  erw [reassoc_of% (b.mapDerivedCategoryAdjunction_unit_app_fac K)]
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 1
  exact Adjunction.mapHomotopyCategory_unit_app_comp (.up ℤ) a b e.hom r.hom h K

/-- For an adjunction `a : L ⊣ R` of exact functors, the levelwise derived adjunction
`D(L) ⊣ D(R)` is the derived adjunction `D(L) ⊣ RR` transported along `RR ≅ D(R)`. -/
lemma _root_.CategoryTheory.Adjunction.mapDerivedCategoryAdjunction_eq_ofNatIsoRight
    {C : Type*} {D : Type*} [Category.{vC} C] [Category.{vD} D] [Abelian C] [Abelian D]
    [IsGrothendieckAbelian.{vC} C] [IsGrothendieckAbelian.{vD} D]
    [HasDerivedCategory.{wC} C] [HasDerivedCategory.{wD} D]
    [MonoidalCategory C] [MonoidalPreadditive C] [SymmetricCategory C] [MonoidalClosed C]
    [MonoidalCategory D] [MonoidalPreadditive D] [SymmetricCategory D] [MonoidalClosed D]
    [Abelian.HasFunctorialFlatResolution C] [Abelian.HasFunctorialFlatResolution D]
    {L : C ⥤ D} {R : D ⥤ C} [L.Additive] [R.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R] (a : L ⊣ R) :
    a.mapDerivedCategoryAdjunction =
      a.mapDerivedCategoryRightDerivedAdjunction.ofNatIsoRight
        R.rightDerivedFunctorIsoMapDerivedCategory := by
  apply Adjunction.ext
  refine Localization.natTrans_ext DerivedCategory.Qh (HomotopyCategory.quasiIso C (.up ℤ))
    fun K ↦ ?_
  simp only [Adjunction.ofNatIsoRight_unit, NatTrans.comp_app, Functor.whiskerLeft_app]
  rw [← cancel_mono (R.mapDerivedCategory.map
    (L.mapDerivedCategoryFactorsh.hom.app K) ≫
      R.mapDerivedCategoryFactorsh.hom.app ((L.mapHomotopyCategory (.up ℤ)).obj K))]
  simp only [Category.assoc]
  rw [a.mapDerivedCategoryAdjunction_unit_app_fac K]
  have hn := R.rightDerivedFunctorIsoMapDerivedCategory.hom.naturality
    (L.mapDerivedCategoryFactorsh.hom.app K)
  rw [← reassoc_of% hn]
  have hη := (a.mapHomotopyCategory (.up ℤ)).derivedη_fac_app
    (HomotopyCategory.quasiIso C (.up ℤ)) L.mapDerivedCategoryFactorsh.hom
    R.rightDerivedFunctorUnit K
  erw [reassoc_of% hη]
  have hR := NatTrans.congr_app R.rightDerivedFunctorIsoMapDerivedCategory_hom_fac
    ((L.mapHomotopyCategory (.up ℤ)).obj K)
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app] at hR
  rw [← Category.assoc _ _ (R.mapDerivedCategoryFactorsh.hom.app _), hR,
    Iso.inv_hom_id_app]
  exact (Category.comp_id _).symm

end IdentityConjugate

/-- A criterion for the conjugate, along the identity adjunction, of an isomorphism
`L ≅ I ≅ 𝟭` to be an isomorphism `R ≅ I ≅ 𝟭`, in terms of the unit of `L ⊣ R`. -/
lemma _root_.CategoryTheory.conjugateEquiv_id_eq_of_unit {C : Type*} [Category C]
    {L R I : C ⥤ C}
    (a : L ⊣ R) (δ : I ≅ 𝟭 C) (e : L ≅ I) (r : R ≅ I)
    (h : a.unit ≫ Functor.whiskerRight e.hom R =
      (((Adjunction.id (C := C)).ofNatIsoLeft δ.symm).ofNatIsoRight δ.symm).unit ≫
        Functor.whiskerLeft I r.inv) :
    conjugateEquiv Adjunction.id a (e ≪≫ δ).hom = (r ≪≫ δ).inv := by
  apply conjugateEquiv_eq_of_unit
  intro K
  have hK := NatTrans.congr_app h K
  simp only [Adjunction.ofNatIsoRight_unit, Adjunction.ofNatIsoLeft_unit,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Iso.symm_hom, Adjunction.id_unit, Functor.id_map, Category.id_comp] at hK
  simp only [Iso.trans_inv, Iso.trans_hom, NatTrans.comp_app,
    Adjunction.id_unit, NatTrans.id_app, Category.id_comp, Functor.map_comp]
  rw [← Category.assoc, hK]
  simp only [Category.assoc]
  rw [← r.inv.naturality (δ.hom.app K), ← reassoc_of% (δ.inv.naturality (δ.hom.app K))]
  simp only [← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]
  rfl

/-- If the conjugate of `e.hom : L ≅ 𝟭` along `a.ofNatIsoRight κ` and the identity adjunction is
`r.inv`, then the conjugate isomorphism of `e.symm` along `a` and the identity adjunction is
`κ ≪≫ r`. -/
lemma _root_.CategoryTheory.conjugateIsoEquiv_id_symm_eq {C : Type*} [Category C]
    {L R S : C ⥤ C}
    (a : L ⊣ R) (κ : R ≅ S) (e : L ≅ 𝟭 C) (r : S ≅ 𝟭 C)
    (h : conjugateEquiv Adjunction.id (a.ofNatIsoRight κ) e.hom = r.inv) :
    conjugateIsoEquiv a Adjunction.id e.symm = κ ≪≫ r := by
  apply Iso.ext
  apply conjugateEquiv_eq_of_unit
  intro K
  have hu := unit_conjugateEquiv Adjunction.id (a.ofNatIsoRight κ) e.hom K
  rw [h] at hu
  simp only [Adjunction.ofNatIsoRight_unit, NatTrans.comp_app,
    Functor.whiskerLeft_app, Adjunction.id_unit, NatTrans.id_app,
    Category.id_comp] at hu
  have ht := congrArg (fun t ↦ t ≫ S.map (e.inv.app K) ≫ r.hom.app (L.obj K)) hu
  simp only [Category.assoc] at ht
  rw [← S.map_comp_assoc, Iso.hom_inv_id_app, S.map_id, Category.id_comp,
    r.hom.naturality (e.inv.app K)] at ht
  simp only [Functor.id_obj, Functor.id_map, ← Category.assoc,
    Iso.inv_hom_id_app, Category.id_comp] at ht
  simpa only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Adjunction.id_unit, NatTrans.id_app, Functor.id_map, Functor.id_obj,
    Category.id_comp, Category.assoc] using ht.symm

section IdentityLowerStar

attribute [local irreducible] Adjunction.mapDerivedCategoryAdjunction

variable (Λ) in
/-- The identification `R(𝟙 X)_* ≅ D((𝟙 X)_*) ≅ D(𝟭) ≅ 𝟭` is the conjugate, under
`D((𝟙 X)^*) ⊣ R(𝟙 X)_*` and the identity adjunction, of `D((𝟙 X)^*) ≅ D(𝟭) ≅ 𝟭`. -/
lemma conjugateIsoEquiv_mapDerivedUpperStarLowerStarAdjunction_id (X : Scheme.{u}) :
    conjugateIsoEquiv (mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) (𝟙 X))
      Adjunction.id
      (Functor.mapDerivedCategoryNatIso (upperStarId (ModuleCat.{u + 1} Λ) X) ≪≫
        Functor.mapDerivedCategoryIdIso _).symm =
      ((𝟙 X)_*[ModuleCat.{u + 1} Λ]).rightDerivedFunctorIsoMapDerivedCategory ≪≫
        Functor.mapDerivedCategoryNatIso (lowerStarId (ModuleCat.{u + 1} Λ) X) ≪≫
          Functor.mapDerivedCategoryIdIso _ := by
  have hu (K : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
      (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) (𝟙 X)).unit.app K ≫
        ((𝟙 X)_*[ModuleCat.{u + 1} Λ]).map ((upperStarId (ModuleCat.{u + 1} Λ) X).hom.app K) =
      Adjunction.id.unit.app K ≫ (lowerStarId (ModuleCat.{u + 1} Λ) X).inv.app K := by
    simpa only [Adjunction.id_unit, NatTrans.id_app, Category.id_comp] using
      upperStarId_hom_app_unit_app (ModuleCat.{u + 1} Λ) X K
  have hd := Adjunction.mapDerivedCategoryAdjunction_unit_comp_whiskerRight
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) (𝟙 X)) Adjunction.id
    (upperStarId (ModuleCat.{u + 1} Λ) X) (lowerStarId (ModuleCat.{u + 1} Λ) X).symm hu
  rw [Adjunction.mapDerivedCategoryAdjunction_id] at hd
  have he := conjugateEquiv_id_eq_of_unit
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) (𝟙 X)).mapDerivedCategoryAdjunction
    (Functor.mapDerivedCategoryIdIso _)
    (Functor.mapDerivedCategoryNatIso (upperStarId (ModuleCat.{u + 1} Λ) X))
    (Functor.mapDerivedCategoryNatIso (lowerStarId (ModuleCat.{u + 1} Λ) X))
    (by simpa only [Functor.mapDerivedCategoryNatIso_symm] using hd)
  rw [Adjunction.mapDerivedCategoryAdjunction_eq_ofNatIsoRight
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) (𝟙 X))] at he
  exact conjugateIsoEquiv_id_symm_eq _ _ _ _ he

end IdentityLowerStar

variable (Λ) in
/-- The isomorphism `R(𝟙 X)_! ≅ 𝟭` is `R(𝟙 X)_! ≅ R(𝟙 X)_*` followed by the conjugate of
`D((𝟙 X)^*) ≅ 𝟭` under `D((𝟙 X)^*) ⊣ R(𝟙 X)_*` and the identity adjunction. -/
lemma rightDerivedLowerShriekIdIso_hom_eq (X : Scheme.{u}) :
    (rightDerivedLowerShriekIdIso (ModuleCat.{u + 1} Λ) X).hom =
      (rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} Λ) (𝟙 X)).hom ≫
        conjugateEquiv (mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) (𝟙 X))
          Adjunction.id
          (Functor.mapDerivedCategoryNatIso (upperStarId (ModuleCat.{u + 1} Λ) X) ≪≫
            Functor.mapDerivedCategoryIdIso _).inv := by
  have h := congrArg Iso.hom (conjugateIsoEquiv_mapDerivedUpperStarLowerStarAdjunction_id Λ X)
  rw [conjugateIsoEquiv_apply_hom, Iso.symm_hom] at h
  rw [rightDerivedLowerShriekIdIso, Iso.trans_hom, h]
  congr 1
  ext K
  simp only [Iso.trans_hom, NatTrans.comp_app]
  exact rightDerivedFunctorNatIso_hom_app_comp_isoMapDerivedCategory_hom_app_assoc _ _ _

variable [Finite Λ]


/-- **`Rf_! ≅ Rf_*` is compatible with restriction of scalars.** For a proper morphism
`f : X ⟶ Y` over a quasi-compact base and finite coefficients `Λ`, the identification
`Rf_! ≅ Rf_*` (`AlgebraicGeometry.Etale.rightDerivedLowerShriekIsoRightDerivedLowerStar`) over
`Λ` and over `Λ'` are related by the coefficient comparisons of `Rf_!` and `Rf_*`, for any bound
`d` on the higher direct images along `f`.

With `(i, g)` the chosen compactification, this is the compatibility of its three building
blocks: the comparison `D(i_!) ⟶ Ri_*` of the open immersion `i`
(`AlgebraicGeometry.Etale.coeffCompatible_derivedOpenImmersionLowerShriekToLowerStar`), whiskered
by `Rg_*`, the composition isomorphism `Ri_* ⋙ Rg_* ≅ R(i ≫ g)_*`
(`AlgebraicGeometry.Etale.coeffCompatible_rightDerivedLowerStarComp`) and `R(i ≫ g)_* ≅ Rf_*`
(`AlgebraicGeometry.Etale.coeffCompatible_rightDerivedLowerStarCongr`). -/
theorem coeffCompatible_rightDerivedLowerShriekIsoRightDerivedLowerStar {X Y : Scheme.{u}}
    (f : X ⟶ Y) [HasCompactification f] [IsProper f] [CompactSpace Y] (d : ℕ)
    (hd : ∀ (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℕ), d < q →
      IsZero ((((f)_*[ModuleCat.{u + 1} Λ]).rightDerived q).obj F)) :
    CoeffCompatible (derivedRestrictScalarsCompRightDerivedLowerShriekIso ρ f)
      (derivedRestrictScalarsCompRightDerivedLowerStarIso ρ f d hd)
      (rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} Λ) f).hom
      (rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} Λ') f).hom := by
  let c := HasCompactification.compactification f
  have := c.isProper
  have := c.isOpenImmersion
  have : CompactSpace c.Z := QuasiCompact.compactSpace_of_compactSpace c.g
  have hg := exists_isZero_rightDerived_lowerStar_of_isProper_of_compactSpace Λ
    isAddTorsion_of_finite c.g
  obtain ⟨di, hdi⟩ := exists_isZero_rightDerived_lowerStar_of_isProper_of_compactSpace Λ
    isAddTorsion_of_finite c.i
  obtain ⟨dc, hdc⟩ := exists_isZero_rightDerived_lowerStar_of_isProper_of_compactSpace Λ
    isAddTorsion_of_finite (c.i ≫ c.g)
  rw [rightDerivedLowerShriekIsoRightDerivedLowerStar_hom,
    rightDerivedLowerShriekIsoRightDerivedLowerStar_hom]
  exact (CoeffCompatible.whiskerRight
    (derivedRestrictScalarsCompRightDerivedLowerStarIso ρ c.g hg.choose hg.choose_spec)
    (coeffCompatible_derivedOpenImmersionLowerShriekToLowerStar ρ c.i di hdi)).comp
    ((coeffCompatible_rightDerivedLowerStarComp ρ c.i c.g di _ dc hdi hg.choose_spec hdc).comp
      (coeffCompatible_rightDerivedLowerStarCongr ρ c.comm.symm dc d hdc hd))

/-- **`R(𝟙 X)_! ≅ 𝟭` is compatible with restriction of scalars.** For a quasi-compact `X` and
finite coefficients `Λ`, the identifications `R(𝟙 X)_! ≅ 𝟭`
(`AlgebraicGeometry.Etale.rightDerivedLowerShriekIdIso`) over `Λ` and over `Λ'` are related by
the coefficient comparison of `R(𝟙 X)_!` and the unitors `Res ⋙ 𝟭 ≅ 𝟭 ⋙ Res`.

The isomorphism is `R(𝟙 X)_! ≅ R(𝟙 X)_*`, compatible by
`AlgebraicGeometry.Etale.coeffCompatible_rightDerivedLowerShriekIsoRightDerivedLowerStar`,
followed by `R(𝟙 X)_* ≅ 𝟭`, which is the conjugate of `D((𝟙 X)^*) ≅ 𝟭`
(`AlgebraicGeometry.Etale.rightDerivedLowerShriekIdIso_hom_eq`); the comparison of `R(𝟙 X)_*` is
the mate of that of `D((𝟙 X)^*)`, so the compatibility follows from that of `D((𝟙 X)^*) ≅ 𝟭`
(`AlgebraicGeometry.Etale.coeffCompatible_mapDerivedCategoryUpperStarIdIso`) by
`AlgebraicGeometry.Etale.CoeffCompatible.conjugateEquiv`. -/
theorem coeffCompatible_rightDerivedLowerShriekIdIso (X : Scheme.{u}) [CompactSpace X] :
    CoeffCompatible (derivedRestrictScalarsCompRightDerivedLowerShriekIso ρ (𝟙 X))
      (Functor.rightUnitor _ ≪≫ (Functor.leftUnitor _).symm)
      (rightDerivedLowerShriekIdIso (ModuleCat.{u + 1} Λ) X).hom
      (rightDerivedLowerShriekIdIso (ModuleCat.{u + 1} Λ') X).hom := by
  obtain ⟨d, hd⟩ := exists_isZero_rightDerived_lowerStar_of_isProper_of_compactSpace Λ
    isAddTorsion_of_finite (𝟙 X)
  rw [rightDerivedLowerShriekIdIso_hom_eq, rightDerivedLowerShriekIdIso_hom_eq]
  exact (coeffCompatible_rightDerivedLowerShriekIsoRightDerivedLowerStar ρ (𝟙 X) d hd).comp
    (CoeffCompatible.conjugateEquiv _ Adjunction.id _ Adjunction.id
      (Functor.mapDerivedCategorySquareIso (upperStarRestrictScalarsIso ρ (𝟙 X)))
      (derivedRestrictScalarsCompRightDerivedLowerStarIso ρ (𝟙 X) d hd) _ _
      (mateEquiv_mapDerivedUpperStarLowerStarAdjunction_restrictScalars ρ (𝟙 X) d hd)
      (mateEquiv_id_rightUnitor_trans_leftUnitor_symm _)
      (CoeffCompatible.inv (coeffCompatible_mapDerivedCategoryUpperStarIdIso ρ X)))

end AlgebraicGeometry.Etale
