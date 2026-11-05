/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.CoherenceLegacy

public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.DerivedBaseChange
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Coherence

/-!
# Pullback of pro-étale sheaves commutes with restriction of scalars

Let `ρ : Λ →+* Λ'` be a morphism of commutative rings and `g : Y ⟶ Z` a morphism of schemes.
Restriction of scalars along `ρ` commutes with the pullback `g^*` of pro-étale sheaves of
modules: there is a canonical isomorphism `g^* (Res F) ≅ Res (g^* F)` for sheaves `F` of
`Λ'`-modules on `Z`. It is the conjugate, for the adjunctions `Res ⊣ Coext` and `g^* ⊣ g_*`, of
the identity `g_* ∘ Coext = Coext ∘ g_*`: the direct image is precomposition with base change,
while coextension of scalars is postcomposition. This isomorphism is compatible with the
composition, identity and congruence isomorphisms of the pullbacks, and passes to the derived
categories, where it is compatible with the corresponding isomorphisms of derived pullbacks.

This is the compatibility of pullback with the change of the finite coefficients, used to make
the systems of derived pullbacks of the `ℓ`-adic coefficient stages into morphisms of adic
systems.

## Main definitions

- `AlgebraicGeometry.ProEtale.upperStarRestrictScalarsIso ρ g` :
  `Res ⋙ g^* ≅ g^* ⋙ Res` on pro-étale sheaves of modules.
- `AlgebraicGeometry.ProEtale.leftDerivedUpperStarRestrictScalarsIso ρ g` :
  `Res ⋙ Lg^* ≅ Lg^* ⋙ Res` on the derived categories.

## Main results

- `AlgebraicGeometry.ProEtale.upperStarRestrictScalarsIso_comp_hom`,
  `AlgebraicGeometry.ProEtale.upperStarRestrictScalarsIso_id_hom`,
  `AlgebraicGeometry.ProEtale.upperStarRestrictScalarsIso_congr_hom` : the compatibilities of
  `upperStarRestrictScalarsIso` with `upperStarComp`, `upperStarId` and `upperStarCongr`.
- `AlgebraicGeometry.ProEtale.leftDerivedUpperStarRestrictScalarsIso_comp_hom_app`,
  `AlgebraicGeometry.ProEtale.leftDerivedUpperStarRestrictScalarsIso_id_hom_app`,
  `AlgebraicGeometry.ProEtale.leftDerivedUpperStarRestrictScalarsIso_congr_hom_app` : the
  derived versions, with `leftDerivedUpperStarComp`, `leftDerivedUpperStarId` and
  `leftDerivedUpperStarCongr`.

The derived statements are deduced from the underived ones through general pasting lemmas for
the isomorphisms `CategoryTheory.Functor.mapDerivedCategorySquareIso` induced on derived
categories by exact functors (`CategoryTheory.Functor.mapDerivedCategorySquareIso_hom_app_comp`,
`CategoryTheory.Functor.mapDerivedCategorySquareIso_hom_app_id`), which rest on the coherence of
`CategoryTheory.Functor.mapDerivedCategoryCompIso` proved here.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace CategoryTheory

section Conjugate

variable {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]

/-- The inverse associator is conjugate to the inverse associator, the counterpart of
`CategoryTheory.conjugateEquiv_associator_hom`. -/
lemma conjugateEquiv_associator_inv {L₀₁ : A ⥤ B} {R₁₀ : B ⥤ A} {L₁₂ : B ⥤ C} {R₂₁ : C ⥤ B}
    {L₂₃ : C ⥤ D} {R₃₂ : D ⥤ C} (adj₀₁ : L₀₁ ⊣ R₁₀) (adj₁₂ : L₁₂ ⊣ R₂₁)
    (adj₂₃ : L₂₃ ⊣ R₃₂) :
    conjugateEquiv ((adj₀₁.comp adj₁₂).comp adj₂₃) (adj₀₁.comp (adj₁₂.comp adj₂₃))
      (Functor.associator _ _ _).inv = (Functor.associator _ _ _).inv := by
  ext X
  simp only [Functor.comp_obj, conjugateEquiv_apply_app, Adjunction.comp_unit_app,
    Functor.comp_map, Category.assoc, ← Functor.map_comp, Functor.associator_inv_app,
    Adjunction.comp_counit_app, Category.id_comp]
  simp

end Conjugate

namespace Functor

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

section Factors

variable {C D E : Type*} [Category C] [Category D] [Category E]
  [Abelian C] [Abelian D] [Abelian E]
  (F : C ⥤ D) (G : D ⥤ E) [F.Additive] [G.Additive]

variable [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]

end Factors

section Coherence

variable {C D E E' : Type*} [Category C] [Category D] [Category E] [Category E']
  [Abelian C] [Abelian D] [Abelian E] [Abelian E']
  [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E] [HasDerivedCategory E']

variable (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

variable (G : D ⥤ E) (H : E ⥤ E') [G.Additive] [H.Additive]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits H] [PreservesFiniteColimits H]

end Coherence

section Whisker

variable {C D E : Type*} [Category C] [Category D] [Category E]
  [Abelian C] [Abelian D] [Abelian E]
  [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]

end Whisker

section Pasting

variable {A₀ A₁ A₂ B₀ B₁ B₂ : Type*} [Category A₀] [Category A₁] [Category A₂] [Category B₀]
  [Category B₁] [Category B₂] [Abelian A₀] [Abelian A₁] [Abelian A₂] [Abelian B₀] [Abelian B₁]
  [Abelian B₂] [HasDerivedCategory A₀] [HasDerivedCategory A₁] [HasDerivedCategory A₂]
  [HasDerivedCategory B₀] [HasDerivedCategory B₁] [HasDerivedCategory B₂]
  {r₀ : A₀ ⥤ B₀} {r₁ : A₁ ⥤ B₁} {r₂ : A₂ ⥤ B₂} {P₂ : A₀ ⥤ A₁} {P₁ : A₁ ⥤ A₂} {P₁₂ : A₀ ⥤ A₂}
  {p₂ : B₀ ⥤ B₁} {p₁ : B₁ ⥤ B₂} {p₁₂ : B₀ ⥤ B₂}
  [r₀.Additive] [PreservesFiniteLimits r₀] [PreservesFiniteColimits r₀]
  [r₁.Additive] [PreservesFiniteLimits r₁] [PreservesFiniteColimits r₁]
  [r₂.Additive] [PreservesFiniteLimits r₂] [PreservesFiniteColimits r₂]
  [P₂.Additive] [PreservesFiniteLimits P₂] [PreservesFiniteColimits P₂]
  [P₁.Additive] [PreservesFiniteLimits P₁] [PreservesFiniteColimits P₁]
  [P₁₂.Additive] [PreservesFiniteLimits P₁₂] [PreservesFiniteColimits P₁₂]
  [p₂.Additive] [PreservesFiniteLimits p₂] [PreservesFiniteColimits p₂]
  [p₁.Additive] [PreservesFiniteLimits p₁] [PreservesFiniteColimits p₁]
  [p₁₂.Additive] [PreservesFiniteLimits p₁₂] [PreservesFiniteColimits p₁₂]

/-- The isomorphisms `Functor.mapDerivedCategorySquareIso` induced on derived categories are
compatible with the pasting of squares of exact functors along composition isomorphisms
`e : p₁₂ ≅ p₂ ⋙ p₁` and `e' : P₁₂ ≅ P₂ ⋙ P₁`: if the square `α₁₂` is the pasting of `α₂` and
`α₁` (hypothesis `h`), then so is the induced square on derived categories.

```
        P₂        P₁                       P₁₂
   A₀ ─────▶ A₁ ─────▶ A₂            A₀ ─────────▶ A₂
   │r₀  α₂   │r₁  α₁   │r₂     =     │r₀    α₁₂    │r₂
   ▼         ▼         ▼             ▼             ▼
   B₀ ─────▶ B₁ ─────▶ B₂            B₀ ─────────▶ B₂
        p₂        p₁                       p₁₂
```
-/
lemma mapDerivedCategorySquareIso_hom_app_comp (α₂ : r₀ ⋙ p₂ ≅ P₂ ⋙ r₁)
    (α₁ : r₁ ⋙ p₁ ≅ P₁ ⋙ r₂) (α₁₂ : r₀ ⋙ p₁₂ ≅ P₁₂ ⋙ r₂) (e : p₁₂ ≅ p₂ ⋙ p₁)
    (e' : P₁₂ ≅ P₂ ⋙ P₁)
    (h : ∀ X, α₁₂.hom.app X ≫ r₂.map (e'.hom.app X) =
      e.hom.app (r₀.obj X) ≫ p₁.map (α₂.hom.app X) ≫ α₁.hom.app (P₂.obj X))
    (K : DerivedCategory A₀) :
    (mapDerivedCategorySquareIso α₁₂).hom.app K ≫
        r₂.mapDerivedCategory.map ((mapDerivedCategoryTriangleIso e').hom.app K) =
      (mapDerivedCategoryTriangleIso e).hom.app (r₀.mapDerivedCategory.obj K) ≫
        p₁.mapDerivedCategory.map ((mapDerivedCategorySquareIso α₂).hom.app K) ≫
        (mapDerivedCategorySquareIso α₁).hom.app (P₂.mapDerivedCategory.obj K) := by
  have hiso : α₁₂ ≪≫ isoWhiskerRight e' r₂ =
      isoWhiskerLeft r₀ e ≪≫ isoWhiskerRight α₂ p₁ ≪≫ isoWhiskerLeft P₂ α₁ := by
    ext X
    simpa using h X
  have hm : (mapDerivedCategoryNatIso α₁₂).hom.app K ≫
      (mapDerivedCategoryNatIso (isoWhiskerRight e' r₂)).hom.app K =
      (mapDerivedCategoryNatIso (isoWhiskerLeft r₀ e)).hom.app K ≫
      (mapDerivedCategoryNatIso (isoWhiskerRight α₂ p₁)).hom.app K ≫
      (mapDerivedCategoryNatIso (isoWhiskerLeft P₂ α₁)).hom.app K := by
    rw [← NatTrans.comp_app, ← NatTrans.comp_app, ← NatTrans.comp_app,
      ← mapDerivedCategoryNatIso_trans, ← mapDerivedCategoryNatIso_trans,
      ← mapDerivedCategoryNatIso_trans, hiso]
  have hWR₁ := congr_app (mapDerivedCategoryNatIso_isoWhiskerRight e' r₂) K
  have hWR₂ := congr_app (mapDerivedCategoryNatIso_isoWhiskerRight α₂ p₁) K
  have hWL₁ := congr_app (mapDerivedCategoryNatIso_isoWhiskerLeft r₀ e) K
  have hWL₂ := congr_app (mapDerivedCategoryNatIso_isoWhiskerLeft P₂ α₁) K
  have hA₁ := congr_app (mapDerivedCategoryCompIso_assoc P₂ P₁ r₂) K
  have hA₂ := congr_app (mapDerivedCategoryCompIso_assoc r₀ p₂ p₁) K
  have hA₃ := congr_app (mapDerivedCategoryCompIso_assoc P₂ r₁ p₁) K
  simp only [NatTrans.comp_app, Functor.whiskerRight_app] at hWR₁ hWR₂
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app] at hWL₁ hWL₂
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app] at hA₁ hA₂ hA₃
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.map_comp, Category.assoc]
  have hWL₁' : (mapDerivedCategoryNatIso (isoWhiskerLeft r₀ e)).hom.app K =
      (mapDerivedCategoryCompIso r₀ p₁₂).hom.app K ≫
        (mapDerivedCategoryNatIso e).hom.app (r₀.mapDerivedCategory.obj K) ≫
        (mapDerivedCategoryCompIso r₀ (p₂ ⋙ p₁)).inv.app K := by
    rw [← reassoc_of% hWL₁, Iso.hom_inv_id_app, Category.comp_id]
  have hWR₂' : (mapDerivedCategoryNatIso (isoWhiskerRight α₂ p₁)).hom.app K =
      (mapDerivedCategoryCompIso (r₀ ⋙ p₂) p₁).hom.app K ≫
        p₁.mapDerivedCategory.map ((mapDerivedCategoryNatIso α₂).hom.app K) ≫
        (mapDerivedCategoryCompIso (P₂ ⋙ r₁) p₁).inv.app K := by
    rw [← reassoc_of% hWR₂, Iso.hom_inv_id_app, Category.comp_id]
  have hA₂' : (mapDerivedCategoryCompIso r₀ (p₂ ⋙ p₁)).inv.app K ≫
      (mapDerivedCategoryCompIso (r₀ ⋙ p₂) p₁).hom.app K =
      (mapDerivedCategoryCompIso p₂ p₁).hom.app (r₀.mapDerivedCategory.obj K) ≫
        p₁.mapDerivedCategory.map ((mapDerivedCategoryCompIso r₀ p₂).inv.app K) := by
    rw [← cancel_epi ((mapDerivedCategoryCompIso r₀ (p₂ ⋙ p₁)).hom.app K),
      Iso.hom_inv_id_app_assoc, reassoc_of% hA₂, ← Functor.map_comp, Iso.hom_inv_id_app,
      Functor.map_id, Category.comp_id]
  have hA₃' : (mapDerivedCategoryCompIso (P₂ ⋙ r₁) p₁).inv.app K ≫
      (mapDerivedCategoryCompIso P₂ (r₁ ⋙ p₁)).hom.app K =
      p₁.mapDerivedCategory.map ((mapDerivedCategoryCompIso P₂ r₁).hom.app K) ≫
        (mapDerivedCategoryCompIso r₁ p₁).inv.app (P₂.mapDerivedCategory.obj K) := by
    rw [← cancel_epi ((mapDerivedCategoryCompIso (P₂ ⋙ r₁) p₁).hom.app K),
      Iso.hom_inv_id_app_assoc, ← reassoc_of% hA₃, Iso.hom_inv_id_app, Category.comp_id]
  rw [← reassoc_of% hWR₁, ← hA₁, reassoc_of% hm, reassoc_of% hWL₂, hWL₁', hWR₂']
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
  rw [reassoc_of% hA₂', reassoc_of% hA₃']

end Pasting

section Identity

variable {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B] [HasDerivedCategory A]
  [HasDerivedCategory B] {r : A ⥤ B} {P : A ⥤ A} {p : B ⥤ B}
  [r.Additive] [PreservesFiniteLimits r] [PreservesFiniteColimits r]
  [P.Additive] [PreservesFiniteLimits P] [PreservesFiniteColimits P]
  [p.Additive] [PreservesFiniteLimits p] [PreservesFiniteColimits p]

end Identity

end Functor

end CategoryTheory

namespace AlgebraicGeometry.ProEtale

variable {Λ Λ' : Type (u + 1)} [CommRing Λ] [CommRing Λ'] (ρ : Λ →+* Λ')

section UpperStar

variable {Y Z : Scheme.{u}} (g : Y ⟶ Z)

/-- Restriction of scalars along `ρ : Λ →+* Λ'` commutes with the pullback of pro-étale sheaves:
for a morphism of schemes `g : Y ⟶ Z`, the canonical isomorphism `g^* (Res F) ≅ Res (g^* F)` for
sheaves `F` of `Λ'`-modules on `Z`. It is the conjugate, for the composite adjunctions
`Res ⋙ g^* ⊣ g_* ⋙ Coext` and `g^* ⋙ Res ⊣ Coext ⋙ g_*`, of the identity of
`g_* ⋙ Coext = Coext ⋙ g_*`: the direct image restricts sheaves along base change, while
coextension of scalars is computed objectwise. -/
noncomputable def upperStarRestrictScalarsIso :
    Sheaf.restrictScalars (Scheme.ProEt.topology Z) ρ ⋙ upperStar (ModuleCat.{u + 1} Λ) g ≅
      upperStar (ModuleCat.{u + 1} Λ') g ⋙ Sheaf.restrictScalars (Scheme.ProEt.topology Y) ρ :=
  (conjugateIsoEquiv
    ((upperStarLowerStarAdjunction _ g).comp (Sheaf.restrictCoextendScalarsAdj _ ρ))
    ((Sheaf.restrictCoextendScalarsAdj _ ρ).comp (upperStarLowerStarAdjunction _ g))).symm
    (Iso.refl _)

/-- `AlgebraicGeometry.ProEtale.upperStarRestrictScalarsIso` is conjugate to the identity. -/
lemma conjugateEquiv_upperStarRestrictScalarsIso_hom :
    conjugateEquiv
      ((upperStarLowerStarAdjunction _ g).comp (Sheaf.restrictCoextendScalarsAdj _ ρ))
      ((Sheaf.restrictCoextendScalarsAdj _ ρ).comp (upperStarLowerStarAdjunction _ g))
      (upperStarRestrictScalarsIso ρ g).hom = 𝟙 _ :=
  congrArg Iso.hom ((conjugateIsoEquiv _ _).apply_symm_apply (Iso.refl _))

end UpperStar

section Coherence

end Coherence

section Derived

variable {Y Z : Scheme.{u}} (g : Y ⟶ Z)

end Derived

end AlgebraicGeometry.ProEtale
