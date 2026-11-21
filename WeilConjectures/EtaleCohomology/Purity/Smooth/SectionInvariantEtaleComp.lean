/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.SectionInvariantEtale
public import WeilConjectures.AlgebraicGeometry.Etale.EtaleAmbientAdjointLocalityComp
public import WeilConjectures.AlgebraicGeometry.Etale.Sum.EtaleSumCompositionCounit
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangePaste
public import WeilConjectures.SixFunctors.Etale.Derived.DerivedEtaleLowerShriekAdjunctionEq

/-!
# Composition of the étale identifications of section invariants

For étale `e : V' ⟶ V`, `g : V ⟶ B` and `g' = e ≫ g`, the identification `Rg'^! ≅ Le^* Rg^!`
(`AlgebraicGeometry.Etale.rightDerivedUpperShriekEtaleCompIso`) is conjugate to the composition
isomorphism `R(g')_! ≅ R(e)_! ⋙ R(g)_!` under the adjunctions `R(e)_! ⊣ Le^*` and
`R(g)_! ⊣ Rg^!`. This file shows that these identifications, and hence the identifications of
section invariants `𝒞(g', s') ≅ 𝒞(g, s)` (`AlgebraicGeometry.Etale.sectionInvariantEtaleIso`),
are compatible with composition and identities: clause `--8` of
`lemma-naturality-under-base-change-etale`, for Noetherian schemes.

## Main statements

- `AlgebraicGeometry.Etale.conjugateEquiv_rightDerivedLowerShriekEtaleAdjunction_comp`: the
  adjunctions `R(e)_! ⊣ Le^*` compose, i.e. the conjugate of
  `R(e₁)_! ⋙ R(e₂)_! ≅ R(e₁ ≫ e₂)_!` is `Le₂^* ⋙ Le₁^* ≅ L(e₁ ≫ e₂)^*`.
- `AlgebraicGeometry.Etale.rightDerivedUpperShriekEtaleCompIso_comp_hom_app`: the
  identifications `Rg'^! ≅ Le^* Rg^!` compose.
- `AlgebraicGeometry.Etale.sectionInvariantEtaleIso_comp`,
  `AlgebraicGeometry.Etale.sectionInvariantEtaleIso_id`: the identifications of section
  invariants respect composition and identities.

## Implementation details

The adjunction `R(e)_! ⊣ Le^*` is the adjunction `De_! ⊣ Le^*` of the extension by zero,
transported along the comparison `De_! ≅ R(e)_!`. The comparisons intertwine the composition
isomorphisms of `D(-)_!` and of `R(-)_!`
(`AlgebraicGeometry.Etale.derivedEtaleSumCompIso_hom_app`), and the composition isomorphism of
`D(-)_!` is conjugate to that of the levelwise pullbacks
(`AlgebraicGeometry.Etale.etaleSumCompositionCounit`). Both inputs, and the associativity of
`R(-)_!` (`AlgebraicGeometry.Etale.unboundedEtaleLowerShriekCompIso_assoc`), are stated for
Noetherian schemes. The identity case follows from the composition case, since the
identification along `𝟙` is then an idempotent isomorphism.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

section EtaleAdjunctionComp

/-- An adjunction transported along `i : L ≅ L'` is conjugate to the original one via `i`. -/
private lemma conjugateEquiv_ofNatIsoLeft_hom {C D : Type*} [Category C] [Category D]
    {L L' : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) (i : L ≅ L') :
    conjugateEquiv (adj.ofNatIsoLeft i) adj i.hom = 𝟙 _ := by
  ext K
  simp [conjugateEquiv_apply_app, Adjunction.ofNatIsoLeft]

/-- The original adjunction is conjugate to its transport along `i : L ≅ L'` via `i⁻¹`. -/
private lemma conjugateEquiv_ofNatIsoLeft_inv {C D : Type*} [Category C] [Category D]
    {L L' : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) (i : L ≅ L') :
    conjugateEquiv adj (adj.ofNatIsoLeft i) i.inv = 𝟙 _ := by
  ext K
  simp [conjugateEquiv_apply_app, Adjunction.ofNatIsoLeft]

/-- The conjugate of the identity between an adjunction and its transport along `j : R ≅ R'`
is `j`. -/
private lemma conjugateEquiv_ofNatIsoRight_id {C D : Type*} [Category C] [Category D]
    {L : C ⥤ D} {R R' : D ⥤ C} (adj : L ⊣ R) (j : R ≅ R') :
    conjugateEquiv adj (adj.ofNatIsoRight j) (𝟙 _) = j.hom := by
  ext K
  simp only [conjugateEquiv_apply_app, Adjunction.ofNatIsoRight_unit, NatTrans.comp_app,
    Functor.whiskerLeft_app, NatTrans.id_app, Category.assoc]
  erw [R'.map_id, Category.id_comp]
  have h := j.hom.naturality (adj.counit.app K)
  erw [← h, Adjunction.right_triangle_components_assoc]
  rfl

/-- The conjugate of the identity between the transport of an adjunction along `j : R ≅ R'` and
the adjunction is `j⁻¹`. -/
private lemma conjugateEquiv_ofNatIsoRight_id' {C D : Type*} [Category C] [Category D]
    {L : C ⥤ D} {R R' : D ⥤ C} (adj : L ⊣ R) (j : R ≅ R') :
    conjugateEquiv (adj.ofNatIsoRight j) adj (𝟙 _) = j.inv := by
  ext K
  simp [conjugateEquiv_apply_app, Adjunction.ofNatIsoRight]

/-- The inverse of the canonical comparison `Rf_!(c) ≅ De_!` is the comparison
`De_! ⟶ Rf_!(c)`. -/
lemma canonicalEtaleCompactSupportComparison_inv {X Y : Scheme.{u}} (e : X ⟶ Y)
    [_root_.AlgebraicGeometry.Etale e] [IsSeparated e] [QuasiCompact e] (c : Compactification e) :
    (canonicalEtaleCompactSupportComparison Λ e c).inv = compactificationEtaleComparison Λ e c := by
  rw [compactificationEtaleComparison_eq_compactSupportDerivedComparison]
  rfl

variable {X Y Z : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y] [IsNoetherian Z] (e₁ : X ⟶ Y)
  (e₂ : Y ⟶ Z) [_root_.AlgebraicGeometry.Etale e₁] [_root_.AlgebraicGeometry.Etale e₂]
  [HasCompactification e₁] [HasCompactification e₂] [HasCompactification (e₁ ≫ e₂)]
  [QuasiCompact e₁] [QuasiCompact e₂]

/-- The comparisons `De_! ⟶ R(e)_!` intertwine the composition isomorphism of the extensions by
zero with that of the compactly supported direct images. -/
lemma compactificationEtaleComparison_comp_unboundedEtaleLowerShriekCompIso
    (M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (compactificationEtaleComparison Λ e₂ (HasCompactification.compactification e₂)).app
        ((etaleLowerShriek (ModuleCat.{u + 1} Λ) e₁ inferInstance).mapDerivedCategory.obj M) ≫
      (R(e₂)_![ModuleCat.{u + 1} Λ]).map
        ((compactificationEtaleComparison Λ e₁ (HasCompactification.compactification e₁)).app M) ≫
      (unboundedEtaleLowerShriekCompIso Λ e₁ e₂).hom.app M =
    (derivedEtaleSumCompIso Λ e₁ e₂).hom.app M ≫
      (compactificationEtaleComparison Λ (e₁ ≫ e₂)
        (HasCompactification.compactification (e₁ ≫ e₂))).app M := by
  have h := derivedEtaleSumCompIso_hom_app Λ e₁ e₂ (HasCompactification.compactification e₁)
    (HasCompactification.compactification e₂) (HasCompactification.compactification (e₁ ≫ e₂)) M
  simp only [canonicalEtaleCompactSupportComparison_inv, ← NatTrans.comp_app,
    compactificationEtaleComparison_comp_rightDerivedLowerShriekIso] at h
  have hd : (rightDerivedLowerShriekIso Λ (HasCompactification.compactification e₂)).hom =
      𝟙 _ := by
    have := isIso_compactificationEtaleComparison Λ e₂ (HasCompactification.compactification e₂)
    rw [← cancel_epi (compactificationEtaleComparison Λ e₂
      (HasCompactification.compactification e₂)),
      compactificationEtaleComparison_comp_rightDerivedLowerShriekIso, Category.comp_id]
  simp only [NatTrans.comp_app, hd, NatTrans.id_app] at h
  rw [h]
  erw [Category.id_comp]

omit [HasCompactification (e₁ ≫ e₂)] in
/-- The extensions by zero `De_! ⊣ Le^*` compose: the conjugate of the composition isomorphism
`De₁_! ⋙ De₂_! ≅ D(e₁ ≫ e₂)_!` is the composition isomorphism `Le₂^* ⋙ Le₁^* ≅ L(e₁ ≫ e₂)^*` of
derived pullbacks. -/
theorem conjugateEquiv_derivedEtaleLowerShriekAdjunction_comp :
    conjugateEquiv ((derivedEtaleLowerShriekAdjunction (ModuleCat.{u + 1} Λ) e₁).comp
        (derivedEtaleLowerShriekAdjunction (ModuleCat.{u + 1} Λ) e₂))
      (derivedEtaleLowerShriekAdjunction (ModuleCat.{u + 1} Λ) (e₁ ≫ e₂))
      (derivedEtaleSumCompIso Λ e₁ e₂).inv =
    (leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) e₁ e₂).inv := by
  set S := derivedEtaleSumCompIso Λ e₁ e₂
  set d₁ := derivedEtaleLowerShriekAdjunction (ModuleCat.{u + 1} Λ) e₁
  set d₂ := derivedEtaleLowerShriekAdjunction (ModuleCat.{u + 1} Λ) e₂
  set d₁₂ := derivedEtaleLowerShriekAdjunction (ModuleCat.{u + 1} Λ) (e₁ ≫ e₂)
  have hd₁ : d₁ = (derivedEtaleLowerShriekUpperStarAdjunction _ e₁ inferInstance).ofNatIsoRight
      (leftDerivedUpperStarIsoMapDerivedCategory _ e₁).symm := by
    rw [← derivedEtaleLowerShriekMapAdjunction_eq]; rfl
  have hd₂ : d₂ = (derivedEtaleLowerShriekUpperStarAdjunction _ e₂ inferInstance).ofNatIsoRight
      (leftDerivedUpperStarIsoMapDerivedCategory _ e₂).symm := by
    rw [← derivedEtaleLowerShriekMapAdjunction_eq]; rfl
  have hd₁₂ : d₁₂ = (derivedEtaleLowerShriekUpperStarAdjunction _ (e₁ ≫ e₂)
      inferInstance).ofNatIsoRight
        (leftDerivedUpperStarIsoMapDerivedCategory _ (e₁ ≫ e₂)).symm := by
    rw [← derivedEtaleLowerShriekMapAdjunction_eq]; rfl
  set u₁ := derivedEtaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) e₁ inferInstance
  set u₂ := derivedEtaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) e₂ inferInstance
  set u₁₂ := derivedEtaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) (e₁ ≫ e₂)
    inferInstance
  have k₁ : conjugateEquiv (d₁.comp d₂) (u₁.comp d₂) (Functor.whiskerRight (𝟙 _) _) =
      Functor.whiskerLeft _ (leftDerivedUpperStarIsoMapDerivedCategory _ e₁).hom := by
    rw [conjugateEquiv_whiskerRight, hd₁, conjugateEquiv_ofNatIsoRight_id']
    rfl
  have k₂ : conjugateEquiv (u₁.comp d₂) (u₁.comp u₂) (Functor.whiskerLeft _ (𝟙 _)) =
      Functor.whiskerRight (leftDerivedUpperStarIsoMapDerivedCategory _ e₂).hom _ := by
    rw [conjugateEquiv_whiskerLeft, hd₂, conjugateEquiv_ofNatIsoRight_id']
    rfl
  have k₃ : conjugateEquiv u₁₂ d₁₂ (𝟙 _) =
      (leftDerivedUpperStarIsoMapDerivedCategory _ (e₁ ≫ e₂)).inv := by
    rw [hd₁₂, conjugateEquiv_ofNatIsoRight_id]
    rfl
  have k₄ : conjugateEquiv (u₁.comp u₂) u₁₂ S.inv =
      (unboundedEtaleUpperStarCompIso Λ e₁ e₂).inv := by
    rw [← cancel_mono (unboundedEtaleUpperStarCompIso Λ e₁ e₂).hom, Iso.inv_hom_id,
      ← (etaleSumCompositionCounit Λ e₁ e₂).2]
    exact conjugateEquiv_comm _ _ S.hom_inv_id
  have hS : S.inv = 𝟙 _ ≫ S.inv ≫
      Functor.whiskerLeft D(etaleLowerShriek (ModuleCat.{u + 1} Λ) e₁ inferInstance)
        (𝟙 D(etaleLowerShriek (ModuleCat.{u + 1} Λ) e₂ inferInstance)) ≫
      Functor.whiskerRight (𝟙 D(etaleLowerShriek (ModuleCat.{u + 1} Λ) e₁ inferInstance))
        D(etaleLowerShriek (ModuleCat.{u + 1} Λ) e₂ inferInstance) := by
    simp
  rw [hS, ← conjugateEquiv_comp (d₁.comp d₂) u₁₂ d₁₂,
    ← conjugateEquiv_comp (d₁.comp d₂) (u₁.comp u₂) u₁₂,
    ← conjugateEquiv_comp (d₁.comp d₂) (u₁.comp d₂) (u₁.comp u₂), k₁, k₂, k₃, k₄]
  ext K
  rw [← cancel_epi ((leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) e₁ e₂).hom.app K),
    Iso.hom_inv_id_app]
  have h := leftDerivedUpperStarComp_hom_app_comp_isoMapDerivedCategory _ e₁ e₂ (e₁ ≫ e₂) rfl K
  change _ = _ ≫ (unboundedEtaleUpperStarCompIso Λ e₁ e₂).hom.app _ at h
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Category.assoc]
  rw [reassoc_of% h]
  simp

/-- **The étale adjunctions compose**: for étale `e₁`, `e₂`, the conjugate of the composition
isomorphism `R(e₁)_! ⋙ R(e₂)_! ≅ R(e₁ ≫ e₂)_!` under the adjunctions `R(e)_! ⊣ Le^*` is the
composition isomorphism `Le₂^* ⋙ Le₁^* ≅ L(e₁ ≫ e₂)^*` of derived pullbacks. -/
theorem conjugateEquiv_rightDerivedLowerShriekEtaleAdjunction_comp :
    conjugateEquiv ((rightDerivedLowerShriekEtaleAdjunction Λ e₁).comp
        (rightDerivedLowerShriekEtaleAdjunction Λ e₂))
      (rightDerivedLowerShriekEtaleAdjunction Λ (e₁ ≫ e₂))
      (unboundedEtaleLowerShriekCompIso Λ e₁ e₂).inv =
    (leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) e₁ e₂).inv := by
  have := isIso_compactificationEtaleComparison Λ e₁ (HasCompactification.compactification e₁)
  have := isIso_compactificationEtaleComparison Λ e₂ (HasCompactification.compactification e₂)
  have := isIso_compactificationEtaleComparison Λ (e₁ ≫ e₂)
    (HasCompactification.compactification (e₁ ≫ e₂))
  set φ₁ : D(etaleLowerShriek (ModuleCat.{u + 1} Λ) e₁ inferInstance) ⟶
      R(e₁)_![ModuleCat.{u + 1} Λ] :=
    compactificationEtaleComparison Λ e₁ (HasCompactification.compactification e₁)
  set φ₂ : D(etaleLowerShriek (ModuleCat.{u + 1} Λ) e₂ inferInstance) ⟶
      R(e₂)_![ModuleCat.{u + 1} Λ] :=
    compactificationEtaleComparison Λ e₂ (HasCompactification.compactification e₂)
  set φ₁₂ : D(etaleLowerShriek (ModuleCat.{u + 1} Λ) (e₁ ≫ e₂) inferInstance) ⟶
      R(e₁ ≫ e₂)_![ModuleCat.{u + 1} Λ] :=
    compactificationEtaleComparison Λ (e₁ ≫ e₂)
      (HasCompactification.compactification (e₁ ≫ e₂))
  set S := derivedEtaleSumCompIso Λ e₁ e₂
  set d₁ := derivedEtaleLowerShriekAdjunction (ModuleCat.{u + 1} Λ) e₁
  set d₂ := derivedEtaleLowerShriekAdjunction (ModuleCat.{u + 1} Λ) e₂
  set d₁₂ := derivedEtaleLowerShriekAdjunction (ModuleCat.{u + 1} Λ) (e₁ ≫ e₂)
  set a₁ := rightDerivedLowerShriekEtaleAdjunction Λ e₁
  set a₂ := rightDerivedLowerShriekEtaleAdjunction Λ e₂
  set a₁₂ := rightDerivedLowerShriekEtaleAdjunction Λ (e₁ ≫ e₂)
  have hU : (unboundedEtaleLowerShriekCompIso Λ e₁ e₂).inv =
      inv φ₁₂ ≫ S.inv ≫ Functor.whiskerLeft _ φ₂ ≫
        Functor.whiskerRight φ₁ R(e₂)_![ModuleCat.{u + 1} Λ] := by
    rw [IsIso.eq_inv_comp, ← cancel_epi S.hom, Iso.hom_inv_id_assoc]
    ext M
    have h := compactificationEtaleComparison_comp_unboundedEtaleLowerShriekCompIso Λ e₁ e₂ M
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
    rw [← reassoc_of% h, Iso.hom_inv_id_app]
    erw [Category.comp_id]
  -- the conjugates of the comparisons `De_! ⟶ R(e)_!` are identities
  have c₁ : conjugateEquiv (a₁.comp a₂) (d₁.comp a₂) (Functor.whiskerRight φ₁ _) = 𝟙 _ := by
    rw [conjugateEquiv_whiskerRight]
    rw [show conjugateEquiv a₁ d₁ φ₁ = 𝟙 _ from conjugateEquiv_ofNatIsoLeft_hom d₁ (asIso φ₁)]
    rfl
  have c₂ : conjugateEquiv (d₁.comp a₂) (d₁.comp d₂) (Functor.whiskerLeft _ φ₂) = 𝟙 _ := by
    rw [conjugateEquiv_whiskerLeft]
    rw [show conjugateEquiv a₂ d₂ φ₂ = 𝟙 _ from conjugateEquiv_ofNatIsoLeft_hom d₂ (asIso φ₂)]
    ext
    simp
  have c₃ : conjugateEquiv d₁₂ a₁₂ (inv φ₁₂) = 𝟙 _ :=
    conjugateEquiv_ofNatIsoLeft_inv d₁₂ (asIso φ₁₂)
  rw [hU, ← conjugateEquiv_comp _ d₁₂, c₃, Category.comp_id,
    ← conjugateEquiv_comp _ (d₁.comp d₂), ← conjugateEquiv_comp _ (d₁.comp a₂), c₁, c₂,
    Category.id_comp, Category.id_comp]
  exact conjugateEquiv_derivedEtaleLowerShriekAdjunction_comp Λ e₁ e₂

end EtaleAdjunctionComp

section Comp

variable {V'' V' V B : Scheme.{u}} [IsNoetherian V''] [IsNoetherian V'] [IsNoetherian V]
  [IsNoetherian B] (e₁ : V'' ⟶ V') (e₂ : V' ⟶ V) [_root_.AlgebraicGeometry.Etale e₁]
  [_root_.AlgebraicGeometry.Etale e₂] [HasCompactification e₁] [HasCompactification e₂]
  [HasCompactification (e₁ ≫ e₂)] (g : V ⟶ B) (g' : V' ⟶ B) (g'' : V'' ⟶ B)
  (w₂ : e₂ ≫ g = g') (w₁ : e₁ ≫ g' = g'') [HasCompactification g] [HasCompactification g']
  [HasCompactification g''] [QuasiCompact g] [QuasiCompact g'] [QuasiCompact g'']
  [QuasiCompact e₁] [QuasiCompact e₂]

omit [Finite Λ] in
/-- The congruence isomorphism `R(f)_! ≅ R(f')_!` of `f = f'` is `eqToIso`. -/
lemma unboundedEtaleLowerShriekCongr_eq_eqToIso {X Y : Scheme.{u}} {f f' : X ⟶ Y}
    [HasCompactification f] [HasCompactification f'] (h : f = f') :
    unboundedEtaleLowerShriekCongr Λ h = eqToIso (by subst h; rfl) := by
  subst h
  rfl

omit [_root_.AlgebraicGeometry.Etale e₁] [_root_.AlgebraicGeometry.Etale e₂] in
/-- The composition isomorphisms `R(g'')_! ≅ R(e)_! ⋙ R(g')_!` of a composite `e₁ ≫ e₂ ≫ g` are
associative. -/
lemma rightDerivedLowerShriekCompIsoOfEq_comp :
    rightDerivedLowerShriekCompIsoOfEq Λ (e₁ ≫ e₂) g g'' (by rw [Category.assoc, w₂, w₁]) =
      rightDerivedLowerShriekCompIsoOfEq Λ e₁ g' g'' w₁ ≪≫
        Functor.isoWhiskerLeft _ (rightDerivedLowerShriekCompIsoOfEq Λ e₂ g g' w₂) ≪≫
        (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (unboundedEtaleLowerShriekCompIso Λ e₁ e₂) _ := by
  subst w₁ w₂
  have : HasCompactification ((e₁ ≫ e₂) ≫ g) := .of_eq (Category.assoc e₁ e₂ g).symm
  have h := unboundedEtaleLowerShriekCompIso_assoc Λ e₁ e₂ g
  rw [unboundedEtaleLowerShriekCongr_eq_eqToIso] at h
  refine Iso.ext ?_
  simp only [rightDerivedLowerShriekCompIsoOfEq, rightDerivedLowerShriekCompIso_eq_symm,
    eqToIso_refl, Iso.refl_trans, Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom]
  erw [eqToIso.hom, eqToHom_refl, Category.comp_id] at h
  apply Iso.inv_ext
  rw [← cancel_epi (Functor.whiskerRight (unboundedEtaleLowerShriekCompIso Λ e₁ e₂).hom _),
    reassoc_of% h]
  ext K
  simp

/-- The conjugate of `R(e₁)_! ⋙ R(e₂)_! ≅ R(e₁ ≫ e₂)_!` is the composition isomorphism of derived
pullbacks, as an isomorphism. -/
lemma conjugateIsoEquiv_unboundedEtaleLowerShriekCompIso :
    conjugateIsoEquiv (rightDerivedLowerShriekEtaleAdjunction Λ (e₁ ≫ e₂))
        ((rightDerivedLowerShriekEtaleAdjunction Λ e₁).comp
          (rightDerivedLowerShriekEtaleAdjunction Λ e₂))
        (unboundedEtaleLowerShriekCompIso Λ e₁ e₂) =
      leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) e₁ e₂ := by
  refine Iso.ext ?_
  rw [conjugateIsoEquiv_apply_hom, ← cancel_epi (leftDerivedUpperStarComp _ e₁ e₂).inv,
    Iso.inv_hom_id, ← conjugateEquiv_rightDerivedLowerShriekEtaleAdjunction_comp]
  exact conjugateEquiv_comm _ _ (Iso.hom_inv_id _)

/-- **The identifications `Rg'^! ≅ Le^* Rg^!` compose**: for `g'' = e₁ ≫ g'` and `g' = e₂ ≫ g`,
the identification along `e₁ ≫ e₂` is the one along `e₁`, followed by `Le₁^*` of the one along
`e₂` and by the composition isomorphism `Le₂^* ⋙ Le₁^* ≅ L(e₁ ≫ e₂)^*`. -/
theorem rightDerivedUpperShriekEtaleCompIso_comp_hom_app
    (K : _root_.DerivedCategory (Sheaf B.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (rightDerivedUpperShriekEtaleCompIso Λ (e₁ ≫ e₂) g g''
        (by rw [Category.assoc, w₂, w₁])).hom.app K =
      (rightDerivedUpperShriekEtaleCompIso Λ e₁ g' g'' w₁).hom.app K ≫
        (L((e₁)^*[ModuleCat.{u + 1} Λ])).map
          ((rightDerivedUpperShriekEtaleCompIso Λ e₂ g g' w₂).hom.app K) ≫
        (leftDerivedUpperStarComp _ e₁ e₂).inv.app ((R(g)^![Λ]).obj K) := by
  set a₁ := rightDerivedLowerShriekEtaleAdjunction Λ e₁
  set a₂ := rightDerivedLowerShriekEtaleAdjunction Λ e₂
  set a₁₂ := rightDerivedLowerShriekEtaleAdjunction Λ (e₁ ≫ e₂)
  set b := rightDerivedUpperShriekAdjunction Λ g
  set b' := rightDerivedUpperShriekAdjunction Λ g'
  set b'' := rightDerivedUpperShriekAdjunction Λ g''
  have key : (rightDerivedUpperShriekEtaleCompIso Λ (e₁ ≫ e₂) g g''
      (by rw [Category.assoc, w₂, w₁])).symm =
      conjugateIsoEquiv (a₁₂.comp b) ((a₁.comp a₂).comp b)
          (Functor.isoWhiskerRight (unboundedEtaleLowerShriekCompIso Λ e₁ e₂) _) ≪≫
        conjugateIsoEquiv ((a₁.comp a₂).comp b) (a₁.comp (a₂.comp b))
          (Functor.associator _ _ _).symm ≪≫
        conjugateIsoEquiv (a₁.comp (a₂.comp b)) (a₁.comp b')
          (Functor.isoWhiskerLeft _ (rightDerivedLowerShriekCompIsoOfEq Λ e₂ g g' w₂)) ≪≫
        (rightDerivedUpperShriekEtaleCompIso Λ e₁ g' g'' w₁).symm := by
    rw [rightDerivedUpperShriekEtaleCompIso, rightDerivedUpperShriekEtaleCompIso, Iso.symm_symm_eq,
      Iso.symm_symm_eq, rightDerivedLowerShriekCompIsoOfEq_comp Λ e₁ e₂ g g' g'' w₂ w₁,
      conjugateIsoEquiv_trans _ (a₁.comp b'), conjugateIsoEquiv_trans _ (a₁.comp (a₂.comp b)),
      conjugateIsoEquiv_trans _ ((a₁.comp a₂).comp b)]
    simp only [Iso.trans_assoc]
    rfl
  rw [conjugateIsoEquiv_isoWhiskerRight, conjugateIsoEquiv_unboundedEtaleLowerShriekCompIso,
    conjugateIsoEquiv_iso_symm, conjugateIsoEquiv_associator, conjugateIsoEquiv_isoWhiskerLeft]
    at key
  have h := congrArg (fun i ↦ i.inv.app K) key
  simp only [Iso.symm_inv, Iso.trans_inv, NatTrans.comp_app, Functor.isoWhiskerLeft_inv,
    Functor.isoWhiskerRight_inv, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Category.id_comp, Category.assoc] at h
  have hα : (rightDerivedUpperShriekEtaleCompIso Λ e₂ g g' w₂).hom =
      ((conjugateIsoEquiv (a₂.comp b) b') (rightDerivedLowerShriekCompIsoOfEq Λ e₂ g g' w₂)).inv :=
    rfl
  rw [h, hα]

end Comp

section Coherence

variable {V'' V' V B : Scheme.{u}}

/-- The identification of section invariants along `e` only depends on `e`. -/
lemma sectionInvariantEtaleIso_congr {e e' : V' ⟶ V} (h : e = e')
    [_root_.AlgebraicGeometry.Etale e] [_root_.AlgebraicGeometry.Etale e']
    [HasCompactification e] [HasCompactification e'] (g : V ⟶ B) (g' : V' ⟶ B)
    (w : e ≫ g = g') (w' : e' ≫ g = g') [HasCompactification g] [HasCompactification g']
    [QuasiCompact g'] (s : B ⟶ V) (s' : B ⟶ V') (hs : s' ≫ e = s) (hs' : s' ≫ e' = s) :
    sectionInvariantEtaleIso Λ e g g' w s s' hs =
      sectionInvariantEtaleIso Λ e' g g' w' s s' hs' := by
  subst h
  rfl

/-- The identifications of section invariants along étale maps are compatible with
composition. -/
theorem sectionInvariantEtaleIso_comp [IsNoetherian V''] [IsNoetherian V'] [IsNoetherian V]
    [IsNoetherian B] (e₁ : V'' ⟶ V') (e₂ : V' ⟶ V)
    [_root_.AlgebraicGeometry.Etale e₁] [_root_.AlgebraicGeometry.Etale e₂]
    [HasCompactification e₁] [HasCompactification e₂] [HasCompactification (e₁ ≫ e₂)]
    (g : V ⟶ B) (g' : V' ⟶ B) (g'' : V'' ⟶ B) (w₂ : e₂ ≫ g = g') (w₁ : e₁ ≫ g' = g'')
    [HasCompactification g] [HasCompactification g'] [HasCompactification g''] [QuasiCompact g]
    [QuasiCompact g'] [QuasiCompact g''] (s : B ⟶ V) (s' : B ⟶ V') (s'' : B ⟶ V'')
    (h₂ : s' ≫ e₂ = s) (h₁ : s'' ≫ e₁ = s') :
    sectionInvariantEtaleIso Λ (e₁ ≫ e₂) g g'' (by rw [Category.assoc, w₂, w₁]) s s''
        (by rw [← Category.assoc, h₁, h₂]) =
      sectionInvariantEtaleIso Λ e₁ g' g'' w₁ s' s'' h₁ ≪≫
        sectionInvariantEtaleIso Λ e₂ g g' w₂ s s' h₂ := by
  have : QuasiCompact (e₂ ≫ g) := w₂ ▸ ‹_›
  have : QuasiCompact e₂ := .of_comp e₂ g
  have : QuasiCompact (e₁ ≫ g') := w₁ ▸ ‹_›
  have : QuasiCompact e₁ := .of_comp e₁ g'
  refine Iso.ext ?_
  simp only [sectionInvariantEtaleIso, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom,
    Iso.app_inv, dualizingComplexEtaleCompIso_hom]
  rw [rightDerivedUpperShriekEtaleCompIso_comp_hom_app Λ e₁ e₂ g g' g'' w₂ w₁]
  simp only [Functor.map_comp, Category.assoc]
  erw [map_leftDerivedUpperStarComp_inv_app_leftDerivedUpperStarComp_inv_app _ s'' e₁ e₂ s'
    (e₁ ≫ e₂) s h₁.symm rfl h₂.symm (dualizingComplex Λ g)]
  have n := (leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) s'' e₁ s' h₁.symm).inv.naturality
    ((rightDerivedUpperShriekEtaleCompIso Λ e₂ g g' w₂).hom.app (𝟙_ _))
  simp only [Functor.comp_map] at n
  erw [reassoc_of% n]
  rfl

/-- The identification of section invariants along the identity is the identity: by
`AlgebraicGeometry.Etale.sectionInvariantEtaleIso_comp` it is an idempotent isomorphism. -/
theorem sectionInvariantEtaleIso_id [IsNoetherian V] [IsNoetherian B] (g : V ⟶ B)
    [HasCompactification g] [QuasiCompact g] [HasCompactification (𝟙 V)] (s : B ⟶ V) :
    sectionInvariantEtaleIso Λ (𝟙 V) g g (Category.id_comp g) s s (Category.comp_id s) =
      Iso.refl _ := by
  have : HasCompactification (𝟙 V ≫ 𝟙 V) := .of_eq (Category.id_comp _).symm
  have h := sectionInvariantEtaleIso_comp Λ (𝟙 V) (𝟙 V) g g g (Category.id_comp g)
    (Category.id_comp g) s s s (Category.comp_id s) (Category.comp_id s)
  rw [sectionInvariantEtaleIso_congr Λ (Category.id_comp (𝟙 V)) g g _ (Category.id_comp g) s s _
    (Category.comp_id s)] at h
  refine Iso.ext ?_
  have h' := congrArg Iso.hom h
  rw [Iso.trans_hom] at h'
  rw [← cancel_epi (sectionInvariantEtaleIso Λ (𝟙 V) g g (Category.id_comp g) s s
    (Category.comp_id s)).hom, Iso.refl_hom, Category.comp_id]
  exact h'.symm

end Coherence

end Etale

end AlgebraicGeometry
