/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q43
-/
module

public import Sheaf.Paper.BoundedConstructibleTower
public import Sheaf.AlgebraicGeometry.AmbientExceptionalRightAdjoint
public import Sheaf.AlgebraicGeometry.ProEtaleDirectImageRestrictionOfScalars
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RestrictScalars

/-!
# Compact-support direct image and finite coefficient restriction

Source: Bhatt--Scholze, Sections 6.5 and 6.7; Stacks Tags 03DI, 0D6E and 0D6J
(blueprint: lem-sf-compact-support-restriction-of-scalars).

All comparisons are normalized before choosing them: realization preserves sections,
extension by zero uses the adjunction unit, and derived direct image uses its
K-injective comparison. Thus the compactification and coefficient map enter the actual
functors and maps.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits

-- Lift the scalar and the section to a common cover to compare the two actions.
private theorem sheafify_restrict_smul
    {D : Type (u + 1)} [Category.{u} D] {J : GrothendieckTopology D}
    {R₀ S₀ : Dᵒᵖ ⥤ RingCat.{u + 1}} {R S : Sheaf J RingCat.{u + 1}}
    (α : R₀ ⟶ R.obj) (β : S₀ ⟶ S.obj)
    [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α]
    [Presheaf.IsLocallyInjective J β] [Presheaf.IsLocallySurjective J β]
    (γ : R₀ ⟶ S₀) (δ : R ⟶ S) (h : α ≫ δ.hom = γ ≫ β)
    (M : PresheafOfModules.{u + 1} R₀) (N : PresheafOfModules.{u + 1} S₀)
    (F G : Sheaf J AddCommGrpCat.{u + 1}) (η : M.presheaf ⟶ F.obj)
    (ζ : N.presheaf ⟶ G.obj)
    [Presheaf.IsLocallyInjective J η] [Presheaf.IsLocallySurjective J η]
    [Presheaf.IsLocallyInjective J ζ] [Presheaf.IsLocallySurjective J ζ]
    (τ : M.presheaf ⟶ N.presheaf) (f : F ⟶ G)
    (hτ : ∀ (U : Dᵒᵖ) (r : R₀.obj U) (x : M.obj U),
      τ.app U (r • x) = @SMul.smul _ (N.obj U) inferInstance (γ.app U r) (τ.app U x))
    (hf : η ≫ f.hom = τ ≫ ζ) (U : Dᵒᵖ) (r : R.obj.obj U) (x : F.obj.obj U) :
    f.hom.app U (PresheafOfModules.Sheafify.smul α η r x) =
      PresheafOfModules.Sheafify.smul β ζ (δ.hom.app U r) (f.hom.app U x) := by
  have hf' (V : Dᵒᵖ) (y : M.obj V) :
      f.hom.app V (η.app V y) = ζ.app V (τ.app V y) :=
    ConcreteCategory.congr_hom (NatTrans.congr_app hf V) y
  apply G.isSeparated _ _ (J.intersection_covering
    (Presheaf.imageSieve_mem J α r) (Presheaf.imageSieve_mem J η x))
  rintro V i ⟨⟨r₀, hr₀⟩, ⟨x₀, hx₀⟩⟩
  rw [← NatTrans.naturality_apply f.hom i.op,
    PresheafOfModules.Sheafify.map_smul_eq α η _ _ i.op r₀ hr₀ x₀ hx₀, hf']
  rw [PresheafOfModules.Sheafify.map_smul_eq β ζ _ _ i.op
    (γ.app _ r₀) (by
      have hh := ConcreteCategory.congr_hom (NatTrans.congr_app h (Opposite.op V)) r₀
      change δ.hom.app _ (α.app _ r₀) = β.app _ (γ.app _ r₀) at hh
      rw [← hh, hr₀]
      exact NatTrans.naturality_apply δ.hom i.op r) (τ.app _ x₀) (by
      rw [← hf', hx₀]
      exact NatTrans.naturality_apply f.hom i.op x)]
  exact congrArg (ζ.app _) (hτ _ r₀ x₀)

private theorem lift_module_iso
    {D : Type (u + 1)} [Category.{u} D] {J : GrothendieckTopology D}
    {R : Sheaf J RingCat.{u + 1}}
    {E : Type*} [Category* E] (F G : E ⥤ SheafOfModules.{u + 1} R)
    (e : F ⋙ SheafOfModules.toSheaf R ≅ G ⋙ SheafOfModules.toSheaf R)
    (he : ∀ (M : E) (U : Dᵒᵖ) (r : R.obj.obj U) (x : (F.obj M).val.obj U),
      (e.hom.app M).hom.app U (r • x) =
        @SMul.smul _ ((G.obj M).val.obj U) inferInstance r
          ((e.hom.app M).hom.app U x)) :
    ∃! i : F ≅ G, ∀ (M : E) (U : Dᵒᵖ) (x : (F.obj M).val.obj U),
      (i.hom.app M).val.app U x = (e.hom.app M).hom.app U x := by
  let η : F ⟶ G :=
    { app M := ⟨PresheafOfModules.homMk (e.hom.app M).hom (he M)⟩
      naturality := by
        intro M N f
        apply (SheafOfModules.toSheaf R).map_injective
        exact e.hom.naturality f }
  have hη (M : E) : (SheafOfModules.toSheaf R).map (η.app M) = e.hom.app M := by
    ext U x
    rfl
  have : IsIso η := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro M
    have : IsIso ((SheafOfModules.toSheaf R).map (η.app M)) := by
      rw [hη]
      infer_instance
    exact isIso_of_reflects_iso _ (SheafOfModules.toSheaf R)
  refine ⟨asIso η, ?_, ?_⟩
  · intro M U x
    rfl
  · intro i hi
    apply Iso.ext
    ext M U x
    exact hi M U x

private noncomputable abbrev moduleRealization
    {D : Type (u + 1)} [Category.{u} D] (J : GrothendieckTopology D)
    [HasWeakSheafify J AddCommGrpCat.{u + 1}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
    (Λ : Type (u + 1)) [Ring Λ] (R : Sheaf J RingCat.{u + 1})
    (α : (Functor.const Dᵒᵖ).obj (RingCat.of Λ) ⟶ R.obj)
    [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α] :=
  sheafToPresheaf J (ModuleCat.{u + 1} Λ) ⋙
    AlgebraicGeometry.ProEtale.finiteCoefficientModulePresheaf D Λ ⋙
    PresheafOfModules.sheafification α

private theorem realization_restrict_smul
    {D : Type (u + 1)} [Category.{u} D] (J : GrothendieckTopology D)
    [HasWeakSheafify J AddCommGrpCat.{u + 1}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
    {Λ₁ Λ₂ : Type (u + 1)} [CommRing Λ₁] [CommRing Λ₂]
    (R S : Sheaf J RingCat.{u + 1})
    (α : (Functor.const Dᵒᵖ).obj (RingCat.of Λ₁) ⟶ R.obj)
    (β : (Functor.const Dᵒᵖ).obj (RingCat.of Λ₂) ⟶ S.obj)
    [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α]
    [Presheaf.IsLocallyInjective J β] [Presheaf.IsLocallySurjective J β]
    (φ : Λ₁ →+* Λ₂) (δ : R ⟶ S)
    (hs : α ≫ δ.hom = (Functor.const Dᵒᵖ).map (RingCat.ofHom φ) ≫ β) :
    ∀ (M : Sheaf J (ModuleCat.{u + 1} Λ₂)) (U : Dᵒᵖ)
      (r : R.obj.obj U) (x : ((moduleRealization J Λ₂ S β).obj M).val.obj U),
      @SMul.smul _ (((SheafOfModules.restrictScalars.{u + 1} δ).obj
        ((moduleRealization J Λ₂ S β).obj M)).val.obj U) inferInstance r x =
      @SMul.smul _ (((moduleRealization J Λ₁ R α).obj
        ((sheafCompose J (ModuleCat.restrictScalars.{u + 1} φ)).obj M)).val.obj U)
        inferInstance r x := by
  intro M U r x
  let M₁ := (AlgebraicGeometry.ProEtale.finiteCoefficientModulePresheaf D Λ₁).obj
    ((sheafCompose J (ModuleCat.restrictScalars.{u + 1} φ)).obj M).obj
  let M₂ := (AlgebraicGeometry.ProEtale.finiteCoefficientModulePresheaf D Λ₂).obj M.obj
  exact (sheafify_restrict_smul α β ((Functor.const Dᵒᵖ).map (RingCat.ofHom φ)) δ hs
    M₁ M₂ ((presheafToSheaf J AddCommGrpCat.{u + 1}).obj M₁.presheaf)
    ((presheafToSheaf J AddCommGrpCat.{u + 1}).obj M₂.presheaf)
    (toSheafify J _) (toSheafify J _) (𝟙 _) (𝟙 _) (by intro V a y; rfl)
    (by simp only [Category.id_comp]; rfl) U r x).symm

private theorem realization_restrict_existsUnique
    {D : Type (u + 1)} [Category.{u} D] (J : GrothendieckTopology D)
    [HasWeakSheafify J AddCommGrpCat.{u + 1}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
    {Λ₁ Λ₂ : Type (u + 1)} [CommRing Λ₁] [CommRing Λ₂]
    (R S : Sheaf J RingCat.{u + 1})
    (α : (Functor.const Dᵒᵖ).obj (RingCat.of Λ₁) ⟶ R.obj)
    (β : (Functor.const Dᵒᵖ).obj (RingCat.of Λ₂) ⟶ S.obj)
    [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α]
    [Presheaf.IsLocallyInjective J β] [Presheaf.IsLocallySurjective J β]
    (φ : Λ₁ →+* Λ₂) (δ : R ⟶ S)
    (hs : α ≫ δ.hom = (Functor.const Dᵒᵖ).map (RingCat.ofHom φ) ≫ β) :
    ∃! e : moduleRealization J Λ₂ S β ⋙ SheafOfModules.restrictScalars.{u + 1} δ ≅
        sheafCompose J (ModuleCat.restrictScalars.{u + 1} φ) ⋙ moduleRealization J Λ₁ R α,
      ∀ (M : Sheaf J (ModuleCat.{u + 1} Λ₂)) (U : Dᵒᵖ)
        (x : ((moduleRealization J Λ₂ S β).obj M).val.obj U),
        (e.hom.app M).val.app U x = x := by
  exact lift_module_iso
    (moduleRealization J Λ₂ S β ⋙ SheafOfModules.restrictScalars.{u + 1} δ)
    (sheafCompose J (ModuleCat.restrictScalars.{u + 1} φ) ⋙ moduleRealization J Λ₁ R α)
    (NatIso.ofComponents (fun _ ↦ Iso.refl _) (by intro M N f; ext U x; rfl))
    (realization_restrict_smul J R S α β φ δ hs)

namespace AlgebraicGeometry.Scheme

variable {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
  [Finite A] [Finite B] [Finite C]

/-- Fixed scalar restriction on the pro-etale site. Source: Stacks Tag 03DA
(blueprint: lem-sf-compact-support-restriction-of-scalars). -/
noncomputable abbrev sfFixedRestriction (T : Scheme.{u}) (φ : A →+* B) :=
  sheafCompose (ProEt.topology T) (ModuleCat.restrictScalars.{u + 1} φ.ulift)

/-- Realization commutes with scalar restriction by the identity on the sheafified
underlying abelian presheaf. Source: Stacks Tags 00YV and 03DA
(blueprint: lem-sf-compact-support-restriction-of-scalars).
Proof: the two input abelian presheaves agree. Module sheafification has precisely
abelian sheafification as its underlying sheaf. The actions agree on constant scalar
sections by naturality of the coefficient unit and hence on all locally constant
sections. Identity is therefore linear and natural, and sectionwise identity is unique. -/
theorem sfRealizationRestriction_existsUnique (T : Scheme.{u}) (φ : A →+* B) :
    ∃! e : (sfIntrinsicModuleEquivalence T B).functor ⋙
        proEtaleCoefficientRestrictScalars T φ ≅
      sfFixedRestriction T φ ⋙ (sfIntrinsicModuleEquivalence T A).functor,
      ∀ (M : Sheaf (ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1, u} B)))
        (U : T.ProEtᵒᵖ)
        (x : (((sfIntrinsicModuleEquivalence T B).functor.obj M).val.obj U)),
        (e.hom.app M).val.app U x = x := by
  let φ' : ULift.{u + 1, u} A →+* ULift.{u + 1, u} B := φ.ulift
  let δ := (sheafCompose (ProEt.topology T)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
      ((constantSheaf (ProEt.topology T) CommRingCat.{u + 1}).map
        (CommRingCat.ofHom φ'))
  apply realization_restrict_existsUnique (ProEt.topology T) _ _
    (ProEtale.finiteCoefficientIntrinsicScalarMap T A)
    (ProEtale.finiteCoefficientIntrinsicScalarMap T B) φ' δ
  exact (congrArg (fun k ↦ Functor.whiskerRight k
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}))
      (toSheafify_naturality (ProEt.topology T)
        ((Functor.const T.ProEtᵒᵖ).map (CommRingCat.ofHom φ')))).symm

/-- The sectionwise normalized realization comparison. Source: Stacks Tag 00YV
(blueprint: lem-sf-compact-support-restriction-of-scalars). -/
noncomputable def sfRealizationRestriction (T : Scheme.{u}) (φ : A →+* B) :=
  (sfRealizationRestriction_existsUnique T φ).exists.choose

/-- The inverse-equivalence coefficient square, obtained by unit and counit from the
normalized realization square. Source: Stacks Tag 00YV
(blueprint: lem-sf-compact-support-restriction-of-scalars). -/
noncomputable def sfInverseRealizationRestriction (T : Scheme.{u}) (φ : A →+* B) :
    proEtaleCoefficientRestrictScalars T φ ⋙ (sfIntrinsicModuleEquivalence T A).inverse ≅
      (sfIntrinsicModuleEquivalence T B).inverse ⋙ sfFixedRestriction T φ :=
  Functor.isoWhiskerRight (sfIntrinsicModuleEquivalence T B).counitIso.symm
      (proEtaleCoefficientRestrictScalars T φ ⋙ (sfIntrinsicModuleEquivalence T A).inverse) ≪≫
    Functor.isoWhiskerLeft (sfIntrinsicModuleEquivalence T B).inverse
      (Functor.isoWhiskerRight (sfRealizationRestriction T φ)
        (sfIntrinsicModuleEquivalence T A).inverse) ≪≫
    Functor.isoWhiskerLeft
      ((sfIntrinsicModuleEquivalence T B).inverse ⋙ sfFixedRestriction T φ)
      (sfIntrinsicModuleEquivalence T A).unitIso.symm

/-- Fixed-scalar extension by zero commutes with restriction: both sides are left
adjoint to the same objectwise composite of open restriction and coextension.
The left-adjoint uniqueness map is normalized by the adjunction units.
Source: Stacks Tag 03DI (blueprint: lem-sf-compact-support-restriction-of-scalars). -/
noncomputable def sfFixedOpenRestriction {X Z : Scheme.{u}} (j : X ⟶ Z)
    [IsOpenImmersion j] (φ : A →+* B) :
    sfFixedRestriction X φ ⋙
        ProEtale.openImmersionLowerShriek (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j ≅
      ProEtale.openImmersionLowerShriek (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) j ⋙
        sfFixedRestriction Z φ :=
  ((Sheaf.restrictCoextendScalarsAdj (ProEt.topology X) φ.ulift).comp
      (ProEtale.openImmersionLowerShriekAdjunction
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j)).leftAdjointUniq
    ((ProEtale.openImmersionLowerShriekAdjunction
      (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) j).comp
      (Sheaf.restrictCoextendScalarsAdj (ProEt.topology Z) φ.ulift))

/-- The intrinsic extension-by-zero coefficient square, transported by the canonical
realization equivalences. Source: Stacks Tags 03DI and 00YV
(blueprint: lem-sf-compact-support-restriction-of-scalars). -/
noncomputable def sfOpenRestriction {X Z : Scheme.{u}} (j : X ⟶ Z)
    [IsOpenImmersion j] (φ : A →+* B) :
    proEtaleCoefficientRestrictScalars X φ ⋙ sfIntrinsicExtensionByZero j A ≅
      sfIntrinsicExtensionByZero j B ⋙ proEtaleCoefficientRestrictScalars Z φ :=
  Functor.isoWhiskerRight (sfInverseRealizationRestriction X φ)
      (ProEtale.openImmersionLowerShriek (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j ⋙
        (sfIntrinsicModuleEquivalence Z A).functor) ≪≫
    Functor.isoWhiskerLeft (sfIntrinsicModuleEquivalence X B).inverse
      (Functor.isoWhiskerRight (sfFixedOpenRestriction j φ)
        (sfIntrinsicModuleEquivalence Z A).functor) ≪≫
    Functor.isoWhiskerLeft
      ((sfIntrinsicModuleEquivalence X B).inverse ⋙
        ProEtale.openImmersionLowerShriek (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) j)
      (sfRealizationRestriction Z φ).symm

/-- Derived direct-image coefficient comparison selected with the full K-injective
normalization of the recorded direct-image theorem. That normalization determines the
natural isomorphism on every K-injective representative and hence after localization.
Source: Stacks Tags 0D6E and 0D6J
(blueprint: lem-sf-compact-support-restriction-of-scalars). -/
noncomputable def sfDerivedImageRestriction {Z Y : Scheme.{u}} (g : Z ⟶ Y)
    (φ : A →+* B) :
    (proEtaleCoefficientRestrictScalars Z φ).mapDerivedCategory ⋙
        proEtaleConstantDerivedDirectImage g A ≅
      proEtaleConstantDerivedDirectImage g B ⋙
        (proEtaleCoefficientRestrictScalars Y φ).mapDerivedCategory :=
  (proEtaleDerivedDirectImage_restrictScalars g φ).choose

/-- The specified compact-support comparison is the extension-by-zero square followed
by the direct-image square, with no change of compactification. Source: Bhatt--Scholze,
Lemma 6.7.7; Stacks Tags 03DI and 0D6E
(blueprint: lem-sf-compact-support-restriction-of-scalars). -/
noncomputable def sfCompactSupportRestriction {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) (φ : A →+* B) :
    (proEtaleCoefficientRestrictScalars X φ).mapDerivedCategory ⋙
        sfAmbientCompactSupportCandidate A c ≅
      sfAmbientCompactSupportCandidate B c ⋙
        (proEtaleCoefficientRestrictScalars Y φ).mapDerivedCategory :=
  Functor.isoWhiskerRight (Functor.mapDerivedCategorySquareIso (sfOpenRestriction c.i φ))
      (proEtaleConstantDerivedDirectImage c.g A) ≪≫
    Functor.isoWhiskerLeft (sfIntrinsicExtensionByZero c.i B).mapDerivedCategory
      (sfDerivedImageRestriction c.g φ)

/-- The normalized scalar-restriction composition map, using the shared sectionwise
identity comparison for commutative ring sheaves. Source: Stacks Tag 03DA
(blueprint: lem-sf-compact-support-restriction-of-scalars). -/
noncomputable def sfCoefficientRestrictionComp (T : Scheme.{u})
    (φ : A →+* B) (ψ : B →+* C) :
    proEtaleCoefficientRestrictScalars T ψ ⋙ proEtaleCoefficientRestrictScalars T φ ≅
      proEtaleCoefficientRestrictScalars T (ψ.comp φ) :=
  pbcRestrictComp
    ((constantSheaf (ProEt.topology T) CommRingCat.{u + 1}).map
      (CommRingCat.ofHom φ.ulift))
    ((constantSheaf (ProEt.topology T) CommRingCat.{u + 1}).map
      (CommRingCat.ofHom ψ.ulift))
    ((constantSheaf (ProEt.topology T) CommRingCat.{u + 1}).map
      (CommRingCat.ofHom (ψ.comp φ).ulift))
    ((constantSheaf (ProEt.topology T) CommRingCat.{u + 1}).map_comp _ _).symm

/-- The termwise derived scalar composition map. Source: Stacks Tag 015F
(blueprint: lem-sf-compact-support-restriction-of-scalars). -/
noncomputable def sfDerivedCoefficientRestrictionComp (T : Scheme.{u})
    (φ : A →+* B) (ψ : B →+* C) :=
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso (sfCoefficientRestrictionComp T φ ψ)

/-- The compact-support coefficient comparisons compose for composable ring maps.
The comparison itself is defined above as precisely the extension-by-zero comparison
followed by the ordinary derived direct-image comparison.
Source: Bhatt--Scholze, Sections 6.5 and 6.7; Stacks Tags 03DI, 0D6E and 0D6J
(blueprint: lem-sf-compact-support-restriction-of-scalars).
Proof: the sectionwise realization and restriction composition maps preserve constant
scalars. Uniqueness of the left-adjoint comparison gives the composition identity for
extension by zero. For direct image, compute on a K-injective representative and a
K-injective resolution after restriction; both composites are the same comparison of
the two ringed-topos factorizations. Uniqueness of the normalized derived comparison
and its naturality give the identity on all derived objects. Whiskering these two
identities proves the displayed compatibility for their compact-support composite. -/
theorem sfCompactSupportRestriction_comp
    (l : ℕ) [Fact l.Prime] {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (_hl : ∀ y : Y, IsUnit (l : Y.presheaf.stalk y))
    (c : Compactification f) (φ : A →+* B) (ψ : B →+* C)
    (K : proEtaleDerivedCategory X C) :
    (sfAmbientCompactSupportCandidate A c).map
        ((sfDerivedCoefficientRestrictionComp X φ ψ).hom.app K) ≫
      (sfCompactSupportRestriction c (ψ.comp φ)).hom.app K =
    (sfCompactSupportRestriction c φ).hom.app
        ((proEtaleCoefficientRestrictScalars X ψ).mapDerivedCategory.obj K) ≫
      (proEtaleCoefficientRestrictScalars Y φ).mapDerivedCategory.map
        ((sfCompactSupportRestriction c ψ).hom.app K) ≫
      (sfDerivedCoefficientRestrictionComp Y φ ψ).hom.app
        ((sfAmbientCompactSupportCandidate C c).obj K) := by
  sorry

end AlgebraicGeometry.Scheme
