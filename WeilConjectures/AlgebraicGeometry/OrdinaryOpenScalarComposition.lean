/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CompactSupportStrictScalarMate
import all WeilConjectures.SecSmoothPurity.ProEtaleOpenScalarCocycle
import Mathlib.CategoryTheory.Adjunction.CompositionIso
import WeilConjectures.AlgebraicGeometry.IntegralCompactSupportCoefficientComparison
import all WeilConjectures.AlgebraicGeometry.ConstantCompletedScalarAssociativity
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp

/-! # Ordinary open tensor balancing and coefficient composition

Source: Stacks 0E8I and 07A6; strict scalar composition, auxiliary Step 4.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open Opposite AlgebraicGeometry.ProEtale.StrictTower
namespace WeilConjectures.PurStrictScalar


private theorem scalarComposition_diagram
    {D₀ D₁ D₂ C₀ C₁ C₂ : Type*}
    [Category D₀] [Category D₁] [Category D₂]
    [Category C₀] [Category C₁] [Category C₂]
    {U₀ : D₀ ⥤ C₀} {U₁ : D₁ ⥤ C₁} {U₂ : D₂ ⥤ C₂}
    {A₁₀ : D₀ ⥤ D₁} {A₂₁ : D₁ ⥤ D₂} {A₂₀ : D₀ ⥤ D₂}
    {B₁₀ : C₀ ⥤ C₁} {B₂₁ : C₁ ⥤ C₂} {B₂₀ : C₀ ⥤ C₂}
    (χ₁₀ : U₀ ⋙ B₁₀ ≅ A₁₀ ⋙ U₁) (χ₂₁ : U₁ ⋙ B₂₁ ≅ A₂₁ ⋙ U₂)
    (χ₂₀ : U₀ ⋙ B₂₀ ≅ A₂₀ ⋙ U₂)
    (αA : A₁₀ ⋙ A₂₁ ≅ A₂₀) (αB : B₁₀ ⋙ B₂₁ ≅ B₂₀)
    {K : D₀} {N₁ : D₁} {N₂' N₂ : D₂}
    (a₁₀ : A₁₀.obj K ⟶ N₁) (a₂₁ : A₂₁.obj N₁ ⟶ N₂')
    (a₂₀ : A₂₀.obj K ⟶ N₂) (b : N₂' ⟶ N₂)
    {T₀ : C₀} {T₁ : C₁} {T₂' T₂ : C₂}
    (v₀ : U₀.obj K ⟶ T₀) (v₁ : U₁.obj N₁ ⟶ T₁)
    (v₂' : U₂.obj N₂' ⟶ T₂') (v₂ : U₂.obj N₂ ⟶ T₂) [Mono v₂]
    (t₁₀ : B₁₀.obj T₀ ⟶ T₁) (t₂₁ : B₂₁.obj T₁ ⟶ T₂')
    (t₂₀ : B₂₀.obj T₀ ⟶ T₂) (w : T₂' ⟶ T₂)
    (hχ : B₂₁.map (χ₁₀.hom.app K) ≫ χ₂₁.hom.app (A₁₀.obj K) ≫
      U₂.map (αA.hom.app K) = αB.hom.app (U₀.obj K) ≫ χ₂₀.hom.app K)
    (h₁₀ : χ₁₀.hom.app K ≫ U₁.map a₁₀ ≫ v₁ = B₁₀.map v₀ ≫ t₁₀)
    (h₂₁ : χ₂₁.hom.app N₁ ≫ U₂.map a₂₁ ≫ v₂' = B₂₁.map v₁ ≫ t₂₁)
    (h₂₀ : χ₂₀.hom.app K ≫ U₂.map a₂₀ ≫ v₂ = B₂₀.map v₀ ≫ t₂₀)
    (hb : U₂.map b ≫ v₂ = v₂' ≫ w)
    (ht : αB.hom.app T₀ ≫ t₂₀ = B₂₁.map t₁₀ ≫ t₂₁ ≫ w) :
    U₂.map (αA.hom.app K ≫ a₂₀) = U₂.map (A₂₁.map a₁₀ ≫ a₂₁ ≫ b) := by
  apply (cancel_epi (B₂₁.map (χ₁₀.hom.app K) ≫ χ₂₁.hom.app (A₁₀.obj K))).mp
  apply (cancel_mono v₂).mp
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% hχ, h₂₀]
  rw [← reassoc_of% χ₂₁.hom.naturality a₁₀, hb, reassoc_of% h₂₁]
  have hmap := congrArg B₂₁.map h₁₀
  simp only [Functor.map_comp] at hmap
  rw [reassoc_of% hmap, ← reassoc_of% αB.hom.naturality v₀]
  exact congrArg (fun a ↦ B₂₁.map (B₁₀.map v₀) ≫ a) ht

private theorem ordinaryOpenTensor_eq
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (F : Type u) [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
    (i : E →ₐ[ℚ_[l]] F) {Z W : Scheme.{u}} (g : Z ⟶ W) [IsOpenImmersion g] :
    ordinaryOpenTensor l E F i g =
      (Functor.whiskeringRight ℕᵒᵖ _ _).map
        (ordinaryBaseOpenTensor (change l E F i) g) := by
  ext M n
  rfl

attribute [local irreducible] pbcScalarAdjunction proEtaleRingModulePullback
  PurCompactSupport.openAdjunction proEtaleRingRestrictionPullbackInv
  CategoryTheory.Functor.mapDerivedCategory CategoryTheory.Functor.rightDerivedFunctor

private theorem derivedRestriction_left_unit
    {A : Type*} [Category A] [Abelian A] [HasDerivedCategory A]
    (U : A ⥤ A) [U.Additive] [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    (ρ : U ≅ 𝟭 A) :
    (Functor.mapDerivedCategoryCompIso U U).symm ≪≫
        Functor.mapDerivedCategoryNatIso (Functor.isoWhiskerLeft U ρ) =
      Functor.isoWhiskerLeft U.mapDerivedCategory
          (Functor.mapDerivedCategoryNatIso ρ ≪≫ Functor.mapDerivedCategoryIdIso A) ≪≫
        Functor.rightUnitor U.mapDerivedCategory := by
  apply Iso.ext
  ext X
  have hn := congr_app (Functor.mapDerivedCategoryNatIso_isoWhiskerLeft U ρ) X
  have hu := congr_app (Functor.mapDerivedCategoryCompIso_comp_id U) X
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app] at hn hu
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Functor.rightUnitor_hom_app]
  apply (cancel_epi ((Functor.mapDerivedCategoryCompIso U U).hom.app X)).mp
  rw [Iso.hom_inv_id_app_assoc]
  simp only [← Category.assoc]
  rw [← hn]
  simp only [Category.assoc]
  simp only [NatTrans.id_app] at hu
  rw [reassoc_of% hu]
  erw [Category.comp_id, Category.comp_id]

private theorem identityConjugate {A : Type*} [Category A]
    {F U : A ⥤ A} (a : F ⊣ U) (e : U ≅ 𝟭 A) :
    a.leftAdjointIdIso e = ((conjugateIsoEquiv a Adjunction.id).symm e).symm := by
  rfl

private theorem normalizedComparison_eq
    {A B C : Type*} [Category A] [Category B] [Category C]
    {F : A ⥤ B} {G : B ⥤ C} {H : A ⥤ C}
    {U : B ⥤ A} {V : C ⥤ B} {W : C ⥤ A}
    (a : F ⊣ U) (b : G ⊣ V) (c : H ⊣ W) (d : V ⋙ U ≅ W) :
    ((a.comp b).ofNatIsoRight d).leftAdjointUniq c =
      a.leftAdjointCompIso b c d := by
  apply Iso.ext
  apply NatTrans.ext
  funext X
  simp only [Adjunction.leftAdjointUniq, Iso.symm_hom,
    conjugateIsoEquiv_symm_apply_inv, Iso.refl_inv, Adjunction.leftAdjointCompIso,
    conjugateIsoEquiv_symm_apply_hom, Iso.symm_hom, conjugateEquiv_symm_apply_app,
    Adjunction.ofNatIsoRight_counit, NatTrans.id_app, NatTrans.comp_app,
    Functor.whiskerRight_app]
  rw [(F ⋙ G).map_id, Category.id_comp]

private theorem ordinaryOpen_conjugate
    {R S : PurCompactSupport.Coefficients.{u}} (a : PurCompactSupport.Change R S)
    {Z W : Scheme.{u}} (g : Z ⟶ W) [IsOpenImmersion g] :
    conjugateEquiv
      ((PurCompactSupport.openAdjunction R g).comp (pbcScalarAdjunction (a.map W)))
      ((pbcScalarAdjunction (a.map Z)).comp (PurCompactSupport.openAdjunction S g))
      (@asIso _ _ _ _ (ordinaryBaseOpenTensor a g)
        (ordinaryBaseOpenTensor_isIso a g)).inv =
      proEtaleRingRestrictionPullbackInv g (R.ring W) (S.ring W)
        (R.ring Z) (S.ring Z) (a.map W) (a.map Z) (R.pull g) (S.pull g)
          (a.square g) := by
  have := proEtaleRingRestrictionPullbackInv_isIso g (R.ring W) (S.ring W)
    (R.ring Z) (S.ring Z) (a.map W) (a.map Z) (R.pull g) (S.pull g) (a.square g)
  let δ := asIso (proEtaleRingRestrictionPullbackInv g (R.ring W) (S.ring W)
    (R.ring Z) (S.ring Z) (a.map W) (a.map Z) (R.pull g) (S.pull g) (a.square g))
  let e := ((conjugateIsoEquiv
    ((PurCompactSupport.openAdjunction R g).comp (pbcScalarAdjunction (a.map W)))
    ((pbcScalarAdjunction (a.map Z)).comp (PurCompactSupport.openAdjunction S g))).symm δ)
  have he : @asIso _ _ _ _ (ordinaryBaseOpenTensor a g)
      (ordinaryBaseOpenTensor_isIso a g) = e.symm := by
    apply Iso.ext
    change ordinaryBaseOpenTensor a g = e.symm.hom
    unfold ordinaryBaseOpenTensor PurCompactSupport.openRestrictionMap
    rw [iterated_mateEquiv_conjugateEquiv_symm]
    simp only [Equiv.trans_apply, TwoSquare.equivNatTrans, e, Iso.symm_hom,
      conjugateIsoEquiv_symm_apply_inv]
    rfl
  rw [he]
  change (conjugateIsoEquiv _ _ e).hom = δ.hom
  exact congrArg Iso.hom ((conjugateIsoEquiv _ _).apply_symm_apply δ)

open AlgebraicGeometry.ProEtale in
private theorem ordinaryComparison_composition
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (φ : A →+* B) (ψ : B →+* C) {Z W : Scheme.{u}} (g : Z ⟶ W)
    (N : proEtaleRingModules W (proEtaleConstantRing W C)) :
    let ρ (V : Scheme.{u}) := pbcRestrictComp _ _ _
      (scalarExtensionFunctor_ringMap_comp φ ψ V)
    (ordinaryRestrictionComparison φ g).app ((ordinaryScalarRestriction ψ W).obj N) ≫
        (ordinaryScalarRestriction φ Z).map ((ordinaryRestrictionComparison ψ g).app N) ≫
        (ρ Z).hom.app ((ordinaryConstantPullback C g).obj N) =
      (ordinaryConstantPullback A g).map ((ρ W).hom.app N) ≫
        (ordinaryRestrictionComparison (ψ.comp φ) g).app N := by
  dsimp only
  let ρ (V : Scheme.{u}) := pbcRestrictComp _ _ _
    (scalarExtensionFunctor_ringMap_comp φ ψ V)
  let P := ordinaryConstantPullback A g
  have h := congrArg (fun t ↦ P.map ((ρ W).hom.app N) ≫ t ≫
      (ρ Z).hom.app ((ordinaryConstantPullback C g).obj N))
    (ordinaryCoefficientComp φ ψ g N)
  simp only [Category.assoc] at h
  change P.map _ ≫ P.map _ ≫ _ = _ at h
  erw [← Functor.map_comp_assoc, Iso.hom_inv_id_app, CategoryTheory.Functor.map_id,
    Category.id_comp] at h
  erw [Iso.inv_hom_id_app] at h
  erw [Category.comp_id] at h
  exact h

/-- Ordinary open balancing respects the normalized scalar associator.
Source: Stacks 0E8I and 07A6; auxiliary Step 4 of
lem-pur-compact-support-strict-scalar-composition.
(blueprint: lem-pur-ordinary-open-scalar-composition).

Proof: the ordinary restriction/pullback comparisons satisfy the coefficient
cocycle (the ordinaryCoefficientComp helper of ProEtaleOpenScalarCocycle).
Cancel its inverse restriction associators using their forward isomorphisms.
The iterated-mate identity identifies the inverse of each ordinary open
comparison with the conjugate of the corresponding restriction/pullback map.
Expanding left-adjoint uniqueness identifies the prescribed scalar associator
with leftAdjointCompIso, whose inverse conjugates to the restriction compositor.
The normalizedCocycle helper applies to these five conjugate identities and
the forward right-hand cocycle, giving exactly the displayed equality.
No nonzero, nonempty, flatness or torsion hypothesis is used in this ordinary
calculation, so it includes zero modules, empty opens and identity embeddings. -/
theorem ordinaryBaseOpenTensor_composition
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (F : Type u) [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
    (i : E →ₐ[ℚ_[l]] F)
    (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (j : F →ₐ[ℚ_[l]] L) {Z W : Scheme.{u}} (g : Z ⟶ W) [IsOpenImmersion g]
    (M : pbcModules Z ((constants l E).ring Z)) :
    let α (V : Scheme.{u}) :=
      (((pbcScalarAdjunction (constantMap l E F i V)).comp
          (pbcScalarAdjunction (constantMap l F L j V))).ofNatIsoRight
        (pbcRestrictComp _ _ _ (by
          unfold constantMap
          rw [← Functor.map_comp]
          congr 1))).leftAdjointUniq
            (pbcScalarAdjunction (constantMap l E L (j.comp i) V))
    (α W).hom.app ((PurCompactSupport.openExtension (constants l E) g).obj M) ≫
        (ordinaryBaseOpenTensor (change l E L (j.comp i)) g).app M =
      (pbcExtend (constantMap l F L j W)).map
          ((ordinaryBaseOpenTensor (change l E F i) g).app M) ≫
        (ordinaryBaseOpenTensor (change l F L j) g).app
          ((pbcExtend (constantMap l E F i Z)).obj M) ≫
        (PurCompactSupport.openExtension (constants l L) g).map ((α Z).hom.app M) := by
  dsimp only
  let φ := integralScalarIntegerInclusion l E F i
  let ψ := integralScalarIntegerInclusion l F L j
  let α (V : Scheme.{u}) :=
    (((pbcScalarAdjunction (constantMap l E F i V)).comp
        (pbcScalarAdjunction (constantMap l F L j V))).ofNatIsoRight
      (pbcRestrictComp _ _ _ (by
        unfold constantMap
        rw [← Functor.map_comp]
        congr 1))).leftAdjointUniq
          (pbcScalarAdjunction (constantMap l E L (j.comp i) V))
  let ρ (V : Scheme.{u}) := pbcRestrictComp
    (constantMap l E F i V) (constantMap l F L j V)
    (constantMap l E L (j.comp i) V) (by
      unfold constantMap
      rw [← Functor.map_comp]
      congr 1)
  have hα (V : Scheme.{u}) :
      conjugateEquiv
        ((pbcScalarAdjunction (constantMap l E F i V)).comp
          (pbcScalarAdjunction (constantMap l F L j V)))
        (pbcScalarAdjunction (constantMap l E L (j.comp i) V))
        (α V).inv = (ρ V).hom := by
    dsimp only [α]
    rw [normalizedComparison_eq]
    exact Adjunction.conjugateEquiv_leftAdjointCompIso_inv _ _ _ _
  have hχ (N : pbcModules W ((constants l L).ring W)) :
      (AlgebraicGeometry.ProEtale.ordinaryRestrictionComparison φ g).app
          ((pbcRestrict (constantMap l F L j W)).obj N) ≫
        (pbcRestrict (constantMap l E F i Z)).map
          ((AlgebraicGeometry.ProEtale.ordinaryRestrictionComparison ψ g).app N) ≫
        (ρ Z).hom.app
          ((proEtaleRingModulePullback g ((constants l L).ring W)
            ((constants l L).ring Z) ((constants l L).pull g)).obj N) =
      (proEtaleRingModulePullback g ((constants l E).ring W)
        ((constants l E).ring Z) ((constants l E).pull g)).map ((ρ W).hom.app N) ≫
        (AlgebraicGeometry.ProEtale.ordinaryRestrictionComparison (ψ.comp φ) g).app N := by
    exact ordinaryComparison_composition φ ψ g N
  have h := AlgebraicGeometry.ProEtale.normalizedCocycle
    (PurCompactSupport.openAdjunction (constants l E) g)
    (PurCompactSupport.openAdjunction (constants l F) g)
    (PurCompactSupport.openAdjunction (constants l L) g)
    (pbcScalarAdjunction (constantMap l E F i Z))
    (pbcScalarAdjunction (constantMap l E F i W))
    (pbcScalarAdjunction (constantMap l F L j Z))
    (pbcScalarAdjunction (constantMap l F L j W))
    (pbcScalarAdjunction (constantMap l E L (j.comp i) Z))
    (pbcScalarAdjunction (constantMap l E L (j.comp i) W))
    (@asIso _ _ _ _ (ordinaryBaseOpenTensor (change l E F i) g)
      (ordinaryBaseOpenTensor_isIso _ _))
    (@asIso _ _ _ _ (ordinaryBaseOpenTensor (change l F L j) g)
      (ordinaryBaseOpenTensor_isIso _ _))
    (@asIso _ _ _ _ (ordinaryBaseOpenTensor (change l E L (j.comp i)) g)
      (ordinaryBaseOpenTensor_isIso _ _)) (α Z) (α W)
    (@asIso _ _ _ _
      (AlgebraicGeometry.ProEtale.ordinaryRestrictionComparison φ g)
      (AlgebraicGeometry.ProEtale.ordinaryComparisonIsIso φ g))
    (@asIso _ _ _ _
      (AlgebraicGeometry.ProEtale.ordinaryRestrictionComparison ψ g)
      (AlgebraicGeometry.ProEtale.ordinaryComparisonIsIso ψ g))
    (@asIso _ _ _ _
      (AlgebraicGeometry.ProEtale.ordinaryRestrictionComparison (ψ.comp φ) g)
      (AlgebraicGeometry.ProEtale.ordinaryComparisonIsIso (ψ.comp φ) g))
    (ρ Z) (ρ W)
    (ordinaryOpen_conjugate (change l E F i) g)
    (ordinaryOpen_conjugate (change l F L j) g)
    (ordinaryOpen_conjugate (change l E L (j.comp i)) g)
    (hα Z) (hα W) hχ M
  exact h

attribute [local irreducible] reductionChange reductionDerivedChange
  pbcDerivedScalarAdjunction PurCompactSupport.tensorComposition
  PurCompactSupport.tensorIdentity

private theorem tensorComposition_identity_left {W : Scheme.{u}}
    (R : Sheaf (ProEt.topology W) CommRingCat.{u + 1})
    (K : DerivedCategory (pbcModules W R)) :
    (PurCompactSupport.tensorComposition (𝟙 R) (𝟙 R) (𝟙 R)
      (Category.id_comp _)).hom.app K =
      (pbcDerivedExtend (𝟙 R)).map ((PurCompactSupport.tensorIdentity R).hom.app K) := by
  let ρ := (PurCompactSupport.restrictIdentity_existsUnique R).exists.choose
  let δ := Functor.mapDerivedCategoryNatIso ρ ≪≫ Functor.mapDerivedCategoryIdIso _
  have he : pbcRestrictComp (𝟙 R) (𝟙 R) (𝟙 R) (Category.id_comp _) =
      Functor.isoWhiskerLeft (pbcRestrict (𝟙 R)) ρ := by
    apply Iso.ext
    ext M U x
    exact (pbcRestrictComp_exists (𝟙 R) (𝟙 R) (𝟙 R)
      (Category.id_comp _)).exists.choose_spec M U x |>.trans
        ((PurCompactSupport.restrictIdentity_existsUnique R).exists.choose_spec M U x).symm
  have hd : pbcDerivedRestrictComp (𝟙 R) (𝟙 R) (𝟙 R) (Category.id_comp _) =
      Functor.isoWhiskerLeft (pbcDerivedRestrict (𝟙 R)) δ ≪≫
        Functor.rightUnitor (pbcDerivedRestrict (𝟙 R)) := by
    unfold pbcDerivedRestrictComp
    rw [he]
    exact derivedRestriction_left_unit (pbcRestrict (𝟙 R)) ρ
  have h := congrArg (fun e ↦ e.hom.app K)
    (Adjunction.leftAdjointCompIso_id_comp (pbcDerivedScalarAdjunction (𝟙 R))
      (pbcDerivedScalarAdjunction (𝟙 R)) _ δ hd)
  have hn := normalizedComparison_eq (pbcDerivedScalarAdjunction (𝟙 R))
    (pbcDerivedScalarAdjunction (𝟙 R)) (pbcDerivedScalarAdjunction (𝟙 R))
    (pbcDerivedRestrictComp (𝟙 R) (𝟙 R) (𝟙 R) (Category.id_comp _))
  unfold PurCompactSupport.tensorComposition
  change ((((pbcDerivedScalarAdjunction (𝟙 R)).comp
    (pbcDerivedScalarAdjunction (𝟙 R))).ofNatIsoRight
      (pbcDerivedRestrictComp (𝟙 R) (𝟙 R) (𝟙 R) (Category.id_comp _))).leftAdjointUniq
        (pbcDerivedScalarAdjunction (𝟙 R))).hom.app K = _
  rw [hn]
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Functor.leftUnitor_hom_app] at h
  erw [Category.comp_id] at h
  have hu : (pbcDerivedScalarAdjunction (𝟙 R)).leftAdjointIdIso δ =
      PurCompactSupport.tensorIdentity R := by
    unfold PurCompactSupport.tensorIdentity
    exact identityConjugate _ _
  rw [hu] at h
  exact h

private theorem tensorComposition_identity_left_of_eq {W : Scheme.{u}}
    (R : Sheaf (ProEt.topology W) CommRingCat.{u + 1}) (a : R ⟶ R)
    (ha : a = 𝟙 R) (hc : a ≫ a = a) (K : DerivedCategory (pbcModules W R)) :
    (PurCompactSupport.tensorComposition a a a hc).hom.app K =
      (pbcDerivedExtend a).map
        ((eqToIso (congrArg (fun a ↦ pbcDerivedExtend a) ha) ≪≫
          PurCompactSupport.tensorIdentity R).hom.app K) := by
  cases ha
  rw [eqToIso_refl, Iso.refl_trans]
  exact tensorComposition_identity_left R K

private theorem tensorComposition_identity_iso_of_eq {W : Scheme.{u}}
    (R : Sheaf (ProEt.topology W) CommRingCat.{u + 1}) (a : R ⟶ R)
    (ha : a = 𝟙 R) (hc : a ≫ a = a) :
    PurCompactSupport.tensorComposition a a a hc =
      Functor.isoWhiskerRight
          (eqToIso (congrArg (fun a ↦ pbcDerivedExtend a) ha) ≪≫
            PurCompactSupport.tensorIdentity R) (pbcDerivedExtend a) ≪≫
        Functor.leftUnitor (pbcDerivedExtend a) := by
  apply Iso.ext
  ext K
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Functor.leftUnitor_hom_app]
  erw [Category.comp_id]
  exact tensorComposition_identity_left_of_eq R a ha hc K

/-- An invertible comparison satisfying its identity-composition and naturality
squares preserves the tensor units. The calculation needs only morphisms in the
target category and its scalar-extension functor; it does not unfold support or
convert the source and target functor presentations. -/
private theorem target_unit_of_composition
    {B : Type*} [Category B] (T : B ⥤ B) (v : T ≅ 𝟭 B)
    {A B₁ C₁ : B} (γ : T.obj A ⟶ B₁) [IsIso γ]
    (δ : T.obj B₁ ⟶ C₁) (x : B₁ ⟶ A) (z z' : C₁ ⟶ B₁)
    (ay : T.obj (T.obj A) ⟶ T.obj A)
    (hy : ay = T.map (v.hom.app A)) (hz : z = z')
    (hc : ay ≫ γ = T.map γ ≫ δ ≫ z)
    (hn : T.map x ≫ γ = δ ≫ z') :
    γ ≫ x = v.hom.app A := by
  have : T.Faithful := Functor.Faithful.of_iso v.symm
  apply T.map_injective
  apply (cancel_mono γ).mp
  rw [hy, hz, ← hn] at hc
  simpa only [Functor.map_comp, Category.assoc] using hc.symm


section LocalizationHelpers
variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (F : Type u) [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
  (i : E →ₐ[ℚ_[l]] F)
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (j : F →ₐ[ℚ_[l]] L)


private def localizedTensorAssociator (V : Scheme.{u})
    (α : tensor l E F i V ⋙ tensor l F L j V ≅ tensor l E L (j.comp i) V) :
    T l E F i V ⋙ T l F L j V ≅ T l E L (j.comp i) V :=
  haveI := (tensor_exact l E F i V).1
  haveI := (tensor_exact l E F i V).2
  haveI := (tensor_exact l F L j V).1
  haveI := (tensor_exact l F L j V).2
  haveI := (tensor_exact l E L (j.comp i) V).1
  haveI := (tensor_exact l E L (j.comp i) V).2
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫ Functor.mapDerivedCategoryNatIso α

private theorem localizedOpenTensor_composition {Z W : Scheme.{u}}
    (g : Z ⟶ W) [IsOpenImmersion g]
    (αZ : tensor l E F i Z ⋙ tensor l F L j Z ≅ tensor l E L (j.comp i) Z)
    (αW : tensor l E F i W ⋙ tensor l F L j W ≅ tensor l E L (j.comp i) W)
    (hordinary : ∀ N : Towers
        (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) Z,
      (tensor l F L j W).map ((ordinaryOpenTensor l E F i g).app N) ≫
          (ordinaryOpenTensor l F L j g).app ((tensor l E F i Z).obj N) ≫
          (towerJ (ULift.{u + 1} (Padic.coefficientExtensionIntegers l L)) g).map
            (αZ.hom.app N) =
        αW.hom.app
            ((towerJ (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) g).obj N) ≫
          (ordinaryOpenTensor l E L (j.comp i) g).app N)
    (K : Derived (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) Z) :
    (localizedTensorAssociator l E F i L j W αW).hom.app
          ((J (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) g).obj K) ≫
        (openTensor l E L (j.comp i) g).app K =
      (T l F L j W).map ((openTensor l E F i g).app K) ≫
        (openTensor l F L j g).app ((T l E F i Z).obj K) ≫
        (J (ULift.{u + 1} (Padic.coefficientExtensionIntegers l L)) g).map
          ((localizedTensorAssociator l E F i L j Z αZ).hom.app K) := by
  have := ordinaryOpenTensor_isIso l E F i g
  have := ordinaryOpenTensor_isIso l F L j g
  have := ordinaryOpenTensor_isIso l E L (j.comp i) g
  have h := localize_scalar_square
    (asIso (ordinaryOpenTensor l E F i g))
    (asIso (ordinaryOpenTensor l F L j g))
    (asIso (ordinaryOpenTensor l E L (j.comp i) g)) αZ αW hordinary K
  simpa only [localizedTensorAssociator, T, J, openTensor_ordinary] using h.symm

private def localizedSelectionAssociator (W : Scheme.{u}) (e h : ℕ)
    (H : ordinarySubsequence l L W h ⋙ ordinarySubsequence l L W e =
      ordinarySubsequence l L W (h * e)) :
    subsequence l L W h ⋙ subsequence l L W e ≅ subsequence l L W (h * e) :=
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso (eqToIso H)

private theorem localizedSelectionRestriction_composition (W : Scheme.{u})
    (e h : ℕ) (he : 1 ≤ e) (_hh : 1 ≤ h)
    (H : ordinarySubsequence l L W h ⋙ ordinarySubsequence l L W e =
      ordinarySubsequence l L W (h * e))
    (K : Derived (ULift.{u + 1} (Padic.coefficientExtensionIntegers l L)) W) :
    (scalarLimitRestriction l L W h).app K ≫
        (scalarLimitRestriction l L W e).app ((subsequence l L W h).obj K) ≫
        (scalarLimit l L W).map ((localizedSelectionAssociator l L W e h H).hom.app K) =
      (scalarLimitRestriction l L W (h * e)).app K := by
  let ε := (eqToIso (H)).symm
  have hi : CategoryTheory.StrictTowerArithmetic.index (h * e) =
      CategoryTheory.StrictTowerArithmetic.index e ⋙
        CategoryTheory.StrictTowerArithmetic.index h := by
    symm
    apply CategoryTheory.Functor.ext
    · intro a b f
      apply Subsingleton.elim
    · intro n
      cases n with
      | op n =>
        apply congrArg op
        change h * (e * (n + 1) - 1 + 1) - 1 = (h * e) * (n + 1) - 1
        rw [Nat.sub_add_cancel (Nat.mul_pos he (Nat.succ_pos n)), Nat.mul_assoc]
  have hcone : scalarLimitRestrictionOrdinary l L W (h * e) ≫
      Functor.whiskerRight ε.hom (lim : Towers
        (ULift.{u + 1} (Padic.coefficientExtensionIntegers l L)) W ⥤ _) =
      scalarLimitRestrictionOrdinary l L W h ≫
        Functor.whiskerLeft (ordinarySubsequence l L W h)
          (scalarLimitRestrictionOrdinary l L W e) := by
    apply NatTrans.ext
    funext A
    have hp (a b : ℕᵒᵖ ⥤ ℕᵒᵖ) (hab : a = b) :
        limit.pre A a ≫ lim.map (eqToHom (congrArg (fun q ↦ q ⋙ A) hab)) =
          limit.pre A b := by
      subst b
      rw [eqToHom_refl, (lim : (ℕᵒᵖ ⥤ Modules
        (ULift.{u + 1} (Padic.coefficientExtensionIntegers l L)) W) ⥤ _).map_id]
      exact Category.comp_id _
    simpa only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      scalarLimitRestrictionOrdinary, ordinarySubsequence,
      CategoryTheory.StrictTowerArithmetic.restriction, Functor.whiskeringLeft_obj_obj,
      limit.pre_pre, ε, Iso.symm_hom,
      eqToIso.inv, eqToHom_app] using hp _ _ hi
  have hc := Functor.rightDerivedPullback_comp
    (ordinarySubsequence l L W h) (ordinarySubsequence l L W e)
    (ordinarySubsequence l L W (h * e)) ε
    (scalarLimitRestrictionOrdinary l L W h)
    (scalarLimitRestrictionOrdinary l L W e)
    (scalarLimitRestrictionOrdinary l L W (h * e)) hcone K
  have heq : Functor.mapDerivedCategoryNatIso ε ≪≫
      Functor.mapDerivedCategoryCompIso (ordinarySubsequence l L W h)
        (ordinarySubsequence l L W e) =
      (localizedSelectionAssociator l L W e h H).symm := by
    apply Iso.ext
    simp only [localizedSelectionAssociator, ε, Iso.trans_hom, Iso.symm_hom,
      Iso.trans_inv, Iso.symm_inv, Functor.mapDerivedCategoryNatIso_symm]
  rw [heq] at hc
  change (scalarLimitRestriction l L W (h * e)).app K ≫
    (scalarLimit l L W).map ((localizedSelectionAssociator l L W e h H).inv.app K) =
      (scalarLimitRestriction l L W h).app K ≫
        (scalarLimitRestriction l L W e).app ((subsequence l L W h).obj K) at hc
  rw [← Category.assoc, ← hc]
  simp only [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app]
  rw [(scalarLimit l L W).map_id]
  exact Category.comp_id _

end LocalizationHelpers


end WeilConjectures.PurStrictScalar
