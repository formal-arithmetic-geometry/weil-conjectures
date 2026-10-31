/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AmbientClopen.AmbientExactClopenData
import all WeilConjectures.AlgebraicGeometry.AmbientClopen.AmbientSystemClopenLocalization
import all WeilConjectures.AlgebraicGeometry.SemilinearProperOpen.SemilinearProperOpenMatePasting

import all WeilConjectures.SixFunctors.AmbientCompositor.Operations.AmbientAdjunctionCompositorNormalization
import WeilConjectures.CategoryTheory.Exact.ExactRestrictionCompositionSupplement
import WeilConjectures.CategoryTheory.ExactDerivedPasting.Word.ExactDerivedTransformationPasting

/-! # Exact localization of the ambient clopen comparison

Source: Stacks Project, Tags 015F, 07A7 and 0F7B.
(blueprint: lem-sf-ambient-ordinary-clopen-localization)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v₁ v₂ w₁ w₂ h₁ h₂
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open WeilConjectures WeilConjectures.IntegralSystemRealization
namespace AlgebraicGeometry.ProEtale.AmbientClopen

private theorem adjunction_on_complexes
    {C : Type v₁} [Category.{h₁} C] [Abelian C] [HasDerivedCategory.{w₁} C]
    {D : Type v₂} [Category.{h₂} D] [Abelian D] [HasDerivedCategory.{w₂} D]
    {F : C ⥤ D} {G : D ⥤ C} [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (a : F ⊣ G) :
    AdjunctionOnComplexes a a.mapExactDerivedCategory := by
  constructor
  · intro K
    simp only [Adjunction.mapExactDerivedCategory, Adjunction.localization_unit_app]
    change (DerivedCategory.Q.map ((a.mapHomologicalComplex (.up ℤ)).unit.app K) ≫
      G.mapDerivedCategoryFactors.inv.app _ ≫
      G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.inv.app K)) ≫
      G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app K) ≫
      G.mapDerivedCategoryFactors.hom.app _ = _
    simp only [Category.assoc, ← Functor.map_comp_assoc, Iso.inv_hom_id_app]
    simp
  · intro K
    simp only [Adjunction.mapExactDerivedCategory, Adjunction.localization_counit_app]
    rfl

private theorem localize_fac
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B] {F G : A ⥤ B}
    [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (a : F ⟶ G) (K : CochainComplex A ℤ) :
    (localize a).app (DerivedCategory.Q.obj K) ≫ G.mapDerivedCategoryFactors.hom.app K =
      F.mapDerivedCategoryFactors.hom.app K ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex a (.up ℤ)).app K) := by
  simp only [localize, Localization.liftNatTrans_app, Localization.Lifting.iso,
    Functor.whiskerRight_app, Category.assoc, Iso.inv_hom_id_app, Category.comp_id]

private theorem adjunction_on_complexes_unit
    {A D : Type*} [Category A] [Category D] [Abelian A] [Abelian D]
    [HasDerivedCategory A] [HasDerivedCategory D]
    {L : A ⥤ D} {R : D ⥤ A} [L.Additive] [R.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    (a : L ⊣ R) (K : CochainComplex A ℤ) :
    a.mapExactDerivedCategory.unit.app (DerivedCategory.Q.obj K) ≫
        R.mapDerivedCategory.map (L.mapDerivedCategoryFactors.hom.app K) ≫
        R.mapDerivedCategoryFactors.hom.app ((L.mapHomologicalComplex (.up ℤ)).obj K) =
      DerivedCategory.Q.map ((a.mapHomologicalComplex (.up ℤ)).unit.app K) :=
  (adjunction_on_complexes a).1 K

private theorem factorsh_hom
    {C : Type v₁} [Category.{h₁} C] [Abelian C] [HasDerivedCategory.{w₁} C]
    {D : Type v₂} [Category.{h₂} D] [Abelian D] [HasDerivedCategory.{w₂} D]
    (F : C ⥤ D) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (K : CochainComplex C ℤ) :
    F.mapDerivedCategoryFactorsh.hom.app ((HomotopyCategory.quotient _ _).obj K) =
      F.mapDerivedCategoryFactors.hom.app K := by
  rw [Functor.mapDerivedCategoryFactorsh_hom_app]
  have h₁ : (DerivedCategory.quotientCompQhIso C).hom.app K = 𝟙 _ := rfl
  have h₂ : (DerivedCategory.quotientCompQhIso D).inv.app
      ((F.mapHomologicalComplex (.up ℤ)).obj K) = 𝟙 _ := rfl
  have h₃ : (F.mapHomotopyCategoryFactors (.up ℤ)).inv.app K = 𝟙 _ := rfl
  simp only [h₁, h₂, h₃, F.mapDerivedCategory.map_id, Category.id_comp]
  erw [DerivedCategory.Qh.map_id, Category.comp_id, Category.comp_id]

private theorem map_adjunction_exact
    {C : Type v₁} [Category.{h₁} C] [Abelian C] [HasDerivedCategory.{w₁} C]
    {D : Type v₂} [Category.{h₂} D] [Abelian D] [HasDerivedCategory.{w₂} D]
    [MonoidalCategory C] [MonoidalPreadditive C] [HasCountableCoproducts C]
    [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
    [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
    [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
    [HasColimitsOfShape ℤ C] [HasExactColimitsOfShape ℤ C]
    [∀ (X : C), PreservesColimitsOfShape ℤ ((MonoidalCategory.curriedTensor C).obj X)]
    [∀ (X : C), PreservesColimitsOfShape ℤ ((MonoidalCategory.curriedTensor C).flip.obj X)]
    [Abelian.HasFunctorialFlatResolution C] [Abelian.HasKInjectiveResolutions D]
    {L : C ⥤ D} {R : D ⥤ C} [L.Additive] [R.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R] (a : L ⊣ R) :
    a.mapDerivedCategoryAdjunction = a.mapExactDerivedCategory := by
  apply Adjunction.ext
  apply Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso C (.up ℤ))
  intro K
  apply (cancel_mono (R.mapDerivedCategory.map (L.mapDerivedCategoryFactors.hom.app K) ≫
    R.mapDerivedCategoryFactors.hom.app ((L.mapHomologicalComplex (.up ℤ)).obj K))).mp
  have h := a.mapDerivedCategoryAdjunction_unit_app_fac
    ((HomotopyCategory.quotient _ _).obj K)
  erw [factorsh_hom L K,
    factorsh_hom R ((L.mapHomologicalComplex (.up ℤ)).obj K),
    Adjunction.mapHomotopyCategory_unit_app_quotient] at h
  exact h.trans ((adjunction_on_complexes a).1 K).symm

private theorem ordinary_open_adjunction_exact
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) j =
      (openImmersionLowerShriekUpperStarAdjunction
        (ModuleCat.{u + 1} Λ) j).mapExactDerivedCategory :=
  map_adjunction_exact _

private theorem localize_adjunction_unit
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B]
    {L : A ⥤ B} {R : B ⥤ A} [L.Additive] [R.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R] (a : L ⊣ R) :
    (Functor.mapDerivedCategoryIdIso A).inv ≫ localize a.unit ≫
      (Functor.mapDerivedCategoryCompIso L R).hom = a.mapExactDerivedCategory.unit := by
  apply Localization.natTrans_ext DerivedCategory.Q (HomologicalComplex.quasiIso A (.up ℤ))
  intro K
  apply (cancel_mono (R.mapDerivedCategory.map (L.mapDerivedCategoryFactors.hom.app K) ≫
    R.mapDerivedCategoryFactors.hom.app ((L.mapHomologicalComplex (.up ℤ)).obj K))).mp
  simp only [NatTrans.comp_app, Category.assoc]
  rw [Functor.mapDerivedCategoryCompIso_hom_app_factors, localize_fac,
    ← Functor.mapDerivedCategoryIdIso_hom_app_Q_obj, Iso.inv_hom_id_app_assoc]
  exact (adjunction_on_complexes a).1 K |>.symm

private theorem localized_unit_word
    (C : Fin 2 → Type v₁) [∀ n, Category.{h₁} (C n)] [∀ n, Abelian (C n)]
    [∀ n, HasDerivedCategory.{w₁} (C n)]
    (L : C 0 ⥤ₑ C 1) (R H : C 1 ⥤ₑ C 0)
    [L.obj.Additive] [R.obj.Additive] [H.obj.Additive]
    (a : L.obj ⊣ R.obj) (t : R.obj ⟶ H.obj) :
    (Functor.mapDerivedCategoryIdIso (C 0)).inv ≫
      localize (a.unit ≫ Functor.whiskerLeft L.obj t) ≫
        (Functor.mapDerivedCategoryCompIso L.obj H.obj).hom =
      a.mapExactDerivedCategory.unit ≫
        Functor.whiskerLeft L.obj.mapDerivedCategory (localize t) := by
  let l := ExactDerivedPasting.Word.edge L
  let r := ExactDerivedPasting.Word.edge R
  let h := ExactDerivedPasting.Word.edge H
  let e : ExactDerivedPasting.Expression C (.nil 0) (.comp l h) :=
    .vcomp (.cell (P := .nil 0) (R := .comp l r) a.unit)
      (.input l (.cell (P := r) (R := h) t))
  have he := (ExactDerivedPasting.exact_derived_transformation_pasting C).1 e
  rw [← localize_adjunction_unit a]
  simpa only [e, l, r, h, ExactDerivedPasting.Expression.ordinary,
    ExactDerivedPasting.Expression.derived, ExactDerivedPasting.Word.cell,
    ExactDerivedPasting.Word.comparison, ExactDerivedPasting.Word.ordinary,
    ExactDerivedPasting.Word.derived, Iso.trans_hom, Iso.trans_inv,
    Iso.refl_hom, Iso.refl_inv, Functor.isoWhiskerLeft_refl,
    Functor.isoWhiskerRight_refl, Category.comp_id, Category.id_comp,
    ExactFunctor.of_fst, localize, Functor.whiskerLeft_id, Functor.whiskerRight_id,
    Category.assoc] using he.symm

private theorem clopen_composite_transport
    {A B C D E : Type*} [Category A] [Category B] [Category C] [Category D] [Category E]
    (I : A ⥤ E) (P P' : E ⥤ D) (Q Q' : A ⥤ B) (S S' : B ⥤ C)
    (J : C ⥤ B) (B₀ : B ⥤ D) (K : C ⥤ D) (R R' : A ⥤ C)
    (p : P ≅ P') (q : Q ≅ Q') (s : S ≅ S') (r : R ≅ R')
    (β : I ⋙ P' ⟶ Q' ⋙ B₀) (π : 𝟭 B ⟶ S' ⋙ J)
    (c : J ⋙ B₀ ⟶ K) (d : Q' ⋙ S' ⟶ R') :
    clopenMateComposite I P Q S J B₀ K R
      (Functor.whiskerLeft I p.hom ≫ β ≫ Functor.whiskerRight q.inv B₀)
      (π ≫ Functor.whiskerRight s.inv J) c
      (Functor.whiskerLeft Q s.hom ≫ Functor.whiskerRight q.hom S' ≫ d ≫ r.inv) =
      Functor.whiskerLeft I p.hom ≫
        clopenMateComposite I P' Q' S' J B₀ K R' β π c d ≫
          Functor.whiskerRight r.inv K := by
  apply NatTrans.ext
  funext M
  simp only [clopenMateComposite_app, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.map_comp, Category.assoc]
  have hπ := B₀.congr_map (π.naturality (q.inv.app M))
  simp only [Functor.id_map, Functor.comp_map, Functor.map_comp] at hπ
  rw [reassoc_of% hπ]
  rw [reassoc_of% (c.naturality (s.inv.app (Q.obj M))),
    reassoc_of% (c.naturality (S'.map (q.inv.app M)))]
  simp only [← K.map_comp_assoc, Iso.inv_hom_id_app_assoc,
    ← S'.map_comp_assoc, Iso.inv_hom_id_app, S'.map_id, Category.id_comp]

private theorem left_uniq_transport
    {A B : Type*} [Category A] [Category B]
    {L M : A ⥤ B} {R R' : B ⥤ A}
    (a : L ⊣ R) (b : M ⊣ R) (e : R ≅ R') :
    (a.ofNatIsoRight e).leftAdjointUniq (b.ofNatIsoRight e) = a.leftAdjointUniq b := by
  apply Iso.ext
  apply NatTrans.ext
  funext X
  apply ((a.ofNatIsoRight e).homEquiv X _).injective
  rw [Adjunction.homEquiv_leftAdjointUniq_hom_app,
    Adjunction.homEquiv_ofNatIsoRight_apply, Adjunction.homEquiv_leftAdjointUniq_hom_app]
  simp only [Adjunction.ofNatIsoRight_unit, NatTrans.comp_app, Functor.whiskerLeft_app]

private theorem left_comp_transport
    {A B C : Type*} [Category A] [Category B] [Category C]
    {L : A ⥤ B} {R R' : B ⥤ A} {M : B ⥤ C} {S S' : C ⥤ B}
    {N : A ⥤ C} {T T' : C ⥤ A}
    (a : L ⊣ R) (b : M ⊣ S) (c : N ⊣ T)
    (e : R ≅ R') (f : S ≅ S') (g : T ≅ T')
    (d : S ⋙ R ≅ T) (d' : S' ⋙ R' ≅ T')
    (hd : Functor.isoWhiskerRight f R ≪≫ Functor.isoWhiskerLeft S' e ≪≫ d' = d ≪≫ g) :
    Adjunction.leftAdjointCompIso (a.ofNatIsoRight e) (b.ofNatIsoRight f)
      (c.ofNatIsoRight g) d' = Adjunction.leftAdjointCompIso a b c d := by
  have ha : ((a.ofNatIsoRight e).comp (b.ofNatIsoRight f)).ofNatIsoRight d' =
      ((a.comp b).ofNatIsoRight d).ofNatIsoRight g := by
    apply Adjunction.ext
    apply NatTrans.ext
    funext X
    have hh := congrArg (fun t ↦ t.hom.app (M.obj (L.obj X))) hd
    simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
      Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app,
      Functor.whiskerLeft_app] at hh
    simp only [Adjunction.ofNatIsoRight_unit, Adjunction.comp_unit_app,
      NatTrans.comp_app, Functor.whiskerLeft_app, Functor.map_comp, Category.assoc]
    rw [← e.hom.naturality_assoc]
    rw [← e.hom.naturality_assoc]
    simpa only [Functor.comp_obj, Category.assoc] using
      congrArg (fun f ↦ a.unit.app X ≫ R.map (b.unit.app (L.obj X)) ≫ f) hh
  rw [← WeilConjectures.AmbientCompositor.left_comp_unique,
    ← WeilConjectures.AmbientCompositor.left_comp_unique, ha, left_uniq_transport]

private theorem projection_transport
    {A B : Type*} [Category A] [Category B]
    {L L' : A ⥤ B} {R R' J : B ⥤ A}
    (a : L ⊣ R) (e : L ≅ L') (f : R ≅ R') (t : R' ⟶ J) :
    a.unit ≫ Functor.whiskerLeft L (f.hom ≫ t) =
      ((a.ofNatIsoLeft e).ofNatIsoRight f).unit ≫
        Functor.whiskerLeft L' t ≫ Functor.whiskerRight e.inv J := by
  apply NatTrans.ext
  funext X
  simp only [Adjunction.ofNatIsoRight_unit, Adjunction.ofNatIsoLeft_unit,
    NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app, Category.assoc]
  rw [← t.naturality, ← f.hom.naturality_assoc]
  simp only [← R.map_comp_assoc, Iso.hom_inv_id_app, R.map_id, Category.id_comp]

private theorem ordinary_projector_localized
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {U X : Scheme.{u}} (s : U ⟶ X) [IsOpenImmersion s] [IsClosedImmersion s] :
    (Functor.mapDerivedCategoryIdIso
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ))).inv ≫
      localize (projector Λ s) ≫
        (Functor.mapDerivedCategoryCompIso (upperStar (ModuleCat.{u + 1} Λ) s)
          (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) s)).hom ≫
        (Functor.isoWhiskerRight
          (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} Λ) s).symm
          (ProperOpenShriek Λ s)).hom = properOpenClopenProjection Λ s := by
  have := isIso_openImmersionLowerShriekToLowerStar_of_isClosed_range
    (ModuleCat.{u + 1} Λ) s s.isClosedEmbedding.isClosed_range
  have := preservesFiniteColimits_lowerStar_of_isClosed_range
    (ModuleCat.{u + 1} Λ) s s.isClosedEmbedding.isClosed_range
  let Y : Fin 2 → Scheme.{u} := ![X, U]
  let D (n : Fin 2) := Sheaf (Scheme.ProEt.topology (Y n)) (ModuleCat.{u + 1} Λ)
  let : ∀ n, Category.{u + 1} (D n) := fun n ↦ inferInstance
  let : ∀ n, Abelian (D n) := fun n ↦ inferInstance
  let : ∀ n, HasDerivedCategory.{u + 1} (D n) :=
    fun n ↦ inferInstance
  let a := upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) s
  let t := @inv _ _ _ _ (openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} Λ) s)
    (isIso_openImmersionLowerShriekToLowerStar_of_isClosed_range
      (ModuleCat.{u + 1} Λ) s s.isClosedEmbedding.isClosed_range)
  have : (ExactFunctor.of (upperStar (ModuleCat.{u + 1} Λ) s)).obj.Additive := by
    change (upperStar (ModuleCat.{u + 1} Λ) s).Additive
    infer_instance
  have : (ExactFunctor.of (lowerStar (ModuleCat.{u + 1} Λ) s)).obj.Additive := by
    change (lowerStar (ModuleCat.{u + 1} Λ) s).Additive
    infer_instance
  have : (ExactFunctor.of
      (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) s)).obj.Additive := by
    change (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) s).Additive
    infer_instance
  have hl := localized_unit_word D (ExactFunctor.of (upperStar (ModuleCat.{u + 1} Λ) s))
    (ExactFunctor.of (lowerStar (ModuleCat.{u + 1} Λ) s))
    (ExactFunctor.of (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) s)) a t
  simp only [ExactFunctor.of_fst] at hl
  dsimp only [D, Y] at hl
  change _ ≫ localize (a.unit ≫ Functor.whiskerLeft _ t) ≫ _ ≫ _ = _
  simp only [← Category.assoc] at hl ⊢
  erw [hl]
  simp only [Category.assoc]
  rw [← map_adjunction_exact a]
  have ht : localize t = (Functor.mapDerivedCategoryNatIso
      (asIso (openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} Λ) s)).symm).hom := rfl
  rw [ht]
  simpa only [properOpenClopenProjection, derivedUpperStarLowerStarAdjunction,
    rightDerivedLowerStarIsoOfIsClosedRange, Iso.trans_hom, Functor.whiskerLeft_comp,
    Functor.isoWhiskerRight_hom, Iso.symm_hom, a,
    Adjunction.mapDerivedCategoryAdjunction,
    leftDerivedUpperStarIsoMapDerivedCategory] using (projection_transport a.derivedAdjunction
    (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} Λ) s)
    (lowerStar (ModuleCat.{u + 1} Λ) s).rightDerivedFunctorIsoMapDerivedCategory
    (Functor.mapDerivedCategoryNatIso
      (asIso (openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} Λ) s)).symm).hom).symm

private theorem exact_open_comp_localized
    {A B C : Type v₁} [Category.{h₁} A] [Category.{h₁} B] [Category.{h₁} C]
    [Abelian A] [Abelian B] [Abelian C]
    [HasDerivedCategory.{w₁} A] [HasDerivedCategory.{w₁} B] [HasDerivedCategory.{w₁} C]
    {L : A ⥤ B} {R : B ⥤ A} {M : B ⥤ C} {S : C ⥤ B}
    {N : A ⥤ C} {T : C ⥤ A}
    [L.Additive] [R.Additive] [M.Additive] [S.Additive] [N.Additive] [T.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    [PreservesFiniteLimits M] [PreservesFiniteColimits M]
    [PreservesFiniteLimits S] [PreservesFiniteColimits S]
    [PreservesFiniteLimits N] [PreservesFiniteColimits N]
    [PreservesFiniteLimits T] [PreservesFiniteColimits T]
    (a : L ⊣ R) (b : M ⊣ S) (c : N ⊣ T) (eta : S ⋙ R ≅ T) :
    Adjunction.leftAdjointCompIso a.mapExactDerivedCategory b.mapExactDerivedCategory
      c.mapExactDerivedCategory ((Functor.mapDerivedCategoryCompIso S R).symm ≪≫
        Functor.mapDerivedCategoryNatIso eta) =
      (Functor.mapDerivedCategoryCompIso L M).symm ≪≫
        Functor.mapDerivedCategoryNatIso (Adjunction.leftAdjointCompIso a b c eta) := by
  let ac := a.mapHomologicalComplex (.up ℤ)
  let bc := b.mapHomologicalComplex (.up ℤ)
  let dc := c.mapHomologicalComplex (.up ℤ)
  let η := eta
  let ηc := Functor.mapHomologicalComplexCompIso η (.up ℤ)
  let δ := (Functor.mapDerivedCategoryCompIso S R).symm ≪≫
    Functor.mapDerivedCategoryNatIso η
  let ν := Adjunction.leftAdjointCompIso a b c η
  let νc := Functor.mapHomologicalComplexCompIso ν (.up ℤ)
  have hn : ∀ K, (ac.comp bc).homEquiv _ _ (νc.hom.app K) ≫
      ηc.hom.app ((N.mapHomologicalComplex (.up ℤ)).obj K) =
        dc.unit.app K := by
    intro K
    apply HomologicalComplex.hom_ext
    intro i
    have h := WeilConjectures.AmbientCompositor.left_comp_unit a b c η
      (K.X i)
    rw [Adjunction.homEquiv_unit] at h ⊢
    exact h
  have hcomp := normalizedAdjunction_composition ac bc
    a.mapExactDerivedCategory b.mapExactDerivedCategory
    L.mapDerivedCategoryFactors.hom
    M.mapDerivedCategoryFactors.hom
    R.mapDerivedCategoryFactors.inv S.mapDerivedCategoryFactors.inv
    (ProEtale.SemilinearProperOpen.exact_hom_fac a)
    (ProEtale.SemilinearProperOpen.exact_hom_fac b)
  have he (K : CochainComplex A ℤ) := normalizedAdjunction_uniqueness
    (QA := DerivedCategory.Q) (QB := DerivedCategory.Q) (ac.comp bc) dc
    (a.mapExactDerivedCategory.comp b.mapExactDerivedCategory) c.mapExactDerivedCategory
    (fun K ↦ M.mapDerivedCategory.map (L.mapDerivedCategoryFactors.hom.app K) ≫
      M.mapDerivedCategoryFactors.hom.app
        ((L.mapHomologicalComplex (.up ℤ)).obj K))
    N.mapDerivedCategoryFactors.hom.app
    (fun L ↦ R.mapDerivedCategoryFactors.inv.app
      ((S.mapHomologicalComplex (.up ℤ)).obj L) ≫
      R.mapDerivedCategory.map (S.mapDerivedCategoryFactors.inv.app L))
    T.mapDerivedCategoryFactors.inv.app
    (by intros P L f; simpa only [Category.assoc] using hcomp P L f)
    (ProEtale.SemilinearProperOpen.exact_hom_fac c)
    ηc δ νc.hom.app hn
    (by
      intro L
      have hv : ηc.hom.app L = (NatIso.mapHomologicalComplex η (.up ℤ)).hom.app L := by
        ext i
        rfl
      rw [hv]
      simpa only [Category.assoc, δ, η,
        Functor.exactDerivedRestrictionComposition] using
        Functor.exactDerivedRestrictionComposition_inv_factors
          S R T η L) K
  apply Iso.ext
  apply Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso A (.up ℤ))
  intro K
  rw [← cancel_mono (N.mapDerivedCategoryFactors.hom.app K)]
  have hk := he K
  rw [WeilConjectures.AmbientCompositor.left_comp_unique] at hk
  change (Adjunction.leftAdjointCompIso a.mapExactDerivedCategory
    b.mapExactDerivedCategory c.mapExactDerivedCategory δ).hom.app
      (DerivedCategory.Q.obj K) ≫ _ = _ at hk
  rw [hk]
  have hv : νc.hom.app K = (NatIso.mapHomologicalComplex ν (.up ℤ)).hom.app K := by
    ext i
    rfl
  rw [hv]
  simpa only [Category.assoc, ν,
    Functor.exactDerivedRestrictionComposition] using
    (Functor.exactDerivedRestrictionComposition_hom_factors
      L M N ν K).symm

private theorem ordinary_open_comp_localized
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {U V X : Scheme.{u}} (j : U ⟶ V) (b : V ⟶ X)
    [IsOpenImmersion j] [IsOpenImmersion b] :
    (Functor.mapDerivedCategoryCompIso
      (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j)
      (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) b)).symm ≪≫
        Functor.mapDerivedCategoryNatIso (openComp Λ j b) =
      properOpenShriekComp Λ j b := by
  have he := exact_open_comp_localized
    (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) j)
    (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) b)
    (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) (j ≫ b))
    (upperStarComp (ModuleCat.{u + 1} Λ) j b).symm
  change _ = (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso (openComp Λ j b) at he
  rw [← he]
  unfold properOpenShriekComp properOpenAdj
  rw [ordinary_open_adjunction_exact Λ j, ordinary_open_adjunction_exact Λ b,
    ordinary_open_adjunction_exact Λ (j ≫ b)]
  symm
  apply left_comp_transport
  apply Iso.ext
  apply NatTrans.ext
  funext M
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    NatTrans.comp_app, leftDerivedUpperStarComp, Functor.leftDerivedFunctorNatIso,
    Functor.leftDerivedFunctorCompIso, Iso.trans_inv, Functor.isoWhiskerLeft_inv,
    Functor.isoWhiskerRight_inv, Category.assoc]
  simp only [Iso.symm_inv, Functor.mapDerivedCategoryNatIso_symm,
    leftDerivedUpperStarIsoMapDerivedCategory, Iso.inv_hom_id_app_assoc,
    ← Functor.map_comp_assoc, Iso.inv_hom_id_app]
  erw [(upperStar (ModuleCat.{u + 1} Λ) j).mapDerivedCategory.map_id]
  exact Category.id_comp _

private theorem ordinary_pull_cell_localized
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {U V X : Scheme.{u}} (j : U ⟶ V) (b : V ⟶ X) (k : U ⟶ X) (h : j ≫ b = k) :
    (leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) j b).inv ≫
      (leftDerivedUpperStarCongr (ModuleCat.{u + 1} Λ) h).hom =
      Functor.whiskerLeft (ProperOpenPull Λ b)
        (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} Λ) j).hom ≫
      Functor.whiskerRight
        (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} Λ) b).hom
        (upperStar (ModuleCat.{u + 1} Λ) j).mapDerivedCategory ≫
      ((Functor.mapDerivedCategoryCompIso (upperStar (ModuleCat.{u + 1} Λ) b)
        (upperStar (ModuleCat.{u + 1} Λ) j)).inv ≫
        localize ((upperStarComp (ModuleCat.{u + 1} Λ) j b).inv ≫
          (upperStarCongr (ModuleCat.{u + 1} Λ) h).hom)) ≫
      (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} Λ) k).inv := by
  subst k
  simp only [leftDerivedUpperStarCongr, upperStarCongr, Iso.refl_hom, Category.comp_id]
  simp only [leftDerivedUpperStarComp, Functor.leftDerivedFunctorNatIso,
    Functor.leftDerivedFunctorCompIso, Iso.trans_inv, Iso.symm_inv,
    Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv, Category.assoc,
    Iso.inv_hom_id_assoc]
  rfl

private theorem ordinary_open_congr_refl
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    openCongr Λ (rfl : j = j) = Iso.refl _ := by
  unfold openCongr sheafOpenCongr
  have he : (openImmersionLowerShriekUpperStarAdjunction
        (ModuleCat.{u + 1} Λ) j).ofNatIsoRight
        (upperStarCongr (ModuleCat.{u + 1} Λ) (rfl : j = j)) =
      openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) j := by
    apply Adjunction.ext
    ext M
    simp [Adjunction.ofNatIsoRight_unit, upperStarCongr]
  rw [he]
  apply Iso.ext
  exact Adjunction.leftAdjointUniq_refl _

private theorem proper_open_congr_refl
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    properOpenShriekCongr Λ (rfl : j = j) = Iso.refl _ := by
  unfold properOpenShriekCongr
  have he : (properOpenAdj Λ j).ofNatIsoRight
        (leftDerivedUpperStarCongr (ModuleCat.{u + 1} Λ) (rfl : j = j)) =
      properOpenAdj Λ j := by
    apply Adjunction.ext
    ext M
    simp [Adjunction.ofNatIsoRight_unit, leftDerivedUpperStarCongr]
  rw [he]
  apply Iso.ext
  exact Adjunction.leftAdjointUniq_refl _

private theorem ordinary_open_cell_localized
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {U V X : Scheme.{u}} (j : U ⟶ V) (b : V ⟶ X) (k : U ⟶ X)
    [IsOpenImmersion j] [IsOpenImmersion b] [IsOpenImmersion k] (h : j ≫ b = k) :
    (Functor.mapDerivedCategoryCompIso
      (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j)
      (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) b)).inv ≫
      localize ((openComp Λ j b).hom ≫ (openCongr Λ h).hom) =
      (properOpenShriekComp Λ j b).hom ≫ (properOpenShriekCongr Λ h).hom := by
  subst k
  simp only [ordinary_open_congr_refl, proper_open_congr_refl, Iso.refl_hom,
    Category.comp_id]
  simpa only [Iso.trans_hom, Iso.symm_hom, Functor.mapDerivedCategoryNatIso,
    Localization.liftNatIso, Functor.isoWhiskerRight_hom, NatIso.mapHomologicalComplex,
    localize] using congrArg Iso.hom (ordinary_open_comp_localized Λ j b)

/-- Ambient OrdinaryClopenLocalization. Source: Stacks Project, Tags 015F, 07A7 and 0F7B.
(blueprint: lem-sf-ambient-ordinary-clopen-localization)

Proof: Localize the beta, clopen projection and the outgoing normalized compositors.
The beta equality follows from its definition as the localized ordinary isomorphism.
For the clopen projection, localize the reverse sheaf adjunction and use the exact
unit formula and the exact/direct-derived identification. The open compositor is
characterized by the composite Hom bijection; localization preserves that bijection.
The pullback compositor is the standard exact composition comparison. Exact-derived
transformation pasting combines these equalities, and transport by the total/exact
pullback isomorphisms gives the stated formula. -/
theorem ordinary_alpha_localized
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {U V W Z : Scheme.{u}} (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
    [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k] [QuasiCompact i]
    [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i) :
    derivedAlpha Λ k r p i h = properOpenAlpha Λ k r p i h := by
  let s := StrictTower.squareLift k r p i h
  have : IsOpenImmersion s := (StrictTower.squareLift_clopen k r p i h).1
  have : IsClosedImmersion s := (StrictTower.squareLift_clopen k r p i h).2
  let a := pullback.snd p i
  let b := pullback.fst p i
  let X : Fin 5 → Scheme.{u} := ![W, pullback p i, U, V, Z]
  let D (n : Fin 5) := Sheaf (Scheme.ProEt.topology (X n)) (ModuleCat.{u + 1} Λ)
  let : ∀ n, Category.{u + 1} (D n) := fun n ↦ inferInstance
  let : ∀ n, Abelian (D n) := fun n ↦ inferInstance
  let : ∀ n, HasDerivedCategory.{u + 1} (D n) :=
    fun n ↦ inferInstance
  have : (ExactFunctor.of (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) i)).obj.Additive := by
    change (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) i).Additive
    infer_instance
  have : (ExactFunctor.of (upperStar (ModuleCat.{u + 1} Λ) p)).obj.Additive := by
    change (upperStar (ModuleCat.{u + 1} Λ) p).Additive
    infer_instance
  have : (ExactFunctor.of (upperStar (ModuleCat.{u + 1} Λ) a)).obj.Additive := by
    change (upperStar (ModuleCat.{u + 1} Λ) a).Additive
    infer_instance
  have : (ExactFunctor.of (upperStar (ModuleCat.{u + 1} Λ) s)).obj.Additive := by
    change (upperStar (ModuleCat.{u + 1} Λ) s).Additive
    infer_instance
  have : (ExactFunctor.of (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) s)).obj.Additive := by
    change (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) s).Additive
    infer_instance
  have : (ExactFunctor.of (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) b)).obj.Additive := by
    change (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) b).Additive
    infer_instance
  have : (ExactFunctor.of (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) k)).obj.Additive := by
    change (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) k).Additive
    infer_instance
  have : (ExactFunctor.of (upperStar (ModuleCat.{u + 1} Λ) r)).obj.Additive := by
    change (upperStar (ModuleCat.{u + 1} Λ) r).Additive
    infer_instance
  have hl := clopen_composite_localized D
    (ExactFunctor.of (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) i))
    (ExactFunctor.of (upperStar (ModuleCat.{u + 1} Λ) p))
    (ExactFunctor.of (upperStar (ModuleCat.{u + 1} Λ) a))
    (ExactFunctor.of (upperStar (ModuleCat.{u + 1} Λ) s))
    (ExactFunctor.of (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) s))
    (ExactFunctor.of (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) b))
    (ExactFunctor.of (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) k))
    (ExactFunctor.of (upperStar (ModuleCat.{u + 1} Λ) r))
    (beta Λ a b i p (IsPullback.of_hasPullback p i).flip).hom (projector Λ s)
    ((openComp Λ s b).hom ≫ (openCongr Λ (squareLift_fst k r p i h)).hom)
    ((upperStarComp (ModuleCat.{u + 1} Λ) s a).inv ≫
      (upperStarCongr (ModuleCat.{u + 1} Λ) (squareLift_snd k r p i h)).hom)
  simp only [ExactFunctor.of_fst] at hl
  change localizeSquare _ _ _ _ (alpha Λ k r p i h) = _ at hl
  change Functor.whiskerLeft _
    (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} Λ) p).hom ≫
      localizeSquare _ _ _ _ (alpha Λ k r p i h) ≫
      Functor.whiskerRight
        (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} Λ) r).inv _ = _
  rw [hl]
  have ht := clopen_composite_transport
    (ProperOpenShriek Λ i)
    (ProperOpenPull Λ p) (upperStar (ModuleCat.{u + 1} Λ) p).mapDerivedCategory
    (ProperOpenPull Λ a) (upperStar (ModuleCat.{u + 1} Λ) a).mapDerivedCategory
    (ProperOpenPull Λ s) (upperStar (ModuleCat.{u + 1} Λ) s).mapDerivedCategory
    (ProperOpenShriek Λ s) (ProperOpenShriek Λ b) (ProperOpenShriek Λ k)
    (ProperOpenPull Λ r) (upperStar (ModuleCat.{u + 1} Λ) r).mapDerivedCategory
    (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} Λ) p)
    (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} Λ) a)
    (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} Λ) s)
    (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} Λ) r)
    (localizeSquare _ _ _ _
      (beta Λ a b i p (IsPullback.of_hasPullback p i).flip).hom)
    ((Functor.mapDerivedCategoryIdIso
      (Sheaf (Scheme.ProEt.topology (pullback p i)) (ModuleCat.{u + 1} Λ))).inv ≫
      localize (projector Λ s) ≫
      (Functor.mapDerivedCategoryCompIso (upperStar (ModuleCat.{u + 1} Λ) s)
        (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) s)).hom)
    ((Functor.mapDerivedCategoryCompIso
      (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) s)
      (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) b)).inv ≫ localize
        ((openComp Λ s b).hom ≫ (openCongr Λ (squareLift_fst k r p i h)).hom))
    ((Functor.mapDerivedCategoryCompIso (upperStar (ModuleCat.{u + 1} Λ) a)
      (upperStar (ModuleCat.{u + 1} Λ) s)).inv ≫ localize
        ((upperStarComp (ModuleCat.{u + 1} Λ) s a).inv ≫
          (upperStarCongr (ModuleCat.{u + 1} Λ) (squareLift_snd k r p i h)).hom))
  erw [← ht]
  have hp := ordinary_projector_localized Λ s
  have hc := ordinary_open_cell_localized Λ s b k (squareLift_fst k r p i h)
  have hd := ordinary_pull_cell_localized Λ s a r (squareLift_snd k r p i h)
  simp only [Functor.isoWhiskerRight_hom, Iso.symm_hom] at hp
  simp only [Category.assoc] at hd ⊢
  erw [hp, hc, ← hd]
  exact (expanded_clopen_composite _ _ _ _ _ _ _ _ _ _ _ _).symm

end AlgebraicGeometry.ProEtale.AmbientClopen
