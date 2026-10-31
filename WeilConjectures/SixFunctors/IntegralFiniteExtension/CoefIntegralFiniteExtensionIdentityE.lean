/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralFiniteExtension.CoefIntegralFiniteExtensionCore
import WeilConjectures.SixFunctors.PurCompactSupport.IntegralScalarTensorIdentity
import WeilConjectures.SixFunctors.IntegralFiniteExtension.CoefIntegralFiniteExtensionUnitReduction

/-! Identity equation for the E-side integral finite-extension comparison.

Source: current blueprint, sec-smooth-purity/sk-lem-sp-tower, order 2494
(blueprint: lem-sf-integral-finite-extension-cocycles).

This is the E component of the cocycle argument.  It is split from the main
statement so that the identity calculation can be proved independently.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option Elab.async false

universe u v
open CategoryTheory Opposite

private theorem tensor_hom_unit
    {C : Type u} [Category.{v} C] (t : C × C ⥤ C) (H : Cᵒᵖ × C ⥤ C)
    (adj : ∀ K, (Functor.curry.obj t).obj K ⊣ (Functor.curry.obj H).obj (op K))
    (he : ∀ (K K' M : C) (f : K' ⟶ K),
      t.map (CategoryTheory.Prod.mkHom (𝟙 K')
        (H.map (CategoryTheory.Prod.mkHom f.op (𝟙 M)))) ≫ (adj K').counit.app M =
      t.map (CategoryTheory.Prod.mkHom f (𝟙 _)) ≫ (adj K).counit.app M)
    (F : C ⥤ C) (e : F ≅ 𝟭 C)
    (mu : t ⋙ F ≅ F.prod F ⋙ t)
    (hmu : ∀ K M, mu.inv.app (K, M) ≫ e.hom.app (t.obj (K, M)) =
      t.map (CategoryTheory.Prod.mkHom (e.hom.app K) (e.hom.app M)))
    (K M : C) :
    (adj (F.obj K)).homEquiv _ _
        (mu.inv.app (K, H.obj (op K, M)) ≫ F.map ((adj K).counit.app M)) ≫
      H.map (CategoryTheory.Prod.mkHom (e.inv.app K).op (e.hom.app M)) =
        e.hom.app (H.obj (op K, M)) := by
  let h : F.obj (H.obj (op K, M)) ⟶ H.obj (op (F.obj K), F.obj M) :=
    (adj (F.obj K)).homEquiv _ _
    (mu.inv.app (K, H.obj (op K, M)) ≫ F.map ((adj K).counit.app M))
  have hh : t.map (CategoryTheory.Prod.mkHom (𝟙 (F.obj K)) h) ≫
      (adj (F.obj K)).counit.app (F.obj M) =
      mu.inv.app (K, H.obj (op K, M)) ≫ F.map ((adj K).counit.app M) :=
    (adj (F.obj K)).homEquiv _ _ |>.symm_apply_apply _
  apply ((adj K).homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_symm_apply, Functor.map_comp, Category.assoc]
  change t.map (CategoryTheory.Prod.mkHom (𝟙 K) h) ≫
      t.map (CategoryTheory.Prod.mkHom (𝟙 K)
        (H.map (CategoryTheory.Prod.mkHom (e.inv.app K).op (e.hom.app M)))) ≫
        (adj K).counit.app M =
    t.map (CategoryTheory.Prod.mkHom (𝟙 K) (e.hom.app (H.obj (op K, M)))) ≫
      (adj K).counit.app M
  have hs : H.map (CategoryTheory.Prod.mkHom (e.inv.app K).op (e.hom.app M)) =
      H.map (CategoryTheory.Prod.mkHom (e.inv.app K).op (𝟙 (F.obj M))) ≫
        H.map (CategoryTheory.Prod.mkHom (𝟙 (op K)) (e.hom.app M)) := by
    simp [← H.map_comp, prod_comp]
  have ht : t.map (CategoryTheory.Prod.mkHom (𝟙 K)
      (H.map (CategoryTheory.Prod.mkHom (e.inv.app K).op (e.hom.app M)))) =
      t.map (CategoryTheory.Prod.mkHom (𝟙 K)
        (H.map (CategoryTheory.Prod.mkHom (e.inv.app K).op (𝟙 (F.obj M))))) ≫
      t.map (CategoryTheory.Prod.mkHom (𝟙 K)
        (H.map (CategoryTheory.Prod.mkHom (𝟙 (op K)) (e.hom.app M)))) := by
    rw [hs]
    simp only [← t.map_comp, prod_comp, Category.id_comp]
  rw [ht, Category.assoc]
  have hn := (adj K).counit.naturality (e.hom.app M)
  change t.map (CategoryTheory.Prod.mkHom (𝟙 K) h) ≫
      t.map (CategoryTheory.Prod.mkHom (𝟙 K)
        (H.map (CategoryTheory.Prod.mkHom (e.inv.app K).op (𝟙 (F.obj M))))) ≫
      t.map (CategoryTheory.Prod.mkHom (𝟙 K)
        (H.map (CategoryTheory.Prod.mkHom (𝟙 (op K)) (e.hom.app M)))) ≫
      (adj K).counit.app M = _
  rw [show t.map (CategoryTheory.Prod.mkHom (𝟙 K)
      (H.map (CategoryTheory.Prod.mkHom (𝟙 (op K)) (e.hom.app M)))) ≫
        (adj K).counit.app M =
      (adj K).counit.app (F.obj M) ≫ e.hom.app M from hn]
  rw [← Category.assoc (t.map (CategoryTheory.Prod.mkHom (𝟙 K)
    (H.map (CategoryTheory.Prod.mkHom (e.inv.app K).op (𝟙 (F.obj M))))))
      ((adj K).counit.app (F.obj M)) (e.hom.app M), he]
  have hc : t.map (CategoryTheory.Prod.mkHom (𝟙 K) h) ≫
      t.map (CategoryTheory.Prod.mkHom (e.inv.app K) (𝟙 _)) =
      t.map (CategoryTheory.Prod.mkHom (e.inv.app K) (𝟙 _)) ≫
        t.map (CategoryTheory.Prod.mkHom (𝟙 (F.obj K)) h) := by
    simp only [← Functor.map_comp, CategoryTheory.prod_comp,
      Category.id_comp, Category.comp_id]
  simp only [Functor.curry_obj_obj_obj] at *
  have hc' := congrArg
    (fun z ↦ z ≫ (adj (F.obj K)).counit.app (F.obj M) ≫ e.hom.app M) hc
  simp only [Category.assoc] at hc' ⊢
  rw [hc']
  rw [← Category.assoc (t.map (CategoryTheory.Prod.mkHom (𝟙 (F.obj K)) h))
    ((adj (F.obj K)).counit.app (F.obj M)) (e.hom.app M), hh]
  simp only [Category.assoc]
  erw [e.hom.naturality ((adj K).counit.app M)]
  simp only [Functor.comp_obj, Functor.curry_obj_obj_obj, Functor.id_map]
  erw [← Category.assoc (mu.inv.app _), hmu, ← Category.assoc, ← t.map_comp]
  simp

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralFiniteExtension

attribute [local irreducible] CategoryTheory.derivedInternalHomOfUniverses
  CategoryTheory.homComplexFunctor
  WeilConjectures.IntegralHom.totalTensor WeilConjectures.IntegralHom.homModelMap
  WeilConjectures.IntegralHom.projection WeilConjectures.IntegralHom.evaluate
  AlgebraicGeometry.Scheme.reductionDerivedChange
  WeilConjectures.PurCompactSupport.tensorIdentity WeilConjectures.PurCompactSupport.scalarTensor

private theorem iso_refl_app {C : Type u} [Category.{v} C]
    {D : Type*} [Category D] (F : C ⥤ D) (K : C) :
    (Iso.refl F).app K = Iso.refl (F.obj K) := rfl

private theorem homMap_unit
    (X : Scheme.{u}) (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (a : IntegralHom.TensorPresentation.{u, u} X R)
    (he : ∀ (K K' M : IntegralHom.Derived.{u, u} X R) (f : K' ⟶ K),
      a.tensor.map (Prod.mkHom (𝟙 K')
        ((IntegralHom.hom.{u, u} X R).map (Prod.mkHom f.op (𝟙 M)))) ≫
          (a.adjunction K').counit.app M =
        a.tensor.map (Prod.mkHom f (𝟙 _)) ≫ (a.adjunction K).counit.app M)
    (φ : R ⟶ R) (hφ : φ = 𝟙 R) (K M : IntegralHom.Derived.{u, u} X R) :
    let e := fun N : IntegralHom.Derived.{u, u} X R ↦
      (eqToIso (congrArg (fun f ↦ pbcDerivedExtend f) hφ)).app N ≪≫
        (PurCompactSupport.tensorIdentity R).app N
    homMap X φ a a K M ≫ (IntegralHom.hom.{u, u} X R).map
      (Prod.mkHom (e K).inv.op (e M).hom) =
        (e ((IntegralHom.hom.{u, u} X R).obj (op K, M))).hom := by
  cases hφ
  simp only [eqToIso_refl, iso_refl_app, Iso.refl_trans]
  unfold homMap
  exact tensor_hom_unit a.tensor (IntegralHom.hom.{u, u} X R) a.adjunction he
    (pbcDerivedExtend (𝟙 R)) (PurCompactSupport.tensorIdentity R)
    (PurCompactSupport.scalarTensor (𝟙 R) (tensorModel X a) (tensorModel X a))
    (PurCompactSupport.scalarTensor_identity R (tensorModel X a)) K M

private theorem conjugate_hom_unit
    {C : Type u} [Category.{v} C] (H : Cᵒᵖ × C ⥤ C)
    {K M FK FM FH TK TM TH : C} (eK : FK ≅ K) (eM : FM ≅ M)
    (eH : FH ≅ H.obj (op K, M)) (cK : FK ≅ TK) (cM : FM ≅ TM) (cH : FH ≅ TH)
    (h : FH ⟶ H.obj (op FK, FM))
    (hh : h ≫ H.map (Prod.mkHom eK.inv.op eM.hom) = eH.hom) :
    (cH.inv ≫ h ≫ H.map (Prod.mkHom cK.inv.op cM.hom)) ≫
        H.map (Prod.mkHom (cK.symm ≪≫ eK).inv.op (cM.symm ≪≫ eM).hom) =
      (cH.symm ≪≫ eH).hom := by
  simp only [Iso.trans_inv, Iso.symm_inv, Iso.trans_hom, Iso.symm_hom,
    Category.assoc, ← H.map_comp]
  have hc : Prod.mkHom cK.inv.op cM.hom ≫
      Prod.mkHom (eK.inv ≫ cK.hom).op (cM.inv ≫ eM.hom) =
      Prod.mkHom eK.inv.op eM.hom := by
    ext <;> simp [← op_comp]
  rw [hc, hh]

/-- E-side identity equations for the fixed integral comparison.
Source: current blueprint, sec-smooth-purity/sk-lem-sp-tower, final paragraph.
(blueprint: lem-sf-integral-finite-extension-identity-e)
Proof: transpose the finite dualizing counit comparisons through the coherent
total limit, then use the tensor-Hom adjunction and the identity multiplication
map to obtain the v and beta equations. -/
theorem comparison_identity_E
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    [X.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]
    (wE : DualizingDatum l X D hl E)
    (a : IntegralHom.TensorPresentation.{u, u} X
      (completedIntegralCommRingSheafUnrestricted l E X))
    (_hevalE : ∀ (K K' M : IntegralVerdier.Ambient l E X) (f : K' ⟶ K),
      a.tensor.map (Prod.mkHom (𝟙 K')
          ((IntegralHom.hom.{u, u} X
            (completedIntegralCommRingSheafUnrestricted l E X)).map
            (Prod.mkHom f.op (𝟙 M)))) ≫ (a.adjunction K').counit.app M =
        a.tensor.map (Prod.mkHom f (𝟙 _)) ≫ (a.adjunction K).counit.app M) :
    IdentityConclusion l E X D hl wE a := by
  have hu := (u_existsUnique l E E (AlgHom.id (Padic l) E) X D hl wE wE).unique
    ((u_existsUnique l E E (AlgHom.id (Padic l) E) X D hl wE wE).exists.choose_spec)
    (unit_dualizing_reduction l E X D hl wE)
  change u l E E (AlgHom.id (Padic l) E) X D hl wE wE =
    (unit l E X wE.omega.obj wE.omega.property.1).hom at hu
  let H := IntegralHom.hom.{u, u} X (completedIntegralCommRingSheafUnrestricted l E X)
  have hv (K M : sfIntegralConstructibleCategory l E X) :
      v l E E (AlgHom.id (Padic l) E) X a a K.obj M.obj K.property.1 M.property.1 ≫
          H.map (Prod.mkHom (unit l E X K.obj K.property.1).inv.op
            (unit l E X M.obj M.property.1).hom) =
        (unit l E X (H.obj (op K.obj, M.obj))
          (scalarInternalHom_complete l E X K.obj M.obj M.property.1)).hom := by
    let R := completedIntegralCommRingSheafUnrestricted l E X
    let φ := completedCoefficientMap l E E (AlgHom.id (Padic l) E) X
    let e := eqToIso (congrArg (fun f ↦ pbcDerivedExtend f)
      (PurCompactSupport.completedMap_identity l E X))
    let m := PurCompactSupport.tensorIdentity R
    have hh := homMap_unit X R a _hevalE φ
      (PurCompactSupport.completedMap_identity l E X) K.obj M.obj
    exact conjugate_hom_unit H (e.app K.obj ≪≫ m.app K.obj)
      (e.app M.obj ≪≫ m.app M.obj)
      (e.app (H.obj (op K.obj, M.obj)) ≪≫ m.app (H.obj (op K.obj, M.obj)))
      (completion l E E (AlgHom.id (Padic l) E) X K.obj K.property.1)
      (completion l E E (AlgHom.id (Padic l) E) X M.obj M.property.1)
      (completion l E E (AlgHom.id (Padic l) E) X _
        (scalarInternalHom_complete l E X K.obj M.obj M.property.1))
      (homMap X φ a a K.obj M.obj)
      hh
  change _ ∧ _ ∧ _
  refine ⟨hu, hv, ?_⟩
  intro K
  change (v l E E (AlgHom.id (Padic l) E) X a a K.obj wE.omega.obj
      K.property.1 wE.omega.property.1 ≫
    H.map (Prod.mkHom (𝟙 _) (u l E E (AlgHom.id (Padic l) E) X D hl wE wE))) ≫
      H.map (Prod.mkHom (unit l E X K.obj K.property.1).inv.op (𝟙 _)) =
    (unit l E X (H.obj (op K.obj, wE.omega.obj))
      (scalarInternalHom_complete l E X K.obj wE.omega.obj wE.omega.property.1)).hom
  rw [hu, Category.assoc, ← H.map_comp]
  have hp : Prod.mkHom (𝟙 _) (unit l E X wE.omega.obj wE.omega.property.1).hom ≫
      Prod.mkHom (unit l E X K.obj K.property.1).inv.op (𝟙 _) =
      Prod.mkHom (unit l E X K.obj K.property.1).inv.op
        (unit l E X wE.omega.obj wE.omega.property.1).hom := by
    ext <;> simp
  rw [hp]
  exact hv K wE.omega

end WeilConjectures.IntegralFiniteExtension
