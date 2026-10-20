/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E5
-/
module

public import Sheaf.Paper.FibreFunctorBasepointTransportData
import Mathlib.CategoryTheory.Adjunction.Limits
import WeilConjectures.ConstructibleSheaf.Biproduct
import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafOver
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import WeilConjectures.AlgebraicGeometry.GaloisPointGeometricComparison

/-! # Linearization and scalar compatibility of finite-set fibre paths

Source: Stacks 0BND (2), 0DV5; naturality with the module operations and the
extension--restriction adjunction.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v w
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
variable {Y : Scheme.{u}}

variable {R : Type (u + 1)} [Ring R]

private noncomputable def pathConstantValueStalkIso
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R))
    (U : Y.Etale) (M : ModuleCat.{u + 1} R)
    (e : F.over U ≅
      (constantSheaf (Y.smallEtaleTopology.over U) (ModuleCat.{u + 1} R)).obj M)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ U.left) :
    ((pointSmallEtale (s ≫ U.hom)).sheafFiber
      (A := ModuleCat.{u + 1} R)).obj F ≅ M := by
  let : PreservesFilteredColimitsOfSize.{u, u}
      (CategoryTheory.forget (ModuleCat.{u + 1} R)) :=
    preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
  let eU : (Etale.upperStar (ModuleCat.{u + 1} R) U.hom).obj F ≅
      (constantSheaf U.left.smallEtaleTopology (ModuleCat.{u + 1} R)).obj M :=
    (overSheafEquivFunctorObjOverIso (ModuleCat.{u + 1} R) U F).symm ≪≫
      (Etale.overSheafEquiv U (ModuleCat.{u + 1} R)).functor.mapIso e ≪≫
      ((Etale.overEquiv U).constantSheafSheafCongrIso
        (Y.smallEtaleTopology.over U) U.left.smallEtaleTopology
        (ModuleCat.{u + 1} R) CategoryTheory.Over.mkIdTerminal).app M
  exact ((Etale.upperStarCompSheafFiberIso (ModuleCat.{u + 1} R) U.hom s).app F).symm ≪≫
    (pointSmallEtale s).sheafFiber.mapIso eU ≪≫
      (pointSmallEtale s).sheafFiberConstantSheafIso M

/-- Local constancy together with finite geometric stalks gives finite constant module
models. Source: Stacks 0DV5; the constant-model geometric stalk calculation.
(blueprint: new-e5-linear-fibre-path-transport).
Proof: choose constant models on a trivializing cover. A nonempty cover member has an
algebraically closed geometric point, whose stalk identifies its model with a finite
stalk of the original sheaf. On an empty member use the zero module. -/
theorem isLisseModuleSheaf_of_locallyConstant_of_finite_stalk
    (R : Type (u + 1)) [Ring R]
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R))
    (hF : IsLocallyConstantSheaf F)
    (hfin : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y),
      Finite (((pointSmallEtale y).ulift.{u + 1}.sheafFiber
        (A := ModuleCat.{u + 1} R)).obj F)) : IsLisseModuleSheaf F := by
  obtain ⟨⟨𝒰, h𝒰⟩⟩ := hF.nonempty_locallyConstantDatum
  refine ⟨𝒰, fun i ↦ ?_⟩
  let U := 𝒰.etalePrecoverageToEtale i
  by_cases hU : IsEmpty U.left
  · let := hU
    let E := (Etale.overSheafEquiv U (ModuleCat.{u + 1} R)).functor
    have h₁ : IsZero (E.obj (F.over U)) := Etale.isZero_sheaf_of_isEmpty _
    have h₂ : IsZero (E.obj
        ((constantSheaf (Y.smallEtaleTopology.over U)
          (ModuleCat.{u + 1} R)).obj (ModuleCat.of R PUnit.{u + 2}))) :=
      Etale.isZero_sheaf_of_isEmpty _
    exact ⟨ModuleCat.of R PUnit.{u + 2}, inferInstance, ⟨E.preimageIso (h₁.iso h₂)⟩⟩
  · have : Nonempty U.left := not_isEmpty_iff.mp hU
    let x : U.left := Classical.choice inferInstance
    let Ω := AlgebraicClosure (U.left.residueField x)
    let y : Spec (.of Ω) ⟶ U.left :=
      Spec.map (CommRingCat.ofHom (algebraMap (U.left.residueField x) Ω)) ≫
        U.left.fromSpecResidueField x
    let := h𝒰 i
    obtain ⟨M, ⟨e⟩⟩ := (F.over U).mem_essImage_of_isConstant
    let eM := ((pointSmallEtale (y ≫ U.hom)).uliftSheafFiberIso.{u + 1}
      (ModuleCat.{u + 1} R)).app F ≪≫ pathConstantValueStalkIso F U M e.symm y
    exact ⟨M, @Finite.of_equiv _ _ (hfin Ω (y ≫ U.hom)) eM.toLinearEquiv.toEquiv,
      ⟨e.symm⟩⟩

private theorem pathLisseUnderlying (R : Type (u + 1)) [Ring R]
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R)) (hF : IsLisseModuleSheaf F) :
    IsLisseEtaleSheafOfSets (galoisUnderlyingSetSheaf R F) := by
  obtain ⟨𝒰, h𝒰⟩ := hF
  constructor
  · refine ⟨𝒰, fun i ↦ ?_⟩
    obtain ⟨M, _, ⟨e⟩⟩ := h𝒰 i
    have : (F.over (𝒰.etalePrecoverageToEtale i)).IsConstant
        (Y.smallEtaleTopology.over (𝒰.etalePrecoverageToEtale i)) :=
      Sheaf.isConstant_of_iso _ e
    change ((sheafCompose (Y.smallEtaleTopology.over (𝒰.etalePrecoverageToEtale i))
      (CategoryTheory.forget (ModuleCat.{u + 1} R))).obj
      (F.over (𝒰.etalePrecoverageToEtale i))).IsConstant _
    infer_instance
  · refine ⟨fun Ω _ _ s ↦ (ConcreteCategory.isFinitelyGenerated_iff_finite _).mpr ?_⟩
    obtain ⟨i, x, hx⟩ := 𝒰.exists_eq (s default)
    have : AlgebraicGeometry.Etale (𝒰.f i) := 𝒰.map_prop i
    obtain ⟨t, ht, -⟩ := exists_fac_of_etale_of_isSepClosed (𝒰.f i) s x hx
    obtain ⟨M, hM, ⟨e⟩⟩ := h𝒰 i
    let := hM
    let : PreservesFilteredColimitsOfSize.{u, u}
        (CategoryTheory.forget (ModuleCat.{u + 1} R)) :=
      preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
    let es := ((pointSmallEtale s).sheafFiberCompIso
      (CategoryTheory.forget (ModuleCat.{u + 1} R))).app F
    have em := pathConstantValueStalkIso F (𝒰.etalePrecoverageToEtale i) M e t
    change ((pointSmallEtale (t ≫ 𝒰.f i)).sheafFiber
      (A := ModuleCat.{u + 1} R)).obj F ≅ M at em
    rw [ht] at em
    exact Finite.of_equiv M
      (es ≪≫ (CategoryTheory.forget (ModuleCat.{u + 1} R)).mapIso em).toEquiv.symm

private theorem pathLisseSelfBiprod (R : Type (u + 1)) [Ring R]
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R))
    (hF : IsLisseModuleSheaf F) : IsLisseModuleSheaf (F ⊞ F) := by
  obtain ⟨𝒰, h𝒰⟩ := hF
  refine ⟨𝒰, fun i ↦ ?_⟩
  obtain ⟨M, hM, ⟨e⟩⟩ := h𝒰 i
  let : Finite M := hM
  have hMM : Finite ↥(M ⊞ M : ModuleCat.{u + 1} R) :=
    Finite.of_equiv (M × M) (ModuleCat.biprodIsoProd M M).toLinearEquiv.toEquiv.symm
  let := Functor.additive_of_preserves_binary_products
    (Y.smallEtaleTopology.overPullback (ModuleCat.{u + 1} R)
      (𝒰.etalePrecoverageToEtale i))
  refine ⟨M ⊞ M, hMM, ⟨?_⟩⟩
  exact ((Over.forget (𝒰.etalePrecoverageToEtale i)).sheafAdjunctionCocontinuous
      (ModuleCat.{u + 1} R)
      (Y.smallEtaleTopology.over (𝒰.etalePrecoverageToEtale i))
      Y.smallEtaleTopology).leftAdjointBiprodIso F F ≪≫
    biprod.mapIso e e ≪≫
      ((constantSheafAdj _ _ terminalIsTerminal).leftAdjointBiprodIso M M).symm

private def pathUnderlyingNatIso {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (y : Spec (.of Ω) ⟶ Y) (R : Type (u + 1)) [Ring R] :
    (pointSmallEtale y).ulift.{u + 1}.sheafFiber ⋙
        CategoryTheory.forget (ModuleCat.{u + 1} R) ≅
      sheafCompose Y.smallEtaleTopology (CategoryTheory.forget (ModuleCat.{u + 1} R)) ⋙
        (pointSmallEtale y).sheafFiber :=
  ((pointSmallEtale y).ulift.{u + 1}.sheafFiberCompIso
    (CategoryTheory.forget (ModuleCat.{u + 1} R))).symm ≪≫
      Functor.isoWhiskerLeft
        (sheafCompose Y.smallEtaleTopology (CategoryTheory.forget (ModuleCat.{u + 1} R)))
        ((pointSmallEtale y).uliftSheafFiberIso (Type (u + 1)))

/-- The underlying-set stalk comparison sends a module germ to the same set germ.
Source: Stacks 0DV5; Weil II (1.1.1) b).
(blueprint: new-e5-linear-fibre-path-transport).
Proof: the forgetful-functor stalk comparison and the universe-lift stalk comparison
both commute with germ maps. Compose those two formulas. -/
theorem pathUnderlyingStalk_germ
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y)
    (R : Type (u + 1)) [Ring R]
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R))
    (U : Y.Etale) (ξ : (pointSmallEtale y).fiber.obj U) (s : F.obj.obj (op U)) :
    pathUnderlyingStalk y R F
        ((pointSmallEtale y).ulift.{u + 1}.toPresheafFiber U ⟨ξ⟩ F.obj s) =
      (pointSmallEtale y).toPresheafFiber U ξ (galoisUnderlyingSetSheaf R F).obj s := by
  let p := (pointSmallEtale y).ulift.{u + 1}
  let κ := (p.sheafFiberCompIso (CategoryTheory.forget (ModuleCat.{u + 1} R))).app F
  have h := ConcreteCategory.congr_hom
    (p.toPresheafFiber_presheafFiberCompIso_hom_app
      (CategoryTheory.forget (ModuleCat.{u + 1} R)) U ⟨ξ⟩ F.obj) s
  have hi : κ.inv (p.toPresheafFiber U ⟨ξ⟩ F.obj s) =
      p.toPresheafFiber U ⟨ξ⟩ (galoisUnderlyingSetSheaf R F).obj s := by
    apply κ.toEquiv.injective
    exact (ConcreteCategory.congr_hom κ.inv_hom_id _).trans h.symm
  change ((pointSmallEtale y).uliftSheafFiberIso (Type (u + 1))).hom.app
      (galoisUnderlyingSetSheaf R F) (κ.inv (p.toPresheafFiber U ⟨ξ⟩ F.obj s)) = _
  rw [hi]
  exact ConcreteCategory.congr_hom
    ((pointSmallEtale y).toPresheafFiber_uliftSheafFiberIso_hom_app
      (Type (u + 1)) (galoisUnderlyingSetSheaf R F) U ξ) s

private def pathSetEquiv
    {Ωy : Type u} [Field Ωy] [IsAlgClosed Ωy] (y : Spec (.of Ωy) ⟶ Y)
    {Ωz : Type u} [Field Ωz] [IsAlgClosed Ωz] (z : Spec (.of Ωz) ⟶ Y)
    (t : flcFiber y ≅ flcFiber z) (R : Type (u + 1)) [Ring R]
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R))
    (hF : IsLisseEtaleSheafOfSets (galoisUnderlyingSetSheaf R F)) :
    (((pointSmallEtale y).ulift.{u + 1}.sheafFiber (A := ModuleCat.{u + 1} R)).obj F) ≃
      (((pointSmallEtale z).ulift.{u + 1}.sheafFiber (A := ModuleCat.{u + 1} R)).obj F) :=
  (pathUnderlyingStalk y R F).trans
    (((t.app (galoisUnderlyingFLC R F hF)).toEquiv).trans
      (pathUnderlyingStalk z R F).symm)

set_option backward.isDefEq.respectTransparency false in
private theorem pathSetEquiv_naturality
    {Ωy : Type u} [Field Ωy] [IsAlgClosed Ωy] (y : Spec (.of Ωy) ⟶ Y)
    {Ωz : Type u} [Field Ωz] [IsAlgClosed Ωz] (z : Spec (.of Ωz) ⟶ Y)
    (t : flcFiber y ≅ flcFiber z) (R : Type (u + 1)) [Ring R]
    (F H : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R))
    (hF : IsLisseEtaleSheafOfSets (galoisUnderlyingSetSheaf R F))
    (hH : IsLisseEtaleSheafOfSets (galoisUnderlyingSetSheaf R H)) (f : F ⟶ H)
    (x : ((pointSmallEtale y).ulift.{u + 1}.sheafFiber (A := ModuleCat.{u + 1} R)).obj F) :
    pathSetEquiv y z t R H hH
      (((pointSmallEtale y).ulift.{u + 1}.sheafFiber
        (A := ModuleCat.{u + 1} R)).map f x) =
      ((pointSmallEtale z).ulift.{u + 1}.sheafFiber (A := ModuleCat.{u + 1} R)).map f
        (pathSetEquiv y z t R F hF x) := by
  apply (pathUnderlyingStalk z R H).injective
  have hy := ConcreteCategory.congr_hom ((pathUnderlyingNatIso y R).hom.naturality f) x
  have hz := ConcreteCategory.congr_hom ((pathUnderlyingNatIso z R).hom.naturality f)
    (pathSetEquiv y z t R F hF x)
  have ht := ConcreteCategory.congr_hom (t.hom.naturality
    (ObjectProperty.homMk
      ((sheafCompose Y.smallEtaleTopology
        (CategoryTheory.forget (ModuleCat.{u + 1} R))).map f) :
      galoisUnderlyingFLC R F hF ⟶ galoisUnderlyingFLC R H hH))
        (pathUnderlyingStalk y R F x)
  change pathUnderlyingStalk y R H
      (((pointSmallEtale y).ulift.{u + 1}.sheafFiber).map f x) =
    ((pointSmallEtale y).sheafFiber).map
      ((sheafCompose Y.smallEtaleTopology
        (CategoryTheory.forget (ModuleCat.{u + 1} R))).map f)
      (pathUnderlyingStalk y R F x) at hy
  change pathUnderlyingStalk z R H
      (((pointSmallEtale z).ulift.{u + 1}.sheafFiber).map f
        (pathSetEquiv y z t R F hF x)) =
    ((pointSmallEtale z).sheafFiber).map
      ((sheafCompose Y.smallEtaleTopology
        (CategoryTheory.forget (ModuleCat.{u + 1} R))).map f)
      (pathUnderlyingStalk z R F (pathSetEquiv y z t R F hF x)) at hz
  rw [hz]
  dsimp only [pathSetEquiv, Equiv.trans_apply]
  dsimp only [galoisUnderlyingFLC, flcFiber, Functor.comp_obj, ObjectProperty.ι_obj]
  erw [Equiv.apply_symm_apply, Equiv.apply_symm_apply, hy]
  exact ht


private theorem pathSetEquiv_evaluation
    {Ωy : Type u} [Field Ωy] [IsAlgClosed Ωy] (y : Spec (.of Ωy) ⟶ Y)
    {Ωz : Type u} [Field Ωz] [IsAlgClosed Ωz] (z : Spec (.of Ωz) ⟶ Y)
    (t : flcFiber y ≅ flcFiber z) (R : Type (u + 1)) [Ring R]
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R))
    (hF : IsLisseEtaleSheafOfSets (galoisUnderlyingSetSheaf R F))
    (x : ((pointSmallEtale y).ulift.{u + 1}.sheafFiber
      (A := ModuleCat.{u + 1} R)).obj F) :
    pathUnderlyingStalk z R F (pathSetEquiv y z t R F hF x) =
      t.hom.app (galoisUnderlyingFLC R F hF) (pathUnderlyingStalk y R F x) := by
  dsimp only [pathSetEquiv, Equiv.trans_apply, galoisUnderlyingFLC]
  erw [Equiv.apply_symm_apply]
  rfl

private def pathSetSmul (R : Type (u + 1)) [Ring R]
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R)) (r : R) :
    galoisUnderlyingSetSheaf R F ⟶ galoisUnderlyingSetSheaf R F where
  hom :=
    { app := fun U ↦ TypeCat.ofHom (fun x : F.obj.obj U ↦ r • x)
      naturality := fun U V f ↦ by
        apply ConcreteCategory.hom_ext
        intro x
        exact (map_smul (F.obj.map f).hom r (@id (F.obj.obj U) x)).symm }

set_option backward.isDefEq.respectTransparency false in
private theorem pathUnderlyingStalk_smul
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y)
    (R : Type (u + 1)) [Ring R]
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R)) (r : R)
    (x : ((pointSmallEtale y).ulift.{u + 1}.sheafFiber
      (A := ModuleCat.{u + 1} R)).obj F) :
    pathUnderlyingStalk y R F (r • x) =
      ((pointSmallEtale y).sheafFiber.map (pathSetSmul R F r))
        (pathUnderlyingStalk y R F x) := by
  obtain ⟨U, ⟨ξ⟩, s, rfl⟩ :=
    (pointSmallEtale y).ulift.{u + 1}.toPresheafFiber_jointly_surjective (P := F.obj) x
  erw [← map_smul, pathUnderlyingStalk_germ, pathUnderlyingStalk_germ]
  exact (ConcreteCategory.congr_hom
    ((pointSmallEtale y).toPresheafFiber_naturality
      (pathSetSmul R F r).hom U ξ) s).symm

private theorem pathSetEquiv_smul
    {Ωy : Type u} [Field Ωy] [IsAlgClosed Ωy] (y : Spec (.of Ωy) ⟶ Y)
    {Ωz : Type u} [Field Ωz] [IsAlgClosed Ωz] (z : Spec (.of Ωz) ⟶ Y)
    (t : flcFiber y ≅ flcFiber z) (R : Type (u + 1)) [Ring R]
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R))
    (hF : IsLisseEtaleSheafOfSets (galoisUnderlyingSetSheaf R F)) (r : R)
    (x : ((pointSmallEtale y).ulift.{u + 1}.sheafFiber
      (A := ModuleCat.{u + 1} R)).obj F) :
    pathSetEquiv y z t R F hF (r • x) = r • pathSetEquiv y z t R F hF x := by
  apply (pathUnderlyingStalk z R F).injective
  rw [pathSetEquiv_evaluation, pathUnderlyingStalk_smul, pathUnderlyingStalk_smul,
    pathSetEquiv_evaluation]
  exact ConcreteCategory.congr_hom
    (t.hom.naturality (ObjectProperty.homMk (pathSetSmul R F r) :
      galoisUnderlyingFLC R F hF ⟶ galoisUnderlyingFLC R F hF))
      (pathUnderlyingStalk y R F x)

set_option backward.isDefEq.respectTransparency false in
private theorem pathSetEquiv_add
    {Ωy : Type u} [Field Ωy] [IsAlgClosed Ωy] (y : Spec (.of Ωy) ⟶ Y)
    {Ωz : Type u} [Field Ωz] [IsAlgClosed Ωz] (z : Spec (.of Ωz) ⟶ Y)
    (t : flcFiber y ≅ flcFiber z) (R : Type (u + 1)) [Ring R]
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R)) (hF : IsLisseModuleSheaf F)
    (x x' : ((pointSmallEtale y).ulift.{u + 1}.sheafFiber
      (A := ModuleCat.{u + 1} R)).obj F) :
    let h := pathLisseUnderlying R F hF
    pathSetEquiv y z t R F h (x + x') =
      pathSetEquiv y z t R F h x + pathSetEquiv y z t R F h x' := by
  dsimp only
  let h : IsLisseEtaleSheafOfSets (galoisUnderlyingSetSheaf R F) :=
    pathLisseUnderlying R F hF
  let hB := pathLisseUnderlying R (F ⊞ F) (pathLisseSelfBiprod R F hF)
  let St := (pointSmallEtale y).ulift.{u + 1}.sheafFiber (A := ModuleCat.{u + 1} R)
  let St' := (pointSmallEtale z).ulift.{u + 1}.sheafFiber (A := ModuleCat.{u + 1} R)
  let := Functor.additive_of_preserves_binary_products St
  let := Functor.additive_of_preserves_binary_products St'
  let v := St.map biprod.inl x + St.map biprod.inr x'
  have hfst : St.map biprod.fst v = x := by
    simp [v, ← ConcreteCategory.comp_apply, ← St.map_comp]
  have hsnd : St.map biprod.snd v = x' := by
    simp [v, ← ConcreteCategory.comp_apply, ← St.map_comp]
  have hadd : St.map (biprod.desc (𝟙 F) (𝟙 F)) v = x + x' := by
    simp only [biprod.desc_eq, Category.comp_id, Functor.map_add]
    change St.map biprod.fst v + St.map biprod.snd v = x + x'
    rw [hfst, hsnd]
  have n₁ := pathSetEquiv_naturality y z t R (F ⊞ F) F hB h
    (biprod.desc (𝟙 F) (𝟙 F)) v
  have n₂ := pathSetEquiv_naturality y z t R (F ⊞ F) F hB h biprod.fst v
  have n₃ := pathSetEquiv_naturality y z t R (F ⊞ F) F hB h biprod.snd v
  rw [hadd] at n₁
  rw [hfst] at n₂
  rw [hsnd] at n₃
  rw [n₁, n₂, n₃]
  simp only [biprod.desc_eq, Category.comp_id, Functor.map_add]
  rfl

private def pathFiniteIso
    {Ωy : Type u} [Field Ωy] [IsAlgClosed Ωy] (y : Spec (.of Ωy) ⟶ Y)
    {Ωz : Type u} [Field Ωz] [IsAlgClosed Ωz] (z : Spec (.of Ωz) ⟶ Y)
    (t : flcFiber y ≅ flcFiber z) (R : Type (u + 1)) [Ring R] :
    pathModuleFiber y R ≅ pathModuleFiber z R :=
  NatIso.ofComponents (fun F ↦ LinearEquiv.toModuleIso
    { pathSetEquiv y z t R F.obj
        (pathLisseUnderlying R F.obj F.property) with
      map_add' := pathSetEquiv_add y z t R F.obj F.property
      map_smul' := pathSetEquiv_smul y z t R F.obj _ }) (by
    intro F H f
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact pathSetEquiv_naturality y z t R F.obj H.obj _ _ f.hom x)

private theorem pathFiniteIso_evaluation
    {Ωy : Type u} [Field Ωy] [IsAlgClosed Ωy] (y : Spec (.of Ωy) ⟶ Y)
    {Ωz : Type u} [Field Ωz] [IsAlgClosed Ωz] (z : Spec (.of Ωz) ⟶ Y)
    (t : flcFiber y ≅ flcFiber z) (R : Type (u + 1)) [Ring R]
    (F : LisseModuleSheafCategory Y R) (x : (pathModuleFiber y R).obj F) :
    pathUnderlyingStalk z R F.obj ((pathFiniteIso y z t R).hom.app F x) =
      t.hom.app (galoisUnderlyingFLC R F.obj
        (pathLisseUnderlying R F.obj F.property))
          (pathUnderlyingStalk y R F.obj x) :=
  pathSetEquiv_evaluation y z t R F.obj _ x

set_option backward.isDefEq.respectTransparency false in
private def pathFiniteFamily (R : Type (u + 1)) [Ring R] :
    LinearFibrePathFamily Y (LisseModuleSheafCategory Y R) R
      (fun y ↦ pathModuleFiber y R) where
  map := by
    intro Ωy _ _ y Ωz _ _ z t
    exact pathFiniteIso y z t R
  identity := by
    intro Ωy _ _ y
    apply Iso.ext
    apply NatTrans.ext
    funext F
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply (pathUnderlyingStalk y R F.obj).injective
    rw [pathFiniteIso_evaluation]
    rfl
  composition := by
    intro Ωy _ _ y Ωz _ _ z Ωq _ _ q t s
    apply Iso.ext
    apply NatTrans.ext
    funext F
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change (pathFiniteIso y q (t ≪≫ s) R).hom.app F x =
      (pathFiniteIso z q s R).hom.app F ((pathFiniteIso y z t R).hom.app F x)
    apply (pathUnderlyingStalk q R F.obj).injective
    rw [pathFiniteIso_evaluation, pathFiniteIso_evaluation, pathFiniteIso_evaluation]
    rfl
  conjugation := by
    intro Ωy _ _ y Ωz _ _ z t g
    apply Iso.ext
    apply NatTrans.ext
    funext F
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change (pathFiniteIso z z (t.conjAut g) R).hom.app F x =
      (pathFiniteIso y z t R).hom.app F
        ((pathFiniteIso y y g R).hom.app F ((pathFiniteIso y z t R).inv.app F x))
    apply (pathUnderlyingStalk z R F.obj).injective
    rw [pathFiniteIso_evaluation, pathFiniteIso_evaluation, pathFiniteIso_evaluation]
    let X := galoisUnderlyingFLC R F.obj
      (pathLisseUnderlying R F.obj F.property)
    change t.hom.app X (g.hom.app X (t.inv.app X (pathUnderlyingStalk z R F.obj x))) = _
    congr 2
    change _ = (pathUnderlyingStalk y R F.obj)
      ((pathUnderlyingStalk y R F.obj).symm
        (t.inv.app X (pathUnderlyingStalk z R F.obj x)))
    exact ((pathUnderlyingStalk y R F.obj).apply_symm_apply _).symm
  change := by
    intro Ωy _ _ y Ωz _ _ z t s
    apply Iso.ext
    apply NatTrans.ext
    funext F
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change (pathFiniteIso y z s R).hom.app F x =
      (pathFiniteIso z z (t.symm ≪≫ s) R).hom.app F
        ((pathFiniteIso y z t R).hom.app F x)
    apply (pathUnderlyingStalk z R F.obj).injective
    rw [pathFiniteIso_evaluation, pathFiniteIso_evaluation, pathFiniteIso_evaluation]
    change s.hom.app _ _ = s.hom.app _ (t.inv.app _ (t.hom.app _ _))
    congr 1
    exact (ConcreteCategory.congr_hom
      (t.hom_inv_id_app (galoisUnderlyingFLC R F.obj _))
        (pathUnderlyingStalk y R F.obj x)).symm

private theorem pathScalarMapTmul {R S : Type (u + 1)} [Ring R] [Ring S]
    (a : R →+* S) {M N : ModuleCat.{u + 1} R} (f : M ⟶ N) (b : S) (x : M) :
    (ModuleCat.ringExtendScalars.{u + 1, u + 1} a).map f
        (ModuleCat.ringExtensionTmul.{u + 1, u + 1} a M b x) =
      ModuleCat.ringExtensionTmul.{u + 1, u + 1} a N b (f x) := by
  let E := ModuleCat.ringExtendScalars.{u + 1, u + 1} a
  let adj := ModuleCat.ringExtendScalarsAdj.{u + 1, u + 1} a
  have h := congrArg (fun k ↦ k x) (adj.unit.naturality f)
  change adj.unit.app N (f x) = E.map f (adj.unit.app M x) at h
  have h' : E.map f (show E.obj M from adj.unit.app M x) =
      (show E.obj N from adj.unit.app N (f x)) := h.symm
  simpa only [ModuleCat.ringExtensionTmul, map_smul] using! congrArg (fun z ↦ b • z) h'

private theorem pathScalarStalk_germ
    {R S : Type (u + 1)} [Ring R] [Ring S]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y) (a : R →+* S)
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R))
    (U : Y.Etale) (ξ : (pointSmallEtale y).fiber.obj U) (b : S)
    (s : F.obj.obj (op U)) :
    (pathScalarStalk y a F).hom
      (ModuleCat.ringExtensionTmul.{u + 1, u + 1} a _ b
        ((pointSmallEtale y).ulift.{u + 1}.toPresheafFiber U ⟨ξ⟩ F.obj s)) =
      (pointSmallEtale y).ulift.{u + 1}.toPresheafFiber U ⟨ξ⟩
        ((Sheaf.ringExtendScalars.{u + 1, u + 1} Y.smallEtaleTopology a).obj F).obj
        ((toSheafify Y.smallEtaleTopology
          (F.obj ⋙ ModuleCat.ringExtendScalars.{u + 1, u + 1} a)).app (op U)
          (ModuleCat.ringExtensionTmul.{u + 1, u + 1} a _ b s)) := by
  let p := (pointSmallEtale y).ulift.{u + 1}
  let E := ModuleCat.ringExtendScalars.{u + 1, u + 1} a
  let := (ModuleCat.ringExtendScalarsAdj.{u + 1, u + 1} a).isLeftAdjoint
  have h : E.map (p.toPresheafFiber U ⟨ξ⟩ F.obj) ≫
      (p.presheafFiberCompIso E).inv.app F.obj ≫
      (p.presheafToSheafCompSheafFiberIso (ModuleCat.{u + 1} S)).inv.app (F.obj ⋙ E) =
      (toSheafify Y.smallEtaleTopology (F.obj ⋙ E)).app (op U) ≫
        p.toPresheafFiber U ⟨ξ⟩ ((presheafToSheaf Y.smallEtaleTopology
          (ModuleCat.{u + 1} S)).obj (F.obj ⋙ E)).obj := by
    rw [← p.toPresheafFiber_presheafFiberCompIso_hom_app E U ⟨ξ⟩ F.obj]
    rw [Category.assoc]
    erw [Iso.hom_inv_id_app_assoc]
    exact p.toPresheafFiber_naturality
      (toSheafify Y.smallEtaleTopology (F.obj ⋙ E)) U ⟨ξ⟩
  have h' := congrArg (fun k ↦ k (ModuleCat.ringExtensionTmul.{u + 1, u + 1} a _ b s)) h
  simp only [ModuleCat.comp_apply] at h'
  erw [pathScalarMapTmul] at h'
  simpa [pathScalarStalk, p, E, Sheaf.ringExtendScalars,
    GrothendieckTopology.Point.sheafFiber] using h'

private def pathScalarUnit {R S : Type (u + 1)} [Ring R] [Ring S] (a : R →+* S)
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R))
    (H : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} S))
    (e : H ≅ (Sheaf.ringExtendScalars.{u + 1, u + 1} Y.smallEtaleTopology a).obj F) :
    galoisUnderlyingSetSheaf R F ⟶ galoisUnderlyingSetSheaf S H where
  hom := Functor.whiskerRight
      (Functor.whiskerLeft F.obj
        (ModuleCat.ringExtendScalarsAdj.{u + 1, u + 1} a).unit)
      (CategoryTheory.forget (ModuleCat.{u + 1} R)) ≫
    Functor.whiskerRight
      (toSheafify Y.smallEtaleTopology
        (F.obj ⋙ ModuleCat.ringExtendScalars.{u + 1, u + 1} a) ≫ e.inv.hom)
      (CategoryTheory.forget (ModuleCat.{u + 1} S))

set_option backward.isDefEq.respectTransparency false in
private theorem pathScalarUnit_stalk
    {R S : Type (u + 1)} [Ring R] [Ring S]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y) (a : R →+* S)
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R))
    (H : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} S))
    (e : H ≅ (Sheaf.ringExtendScalars.{u + 1, u + 1} Y.smallEtaleTopology a).obj F)
    (x : ((pointSmallEtale y).ulift.{u + 1}.sheafFiber
      (A := ModuleCat.{u + 1} R)).obj F) :
    pathUnderlyingStalk y S H
      (((pointSmallEtale y).ulift.{u + 1}.sheafFiber).map e.inv
        ((pathScalarStalk y a F).hom
          ((ModuleCat.ringExtendScalarsAdj.{u + 1, u + 1} a).unit.app _ x))) =
      (pointSmallEtale y).sheafFiber.map (pathScalarUnit a F H e)
        (pathUnderlyingStalk y R F x) := by
  obtain ⟨U, ⟨ξ⟩, s, rfl⟩ :=
    (pointSmallEtale y).ulift.{u + 1}.toPresheafFiber_jointly_surjective (P := F.obj) x
  have h := pathScalarStalk_germ y a F U ξ 1 s
  simp only [ModuleCat.ringExtensionTmul, one_smul] at h
  erw [h]
  have he := ConcreteCategory.congr_hom
    ((pointSmallEtale y).ulift.{u + 1}.toPresheafFiber_naturality e.inv.hom U ⟨ξ⟩)
      ((toSheafify Y.smallEtaleTopology
        (F.obj ⋙ ModuleCat.ringExtendScalars.{u + 1, u + 1} a)).app (op U)
          ((ModuleCat.ringExtendScalarsAdj.{u + 1, u + 1} a).unit.app _ s))
  simp only [ModuleCat.comp_apply] at he
  erw [he]
  erw [pathUnderlyingStalk_germ, pathUnderlyingStalk_germ]
  exact (ConcreteCategory.congr_hom
    ((pointSmallEtale y).toPresheafFiber_naturality
      (pathScalarUnit a F H e).hom U ξ) s).symm

set_option backward.isDefEq.respectTransparency false in
private theorem pathFiniteScalar
    {Ωy : Type u} [Field Ωy] [IsAlgClosed Ωy] (y : Spec (.of Ωy) ⟶ Y)
    {Ωz : Type u} [Field Ωz] [IsAlgClosed Ωz] (z : Spec (.of Ωz) ⟶ Y)
    (t : flcFiber y ≅ flcFiber z) (R S : Type (u + 1))
    [Ring R] [Finite R] [Ring S] [Finite S] (a : R →+* S)
    (F : LisseModuleSheafCategory Y R) (H : LisseModuleSheafCategory Y S)
    (e : H.obj ≅ (Sheaf.ringExtendScalars.{u + 1, u + 1} Y.smallEtaleTopology a).obj F.obj) :
    (ModuleCat.ringExtendScalars.{u + 1, u + 1} a).map
        ((pathFiniteIso y z t R).hom.app F) ≫ (pathScalarStalk z a F.obj).hom ≫
      ((pointSmallEtale z).ulift.{u + 1}.sheafFiber).map e.inv =
      (pathScalarStalk y a F.obj).hom ≫
        ((pointSmallEtale y).ulift.{u + 1}.sheafFiber).map e.inv ≫
          (pathFiniteIso y z t S).hom.app H := by
  let adj := ModuleCat.ringExtendScalarsAdj.{u + 1, u + 1} a
  apply (adj.homEquiv _ _).injective
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  have hu := ConcreteCategory.congr_hom
    (adj.unit.naturality ((pathFiniteIso y z t R).hom.app F)) x
  simp only [ModuleCat.comp_apply] at hu
  change adj.unit.app _ ((pathFiniteIso y z t R).hom.app F x) =
    (ModuleCat.ringExtendScalars.{u + 1, u + 1} a).map
      ((pathFiniteIso y z t R).hom.app F) (adj.unit.app _ x) at hu
  change ((pointSmallEtale z).ulift.{u + 1}.sheafFiber).map e.inv
      ((pathScalarStalk z a F.obj).hom
        ((ModuleCat.ringExtendScalars.{u + 1, u + 1} a).map
          ((pathFiniteIso y z t R).hom.app F) (adj.unit.app _ x))) =
    (pathFiniteIso y z t S).hom.app H
      (((pointSmallEtale y).ulift.{u + 1}.sheafFiber).map e.inv
        ((pathScalarStalk y a F.obj).hom (adj.unit.app _ x)))
  rw [← hu]
  apply (pathUnderlyingStalk z S H.obj).injective
  erw [pathScalarUnit_stalk z a F.obj H.obj e, pathFiniteIso_evaluation,
    pathFiniteIso_evaluation, pathScalarUnit_stalk y a F.obj H.obj e]
  exact (ConcreteCategory.congr_hom (t.hom.naturality
    (ObjectProperty.homMk (pathScalarUnit a F.obj H.obj e) :
      galoisUnderlyingFLC R F.obj _ ⟶ galoisUnderlyingFLC S H.obj _))
        (pathUnderlyingStalk y R F.obj x)).symm

private def pathFiniteTransport : FiniteFibrePathTransport Y where
  linear := fun R ↦ pathFiniteFamily R
  evaluation := by
    intro Ωy _ _ y Ωz _ _ z t R _ _ F
    exact ⟨_, pathFiniteIso_evaluation y z t R F⟩
  scalar := by
    intro Ωy _ _ y Ωz _ _ z t R S _ _ _ _ a F H e
    exact pathFiniteScalar y z t R S a F H e

/-- A set path linearizes on lisse sheaves with finite constant module values, even
when the coefficient ring is infinite. Source: Stacks 0BND (2), 0DV5.
(blueprint: new-e5-linear-fibre-path-transport).
Proof: the underlying sheaf is finite locally constant. Naturality with projections and
addition proves additivity, and naturality with each scalar multiplication proves linearity.
Apply the underlying inverse path to obtain the inverse. Naturality and the four path laws
are the corresponding set identities, through the canonical stalk comparison. -/
theorem lisse_linear_fibre_path_family_exists (Y : Scheme.{u})
    (R : Type (u + 1)) [Ring R] :
    ∃ d : LinearFibrePathFamily Y (LisseModuleSheafCategory Y R) R
        (fun y ↦ pathModuleFiber y R),
      ∀ {Ωy : Type u} [Field Ωy] [IsAlgClosed Ωy] (y : Spec (.of Ωy) ⟶ Y)
        {Ωz : Type u} [Field Ωz] [IsAlgClosed Ωz] (z : Spec (.of Ωz) ⟶ Y)
        (t : flcFiber y ≅ flcFiber z) (F : LisseModuleSheafCategory Y R),
        ∃ h : IsLisseEtaleSheafOfSets (galoisUnderlyingSetSheaf R F.obj),
          ∀ x : (pathModuleFiber y R).obj F,
            pathUnderlyingStalk z R F.obj ((d.map y z t).hom.app F x) =
              t.hom.app (galoisUnderlyingFLC R F.obj h)
                (pathUnderlyingStalk y R F.obj x) := by
  refine ⟨pathFiniteFamily R, ?_⟩
  intro Ωy _ _ y Ωz _ _ z t F
  exact ⟨_, pathFiniteIso_evaluation y z t R F⟩

/-- The normalized path family, determined by its underlying-set evaluation.
Source: Stacks 0BND (2), 0DV5.
(blueprint: new-e5-linear-fibre-path-transport). -/
@[irreducible]
def lisseLinearFibrePathFamily (Y : Scheme.{u}) (R : Type (u + 1)) [Ring R] :
    LinearFibrePathFamily Y (LisseModuleSheafCategory Y R) R
      (fun y ↦ pathModuleFiber y R) :=
  (lisse_linear_fibre_path_family_exists Y R).choose

/-- Evaluation characterizes the chosen family, including over infinite rings.
Source: Stacks 0BND (2), 0DV5.
(blueprint: new-e5-linear-fibre-path-transport).
Proof: this is the normalization clause of the existence theorem used to select it. -/
theorem lisseLinearFibrePathFamily_evaluation (R : Type (u + 1)) [Ring R]
    {Ωy : Type u} [Field Ωy] [IsAlgClosed Ωy] (y : Spec (.of Ωy) ⟶ Y)
    {Ωz : Type u} [Field Ωz] [IsAlgClosed Ωz] (z : Spec (.of Ωz) ⟶ Y)
    (t : flcFiber y ≅ flcFiber z) (F : LisseModuleSheafCategory Y R) :
    ∃ h : IsLisseEtaleSheafOfSets (galoisUnderlyingSetSheaf R F.obj),
      ∀ x : (pathModuleFiber y R).obj F,
        pathUnderlyingStalk z R F.obj
          (((lisseLinearFibrePathFamily Y R).map y z t).hom.app F x) =
          t.hom.app (galoisUnderlyingFLC R F.obj h)
            (pathUnderlyingStalk y R F.obj x) := by
  unfold lisseLinearFibrePathFamily
  exact (lisse_linear_fibre_path_family_exists Y R).choose_spec y z t F

/-- The linearized paths commute with arbitrary finite-ring scalar extension.
Source: Stacks 0BND (2), 0DV5; Weil II (1.1.1) a).
(blueprint: new-e5-linear-fibre-path-transport).
Proof: for scalar extension, use naturality on the set map sending a section to its
universal scalar image. The canonical stalk comparison carries these section generators
to the corresponding stalk generators. The extension--restriction adjunction says that
equality on these generators determines the scalar-linear maps, proving the scalar square.
Together with the linearization construction this gives every field of the record. -/
theorem finite_fibre_path_transport_exists (Y : Scheme.{u}) :
    Nonempty (FiniteFibrePathTransport Y) := ⟨pathFiniteTransport⟩

end AlgebraicGeometry.Scheme
