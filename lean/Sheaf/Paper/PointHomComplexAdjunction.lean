/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A8
-/
module

public import Sheaf.Paper.PointDerivedHomModels
import WeilConjectures.Algebra.Homology.HomComplexComponents

/-! # The Hom-complex adjunction for extension from a point

Source: Stacks Project, Tags 0A8X and 04TT.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe t u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open CochainComplex.HomComplex

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

namespace WeilConjectures.PointDerivedHom

variable (k : Type t) [Field k]
  {R : CommRingCat.{max u (t + 1)}}
  (B : Sheaf (Scheme.ProEt.topology (Spec (.of k))) CommRingCat.{max u (t + 1)})
  (α : constantRing.{t, u} k R ⟶ B)

private theorem final_hom_unique {U : Scheme.ProEt (Spec (.of k))}
    (f g : U ⟶ finalObject k) : f = g := by
  apply MorphismProperty.Over.Hom.ext
  have hf := MorphismProperty.Over.w f
  have hg := MorphismProperty.Over.w g
  change f.left ≫ 𝟙 _ = U.hom at hf
  change g.left ≫ 𝟙 _ = U.hom at hg
  rw [Category.comp_id] at hf hg
  exact hf.trans hg.symm

@[no_expose]
private def localHomGlobal
    (A V : Modules.{t, u} k B)
    (f : (PresheafOfModules.restrictOver B.obj (finalObject k)).obj A.val ⟶
      (PresheafOfModules.restrictOver B.obj (finalObject k)).obj V.val) : A ⟶ V where
  val :=
    { app := fun U ↦ f.app (op (Over.mk (toFinal k U.unop)))
      naturality := fun {U V} g ↦ by
        let g' : Over.mk (toFinal k V.unop) ⟶ Over.mk (toFinal k U.unop) :=
          Over.homMk g.unop (final_hom_unique k _ _)
        exact f.naturality g'.op }

@[no_expose]
private def localHomGlobalEquiv (A V : Modules.{t, u} k B) :
    ((PresheafOfModules.restrictOver B.obj (finalObject k)).obj A.val ⟶
      (PresheafOfModules.restrictOver B.obj (finalObject k)).obj V.val) ≃+ (A ⟶ V) where
  toFun := localHomGlobal k B A V
  invFun := fun f ↦ (PresheafOfModules.restrictOver B.obj (finalObject k)).map f.val
  left_inv f := by
    ext W x
    exact PresheafOfModules.restrictOver_hom_app_congr f
      (final_hom_unique k _ _) x
  right_inv f := by rfl
  map_add' f g := by rfl

private theorem localHomGlobal_final (A V : Modules.{t, u} k B)
    (f : (PresheafOfModules.restrictOver B.obj (finalObject k)).obj A.val ⟶
      (PresheafOfModules.restrictOver B.obj (finalObject k)).obj V.val)
    (x : A.val.obj (op (finalObject k))) :
    (localHomGlobal k B A V f).val.app (op (finalObject k)) x =
      f.app (op (Over.mk (𝟙 (finalObject k)))) x := by
  exact PresheafOfModules.restrictOver_hom_app_congr f
    (final_hom_unique k _ _) x

set_option backward.isDefEq.respectTransparency true

variable (L : ModuleCat.{max u (t + 1)} R ⥤ Modules.{t, u} k B)
  (hobj : ∀ M : ModuleCat.{max u (t + 1)} R,
    L.obj M = extensionObject.{t, u} k B α M)
  (adj : L ⊣ sections.{t, u} k B α)
  (c : CochainComplex (ModuleCat.{max u (t + 1)} R) ℤ)
  (I : CochainComplex (Modules.{t, u} k B) ℤ)

@[no_expose]
private def degreeComponentEquiv (p q : ℤ) :
    ((PresheafOfModules.restrictOver B.obj (finalObject k)).obj (L.obj (c.X p)).val ⟶
      (PresheafOfModules.restrictOver B.obj (finalObject k)).obj (I.X q).val) ≃+
        (c.X p ⟶ ((sectionComplex k B α).obj I).X q) := by
  let := adj.left_adjoint_additive
  exact (localHomGlobalEquiv k B (L.obj (c.X p)) (I.X q)).trans
    (adj.homAddEquiv (c.X p) (I.X q))

set_option backward.isDefEq.respectTransparency false

@[no_expose]
private def degreeMap (j : ℤ) :
    (((sectionComplex.{t, u} k B α).obj
      (sheafHom.{t, u} k B ((extensionComplex.{t, u} k B α L adj).obj c) I)).X j) →+
        Cochain c ((sectionComplex.{t, u} k B α).obj I) j where
  toFun h := Cochain.mk fun p q hpq ↦
    degreeComponentEquiv k B α L adj c I p q
      ((homComplexπ ((extensionComplex k B α L adj).obj c) I j p q hpq).val.app
        (op (finalObject k)) h)
  map_zero' := by
    apply Cochain.ext
    intro p q hpq
    change degreeComponentEquiv k B α L adj c I p q
      ((homComplexπ ((extensionComplex k B α L adj).obj c) I j p q hpq).val.app
        (op (finalObject k)) 0) = 0
    rw [map_zero]
    exact (degreeComponentEquiv k B α L adj c I p q).map_zero
  map_add' x y := by
    apply Cochain.ext
    intro p q hpq
    change degreeComponentEquiv k B α L adj c I p q
      ((homComplexπ ((extensionComplex k B α L adj).obj c) I j p q hpq).val.app
        (op (finalObject k)) (x + y)) = _
    change degreeComponentEquiv k B α L adj c I p q
      ((homComplexπ ((extensionComplex k B α L adj).obj c) I j p q hpq).val.app
        (op (finalObject k)) (x + y)) =
      degreeComponentEquiv k B α L adj c I p q
        ((homComplexπ ((extensionComplex k B α L adj).obj c) I j p q hpq).val.app
          (op (finalObject k)) x) +
      degreeComponentEquiv k B α L adj c I p q
        ((homComplexπ ((extensionComplex k B α L adj).obj c) I j p q hpq).val.app
          (op (finalObject k)) y)
    rw [map_add]
    exact (degreeComponentEquiv k B α L adj c I p q).map_add _ _

private theorem fan_projection_bijective.{w} {ι : Type} {X : ι → Type w}
    {P : Type w} (π : ∀ i, P ⟶ X i) (h : IsLimit (Fan.mk P π)) :
    Function.Bijective (fun x i ↦ π i x) := by
  let e := h.conePointUniqueUpToIso (Limits.Types.productLimitCone X).isLimit
  have he (x : P) (i : ι) : e.hom x i = π i x :=
    ConcreteCategory.congr_hom (h.conePointUniqueUpToIso_hom_comp
      (Limits.Types.productLimitCone X).isLimit ⟨i⟩) x
  have hf : (fun x i ↦ π i x) = e.toEquiv := by
    funext x i
    exact (he x i).symm
  rw [hf]
  exact e.toEquiv.bijective

private theorem degreeMap_bijective (j : ℤ) :
    Function.Bijective (degreeMap k B α L adj c I j) := by
  let P := (extensionComplex k B α L adj).obj c
  let E := SheafOfModules.forget (ring k B) ⋙
    PresheafOfModules.evaluation (ring k B).obj (op (finalObject k)) ⋙
      forget (ModuleCat.{max u (t + 1)} ((ring k B).obj.obj (op (finalObject k))))
  let H := fun p : ℤ ↦ SheafOfModules.homObj (R := B) (P.X p) (I.X (p + j))
  let π := fun p : ℤ ↦ homComplexπ P I j p (p + j) rfl
  have h := isLimitFanMkObjOfIsLimit E H π (homComplexIsLimit P I j)
  have hb := fan_projection_bijective _ h
  constructor
  · intro x y hxy
    apply hb.1
    funext p
    apply (degreeComponentEquiv k B α L adj c I p (p + j)).injective
    exact congrArg (fun z ↦ z.v p (p + j) rfl) hxy
  · intro z
    obtain ⟨x, hx⟩ := hb.2 (fun p ↦
      (degreeComponentEquiv k B α L adj c I p (p + j)).symm (z.v p (p + j) rfl))
    refine ⟨x, ?_⟩
    apply Cochain.ext
    intro p q hpq
    subst q
    change degreeComponentEquiv k B α L adj c I p (p + j)
      ((homComplexπ P I j p (p + j) rfl).val.app (op (finalObject k)) x) = _
    rw [show (homComplexπ P I j p (p + j) rfl).val.app (op (finalObject k)) x =
      (degreeComponentEquiv k B α L adj c I p (p + j)).symm (z.v p (p + j) rfl) from
        congrFun hx p]
    exact (degreeComponentEquiv k B α L adj c I p (p + j)).apply_symm_apply _

private theorem degreeMap_apply
    (hex : ExplicitAdjunction.{t, u} k B α L hobj adj)
    (j p : ℤ)
    (h : (((sectionComplex.{t, u} k B α).obj
      (sheafHom.{t, u} k B ((extensionComplex.{t, u} k B α L adj).obj c) I)).X j))
    (x : c.X p) :
    (((degreeMap k B α L adj c I j h).v p (p + j) rfl).hom x) =
      homValue.{t, u} k B ((extensionComplex.{t, u} k B α L adj).obj c) I j p
        (op (finalObject k)) h
        (generator.{t, u} k B α L hobj (c.X p) (op (finalObject k)) 1 x) := by
  let φ := ((homComplexπ ((extensionComplex k B α L adj).obj c) I j p (p + j) rfl).val.app
    (op (finalObject k)) h)
  change (adj.homEquiv (c.X p) (I.X (p + j))
    (localHomGlobal k B _ _ φ)).hom x = _
  rw [hex.1, localHomGlobal_final]
  rfl

set_option backward.isDefEq.respectTransparency true in
private theorem homValue_smul
    (P : CochainComplex (Modules.{t, u} k B) ℤ) (j p : ℤ)
    (U : (Scheme.ProEt (Spec (.of k)))ᵒᵖ)
    (a : B.obj.obj U) (h : ((sheafHom.{t, u} k B P I).X j).val.obj U)
    (x : (P.X p).val.obj U) :
    homValue k B P I j p U (a • h) x = a • homValue k B P I j p U h x := by
  set_option backward.isDefEq.respectTransparency false in
    let π := IntegralHom.projection (Spec (.of k)) B P I j p
    have hπ := (π.val.app U).hom.map_smul a h
    have hx := congrArg (fun φ ↦ (φ.app (op (Over.mk (𝟙 U.unop)))).hom x) hπ
    change homValue k B P I j p U (a • h) x = _ at hx
    refine hx.trans ?_
    rw [PresheafOfModules.smul_app, ModuleCat.hom_comp, LinearMap.comp_apply,
      PresheafOfModules.sectionsSMul_app_apply, PresheafOfModules.overSections_coe_apply]
    change B.obj.map (𝟙 U) a • _ = _
    rw [B.obj.map_id]
    rfl

private theorem degreeMap_smul
    (hex : ExplicitAdjunction.{t, u} k B α L hobj adj) (j : ℤ) (a : R)
    (h : (((sectionComplex.{t, u} k B α).obj
      (sheafHom.{t, u} k B ((extensionComplex.{t, u} k B α L adj).obj c) I)).X j)) :
    degreeMap k B α L adj c I j (a • h) = a • degreeMap k B α L adj c I j h := by
  apply Cochain.ext
  intro p q hpq
  subst q
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rw [Cochain.smul_v, ModuleCat.hom_smul, LinearMap.smul_apply]
  rw [degreeMap_apply k B α L hobj adj c I hex,
    degreeMap_apply k B α L hobj adj c I hex]
  exact homValue_smul k B I ((extensionComplex k B α L adj).obj c) j p
    (op (finalObject k)) (scalar k B α (op (finalObject k)) a) h
    (generator k B α L hobj (c.X p) (op (finalObject k)) 1 x)

private theorem degreeComponentEquiv_map
    (p p' q q' : ℤ) (f : c.X p' ⟶ c.X p) (g : I.X q ⟶ I.X q')
    (φ : (PresheafOfModules.restrictOver B.obj (finalObject k)).obj
      (L.obj (c.X p)).val ⟶
        (PresheafOfModules.restrictOver B.obj (finalObject k)).obj (I.X q).val) :
    degreeComponentEquiv k B α L adj c I p' q'
      ((SheafOfModules.homObjMap (R := B) (L.map f) g).val.app
        (op (finalObject k)) φ) =
      f ≫ degreeComponentEquiv k B α L adj c I p q φ ≫ (sections k B α).map g := by
  let := adj.left_adjoint_additive
  change adj.homEquiv _ _ (localHomGlobal k B _ _ _) = _
  have hφ : localHomGlobal k B _ _
      ((SheafOfModules.homObjMap (R := B) (L.map f) g).val.app
        (op (finalObject k)) φ) =
      L.map f ≫ localHomGlobal k B _ _ φ ≫ g := by
    ext U x
    rfl
  rw [hφ, adj.homEquiv_naturality_left, adj.homEquiv_naturality_right]
  rfl

private theorem section_sub_units
    {M N : Modules.{t, u} k B} (f g : M ⟶ N) (n : ℤˣ)
    (x : M.val.obj (op (finalObject k))) :
    ((f - n • g).val.app (op (finalObject k))) x =
      (f.val.app (op (finalObject k))) x - n • (g.val.app (op (finalObject k))) x := by
  let V := SheafOfModules.forget (ring k B) ⋙
    PresheafOfModules.evaluation (ring k B).obj (op (finalObject k))
  change (V.map (f - n • g)).hom x = _
  rw [Functor.map_sub]
  simp only [Units.smul_def, Functor.map_zsmul, ModuleCat.hom_sub,
    ModuleCat.hom_zsmul, LinearMap.sub_apply, LinearMap.smul_apply]
  rfl

private theorem degreeMap_d (n m : ℤ) (hnm : n + 1 = m)
    (h : (((sectionComplex.{t, u} k B α).obj
      (sheafHom.{t, u} k B ((extensionComplex.{t, u} k B α L adj).obj c) I)).X n)) :
    degreeMap k B α L adj c I m
      ((((sectionComplex k B α).obj
        (sheafHom k B ((extensionComplex k B α L adj).obj c) I)).d n m).hom h) =
      δ n m (degreeMap k B α L adj c I n h) := by
  apply Cochain.ext
  intro p q hpq
  rw [δ_v n m hnm _ p q hpq (p + n) (p + 1) (by omega) rfl]
  let P := (extensionComplex k B α L adj).obj c
  have hd := congrArg (fun f ↦ f.val.app (op (finalObject k)) h)
    (homComplex_d_π P I n m p q (p + n) (p + 1) hnm hpq rfl (by omega))
  rw [section_sub_units k B] at hd
  simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app,
    ModuleCat.hom_comp, LinearMap.comp_apply] at hd
  change degreeComponentEquiv k B α L adj c I p q
    ((homComplexπ P I m p q hpq).val.app (op (finalObject k))
      ((sheafHom k B P I).d n m |>.val.app (op (finalObject k)) h)) = _
  rw [hd, map_sub]
  simp only [Units.smul_def, map_zsmul]
  have hpost := degreeComponentEquiv_map k B α L adj c I p p (p + n) q
    (𝟙 _) (I.d _ _)
    ((homComplexπ P I n p (p + n) rfl).val.app (op (finalObject k)) h)
  rw [L.map_id, Category.id_comp] at hpost
  have hpre := degreeComponentEquiv_map k B α L adj c I (p + 1) p q q
    (c.d _ _) (𝟙 _)
    ((homComplexπ P I n (p + 1) q (by omega)).val.app (op (finalObject k)) h)
  erw [(sections k B α).map_id, Category.comp_id] at hpre
  erw [hpost]
  change _ - (n.negOnePow : ℤ) •
    degreeComponentEquiv k B α L adj c I p q
      ((SheafOfModules.homObjMap (R := B) (L.map (c.d p (p + 1))) (𝟙 _)).val.app
        (op (finalObject k)) _) = _
  erw [hpre]
  have hs : (m.negOnePow : ℤ) = -(n.negOnePow : ℤ) := by
    rw [← hnm, Int.negOnePow_succ]
    rfl
  rw [hs, neg_smul, ← sub_eq_add_neg]
  rfl

/-- The explicit extension-sections adjunction identifies the two total Hom complexes.
Source: Stacks Project, Tags 0A8X and 04TT
(blueprint: lem-pod-point-hom-complex-adjunction).

Proof: local module maps on the slice over the final object are global module
maps, since every object has a unique map to the final object. Apply the additive
adjunction to every factor of the Hom product. Evaluation preserves products,
so the resulting degreewise maps are bijective, including for unbounded complexes.
Their formula is evaluation on the adjunction unit, hence they are R-linear.
The differential projection formula and the left and right naturality of the
adjunction show that these maps commute with the Hom differential: the sign in
degree m=n+1 is the negative of that in degree n. Assemble the degreewise linear
isomorphisms into a chain isomorphism. The assumed explicit unit formula gives
the stated normalization. No exactness, flatness or injectivity is used. -/
theorem point_hom_complex_adjunction
    (hex : ExplicitAdjunction.{t, u} k B α L hobj adj) :
    ∃ q : (sectionComplex.{t, u} k B α).obj
      (sheafHom.{t, u} k B ((extensionComplex.{t, u} k B α L adj).obj c) I) ≅
        CochainComplex.moduleHomComplex c ((sectionComplex.{t, u} k B α).obj I),
      IsComparison.{t, u} k B α L hobj adj c I q := by
  let S := (sectionComplex k B α).obj
    (sheafHom k B ((extensionComplex k B α L adj).obj c) I)
  let T := CochainComplex.moduleHomComplex c ((sectionComplex k B α).obj I)
  let f (j : ℤ) : S.X j →ₗ[R] T.X j :=
    { degreeMap k B α L adj c I j with
      map_smul' := degreeMap_smul k B α L hobj adj c I hex j }
  let e (j : ℤ) : S.X j ≃ₗ[R] T.X j :=
    LinearEquiv.ofBijective (f j) (degreeMap_bijective k B α L adj c I j)
  let q : S ≅ T := HomologicalComplex.Hom.isoOfComponents
    (fun j ↦ (e j).toModuleIso) (by
      intro n m hnm
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro h
      exact (degreeMap_d k B α L adj c I n m hnm h).symm)
  exact ⟨q, degreeMap_apply k B α L hobj adj c I hex⟩

end WeilConjectures.PointDerivedHom
