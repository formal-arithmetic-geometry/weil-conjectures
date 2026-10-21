/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V5
-/
module

public import Sheaf.Paper.ExternalRHomConePairingDefs
import WeilConjectures.Algebra.Homology.InternalHom
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction

/-! # Evaluation of a chain map into global cochains -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
namespace AlgebraicGeometry.Etale.ExternalRHom
variable (A : Type (u + 1)) [CommRing A]

private theorem monoidalAdjunction_unit_tensor
    {B D : Type*} [Category B] [Category D] [MonoidalCategory B] [MonoidalCategory D]
    {L : B ⥤ D} {R : D ⥤ B} [L.Monoidal] [R.LaxMonoidal] (adj : L ⊣ R)
    [adj.IsMonoidal] (P : B) (F : D) [IsIso (adj.counit.app F)] :
    (adj.unit.app P ⊗ₘ 𝟙 (R.obj F)) ≫
      Functor.LaxMonoidal.μ R (L.obj P) F ≫
      R.map ((𝟙 (L.obj P) ⊗ₘ inv (adj.counit.app F)) ≫
        Functor.LaxMonoidal.μ L P (R.obj F)) = adj.unit.app (P ⊗ R.obj F) := by
  have he : R.map (inv (adj.counit.app F)) = adj.unit.app (R.obj F) := by
    apply (cancel_mono (R.map (adj.counit.app F))).1
    rw [← CategoryTheory.Functor.map_comp, IsIso.inv_hom_id,
      CategoryTheory.Functor.map_id]
    exact (adj.right_triangle_components F).symm
  rw [CategoryTheory.Functor.map_comp, ← Functor.LaxMonoidal.μ_natural_assoc]
  simp only [CategoryTheory.Functor.map_id]
  rw [tensorHom_comp_tensorHom_assoc]
  change ((adj.unit.app P ≫ 𝟙 (R.obj (L.obj P))) ⊗ₘ
    (𝟙 (R.obj F) ≫ R.map (inv (adj.counit.app F)))) ≫ _ = _
  erw [Category.comp_id (adj.unit.app P), Category.id_comp]
  rw [he]
  erw [← adj.unit_app_tensor_comp_map_δ_assoc, ← CategoryTheory.Functor.map_comp,
    Functor.Monoidal.δ_μ, CategoryTheory.Functor.map_id, Category.comp_id]
  rfl

private def constantTensorIso {X : Scheme.{u}} (M : ModuleCat.{u + 1} A)
    (F : Modules A X) :
    (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)).obj M ⊗ F ≅
      (presheafToSheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)).obj
        ((Functor.const X.Etaleᵒᵖ).obj M ⊗ F.obj) :=
  (Iso.refl _ ⊗ᵢ (asIso ((sheafificationAdjunction X.smallEtaleTopology
    (ModuleCat.{u + 1} A)).counit.app F)).symm) ≪≫
    Functor.Monoidal.μIso (presheafToSheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) _ _

@[reassoc]
private theorem constantTensorIso_unit {X : Scheme.{u}} (M : ModuleCat.{u + 1} A)
    (F : Modules A X) :
    (toSheafify X.smallEtaleTopology ((Functor.const X.Etaleᵒᵖ).obj M) ⊗ₘ 𝟙 F.obj) ≫
      Functor.LaxMonoidal.μ (sheafToPresheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) _ F ≫
      (constantTensorIso A M F).hom.hom =
        toSheafify X.smallEtaleTopology ((Functor.const X.Etaleᵒᵖ).obj M ⊗ F.obj) := by
  exact monoidalAdjunction_unit_tensor
    (sheafificationAdjunction X.smallEtaleTopology (ModuleCat.{u + 1} A))
    ((Functor.const X.Etaleᵒᵖ).obj M) F

private def rawPair {X : Scheme.{u}} (M : ModuleCat.{u + 1} A)
    {F G : Modules A X} (b : M →ₗ[A] (F ⟶ G)) :
    (Functor.const X.Etaleᵒᵖ).obj M ⊗ F.obj ⟶ G.obj where
  app W := ModuleCat.ofHom (TensorProduct.lift
    { toFun := fun w ↦ ((b w).hom.app W).hom
      map_add' := by intros; rw [map_add]; rfl
      map_smul' := by intros; rw [map_smul]; rfl })
  naturality W V f := by
    apply ModuleCat.hom_ext
    apply TensorProduct.ext'
    intro w e
    exact ConcreteCategory.congr_hom ((b w).hom.naturality f) e

private def constantPair {X : Scheme.{u}} (M : ModuleCat.{u + 1} A)
    {F G : Modules A X} (b : M →ₗ[A] (F ⟶ G)) :
    (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)).obj M ⊗ F ⟶ G :=
  (constantTensorIso A M F).hom ≫
    ((sheafificationAdjunction X.smallEtaleTopology (ModuleCat.{u + 1} A)).homEquiv _ _).symm
      (rawPair A M b)

private theorem constantPair_unit {X : Scheme.{u}} (M : ModuleCat.{u + 1} A)
    {F G : Modules A X} (b : M →ₗ[A] (F ⟶ G)) :
    (toSheafify X.smallEtaleTopology ((Functor.const X.Etaleᵒᵖ).obj M) ⊗ₘ 𝟙 F.obj) ≫
      Functor.LaxMonoidal.μ (sheafToPresheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) _ F ≫
      (constantPair A M b).hom = rawPair A M b := by
  rw [constantPair, ObjectProperty.FullSubcategory.comp_hom,
    constantTensorIso_unit_assoc]
  exact Equiv.apply_symm_apply
    ((sheafificationAdjunction X.smallEtaleTopology (ModuleCat.{u + 1} A)).homEquiv _ _)
    (rawPair A M b)

private theorem constantPair_apply {X : Scheme.{u}} (M : ModuleCat.{u + 1} A)
    {F G : Modules A X} (b : M →ₗ[A] (F ⟶ G)) (W : X.Etaleᵒᵖ)
    (w : M) (e : F.obj.obj W) :
    ((constantPair A M b).hom.app W)
      (tensorSection A _ F W (constantSection A X M W w) e) =
        ((b w).hom.app W) e := by
  exact DFunLike.congr_fun (congrArg ModuleCat.Hom.hom
    (NatTrans.congr_app (constantPair_unit A M b) W)) (w ⊗ₜ[A] e)

private theorem constantPair_ext {X : Scheme.{u}} (M : ModuleCat.{u + 1} A)
    {F G : Modules A X}
    (f g : (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)).obj M ⊗ F ⟶ G)
    (h : ∀ (W : X.Etaleᵒᵖ) (w : M) (e : F.obj.obj W),
      (f.hom.app W) (tensorSection A _ F W (constantSection A X M W w) e) =
      (g.hom.app W) (tensorSection A _ F W (constantSection A X M W w) e)) :
    f = g := by
  have h' :
      (toSheafify X.smallEtaleTopology ((Functor.const X.Etaleᵒᵖ).obj M) ⊗ₘ 𝟙 F.obj) ≫
        Functor.LaxMonoidal.μ (sheafToPresheaf X.smallEtaleTopology
          (ModuleCat.{u + 1} A)) _ F ≫ f.hom =
      (toSheafify X.smallEtaleTopology ((Functor.const X.Etaleᵒᵖ).obj M) ⊗ₘ 𝟙 F.obj) ≫
        Functor.LaxMonoidal.μ (sheafToPresheaf X.smallEtaleTopology
          (ModuleCat.{u + 1} A)) _ F ≫ g.hom := by
    apply NatTrans.ext
    funext W
    apply ModuleCat.hom_ext
    apply TensorProduct.ext'
    exact h W
  apply (cancel_epi (constantTensorIso A M F).inv).1
  apply ((sheafificationAdjunction X.smallEtaleTopology
    (ModuleCat.{u + 1} A)).homEquiv _ _).injective
  let R := sheafToPresheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)
  change toSheafify X.smallEtaleTopology _ ≫
    R.map ((constantTensorIso A M F).inv ≫ f) =
    toSheafify X.smallEtaleTopology _ ≫ R.map ((constantTensorIso A M F).inv ≫ g)
  rw [← constantTensorIso_unit A M F]
  change (_ ≫ _ ≫ R.map (constantTensorIso A M F).hom) ≫
    R.map ((constantTensorIso A M F).inv ≫ f) =
    (_ ≫ _ ≫ R.map (constantTensorIso A M F).hom) ≫
    R.map ((constantTensorIso A M F).inv ≫ g)
  simp only [Category.assoc, ← CategoryTheory.Functor.map_comp, Iso.hom_inv_id_assoc]
  exact h'

private theorem tensorSection_map {X : Scheme.{u}} {M M' N N' : Modules A X}
    (f : M ⟶ M') (g : N ⟶ N') (W : X.Etaleᵒᵖ)
    (x : M.obj.obj W) (y : N.obj.obj W) :
    ((f ⊗ₘ g).hom.app W) (tensorSection A M N W x y) =
      tensorSection A M' N' W ((f.hom.app W) x) ((g.hom.app W) y) := by
  exact (ConcreteCategory.congr_hom
    (NatTrans.congr_app
      (Functor.LaxMonoidal.μ_natural
        (sheafToPresheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) f g) W) (x ⊗ₜ[A] y)).symm

private theorem constantSection_map {X : Scheme.{u}} {M N : ModuleCat.{u + 1} A}
    (f : M ⟶ N) (W : X.Etaleᵒᵖ) (w : M) :
    (((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)).map f).hom.app W)
      (constantSection A X M W w) = constantSection A X N W (f w) := by
  exact (ConcreteCategory.congr_hom
    (NatTrans.congr_app
      (toSheafify_naturality X.smallEtaleTopology
        ((Functor.const X.Etaleᵒᵖ).map f)) W) w).symm

private def evaluationCoefficients {X : Scheme.{u}} (E I : Complexes A X)
    (U : CochainComplex (ModuleCat.{u + 1} A) ℤ) (alpha : U ⟶ homComplex A E I)
    (r q n : ℤ) (h : q + r = n) : (U.X r) →ₗ[A] (E.X q ⟶ I.X n) where
  toFun w := ((alpha.f r).hom w).v q n h
  map_add' := by intros; rw [map_add]; rfl
  map_smul' := by intros; rw [map_smul]; rfl

private def evaluationGraded {X : Scheme.{u}} (E I : Complexes A X)
    (U : CochainComplex (ModuleCat.{u + 1} A) ℤ) (alpha : U ⟶ homComplex A E I)
    (n : ℤ) : (chainEvaluationSource A X U E).X n ⟶ I.X n :=
  HomologicalComplex.mapBifunctorDesc fun r q h ↦
    constantPair A (U.X r) (evaluationCoefficients A E I U alpha r q n (by
      change r + q = n at h
      omega))

private theorem inclusion_evaluationGraded {X : Scheme.{u}} (E I : Complexes A X)
    (U : CochainComplex (ModuleCat.{u + 1} A) ℤ) (alpha : U ⟶ homComplex A E I)
    (r q n : ℤ) (h : r + q = n) :
    HomologicalComplex.ιTensorObj ((constantComplex A X).obj U) E r q n h ≫
      evaluationGraded A E I U alpha n =
        constantPair A (U.X r)
          (evaluationCoefficients A E I U alpha r q n (by omega)) :=
  HomologicalComplex.ι_mapBifunctorDesc _ r q h

private theorem evaluation_differential {X : Scheme.{u}} (E I : Complexes A X)
    (U : CochainComplex (ModuleCat.{u + 1} A) ℤ) (alpha : U ⟶ homComplex A E I)
    (r q n m : ℤ) (hn : q + r = n) (hm : n + 1 = m)
    (w : U.X r) :
    (((alpha.f r).hom w).v q n hn) ≫ I.d n m =
      (((alpha.f (r + 1)).hom ((U.d r (r + 1)) w)).v q m (by omega)) +
        r.negOnePow • (E.d q (q + 1) ≫
          (((alpha.f r).hom w).v (q + 1) m (by omega))) := by
  have h := (ConcreteCategory.congr_hom (alpha.comm r (r + 1)) w).symm
  change (alpha.f (r + 1)).hom ((U.d r (r + 1)) w) =
    CochainComplex.HomComplex.δ r (r + 1) ((alpha.f r).hom w) at h
  have hv := congrArg (fun z ↦ z.v q m (by omega)) h
  rw [CochainComplex.HomComplex.δ_v r (r + 1) rfl _ q m (by omega)
    n (q + 1) (by omega) rfl, Int.negOnePow_succ, Units.neg_smul] at hv
  exact eq_add_of_sub_eq (by simpa only [sub_eq_add_neg] using hv.symm)

/-- Every map into global cochains has its unsigned chain evaluation.
Source: Stacks Project, Cohomology on Sites, Tags 0A8X and 0A90
(blueprint: lem-pur-global-hom-chain-evaluation).

Proof: for each r and q the A-linear map w to alpha(w)^q gives the bilinear
pairing (w,e) to alpha(w)^q(e). It respects restriction. Extend first across
constant sheafification and then across the sheafified tensor, and take the
coproduct over r+q=n. Since alpha is a chain map, the Hom differential identity
gives d_I(alpha(w)(e)) = alpha(dw)(e) + (-1)^r alpha(w)(d_E e).
This is the total-tensor differential identity on each summand. The coproduct
universal property gives the chain map, and the construction on pure tensors
gives the stated equation. Neither boundedness nor flatness is needed; integer
powers give the same calculation in negative degrees. -/
theorem globalHom_chain_evaluation {X : Scheme.{u}} (E I : Complexes A X)
    (U : CochainComplex (ModuleCat.{u + 1} A) ℤ) (alpha : U ⟶ homComplex A E I) :
    ∃ t : chainEvaluationSource A X U E ⟶ I,
      IsChainEvaluation A E I U alpha t := by
  let C := (constantComplex A X).obj U
  have hc (n m : ℤ) (h : n + 1 = m) :
      evaluationGraded A E I U alpha n ≫ I.d n m =
        (C ⊗ E).d n m ≫ evaluationGraded A E I U alpha m := by
    apply HomologicalComplex.mapBifunctor.hom_ext
    intro r q hrq
    change r + q = n at hrq
    rw [← Category.assoc, inclusion_evaluationGraded,
      ← Category.assoc, CochainComplex.ιTensorObj_d C E r q n m hrq h,
      Preadditive.add_comp, Linear.units_smul_comp, Category.assoc, Category.assoc,
      inclusion_evaluationGraded, inclusion_evaluationGraded]
    apply constantPair_ext A (U.X r)
    intro W w e
    let x := constantSection A X (U.X r) W w
    have ht₁ : (((C.d r (r + 1)) ▷ E.X q).hom.app W)
        (tensorSection A _ _ W x e) =
      tensorSection A _ _ W
        (constantSection A X (U.X (r + 1)) W ((U.d r (r + 1)) w)) e := by
      have hh := tensorSection_map A (C.d r (r + 1)) (𝟙 (E.X q)) W x e
      simp only [tensorHom_id, ObjectProperty.FullSubcategory.id_hom, NatTrans.id_app,
        ModuleCat.id_apply, x, C, constantComplex,
        Functor.mapHomologicalComplex_obj_d] at hh
      change _ = tensorSection A _ _ W
        ((((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)).map
          (U.d r (r + 1))).hom.app W) (constantSection A X (U.X r) W w)) e at hh
      rw [constantSection_map] at hh
      exact hh
    have ht₂ : ((C.X r ◁ E.d q (q + 1)).hom.app W)
        (tensorSection A _ _ W x e) =
      tensorSection A _ _ W x (((E.d q (q + 1)).hom.app W) e) := by
      have hh := tensorSection_map A (𝟙 (C.X r)) (E.d q (q + 1)) W x e
      simp only [id_tensorHom, ObjectProperty.FullSubcategory.id_hom, NatTrans.id_app,
        ModuleCat.id_apply] at hh
      with_unfolding_all exact hh
    change ((I.d n m).hom.app W)
        (((constantPair A (U.X r) _).hom.app W) (tensorSection A _ _ W x e)) =
      ((constantPair A (U.X (r + 1)) _).hom.app W)
        ((((C.d r (r + 1)) ▷ E.X q).hom.app W) (tensorSection A _ _ W x e)) +
      r.negOnePow • (((constantPair A (U.X r) _).hom.app W)
        (((C.X r ◁ E.d q (q + 1)).hom.app W) (tensorSection A _ _ W x e)))
    rw [ht₁, ht₂]
    simp only [x, constantPair_apply]
    exact ConcreteCategory.congr_hom
      (NatTrans.congr_app (congrArg InducedCategory.Hom.hom
        (evaluation_differential A E I U alpha r q n m (by omega) h w)) W) e
  let t : chainEvaluationSource A X U E ⟶ I :=
    { f := fun n ↦ evaluationGraded A E I U alpha n
      comm' := fun n m h ↦ hc n m h }
  refine ⟨t, ?_⟩
  intro r q W w e
  have h := inclusion_evaluationGraded A E I U alpha r q (q + r) (add_comm r q)
  have hv := ConcreteCategory.congr_hom (congrArg (fun z ↦ z.hom.app W) h)
    (tensorSection A _ _ W (constantSection A X (U.X r) W w) e)
  exact hv.trans (constantPair_apply A (U.X r)
    (evaluationCoefficients A E I U alpha r q (q + r) rfl) W w e)

end AlgebraicGeometry.Etale.ExternalRHom
