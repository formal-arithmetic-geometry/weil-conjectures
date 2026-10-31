/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.Modules.PullbackMonoidal
public import WeilConjectures.AlgebraicGeometry.Cohomology.Defs
public import Mathlib.CategoryTheory.Sites.Descent.IsPrestack
public import WeilConjectures.AlgebraicGeometry.Modules.PullbackUnit
import WeilConjectures.AlgebraicGeometry.Modules.TensorSection
import WeilConjectures.AlgebraicGeometry.PullbackTensorComposition
import WeilConjectures.AlgebraicGeometry.PullbackMonoidalUnitComparison
import WeilConjectures.AlgebraicGeometry.Modules.AffineDescent
import WeilConjectures.Mathlib.CategoryTheory.Sites.Descent.IsPrestack
/-! # Tensoring frames under monoidal pullback
Source: Stacks Project, Tags 0095 and 0096, tensor pullback coherence.
(blueprint: lem-pur-tensor-pullback-frames). -/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
universe u v u' v' u'' v''
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian MonoidalCategory Opposite
open scoped AlgebraicGeometry.Scheme.Modules
namespace AlgebraicGeometry.Scheme.Modules

/-- Tensor two pulled-back frames using the monoidal comparison.
Source: Stacks 0095, 0096 (blueprint: lem-pur-tensor-pullback-frames). -/
def tensorPullbackFrames {T : Scheme.{u}} (L M : T.Modules)
    {X : Scheme.{u}} (f : X ⟶ T)
    (x : (Scheme.Modules.pullback f).obj (Scheme.Modules.unit T) ⟶
      (Scheme.Modules.pullback f).obj L)
    (y : (Scheme.Modules.pullback f).obj (Scheme.Modules.unit T) ⟶
      (Scheme.Modules.pullback f).obj M) :
    (Scheme.Modules.pullback f).obj (Scheme.Modules.unit T) ⟶
      (Scheme.Modules.pullback f).obj (L ⊗ M) :=
  (Scheme.Modules.pullback f).map (λ_ (Scheme.Modules.unit T)).inv ≫
    (Functor.Monoidal.μIso (Scheme.Modules.pullback f)
      (Scheme.Modules.unit T) (Scheme.Modules.unit T)).inv ≫
        (x ⊗ₘ y) ≫ (Functor.Monoidal.μIso (Scheme.Modules.pullback f) L M).hom
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Tensoring the pullbacks of two global maps equals the pullback of their tensor.
Source: Stacks 0095, 0096 (blueprint: lem-pur-tensor-pullback-frames).
Proof: monoidal naturality and cancellation of comparison isomorphisms; for scalars,
check pure tensors and use linearity of all module maps. -/
theorem tensorPullbackFrames_map {T : Scheme.{u}} (L M : T.Modules)
    {X : Scheme.{u}} (f : X ⟶ T)
    (s : Scheme.Modules.unit T ⟶ L) (t : Scheme.Modules.unit T ⟶ M) :
    tensorPullbackFrames L M f ((Scheme.Modules.pullback f).map s)
      ((Scheme.Modules.pullback f).map t) =
      (Scheme.Modules.pullback f).map
        ((λ_ (Scheme.Modules.unit T)).inv ≫ (s ⊗ₘ t)) := by
  unfold tensorPullbackFrames
  have hn := Functor.LaxMonoidal.μ_natural (Scheme.Modules.pullback f) s t
  change ((Scheme.Modules.pullback f).map s ⊗ₘ
      (Scheme.Modules.pullback f).map t) ≫
      (Functor.Monoidal.μIso (Scheme.Modules.pullback f) L M).hom =
    (Functor.Monoidal.μIso (Scheme.Modules.pullback f)
      (Scheme.Modules.unit T) (Scheme.Modules.unit T)).hom ≫
      (Scheme.Modules.pullback f).map (s ⊗ₘ t) at hn
  rw [hn]
  simp only [Iso.inv_hom_id_assoc]
  exact ((Scheme.Modules.pullback f).map_comp _ _).symm

private lemma tensor_comparison_inv
    {C : Type u} [Category.{v} C] [MonoidalCategory C]
    {D : Type u'} [Category.{v'} D] [MonoidalCategory D]
    {E : Type u''} [Category.{v''} E] [MonoidalCategory E]
    (F : C ⥤ D) (G : D ⥤ E) (H : C ⥤ E)
    [F.Monoidal] [G.Monoidal] [H.Monoidal] (c : F ⋙ G ≅ H)
    (ht : ∀ A B, (Functor.Monoidal.μIso G (F.obj A) (F.obj B)).hom ≫
      G.map (Functor.Monoidal.μIso F A B).hom ≫ c.hom.app (A ⊗ B) =
      (c.hom.app A ⊗ₘ c.hom.app B) ≫ (Functor.Monoidal.μIso H A B).hom)
    (A B : C) :
    c.inv.app (A ⊗ B) ≫ G.map (Functor.Monoidal.μIso F A B).inv =
      (Functor.Monoidal.μIso H A B).inv ≫ (c.inv.app A ⊗ₘ c.inv.app B) ≫
        (Functor.Monoidal.μIso G (F.obj A) (F.obj B)).hom := by
  apply (cancel_mono (G.map (Functor.Monoidal.μIso F A B).hom ≫
    c.hom.app (A ⊗ B))).mp
  simp only [Category.assoc, ← Functor.map_comp_assoc, Iso.inv_hom_id]
  rw [ht]
  simp only [tensorHom_comp_tensorHom_assoc, Iso.inv_hom_id_app,
    id_tensorHom_id, Category.id_comp, Iso.inv_hom_id]
  all_goals simp only [CategoryTheory.Functor.map_id, Category.id_comp, Iso.inv_hom_id_app]

private lemma tensor_frame_comparison
    {C : Type u} [Category.{v} C] [MonoidalCategory C]
    {D : Type u'} [Category.{v'} D] [MonoidalCategory D]
    {E : Type u''} [Category.{v''} E] [MonoidalCategory E]
    (F : C ⥤ D) (G : D ⥤ E) (H : C ⥤ E)
    [F.Monoidal] [G.Monoidal] [H.Monoidal] (c : F ⋙ G ≅ H)
    (ht : ∀ A B, (Functor.Monoidal.μIso G (F.obj A) (F.obj B)).hom ≫
      G.map (Functor.Monoidal.μIso F A B).hom ≫ c.hom.app (A ⊗ B) =
      (c.hom.app A ⊗ₘ c.hom.app B) ≫ (Functor.Monoidal.μIso H A B).hom)
    (A L M : C) (s : A ⟶ A ⊗ A) (x : F.obj A ⟶ F.obj L) (y : F.obj A ⟶ F.obj M) :
    c.inv.app A ≫ G.map (F.map s ≫ (Functor.Monoidal.μIso F A A).inv ≫
      (x ⊗ₘ y) ≫ (Functor.Monoidal.μIso F L M).hom) ≫ c.hom.app (L ⊗ M) =
    H.map s ≫ (Functor.Monoidal.μIso H A A).inv ≫
      ((c.inv.app A ≫ G.map x ≫ c.hom.app L) ⊗ₘ
        (c.inv.app A ≫ G.map y ≫ c.hom.app M)) ≫
      (Functor.Monoidal.μIso H L M).hom := by
  simp only [Functor.map_comp, Category.assoc]
  have hn := c.inv.naturality s
  dsimp only [Functor.comp_map] at hn
  rw [← reassoc_of% hn]
  erw [reassoc_of% (tensor_comparison_inv F G H c ht A A)]
  simp only [Functor.Monoidal.μIso_hom]
  rw [← Functor.LaxMonoidal.μ_natural_assoc]
  simp only [Functor.Monoidal.μIso_hom] at ht
  rw [ht]
  simp only [tensorHom_comp_tensorHom_assoc]
/-- The tensor pairing commutes with ordinary pullback composition.
Source: Stacks 0095, 0096 (blueprint: lem-pur-tensor-pullback-frames).
Proof: monoidal naturality and cancellation of comparison isomorphisms; for scalars,
check pure tensors and use linearity of all module maps. -/
theorem tensorPullbackFrames_comp {X Y Z : Scheme.{u}} (f : Y ⟶ X) (g : Z ⟶ Y)
    (L M : X.Modules)
    (x : (Scheme.Modules.pullback f).obj (Scheme.Modules.unit X) ⟶
      (Scheme.Modules.pullback f).obj L)
    (y : (Scheme.Modules.pullback f).obj (Scheme.Modules.unit X) ⟶
      (Scheme.Modules.pullback f).obj M) :
    (Scheme.Modules.pullbackComp g f).inv.app (Scheme.Modules.unit X) ≫
      (Scheme.Modules.pullback g).map
        (tensorPullbackFrames L M f x y) ≫
      (Scheme.Modules.pullbackComp g f).hom.app (L ⊗ M) =
    tensorPullbackFrames L M (g ≫ f)
      ((Scheme.Modules.pullbackComp g f).inv.app (Scheme.Modules.unit X) ≫
        (Scheme.Modules.pullback g).map x ≫ (Scheme.Modules.pullbackComp g f).hom.app L)
      ((Scheme.Modules.pullbackComp g f).inv.app (Scheme.Modules.unit X) ≫
        (Scheme.Modules.pullback g).map y ≫ (Scheme.Modules.pullbackComp g f).hom.app M) := by
  unfold tensorPullbackFrames
  convert tensor_frame_comparison (Scheme.Modules.pullback f) (Scheme.Modules.pullback g)
    (Scheme.Modules.pullback (g ≫ f)) (Scheme.Modules.pullbackComp g f)
    (Scheme.Modules.pullbackComp_tensor g f) _ L M _ x y

private lemma scalar_natural {X : Scheme.{u}} {A B : X.Modules}
    (f : A ⟶ B) (r : Γ(X, ⊤)) :
    Scheme.Modules.smulHom A r ≫ f = f ≫ Scheme.Modules.smulHom B r := by
  ext U x
  exact Scheme.Modules.Hom.app_smul f _ _

private lemma tensor_scalar_left {X : Scheme.{u}} (A B : X.Modules) (r : Γ(X, ⊤)) :
    Scheme.Modules.smulHom A r ▷ B = Scheme.Modules.smulHom (A ⊗ B) r := by
  apply (cancel_epi (SheafOfModules.tensorObjIsoSheafification A B).inv).mp
  apply ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).homEquiv
    (A.val ⊗ B.val) (A ⊗ B : X.Modules)).injective
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro x y
  change (Scheme.Modules.smulHom A r ▷ B).app U.unop
      (Scheme.Modules.tmulSection x y) =
    (Scheme.Modules.smulHom (A ⊗ B) r).app U.unop (Scheme.Modules.tmulSection x y)
  rw [Scheme.Modules.whiskerRight_app_tmulSection, Scheme.Modules.smulHom_app_apply,
    Scheme.Modules.smul_tmulSection, Scheme.Modules.smulHom_app_apply]

private lemma tensor_scalar_right {X : Scheme.{u}} (A B : X.Modules) (r : Γ(X, ⊤)) :
    A ◁ Scheme.Modules.smulHom B r = Scheme.Modules.smulHom (A ⊗ B) r := by
  apply (cancel_epi (SheafOfModules.tensorObjIsoSheafification A B).inv).mp
  apply ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).homEquiv
    (A.val ⊗ B.val) (A ⊗ B : X.Modules)).injective
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro x y
  change (A ◁ Scheme.Modules.smulHom B r).app U.unop
      (Scheme.Modules.tmulSection x y) =
    (Scheme.Modules.smulHom (A ⊗ B) r).app U.unop (Scheme.Modules.tmulSection x y)
  rw [Scheme.Modules.whiskerLeft_app_tmulSection, Scheme.Modules.smulHom_app_apply,
    Scheme.Modules.tmulSection_smul, Scheme.Modules.smulHom_app_apply]

/-- Scaling the first frame scales their tensor frame.
Source: Stacks 0095, 0096 (blueprint: lem-pur-tensor-pullback-frames).
Proof: monoidal naturality and cancellation of comparison isomorphisms; for scalars,
check pure tensors and use linearity of all module maps. -/
theorem tensorPullbackFrames_scalar_left {T : Scheme.{u}} (L M : T.Modules)
    {X : Scheme.{u}} (f : X ⟶ T)
    (x : (Scheme.Modules.pullback f).obj (Scheme.Modules.unit T) ⟶
      (Scheme.Modules.pullback f).obj L)
    (y : (Scheme.Modules.pullback f).obj (Scheme.Modules.unit T) ⟶
      (Scheme.Modules.pullback f).obj M) (r : Γ(X, ⊤)) :
    tensorPullbackFrames L M f
      (Scheme.Modules.smulHom _ r ≫ x) y =
      Scheme.Modules.smulHom _ r ≫ tensorPullbackFrames L M f x y := by
  unfold tensorPullbackFrames
  have h : (Scheme.Modules.smulHom _ r ≫ x) ⊗ₘ y =
      Scheme.Modules.smulHom _ r ≫ (x ⊗ₘ y) := by
    rw [← tensor_scalar_left]
    erw [← MonoidalCategory.tensorHom_id, tensorHom_comp_tensorHom]
    simp only [Category.id_comp]
  let d := (Scheme.Modules.pullback f).map (λ_ (Scheme.Modules.unit T)).inv ≫
    (Functor.Monoidal.μIso (Scheme.Modules.pullback f)
      (Scheme.Modules.unit T) (Scheme.Modules.unit T)).inv
  have hn := scalar_natural d r
  have hn' := congrArg (· ≫ (x ⊗ₘ y) ≫
    (Functor.Monoidal.μIso (Scheme.Modules.pullback f) L M).hom) hn
  rw [h]
  convert hn'.symm using 1 <;> rfl
/-- Scaling the second frame scales their tensor frame.
Source: Stacks 0095, 0096 (blueprint: lem-pur-tensor-pullback-frames).
Proof: monoidal naturality and cancellation of comparison isomorphisms; for scalars,
check pure tensors and use linearity of all module maps. -/
theorem tensorPullbackFrames_scalar_right {T : Scheme.{u}} (L M : T.Modules)
    {X : Scheme.{u}} (f : X ⟶ T)
    (x : (Scheme.Modules.pullback f).obj (Scheme.Modules.unit T) ⟶
      (Scheme.Modules.pullback f).obj L)
    (y : (Scheme.Modules.pullback f).obj (Scheme.Modules.unit T) ⟶
      (Scheme.Modules.pullback f).obj M) (r : Γ(X, ⊤)) :
    tensorPullbackFrames L M f
      x (Scheme.Modules.smulHom _ r ≫ y) =
      Scheme.Modules.smulHom _ r ≫ tensorPullbackFrames L M f x y := by
  unfold tensorPullbackFrames
  have h : x ⊗ₘ (Scheme.Modules.smulHom _ r ≫ y) =
      Scheme.Modules.smulHom _ r ≫ (x ⊗ₘ y) := by
    rw [← tensor_scalar_right]
    erw [← MonoidalCategory.id_tensorHom, tensorHom_comp_tensorHom]
    simp only [Category.id_comp]
  let d := (Scheme.Modules.pullback f).map (λ_ (Scheme.Modules.unit T)).inv ≫
    (Functor.Monoidal.μIso (Scheme.Modules.pullback f)
      (Scheme.Modules.unit T) (Scheme.Modules.unit T)).inv
  have hn := scalar_natural d r
  have hn' := congrArg (· ≫ (x ⊗ₘ y) ≫
    (Functor.Monoidal.μIso (Scheme.Modules.pullback f) L M).hom) hn
  rw [h]
  convert hn'.symm using 1 <;> rfl


instance {T X : Scheme.{u}} (L M : T.Modules) (f : X ⟶ T)
    (x : (pullback f).obj (unit T) ⟶ (pullback f).obj L)
    (y : (pullback f).obj (unit T) ⟶ (pullback f).obj M) [IsIso x] [IsIso y] :
    IsIso (tensorPullbackFrames L M f x y) := by
  unfold tensorPullbackFrames
  infer_instance

/-- The tensor pairing equals the formula using the unit comparison isomorphism.
Source: Stacks 0095, 0096 (blueprint: lem-pur-tensor-pullback-frames).
Proof: the unit comparison inverse is the lax monoidal unit map. Left unitality
identifies the two diagonal maps, and tensoring the input frames preserves equality. -/
theorem tensorPullbackFrames_eq_unit {T X : Scheme.{u}} (L M : T.Modules) (f : X ⟶ T)
    (x : (pullback f).obj (unit T) ⟶ (pullback f).obj L)
    (y : (pullback f).obj (unit T) ⟶ (pullback f).obj M) :
    tensorPullbackFrames L M f x y =
      (pullbackObjUnitIso f).hom ≫ (λ_ (unit X)).inv ≫
        ((pullbackObjUnitIso f).inv ⊗ₘ (pullbackObjUnitIso f).inv) ≫
          (x ⊗ₘ y) ≫ (Functor.Monoidal.μIso (pullback f) L M).hom := by
  let F := Scheme.Modules.pullback f
  let e := Scheme.Modules.pullbackObjUnitIso f
  have he : e.inv = Functor.LaxMonoidal.ε F := by
    apply (cancel_mono e.hom).mp
    rw [Iso.inv_hom_id]
    exact (Functor.Monoidal.ε_η F).symm.trans
      (congrArg (Functor.LaxMonoidal.ε F ≫ ·)
        (Scheme.Modules.pullback_monoidal_unit_comparison f))
  have h : e.hom ≫ (λ_ (Scheme.Modules.unit X)).inv ≫ (e.inv ⊗ₘ e.inv) ≫
      (Functor.Monoidal.μIso F (Scheme.Modules.unit T) (Scheme.Modules.unit T)).hom =
      F.map (λ_ (Scheme.Modules.unit T)).inv := by
    rw [he, MonoidalCategory.tensorHom_def']
    simp only [Category.assoc]
    erw [← leftUnitor_inv_naturality_assoc (Functor.LaxMonoidal.ε F)]
    rw [← he, Iso.hom_inv_id_assoc, he]
    exact Functor.LaxMonoidal.left_unitality_inv F _
  have h' := congrArg (· ≫ (Functor.Monoidal.μIso F
      (Scheme.Modules.unit T) (Scheme.Modules.unit T)).inv) h
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id] at h'
  unfold tensorPullbackFrames
  symm
  change e.hom ≫ (λ_ (Scheme.Modules.unit X)).inv ≫ (e.inv ⊗ₘ e.inv) ≫
    (x ⊗ₘ y) ≫ (Functor.Monoidal.μIso F L M).hom = _
  simpa only [Category.assoc] using
    congrArg (· ≫ (x ⊗ₘ y) ≫ (Functor.Monoidal.μIso F L M).hom) h'

/-- Tensor frames commute with the module pseudofunctor's restriction of morphisms.
Source: Stacks 01CD, pullback of tensor products
(blueprint: lem-pur-tensor-pullback-frames).
Proof: express restriction by the ordinary pullback-composition isomorphism,
then apply the tensor compatibility of that isomorphism. -/
theorem tensorPullbackFrames_pullHom {T X Y : Scheme.{u}} (L M : T.Modules)
    (f : X ⟶ T) (g : Y ⟶ X) (q : Y ⟶ T) (h : g ≫ f = q)
    (x : (pullback f).obj (unit T) ⟶ (pullback f).obj L)
    (y : (pullback f).obj (unit T) ⟶ (pullback f).obj M) :
    Pseudofunctor.LocallyDiscreteOpToCat.pullHom (F := modulesPseudofunctor)
      (f₁ := f) (f₂ := f) (tensorPullbackFrames L M f x y) g q q h h =
      tensorPullbackFrames L M q
        (Pseudofunctor.LocallyDiscreteOpToCat.pullHom (F := modulesPseudofunctor)
          (f₁ := f) (f₂ := f) x g q q h h)
        (Pseudofunctor.LocallyDiscreteOpToCat.pullHom (F := modulesPseudofunctor)
          (f₁ := f) (f₂ := f) y g q q h h) := by
  rw [modulesPseudofunctor_pullHom_eq_pullbackCompOfEq,
    modulesPseudofunctor_pullHom_eq_pullbackCompOfEq,
    modulesPseudofunctor_pullHom_eq_pullbackCompOfEq]
  subst q
  simpa only [pullbackCompOfEq, pullbackCongr, eqToIso_refl, Iso.app,
    Iso.refl_hom, Iso.refl_inv, Iso.trans_hom, Iso.trans_inv, NatTrans.id_app,
    Category.comp_id, Category.id_comp] using tensorPullbackFrames_comp f g L M x y

private theorem presheafHom_map_eq {T : Scheme.{u}} (L M : T.Modules)
    {A B : Over T} (f : B ⟶ A)
    (x : (pullback A.hom).obj L ⟶ (pullback A.hom).obj M) :
    (modulesPseudofunctor.presheafHom L M).map f.op x =
      Pseudofunctor.LocallyDiscreteOpToCat.pullHom (F := modulesPseudofunctor)
        (f₁ := A.hom) (f₂ := A.hom) x f.left B.hom B.hom
        (Over.w f) (Over.w f) := by
  simp only [Pseudofunctor.presheafHom_map, TypeCat.ofHom_apply, Quiver.Hom.unop_op]

/-- The presheaf tensor pairing commutes with restriction over the base.
Source: Stacks 01CD (blueprint: lem-pur-tensor-pullback-frames).
Proof: express the presheaf maps by pullHom and use monoidal composition coherence. -/
theorem tensorPullbackFrames_presheaf_map {T : Scheme.{u}} (L M N : T.Modules)
    {A B : Over T} (f : B ⟶ A) (e : (L ⊗ M : T.Modules) ⟶ N)
    (x : (pullback A.hom).obj (unit T) ⟶ (pullback A.hom).obj L)
    (y : (pullback A.hom).obj (unit T) ⟶ (pullback A.hom).obj M) :
    (modulesPseudofunctor.presheafHom (unit T) N).map f.op
        (tensorPullbackFrames L M A.hom x y ≫ (pullback A.hom).map e) =
      tensorPullbackFrames L M B.hom
        ((modulesPseudofunctor.presheafHom (unit T) L).map f.op x)
        ((modulesPseudofunctor.presheafHom (unit T) M).map f.op y) ≫
        (pullback B.hom).map e := by
  rw [presheafHom_map_eq,
    Pseudofunctor.LocallyDiscreteOpToCat.pullHom_comp _ _ _ B.hom B.hom B.hom
      (Over.w f) (Over.w f) (Over.w f),
    tensorPullbackFrames_pullHom, presheafHom_map_eq, presheafHom_map_eq]
  congr 1
  exact Pseudofunctor.LocallyDiscreteOpToCat.pullHom_map
    (F := modulesPseudofunctor) e A.hom f.left B.hom (Over.w f)

/-- Restricting a pulled-back global map gives its pullback on the smaller object.
Source: Stacks 01CD (blueprint: lem-pur-tensor-pullback-frames).
Proof: use the pseudofunctor restriction formula on a mapped global morphism. -/
theorem pullbackMap_presheaf_map {T : Scheme.{u}} (L M : T.Modules)
    {A B : Over T} (f : B ⟶ A) (s : L ⟶ M) :
    (modulesPseudofunctor.presheafHom L M).map f.op ((pullback A.hom).map s) =
      (pullback B.hom).map s := by
  rw [presheafHom_map_eq]
  exact Pseudofunctor.LocallyDiscreteOpToCat.pullHom_map
    (F := modulesPseudofunctor) s A.hom f.left B.hom (Over.w f)

attribute [irreducible] tensorPullbackFrames

end AlgebraicGeometry.Scheme.Modules
