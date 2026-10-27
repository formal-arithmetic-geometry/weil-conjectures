/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.CoherentHigherImageClasses
public import Sheaf.AlgebraicGeometry.TensorPullbackQuasiCoherent
public import Sheaf.AlgebraicGeometry.QcoherentPullbackSections
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.InternalHom
import Mathlib.Lean.Meta.CongrTheorems

/-! # Tensor coefficient compatibility of successive etale restrictions -/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.Modules
/- The chart pullback objects have two definitionally equal presentations. Build the
conversion by congruence and cache repeated subproofs, rather than asking the kernel
to unfold the tensor constructions independently at every occurrence. -/
private meta def strictCongr (cache : IO.Ref (Std.HashMap Lean.Expr Lean.Expr)) :
    Nat → Lean.MVarId → Lean.MetaM Unit
  | 0, g => Lean.Meta.withReducible g.hrefl
  | n + 1, g => g.withContext do
    let g ← Lean.Meta.withReducible g.eqOfHEq
    let ty ← Lean.Meta.withReducible g.getType'
    if let some pf := (← cache.get)[ty]? then
      g.assign pf
      return
    if ty.isForall then
      let (_, g) ← g.intro1
      strictCongr cache n g
      return
    let some (_, lhs, _, rhs) := ty.heq? |
      throwError "strict congruence expected HEq, got {ty}"
    let solve : Lean.MetaM Unit := do
      if lhs == rhs then
        Lean.Meta.withReducible g.hrefl
      else if ← Lean.Meta.isProof lhs then
        let pf ← Lean.Meta.mkConstWithFreshMVarLevels ``proof_irrel_heq
        let gs ← Lean.Meta.withReducible (g.apply pf)
        for h in gs do strictCongr cache n h
      else if lhs.isApp && rhs.isApp && lhs.getAppFn == rhs.getAppFn then
        let f := lhs.getAppFn
        let info ← Lean.Meta.getFunInfoNArgs f lhs.getAppNumArgs
        let cthm ← Lean.Meta.mkRichHCongr (forceHEq := true)
          (← Lean.Meta.inferType f) info (fixedFun := true) (fixedParams := #[])
        let gs ← Lean.Meta.withReducible (g.apply (cthm.proof.beta #[f]))
        for h in gs do strictCongr cache n h
      else
        let lhs' ← Lean.Meta.withReducible (Lean.Meta.whnf lhs)
        let rhs' ← Lean.Meta.withReducible (Lean.Meta.whnf rhs)
        if lhs' != lhs || rhs' != rhs then
          let g ← g.change (← Lean.Meta.mkHEq lhs' rhs')
          strictCongr cache n g
        else
          let tp ← Lean.Meta.inferType lhs
          if tp.getAppFn.isConstOf ``AlgebraicGeometry.Scheme then
            let g ← Lean.Meta.withReducible g.heqOfEq
            let projectionProof ← Lean.Meta.mkConstWithFreshMVarLevels
              ``CategoryTheory.MorphismProperty.Over.pullback_obj_left
            let gs ← Lean.Meta.withReducible (g.apply projectionProof)
            for h in gs do strictCongr cache n h
          else
            Lean.Meta.withReducible g.hrefl
    solve
    let pf ← Lean.instantiateMVars (Lean.mkMVar g)
    cache.modify (·.insert ty pf)

noncomputable section
set_option autoImplicit false
attribute [local irreducible] tensorPullback tensorPullbackObj tensorSectionsComp
  tensorSectionsUnit qcoherentPullbackSection coherentEtaleRestrictionIso
attribute [local instance 2000]
  instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensCarrierAbPresheaf
attribute [local instance] Etale.RawRestrictedComparison.etaleComposition
  Etale.RawRestrictedComparison.etaleIdentities Etale.RawRestrictedComparison.etalePullbacks
  Etale.RawRestrictedComparison.etaleBaseChange Etale.RawRestrictedComparison.sheafifyInstance
  Etale.RawRestrictedComparison.weakSheafifyInstance
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem sheafCompose_obj_map {C : Type*} [Category C]
    (J : GrothendieckTopology C) (F : Sheaf J AddCommGrpCat.{u})
    {U V : Cᵒᵖ} (a : U ⟶ V) :
    ((sheafCompose J AddCommGrpCat.uliftFunctor.{u + 1, u}).obj F).obj.map a =
      AddCommGrpCat.uliftFunctor.{u + 1, u}.map (F.obj.map a) := rfl


private theorem tensorSheaf_map {Y : Scheme.{u}} (F : Y.Modules)
    [F.IsQuasicoherent] {U V : Y.Etale} (a : U ⟶ V) :
    (etaleTensorSectionsSheaf F).obj.map a.op = etaleTensorSectionsRestriction F a := rfl


private theorem liftedSections_map {Y : Scheme.{u}} (F : Y.Modules)
    [F.IsQuasicoherent] {U V : Y.Etale} (a : U ⟶ V) :
    (liftedCoherentEtaleSheaf F).obj.map a.op =
      AddCommGrpCat.uliftFunctor.{u + 1, u}.map (etaleTensorSectionsRestriction F a) := by
  change ((sheafCompose Y.smallEtaleTopology AddCommGrpCat.uliftFunctor.{u + 1, u}).obj
    (etaleTensorSectionsSheaf F)).obj.map a.op = _
  rw [sheafCompose_obj_map, tensorSheaf_map]


private theorem leftAdjointUniq_homEquiv_comp {C D : Type*} [Category C] [Category D]
    {L L' : C ⥤ D} {R : D ⥤ C} (a : L ⊣ R) (a' : L' ⊣ R)
    (X : C) (Y : D) (t : L'.obj X ⟶ Y) :
    a.homEquiv _ _ ((a.leftAdjointUniq a').hom.app X ≫ t) = a'.homEquiv _ _ t := by
  rw [a.homEquiv_naturality_right, Adjunction.homEquiv_leftAdjointUniq_hom_app,
    a'.homEquiv_unit]


private theorem iso_factor {C : Type*} [Category C] {A B D : C}
    (e : A ≅ B) (r : A ≅ D) : e = r ≪≫ (e.symm ≪≫ r).symm := by
  apply Iso.ext
  simp

private theorem ulift_map_apply {A B : AddCommGrpCat.{u}} (f : A ⟶ B) (x : A) :
    AddCommGrpCat.uliftFunctor.{u + 1, u}.map f (ULift.up x) = ULift.up (f x) := rfl

private theorem eqLiftedHom {A B : AddCommGrpCat.{u}}
    (h : AddCommGrpCat.uliftFunctor.{u + 1, u}.obj A ⟶
      AddCommGrpCat.uliftFunctor.{u + 1, u}.obj B) (f : A ⟶ B)
    (hh : ∀ s : A, h (ULift.up s) = ULift.up (f s)) :
    h = AddCommGrpCat.uliftFunctor.map f := by
  apply ConcreteCategory.hom_ext
  intro s
  obtain ⟨s⟩ := s
  exact (hh s).trans (ulift_map_apply f s).symm

private theorem homEquiv_iso_factor {C D : Type*} [Category C] [Category D]
    {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) {A : C} {B B' : D}
    (e : B ≅ B') (θ : A ⟶ R.obj B) (t : L.obj A ⟶ B')
    (h : θ ≫ R.map e.hom = adj.homEquiv _ _ t) :
    θ = adj.homEquiv _ _ (t ≫ e.inv) := by
  rw [adj.homEquiv_naturality_right]
  have ht := congrArg (fun z ↦ z ≫ R.map e.inv) h
  simpa only [Category.assoc, ← R.map_comp, e.hom_inv_id,
    R.map_id, Category.comp_id] using ht


private theorem homEquiv_iso_factor_two {C D : Type*} [Category C] [Category D]
    {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) {A : C} {B₀ B B' : D}
    (e : B ≅ B') (θ : A ⟶ R.obj B) (t : L.obj A ⟶ B₀) (s : B₀ ⟶ B')
    (h : θ ≫ R.map e.hom = adj.homEquiv _ _ (t ≫ s)) :
    θ = adj.homEquiv _ _ (t ≫ s ≫ e.inv) := by
  simpa only [Category.assoc] using homEquiv_iso_factor adj e θ (t ≫ s) h


private theorem localizationUnit_app {Y Z : Scheme.{u}} (b : Z ⟶ Y)
    [AlgebraicGeometry.Etale b] (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})
    (U : Y.Etale) :
    ((Etale.localizationRestrictionLowerStarAdjunction AddCommGrpCat.{u + 1} b
      inferInstance).unit.app F).hom.app (op U) =
    F.obj.map ((MorphismProperty.Over.mapPullbackAdj @AlgebraicGeometry.Etale ⊤ b
      (show AlgebraicGeometry.Etale b from inferInstance) trivial).counit.app U).op := by
  exact Etale.localizationRestrictionLowerStarAdjunction_unit_app_hom_app
    AddCommGrpCat.{u + 1} b inferInstance F (op U)


private theorem localizationAdjunct_comp_app {Y Z : Scheme.{u}} (b : Z ⟶ Y)
    [AlgebraicGeometry.Etale b] (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})
    {H K : Sheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (α : (Etale.localizationRestriction AddCommGrpCat.{u + 1} b inferInstance).obj F ⟶ H)
    (β : H ⟶ K) (U : Y.Etale) :
    (((Etale.localizationRestrictionLowerStarAdjunction AddCommGrpCat.{u + 1} b
      inferInstance).homEquiv _ _ (α ≫ β)).hom.app (op U)) =
    F.obj.map ((MorphismProperty.Over.mapPullbackAdj @AlgebraicGeometry.Etale ⊤ b
      (show AlgebraicGeometry.Etale b from inferInstance) trivial).counit.app U).op ≫
      α.hom.app (op ((MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ b).obj U)) ≫
      β.hom.app (op ((MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ b).obj U)) := by
  rw [Adjunction.homEquiv_unit, ObjectProperty.FullSubcategory.comp_hom,
    NatTrans.comp_app, Etale.lowerStar_map_hom_app,
    ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app, localizationUnit_app]


private theorem localizationFactorFromComponents {Y Z : Scheme.{u}}
    (b : Z ⟶ Y) [AlgebraicGeometry.Etale b]
    {F P : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}}
    {H K : Sheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (e : H ≅ K) (α : F ⟶ P)
    (β : (Etale.localizationRestriction AddCommGrpCat.{u + 1} b inferInstance).obj P ⟶ K)
    (θ : F ⟶ (Etale.lowerStar AddCommGrpCat.{u + 1} b).obj H)
    (h : ∀ U : Y.Etale,
      let V := (MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ b).obj U
      let ε := (MorphismProperty.Over.mapPullbackAdj @AlgebraicGeometry.Etale ⊤ b
        (show AlgebraicGeometry.Etale b from inferInstance) trivial).counit.app U
      θ.hom.app (op U) ≫ e.hom.hom.app (op V) =
        F.obj.map ε.op ≫ α.hom.app
          (op ((MorphismProperty.Over.map ⊤
            (show AlgebraicGeometry.Etale b from inferInstance)).obj V)) ≫
          β.hom.app (op V)) :
    θ = (Etale.localizationRestrictionLowerStarAdjunction AddCommGrpCat.{u + 1} b
      inferInstance).homEquiv _ _
      ((Etale.localizationRestriction AddCommGrpCat.{u + 1} b inferInstance).map α ≫
        β ≫ e.inv) := by
  apply homEquiv_iso_factor_two
    (Etale.localizationRestrictionLowerStarAdjunction AddCommGrpCat.{u + 1} b
      inferInstance) e θ
    ((Etale.localizationRestriction AddCommGrpCat.{u + 1} b inferInstance).map α) β
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  rw [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    Etale.lowerStar_map_hom_app]
  conv_rhs => rw [localizationAdjunct_comp_app]
  conv_rhs => rw [Etale.localizationRestriction_map_hom_app]
  exact h U.unop

private def restrictionCompOfAdjunction
    (L : ∀ {A B : Scheme.{u}}, (A ⟶ B) → B.Modules ⥤ A.Modules)
    (adj : ∀ {A B : Scheme.{u}} (f : A ⟶ B), L f ⊣ pushforward f)
    {A B C : Scheme.{u}} (a : A ⟶ B) (b : B ⟶ C) :
    L b ⋙ L a ≅ L (a ≫ b) :=
  (conjugateIsoEquiv (adj (a ≫ b)) ((adj b).comp (adj a))).symm
    (pushforwardComp a b).symm

private theorem compOfAdjunction_assoc
    (L : ∀ {A B : Scheme.{u}}, (A ⟶ B) → B.Modules ⥤ A.Modules)
    (adj : ∀ {A B : Scheme.{u}} (f : A ⟶ B), L f ⊣ pushforward f)
    {A B C D : Scheme.{u}} (a : A ⟶ B) (b : B ⟶ C) (c : C ⟶ D) (F : D.Modules) :
    ((restrictionCompOfAdjunction L adj a b).hom.app ((L c).obj F)) ≫
      (restrictionCompOfAdjunction L adj (a ≫ b) c).hom.app F ≫
      eqToHom (congrArg (fun f ↦ (L f).obj F) (Category.assoc a b c)) =
    (L a).map ((restrictionCompOfAdjunction L adj b c).hom.app F) ≫
      (restrictionCompOfAdjunction L adj a (b ≫ c)).hom.app F := by
  have he : Functor.isoWhiskerLeft (pushforward a) (pushforwardComp b c) ≪≫
      pushforwardComp a (b ≫ c) =
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (pushforwardComp a b) (pushforward c) ≪≫
        pushforwardComp (a ≫ b) c := by
    ext M V x
    rfl
  have h := Adjunction.leftAdjointCompIso_assoc (adj c) (adj b) (adj a)
    (adj (b ≫ c)) (adj (a ≫ b)) (adj (a ≫ (b ≫ c)))
    (pushforwardComp b c) (pushforwardComp a b)
    (pushforwardComp (a ≫ b) c) (pushforwardComp a (b ≫ c)) he
  have hc := congrArg (fun e ↦ e.hom.app F) h
  dsimp only [Adjunction.leftAdjointCompIso, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Functor.associator_inv_app] at hc
  erw [Category.id_comp] at hc
  erw [eqToHom_refl, Category.comp_id]
  exact hc


private theorem compOfAdjunction_square
    (L : ∀ {A B : Scheme.{u}}, (A ⟶ B) → B.Modules ⥤ A.Modules)
    (adj : ∀ {A B : Scheme.{u}} (f : A ⟶ B), L f ⊣ pushforward f)
    {A B C D : Scheme.{u}} (a : A ⟶ B) (b : B ⟶ C) (j : C ⟶ D) (F : D.Modules) :
    (restrictionCompOfAdjunction L adj a b).inv.app ((L j).obj F) ≫
      (L a).map ((restrictionCompOfAdjunction L adj b j).hom.app F) ≫
      (restrictionCompOfAdjunction L adj a (b ≫ j)).hom.app F =
    (restrictionCompOfAdjunction L adj (a ≫ b) j).hom.app F := by
  have h := compOfAdjunction_assoc L adj a b j F
  erw [eqToHom_refl, Category.comp_id] at h
  apply (cancel_epi
    ((restrictionCompOfAdjunction L adj a b).hom.app ((L j).obj F))).mp
  simpa only [Category.assoc, Iso.hom_inv_id_app_assoc] using h.symm


private theorem restrictionCompOfAdjunction_tensor {A B C : Scheme.{u}}
    (a : A ⟶ B) (b : B ⟶ C) :
    restrictionCompOfAdjunction (fun f ↦ tensorPullback f)
      (fun f ↦ Classical.choose (exists_tensorPullbackAdjunction f)) a b =
      tensorSectionsComp a b := by
  unfold tensorSectionsComp
  rfl


private theorem tensorSquare {X Y Z : Scheme.{u}} (b : Z ⟶ Y) (j : Y ⟶ X)
    (k : Z ⟶ X) (w : b ≫ j = k) (G : X.Modules)
    (U : Y.Etale) (V : Z.Etale) (p : V.left ⟶ U.left)
    (hp : p ≫ U.hom = V.hom ≫ b) :
    qcoherentPullbackSection b ((tensorPullback j).obj G) ((tensorPullback k).obj G)
        ((tensorSectionsComp b j).hom.app G ≫
          eqToHom (congrArg (fun a ↦ (tensorPullback a).obj G) w)) U V p hp ≫
      ((tensorSectionsComp V.hom k).hom.app G).app ⊤ =
    (tensorSectionsUnit p ((tensorPullback U.hom).obj ((tensorPullback j).obj G)) ≫
      ((tensorSectionsComp p U.hom).hom.app ((tensorPullback j).obj G)).app ⊤ ≫
      (eqToHom (congrArg (fun a ↦ (tensorPullback a).obj
        ((tensorPullback j).obj G)) hp)).app ⊤) ≫
      ((tensorSectionsComp (V.hom ≫ b) j).hom.app G).app ⊤ ≫
      (eqToHom (congrArg (fun a ↦ (tensorPullback a).obj G)
        (show (V.hom ≫ b) ≫ j = V.hom ≫ k by rw [Category.assoc, w]))).app ⊤ := by
  subst k
  let η := tensorSectionsUnit p ((tensorPullback U.hom).obj ((tensorPullback j).obj G)) ≫
    ((tensorSectionsComp p U.hom).hom.app ((tensorPullback j).obj G)).app ⊤ ≫
    (eqToHom (congrArg (fun a ↦ (tensorPullback a).obj
      ((tensorPullback j).obj G)) hp)).app ⊤
  have h := congrArg (fun φ ↦ φ.app ⊤)
    (compOfAdjunction_square (fun a ↦ tensorPullback a)
      (fun a ↦ Classical.choose (exists_tensorPullbackAdjunction a)) V.hom b j G)
  have hs :
      ((tensorSectionsComp V.hom b).inv.app ((tensorPullback j).obj G)).app ⊤ ≫
        ((tensorPullback V.hom).map ((tensorSectionsComp b j).hom.app G)).app ⊤ ≫
        ((tensorSectionsComp V.hom (b ≫ j)).hom.app G).app ⊤ =
      ((tensorSectionsComp (V.hom ≫ b) j).hom.app G).app ⊤ := by
    simpa only [restrictionCompOfAdjunction_tensor, Hom.comp_app] using h
  unfold qcoherentPullbackSection
  simp only [eqToHom_refl, Category.comp_id, Hom.id_app]
  simpa only [Category.assoc, η] using congrArg (fun z ↦ η ≫ z) hs


private theorem qcoherentSection_congr {X Y : Scheme.{u}} (b : Y ⟶ X)
    (F : X.Modules) (H : Y.Modules) (ψ : (tensorPullback b).obj F ⟶ H)
    (U : X.Etale) (V : Y.Etale) (p p' : V.left ⟶ U.left)
    (hp : p ≫ U.hom = V.hom ≫ b) (hp' : p' ≫ U.hom = V.hom ≫ b)
    (h : p = p') :
    qcoherentPullbackSection b F H ψ U V p hp =
      qcoherentPullbackSection b F H ψ U V p' hp' := by
  subst p'
  rfl

private theorem siteCounit_left {Y Z : Scheme.{u}} (b : Z ⟶ Y)
    [AlgebraicGeometry.Etale b] (U : Y.Etale) :
    ((MorphismProperty.Over.mapPullbackAdj @AlgebraicGeometry.Etale ⊤ b
      (show AlgebraicGeometry.Etale b from inferInstance) trivial).counit.app U).left =
      pullback.fst U.hom b := rfl

private theorem qcoherentCounit_formula {Y Z : Scheme.{u}} (b : Z ⟶ Y)
    [AlgebraicGeometry.Etale b]
    (F : Y.Modules) (H : Z.Modules) (ψ : (tensorPullback b).obj F ⟶ H)
    (U : Y.Etale) :
    let V := (MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ b).obj U
    let ε := (MorphismProperty.Over.mapPullbackAdj @AlgebraicGeometry.Etale ⊤ b
      (show AlgebraicGeometry.Etale b from inferInstance) trivial).counit.app U
    qcoherentPullbackSection b F H ψ U V (pullback.fst U.hom b) pullback.condition =
      qcoherentPullbackSection b F H ψ U V ε.left ε.w := by
  exact qcoherentSection_congr b F H ψ U _ _ _ _ _ (siteCounit_left b U).symm

private theorem replaceSectionFormula {A B : AddCommGrpCat.{u}}
    (φ : AddCommGrpCat.uliftFunctor.{u + 1, u}.obj A ⟶
      AddCommGrpCat.uliftFunctor.{u + 1, u}.obj B)
    (q q' : A ⟶ B) (hq : q = q')
    (hφ : ∀ s : A, φ (ULift.up s) = ULift.up (q s)) :
    ∀ s : A, φ (ULift.up s) = ULift.up (q' s) := by
  subst q'
  exact hφ

private theorem restrictionTensorSquare {X Y Z : Scheme.{u}}
    (b : Z ⟶ Y) (j : Y ⟶ X) [AlgebraicGeometry.Etale b]
    (k : Z ⟶ X) (w : b ≫ j = k) (G : X.Modules)
    (U : Y.Etale) (V : Z.Etale)
    (ε : (MorphismProperty.Over.map ⊤
      (show AlgebraicGeometry.Etale b from inferInstance)).obj V ⟶ U) :
    qcoherentPullbackSection b ((tensorPullback j).obj G) ((tensorPullback k).obj G)
        ((tensorSectionsComp b j).hom.app G ≫
          eqToHom (congrArg (fun a ↦ (tensorPullback a).obj G) w)) U V ε.left ε.w ≫
      ((tensorSectionsComp V.hom k).hom.app G).app ⊤ =
    etaleTensorSectionsRestriction ((tensorPullback j).obj G) ε ≫
      ((tensorSectionsComp ((MorphismProperty.Over.map ⊤
        (show AlgebraicGeometry.Etale b from inferInstance)).obj V).hom j).hom.app G).app ⊤ ≫
      (eqToHom (congrArg (fun a ↦ (tensorPullback a).obj G)
        (show (V.hom ≫ b) ≫ j = V.hom ≫ k by rw [Category.assoc, w]))).app ⊤ := by
  exact tensorSquare b j k w G U V ε.left ε.w

private theorem changeLeftComp
    {C D E : Type*} [Category C] [Category D] [Category E]
    {L L' : C ⥤ D} {M M' : D ⥤ E} {N N' : C ⥤ E}
    {R : D ⥤ C} {S : E ⥤ D} {T : E ⥤ C}
    (a : L ⊣ R) (a' : L' ⊣ R) (b : M ⊣ S) (b' : M' ⊣ S)
    (c : N ⊣ T) (c' : N' ⊣ T) (σ : L' ⋙ M' ⟶ N') (τ : T ⟶ S ⋙ R)
    (hσ : conjugateEquiv c' (a'.comp b') σ = τ) :
    Functor.whiskerRight (a.leftAdjointUniq a').hom M ≫
        Functor.whiskerLeft L' (b.leftAdjointUniq b').hom ≫
        σ ≫ (c.leftAdjointUniq c').inv =
      (conjugateEquiv c (a.comp b)).symm τ := by
  have hL : conjugateEquiv a' a (a.leftAdjointUniq a').hom = 𝟙 R := by
    simp only [Adjunction.leftAdjointUniq, Iso.symm_hom,
      conjugateIsoEquiv_symm_apply_inv, Iso.refl_inv, Equiv.apply_symm_apply]
  have hM : conjugateEquiv b' b (b.leftAdjointUniq b').hom = 𝟙 S := by
    simp only [Adjunction.leftAdjointUniq, Iso.symm_hom,
      conjugateIsoEquiv_symm_apply_inv, Iso.refl_inv, Equiv.apply_symm_apply]
  have hN : conjugateEquiv c c' (c.leftAdjointUniq c').inv = 𝟙 T := by
    simp only [Adjunction.leftAdjointUniq, Iso.symm_inv,
      conjugateIsoEquiv_symm_apply_hom, Iso.refl_hom, Equiv.apply_symm_apply]
  apply (conjugateEquiv c (a.comp b)).injective
  rw [← conjugateEquiv_comp c (a'.comp b) (a.comp b)]
  rw [← conjugateEquiv_comp c (a'.comp b') (a'.comp b)]
  rw [← conjugateEquiv_comp c c' (a'.comp b')]
  simp only [conjugateEquiv_whiskerLeft, conjugateEquiv_whiskerRight,
    hL, hM, hN, hσ, Functor.whiskerLeft_id', Functor.whiskerRight_id',
    Category.comp_id, Category.id_comp, Equiv.apply_symm_apply]


private def localizationComp {X Y Z : Scheme.{u}} (b : Z ⟶ Y) (j : Y ⟶ X)
    [AlgebraicGeometry.Etale b] [AlgebraicGeometry.Etale j] (k : Z ⟶ X)
    (w : k = b ≫ j) :
    Etale.localizationRestriction AddCommGrpCat.{u + 1} j inferInstance ⋙
      Etale.localizationRestriction AddCommGrpCat.{u + 1} b inferInstance ≅
    Etale.localizationRestriction AddCommGrpCat.{u + 1} k (by rw [w]; infer_instance) := by
  letI : (MorphismProperty.Over.map ⊤
      (show AlgebraicGeometry.Etale b from inferInstance)).IsContinuous
      Z.smallEtaleTopology Y.smallEtaleTopology :=
    Scheme.isContinuous_overMap (show AlgebraicGeometry.Etale b from inferInstance) le_rfl
  letI : (MorphismProperty.Over.map ⊤
      (show AlgebraicGeometry.Etale j from inferInstance)).IsContinuous
      Y.smallEtaleTopology X.smallEtaleTopology :=
    Scheme.isContinuous_overMap (show AlgebraicGeometry.Etale j from inferInstance) le_rfl
  letI : (MorphismProperty.Over.map ⊤
      (show AlgebraicGeometry.Etale k by rw [w]; infer_instance)).IsContinuous
      Z.smallEtaleTopology X.smallEtaleTopology :=
    Scheme.isContinuous_overMap
      (show AlgebraicGeometry.Etale k by rw [w]; infer_instance) le_rfl
  exact Functor.sheafPushforwardContinuousComp'
    (eFG := (MorphismProperty.Over.mapComp (Q := ⊤)
      (show AlgebraicGeometry.Etale b from inferInstance)
      (show AlgebraicGeometry.Etale j from inferInstance) k w).symm)
    AddCommGrpCat.{u + 1} Z.smallEtaleTopology Y.smallEtaleTopology X.smallEtaleTopology

private theorem localizationComp_conjugate {X Y Z : Scheme.{u}}
    (b : Z ⟶ Y) (j : Y ⟶ X)
    [AlgebraicGeometry.Etale b] [AlgebraicGeometry.Etale j] (k : Z ⟶ X)
    (w : k = b ≫ j) :
    conjugateEquiv
      (Etale.localizationRestrictionLowerStarAdjunction AddCommGrpCat.{u + 1} k
        (by rw [w]; infer_instance))
      ((Etale.localizationRestrictionLowerStarAdjunction AddCommGrpCat.{u + 1} j
        inferInstance).comp
        (Etale.localizationRestrictionLowerStarAdjunction AddCommGrpCat.{u + 1} b
          inferInstance))
      (localizationComp b j k w).hom =
    (Etale.lowerStarComp AddCommGrpCat.{u + 1} b j k w).inv := by
  ext F U x
  simp only [conjugateEquiv_apply_app, Adjunction.comp_unit_app,
    Functor.comp_map]
  let Qk := MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ k
  let Qj := MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ j
  let Qb := MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ b
  let J := MorphismProperty.Over.map ⊤
    (show AlgebraicGeometry.Etale j from inferInstance)
  let ak := MorphismProperty.Over.mapPullbackAdj @AlgebraicGeometry.Etale ⊤ k
    (by rw [w]; infer_instance) trivial
  let aj := MorphismProperty.Over.mapPullbackAdj @AlgebraicGeometry.Etale ⊤ j
    (show AlgebraicGeometry.Etale j from inferInstance) trivial
  let ab := MorphismProperty.Over.mapPullbackAdj @AlgebraicGeometry.Etale ⊤ b
    (show AlgebraicGeometry.Etale b from inferInstance) trivial
  let e := MorphismProperty.Over.mapComp (Q := ⊤)
    (show AlgebraicGeometry.Etale b from inferInstance)
    (show AlgebraicGeometry.Etale j from inferInstance) k w
  have hs : ak.unit.app (Qb.obj (Qj.obj U.unop)) ≫
      Qk.map (e.hom.app (Qb.obj (Qj.obj U.unop))) ≫
      Qk.map (J.map (ab.counit.app (Qj.obj U.unop))) ≫
      Qk.map (aj.counit.app U.unop) =
      (MorphismProperty.Over.pullbackComp b j k w).inv.app U.unop := by
    apply MorphismProperty.Over.Hom.ext
    dsimp [Qk, Qj, Qb, J, ak, aj, ab, e,
      MorphismProperty.Over.mapPullbackAdj, MorphismProperty.Over.map,
      MorphismProperty.Over.pullback, MorphismProperty.Over.mapComp]
    apply pullback.hom_ext <;>
      simp only [MorphismProperty.Over.mk_hom, MorphismProperty.Over.homMk_hom,
        Over.homMk_left, MorphismProperty.Over.isoMk_hom_left, Iso.refl_hom,
        Category.comp_id, MorphismProperty.Comma.mapRight_map_left, Category.assoc,
        limit.lift_π, PullbackCone.mk_π_app, limit.lift_π_assoc, cospan_left,
        MorphismProperty.Over.pullbackComp_inv_app_left,
        pullbackLeftPullbackSndIso_hom_fst, pullbackLeftPullbackSndIso_hom_snd]
    · exact Category.id_comp _
    · rfl
  change (F.obj.map (Qk.map (aj.counit.app U.unop)).op ≫
    F.obj.map (Qk.map (J.map (ab.counit.app (Qj.obj U.unop)))).op ≫
    F.obj.map (Qk.map (e.hom.app (Qb.obj (Qj.obj U.unop)))).op ≫
    F.obj.map (ak.unit.app (Qb.obj (Qj.obj U.unop))).op) x =
      F.obj.map ((MorphismProperty.Over.pullbackComp b j k w).inv.app U.unop).op x
  simp only [← Functor.map_comp] at hs
  simp only [← Functor.map_comp, ← op_comp, Category.assoc]
  erw [hs]
  rfl


private theorem removeInverse {C : Type*} [Category C] {X A B : C}
    (e : A ≅ B) (f : X ⟶ B) (g : X ⟶ A) (h : f ≫ e.inv = g) :
    f = g ≫ e.hom := by
  simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using
    congrArg (fun z ↦ z ≫ e.hom) h

private theorem changeLeftCompFactor
    {C D E : Type*} [Category C] [Category D] [Category E]
    {L L' : C ⥤ D} {M M' : D ⥤ E} {N N' : C ⥤ E}
    {R : D ⥤ C} {S : E ⥤ D} {T : E ⥤ C}
    (a : L ⊣ R) (a' : L' ⊣ R) (b : M ⊣ S) (b' : M' ⊣ S)
    (c : N ⊣ T) (c' : N' ⊣ T) (σ : L' ⋙ M' ⟶ N') (τ : T ⟶ S ⋙ R)
    (hσ : conjugateEquiv c' (a'.comp b') σ = τ) :
    Functor.whiskerRight (a.leftAdjointUniq a').hom M ≫
        Functor.whiskerLeft L' (b.leftAdjointUniq b').hom ≫
        σ =
      (conjugateEquiv c (a.comp b)).symm τ ≫ (c.leftAdjointUniq c').hom := by
  apply removeInverse (c.leftAdjointUniq c')
  simpa only [Category.assoc] using changeLeftComp a a' b b' c c' σ τ hσ

private theorem localizationFactor {X Y Z : Scheme.{u}}
    (b : Z ⟶ Y) (j : Y ⟶ X)
    [AlgebraicGeometry.Etale b] [AlgebraicGeometry.Etale j] (k : Z ⟶ X)
    (w : k = b ≫ j) (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    (Etale.upperStar AddCommGrpCat.{u + 1} b).map
        ((Etale.upperStarIsoLocalizationRestriction AddCommGrpCat.{u + 1} j
          inferInstance).hom.app F) ≫
      (Etale.upperStarIsoLocalizationRestriction AddCommGrpCat.{u + 1} b
        inferInstance).hom.app
        ((Etale.localizationRestriction AddCommGrpCat.{u + 1} j inferInstance).obj F) ≫
      (localizationComp b j k w).hom.app F =
    (Etale.upperStarComp AddCommGrpCat.{u + 1} b j k w).inv.app F ≫
      (Etale.upperStarIsoLocalizationRestriction AddCommGrpCat.{u + 1} k
        (by rw [w]; infer_instance)).hom.app F := by
  have hc := changeLeftCompFactor
    (C := Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (D := Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})
    (E := Sheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1})
    (Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} j)
    (Etale.localizationRestrictionLowerStarAdjunction AddCommGrpCat.{u + 1} j
      inferInstance)
    (Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} b)
    (Etale.localizationRestrictionLowerStarAdjunction AddCommGrpCat.{u + 1} b
      inferInstance)
    (Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} k)
    (Etale.localizationRestrictionLowerStarAdjunction AddCommGrpCat.{u + 1} k
      (by rw [w]; infer_instance))
    (localizationComp b j k w).hom
    (Etale.lowerStarComp AddCommGrpCat.{u + 1} b j k w).inv
    (localizationComp_conjugate b j k w)
  simpa only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Category.assoc, Etale.upperStarIsoLocalizationRestriction,
    Etale.upperStarComp, Iso.symm_inv, Iso.symm_hom,
    conjugateIsoEquiv_symm_apply_hom] using congrArg (fun α ↦ α.app F) hc


private theorem isoMap_hom_eq {C D : Type*} [Category C] [Category D]
    (H : C ⥤ D) {A B : C} (e : A ≅ B) (t : H.obj A ≅ H.obj B)
    (h : H.map e.inv = t.inv) : H.map e.hom = t.hom := by
  apply (cancel_mono (H.map e.inv)).mp
  rw [← H.map_comp, e.hom_inv_id, H.map_id, h, t.hom_inv_id]

private def tensorGlobalCompIso {A B C : Scheme.{u}}
    (a : A ⟶ B) (b : B ⟶ C) (F : C.Modules) :
    Γ((tensorPullback a).obj ((tensorPullback b).obj F), ⊤) ≅
      Γ((tensorPullback (a ≫ b)).obj F, ⊤) :=
  (SheafOfModules.evaluation A.ringCatSheaf (op ⊤) ⋙
    forget₂ _ AddCommGrpCat.{u}).mapIso ((tensorSectionsComp a b).app F)

private def tensorLocalizationIso {X Y : Scheme.{u}} (j : Y ⟶ X)
    [AlgebraicGeometry.Etale j] (F : X.Modules) [F.IsQuasicoherent] :
    liftedCoherentEtaleSheaf ((tensorPullback j).obj F) ≅
      (Etale.localizationRestriction AddCommGrpCat.{u + 1} j inferInstance).obj
        (liftedCoherentEtaleSheaf F) :=
  (coherentEtaleRestrictionIso j F).symm ≪≫
    (Etale.upperStarIsoLocalizationRestriction AddCommGrpCat.{u + 1} j
      inferInstance).app (liftedCoherentEtaleSheaf F)

private theorem tensorLocalizationIso_inv_app {X Y : Scheme.{u}} (j : Y ⟶ X)
    [AlgebraicGeometry.Etale j] (F : X.Modules) [F.IsQuasicoherent] (W : Y.Etale) :
    (tensorLocalizationIso j F).inv.hom.app (op W) =
      AddCommGrpCat.uliftFunctor.map
        (((tensorSectionsComp W.hom j).inv.app F).app ⊤) := by
  apply eqLiftedHom
  intro s
  change (coherentEtaleRestrictionIso j F).hom.hom.app (op W)
    (((Etale.upperStarIsoLocalizationRestriction AddCommGrpCat.{u + 1} j
      inferInstance).inv.app (liftedCoherentEtaleSheaf F)).hom.app (op W)
        (ULift.up s)) = _
  unfold coherentEtaleRestrictionIso
  exact (Classical.choose_spec (existsUnique_coherentEtaleRestrictionIso j F)).1 W s


private theorem tensorLocalizationIso_hom_app {X Y : Scheme.{u}} (j : Y ⟶ X)
    [AlgebraicGeometry.Etale j] (F : X.Modules) [F.IsQuasicoherent] (W : Y.Etale) :
    (tensorLocalizationIso j F).hom.hom.app (op W) =
      AddCommGrpCat.uliftFunctor.map
        (((tensorSectionsComp W.hom j).hom.app F).app ⊤) := by
  let H := sheafToPresheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1} ⋙
    (CategoryTheory.evaluation Y.Etaleᵒᵖ AddCommGrpCat.{u + 1}).obj (op W)
  exact isoMap_hom_eq H (tensorLocalizationIso j F)
    (AddCommGrpCat.uliftFunctor.mapIso (tensorGlobalCompIso W.hom j F))
    (tensorLocalizationIso_inv_app j F W)


private theorem restrictionFactor {X Y : Scheme.{u}} (j : Y ⟶ X)
    [AlgebraicGeometry.Etale j] (F : X.Modules) [F.IsQuasicoherent] :
    coherentEtaleRestrictionIso j F =
      (Etale.upperStarIsoLocalizationRestriction AddCommGrpCat.{u + 1} j
        inferInstance).app (liftedCoherentEtaleSheaf F) ≪≫
      (tensorLocalizationIso j F).symm := by
  exact iso_factor (coherentEtaleRestrictionIso j F)
    ((Etale.upperStarIsoLocalizationRestriction AddCommGrpCat.{u + 1} j
      inferInstance).app (liftedCoherentEtaleSheaf F))

private theorem localizationComp_app {X Y Z : Scheme.{u}}
    (b : Z ⟶ Y) (j : Y ⟶ X)
    [AlgebraicGeometry.Etale b] [AlgebraicGeometry.Etale j]
    (k : Z ⟶ X) (w : b ≫ j = k) [AlgebraicGeometry.Etale k]
    (G : X.Modules) [G.IsQuasicoherent]
    (V : Z.Etale) :
    ((localizationComp b j k w.symm).hom.app (liftedCoherentEtaleSheaf G)).hom.app
        (op V) =
      AddCommGrpCat.uliftFunctor.map
        ((eqToHom (congrArg (fun a ↦ (tensorPullback a).obj G)
          (show (V.hom ≫ b) ≫ j = V.hom ≫ k by rw [Category.assoc, w]))).app ⊤) := by
  subst k
  change AddCommGrpCat.uliftFunctor.map
      (etaleTensorSectionsRestriction G (𝟙 (Scheme.Etale.mk (V.hom ≫ (b ≫ j))))) =
    AddCommGrpCat.uliftFunctor.map (𝟙 _)
  rw [etaleTensorSectionsRestriction_id]


attribute [local irreducible] tensorLocalizationIso localizationComp

private theorem mapSquare {C D : Type*} [Category C] [Category D]
    (H : C ⥤ D) {A B E F K : C}
    (q : A ⟶ B) (d : B ⟶ K) (r : A ⟶ E) (c : E ⟶ F) (t : F ⟶ K)
    (q' : H.obj A ⟶ H.obj B) (d' : H.obj B ⟶ H.obj K)
    (r' : H.obj A ⟶ H.obj E) (c' : H.obj E ⟶ H.obj F)
    (t' : H.obj F ⟶ H.obj K)
    (hq : q' = H.map q) (hd : d' = H.map d) (hr : r' = H.map r)
    (hc : c' = H.map c) (ht : t' = H.map t) (h : q ≫ d = r ≫ c ≫ t) :
    q' ≫ d' = r' ≫ c' ≫ t' := by
  rw [hq, hd, hr, hc, ht, ← H.map_comp, ← H.map_comp, ← H.map_comp, h]

private theorem localizationComponentSquare {X Y Z : Scheme.{u}}
    (b : Z ⟶ Y) (j : Y ⟶ X)
    [AlgebraicGeometry.Etale b] [AlgebraicGeometry.Etale j]
    (k : Z ⟶ X) (w : b ≫ j = k) [AlgebraicGeometry.Etale k]
    (G : X.Modules) [G.IsQuasicoherent]
    (U : Y.Etale) (V : Z.Etale)
    (ε : (MorphismProperty.Over.map ⊤
      (show AlgebraicGeometry.Etale b from inferInstance)).obj V ⟶ U)
    (φ : (liftedCoherentEtaleSheaf ((tensorPullback j).obj G)).obj.obj (op U) ⟶
      (liftedCoherentEtaleSheaf ((tensorPullback k).obj G)).obj.obj (op V))
    (hφ : ∀ s : Γ((tensorPullback U.hom).obj ((tensorPullback j).obj G), ⊤),
      φ (ULift.up s) = ULift.up
        (qcoherentPullbackSection b ((tensorPullback j).obj G) ((tensorPullback k).obj G)
          ((tensorSectionsComp b j).hom.app G ≫
            eqToHom (congrArg (fun a ↦ (tensorPullback a).obj G) w)) U V ε.left ε.w s)) :
    φ ≫ (tensorLocalizationIso k G).hom.hom.app (op V) =
      (liftedCoherentEtaleSheaf ((tensorPullback j).obj G)).obj.map ε.op ≫
        (tensorLocalizationIso j G).hom.hom.app
          (op ((MorphismProperty.Over.map ⊤
            (show AlgebraicGeometry.Etale b from inferInstance)).obj V)) ≫
        ((localizationComp b j k w.symm).hom.app (liftedCoherentEtaleSheaf G)).hom.app
          (op V) := by
  exact mapSquare AddCommGrpCat.uliftFunctor _ _ _ _ _ _ _ _ _ _
    (eqLiftedHom _ _ hφ) (tensorLocalizationIso_hom_app k G V)
    (liftedSections_map ((tensorPullback j).obj G) ε)
    (tensorLocalizationIso_hom_app j G
      ((MorphismProperty.Over.map ⊤
        (show AlgebraicGeometry.Etale b from inferInstance)).obj V))
    (localizationComp_app b j k w G V)
    (restrictionTensorSquare b j k w G U V ε)

set_option backward.defeqAttrib.useBackward true in
private theorem thetaFactor {X Y Z : Scheme.{u}}
    (b : Z ⟶ Y) (j : Y ⟶ X)
    [AlgebraicGeometry.Etale b] [AlgebraicGeometry.Etale j]
    (k : Z ⟶ X) (w : b ≫ j = k) [AlgebraicGeometry.Etale k]
    (G : X.Modules) [G.IsQuasicoherent]
    (θ : liftedCoherentEtaleSheaf ((tensorPullback j).obj G) ⟶
      (Etale.lowerStar AddCommGrpCat.{u + 1} b).obj
        (liftedCoherentEtaleSheaf ((tensorPullback k).obj G)))
    (hθ : ∀ (U : Y.Etale)
      (s : (etaleTensorSectionsSheaf ((tensorPullback j).obj G)).obj.obj (op U)),
      θ.hom.app (op U) (ULift.up s) = ULift.up
        (qcoherentPullbackSection b ((tensorPullback j).obj G) ((tensorPullback k).obj G)
          ((tensorSectionsComp b j).hom.app G ≫
            eqToHom (congrArg (fun a ↦ (tensorPullback a).obj G) w)) U
          ((MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ b).obj U)
          (pullback.fst U.hom b) pullback.condition s)) :
    θ = (Etale.localizationRestrictionLowerStarAdjunction AddCommGrpCat.{u + 1} b
      inferInstance).homEquiv _ _
      ((Etale.localizationRestriction AddCommGrpCat.{u + 1} b inferInstance).map
          (tensorLocalizationIso j G).hom ≫
        (localizationComp b j k w.symm).hom.app (liftedCoherentEtaleSheaf G) ≫
        (tensorLocalizationIso k G).inv) := by
  apply localizationFactorFromComponents b (tensorLocalizationIso k G)
    (tensorLocalizationIso j G).hom
    ((localizationComp b j k w.symm).hom.app (liftedCoherentEtaleSheaf G)) θ
  intro U
  let V := (MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ b).obj U
  let ε := (MorphismProperty.Over.mapPullbackAdj @AlgebraicGeometry.Etale ⊤ b
    (show AlgebraicGeometry.Etale b from inferInstance) trivial).counit.app U
  apply localizationComponentSquare b j k w G U V ε (θ.hom.app (op U))
  exact replaceSectionFormula _ _ _
    (qcoherentCounit_formula b ((tensorPullback j).obj G) ((tensorPullback k).obj G)
      ((tensorSectionsComp b j).hom.app G ≫
        eqToHom (congrArg (fun a ↦ (tensorPullback a).obj G) w)) U) (hθ U)



private theorem adjointTranspose {C D : Type*} [Category C] [Category D]
    {L L' : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) (adj' : L' ⊣ R)
    {A : C} {B : D} (θ : A ⟶ R.obj B) (t : L'.obj A ⟶ B)
    (hθ : θ = adj'.homEquiv _ _ t) :
    (adj.homEquiv _ _).symm θ = (adj.leftAdjointUniq adj').hom.app A ≫ t := by
  apply (adj.homEquiv _ _).injective
  rw [Equiv.apply_symm_apply, hθ]
  exact (leftAdjointUniq_homEquiv_comp adj adj' A B t).symm

private theorem cancelRestrictionFactors {A B C : Type*}
    [Category A] [Category B] [Category C]
    {Pj Dj : A ⥤ B} {Pb Db : B ⥤ C} {Pk Dk : A ⥤ C}
    (ρj : Pj ≅ Dj) (ρb : Pb ≅ Db) (ρk : Pk ≅ Dk)
    (σ : Dj ⋙ Db ≅ Dk) (γ : Pk ≅ Pj ⋙ Pb)
    (F : A) {Fj : B} {Fk : C} (cj : Fj ≅ Dj.obj F) (ck : Fk ≅ Dk.obj F)
    (ej : Pj.obj F ≅ Fj) (ek : Pk.obj F ≅ Fk)
    (hej : ej = ρj.app F ≪≫ cj.symm) (hek : ek = ρk.app F ≪≫ ck.symm)
    (t : Pb.obj Fj ⟶ Fk)
    (ht : t = ρb.hom.app Fj ≫ Db.map cj.hom ≫ σ.hom.app F ≫ ck.inv)
    (hσ : Pb.map (ρj.hom.app F) ≫ ρb.hom.app (Dj.obj F) ≫ σ.hom.app F =
      γ.inv.app F ≫ ρk.hom.app F) :
    Pb.map ej.hom ≫ t = γ.inv.app F ≫ ek.hom := by
  rw [hej, hek, ht]
  dsimp only [Iso.trans_hom, Iso.symm_hom, Iso.app_hom]
  rw [Pb.map_comp]
  simp only [Category.assoc]
  rw [ρb.hom.naturality_assoc]
  simp only [← Db.map_comp_assoc, cj.inv_hom_id, Db.map_id, Category.id_comp]
  simpa only [Category.assoc] using congrArg (fun z ↦ z ≫ ck.inv) hσ

private theorem restrictionComposition {X Y Z : Scheme.{u}}
    (b : Z ⟶ Y) (j : Y ⟶ X)
    [AlgebraicGeometry.Etale b] [AlgebraicGeometry.Etale j]
    (k : Z ⟶ X) (w : b ≫ j = k) [AlgebraicGeometry.Etale k]
    (G : X.Modules) [G.IsQuasicoherent]
    (θ : liftedCoherentEtaleSheaf ((tensorPullback j).obj G) ⟶
      (Etale.lowerStar AddCommGrpCat.{u + 1} b).obj
        (liftedCoherentEtaleSheaf ((tensorPullback k).obj G)))
    (hθ : ∀ (U : Y.Etale)
      (s : (etaleTensorSectionsSheaf ((tensorPullback j).obj G)).obj.obj (op U)),
      θ.hom.app (op U) (ULift.up s) = ULift.up
        (qcoherentPullbackSection b ((tensorPullback j).obj G) ((tensorPullback k).obj G)
          ((tensorSectionsComp b j).hom.app G ≫
            eqToHom (congrArg (fun a ↦ (tensorPullback a).obj G) w)) U
          ((MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ b).obj U)
          (pullback.fst U.hom b) pullback.condition s)) :
    (Etale.upperStar AddCommGrpCat.{u + 1} b).map
        (coherentEtaleRestrictionIso j G).hom ≫
      ((Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} b).homEquiv
        _ _).symm θ =
    (Etale.upperStarComp AddCommGrpCat.{u + 1} b j k w.symm).inv.app
      (liftedCoherentEtaleSheaf G) ≫ (coherentEtaleRestrictionIso k G).hom := by
  let ρ := Etale.upperStarIsoLocalizationRestriction AddCommGrpCat.{u + 1} b
    inferInstance
  let t := (Etale.localizationRestriction AddCommGrpCat.{u + 1} b inferInstance).map
      (tensorLocalizationIso j G).hom ≫
    (localizationComp b j k w.symm).hom.app (liftedCoherentEtaleSheaf G) ≫
      (tensorLocalizationIso k G).inv
  have ht : θ =
      (Etale.localizationRestrictionLowerStarAdjunction AddCommGrpCat.{u + 1} b
        inferInstance).homEquiv _ _ t :=
    thetaFactor b j k w G θ hθ
  have ha : ((Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} b).homEquiv
      _ _).symm θ = ρ.hom.app (liftedCoherentEtaleSheaf ((tensorPullback j).obj G)) ≫
        t := by
    exact adjointTranspose
      (Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} b)
      (Etale.localizationRestrictionLowerStarAdjunction AddCommGrpCat.{u + 1} b
        inferInstance) θ t ht
  exact cancelRestrictionFactors
    (Etale.upperStarIsoLocalizationRestriction AddCommGrpCat.{u + 1} j inferInstance)
    ρ (Etale.upperStarIsoLocalizationRestriction AddCommGrpCat.{u + 1} k inferInstance)
    (localizationComp b j k w.symm)
    (Etale.upperStarComp AddCommGrpCat.{u + 1} b j k w.symm)
    (liftedCoherentEtaleSheaf G) (tensorLocalizationIso j G) (tensorLocalizationIso k G)
    (coherentEtaleRestrictionIso j G) (coherentEtaleRestrictionIso k G)
    (restrictionFactor j G) (restrictionFactor k G) _ ha
    (localizationFactor b j k w.symm (liftedCoherentEtaleSheaf G))



/-- The sectionwise structural coefficient map is compatible with the normalized
coherent restriction isomorphisms. This is an equality of sheaf maps, before
applying any cohomology functor or raw evaluation.
Source: Stacks Project, Tag 03DR, equation-quasi-coherent-presheaf; Tag 03Q8.
Agent expansion of step 3 of lem-weil-pbc-affine-raw-evaluation-pullback.
(blueprint: lem-weil-pbc-coherent-etale-restriction-composition).

Proof: transpose the proposed equality under b* adjoint to b_*. Identify b* with
localization restriction, using uniqueness of left adjoints and its unit equation.
At an etale object U over Y this unit is restriction along the counit of the
map/pullback site adjunction, whose scheme map is pullback.fst. Insert the inverse
tensorSectionsComp formulas defining the two coherentEtaleRestrictionIso maps.
Naturality of the tensor section unit moves the comparison for j past the unit.
Associativity of unit-normalized tensor composition identifies the remaining two
ways of composing comparisons. Transport along w cancels the final equality
comparison. The resulting component is precisely qcoherentPullbackSection for
psi. The hypothesis identifies it with theta on each ULift.up s. Every lifted
section is of that form, so sectionwise, natural-transformation and sheaf
extensionality give equality of the adjuncts. The adjunction Hom equivalence
is injective, proving the assertion. Here b is the induced map between the two charts,
and j and j' are their projections. No affine or nonempty hypothesis enters these equations. -/
theorem coherentEtaleRestrictionIso_composition {X S : Scheme.{u}} (f : X ⟶ S)
    (G : X.Modules) [G.IsQuasicoherent] (V V' : S.Etale) (h : V' ⟶ V)
    (θ : liftedCoherentEtaleSheaf (affineRealizationCoefficient f G V) ⟶
      (Etale.lowerStar AddCommGrpCat.{u + 1}
        ((MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ f).map h).left).obj
        (liftedCoherentEtaleSheaf (affineRealizationCoefficient f G V')))
    (hθ : let b := (MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ f).map h
      let ψ : (tensorPullback b.left).obj (affineRealizationCoefficient f G V) ⟶
          affineRealizationCoefficient f G V' :=
        (tensorSectionsComp b.left (Limits.pullback.snd V.hom f)).hom.app G ≫
          eqToHom (congrArg (fun j ↦ (tensorPullback j).obj G) b.w)
      ∀ (U : (Limits.pullback V.hom f : Scheme.{u}).Etale)
        (s : (etaleTensorSectionsSheaf (affineRealizationCoefficient f G V)).obj.obj (op U)),
        θ.hom.app (op U) (ULift.up s) = ULift.up
          (qcoherentPullbackSection b.left _ _ ψ U
            ((MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ b.left).obj U)
            (pullback.fst U.hom b.left) pullback.condition s)) :
    (Etale.upperStar AddCommGrpCat.{u + 1}
        ((MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ f).map h).left).map
        (coherentEtaleRestrictionIso (pullback.snd V.hom f) G).hom ≫
      ((Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1}
        ((MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ f).map h).left).homEquiv
        _ _ |>.symm θ) =
    (Etale.upperStarComp AddCommGrpCat.{u + 1}
      ((MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ f).map h).left
      (pullback.snd V.hom f) (pullback.snd V'.hom f)
      ((MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ f).map h).w.symm).inv.app
        (liftedCoherentEtaleSheaf G) ≫
      (coherentEtaleRestrictionIso (pullback.snd V'.hom f) G).hom := by
  apply restrictionComposition
    (X := X) (Y := Limits.pullback V.hom f) (Z := Limits.pullback V'.hom f)
    ((MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ f).map h).left
    (pullback.snd V.hom f) (pullback.snd V'.hom f)
    ((MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ f).map h).w G θ
  intro U s
  refine Eq.mp ?_ (hθ U s)
  run_tac do
    let g ← Lean.Elab.Tactic.getMainGoal
    let cache ← IO.mkRef ({} : Std.HashMap Lean.Expr Lean.Expr)
    strictCongr cache 60 g
    Lean.Elab.Tactic.replaceMainGoal []


end
end AlgebraicGeometry.Scheme.Modules
