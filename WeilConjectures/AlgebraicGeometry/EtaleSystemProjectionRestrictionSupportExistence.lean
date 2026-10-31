/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.EtaleSystemProjectionBasicData
import WeilConjectures.CategoryTheory.Adjunction.MateCube
import WeilConjectures.CategoryTheory.DerivedExactCube
import WeilConjectures.AlgebraicGeometry.EtaleSystemProjectionSupportEvaluationExistence
import all WeilConjectures.AlgebraicGeometry.EtaleSingleCoefficientProjection
import all WeilConjectures.AlgebraicGeometry.EtaleProperCoefficientTensorUnit
import all WeilConjectures.AlgebraicGeometry.FiniteCoefficientDirectImage
import WeilConjectures.CategoryTheory.RightDerivedMateIndependence
import all WeilConjectures.AlgebraicGeometry.EtaleRestrictScalarsAdjunctionIdentities

/-! # Restriction support comparison existence for normalized etale systems

Source: Zheng, Construction 4.1, Lemma 5.16; Stacks Tag 0GL6.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option maxRecDepth 4096
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Etale.SystemProjection

open WeilConjectures WeilConjectures.SemilinearSections

attribute [local implicit_reducible] TwoSquare MorphismProperty Scheme.Etale

attribute [local instance] cachedEtaleGroth cachedEtaleSheafify
attribute [local instance] cachedEtaleMonoidalPreadditive cachedEtaleCoproducts
  cachedEtaleColimits cachedEtaleFlatResolution cachedEtaleInjectiveResolution
  cachedEtaleExactColimits cachedEtaleTensor4 cachedEtaleTensor12 cachedEtaleTensor23
  cachedEtaleTensorColimits cachedEtaleTensorFlipColimits

private local instance baseContinuous {X Y : Scheme.{u}} (g : X ⟶ Y) :
    (MorphismProperty.Over.pullback @Etale ⊤ g).IsContinuous
      Y.smallEtaleTopology X.smallEtaleTopology :=
  AlgebraicGeometry.Etale.isContinuous_overPullback g

private def constantDirect {X Y : Scheme.{u}} (g : X ⟶ Y)
    (A : CommRingCat.{u + 1}) :
    (constantSheaf Y.smallEtaleTopology CommRingCat.{u + 1}).obj A ⟶
      ((MorphismProperty.Over.pullback @Etale ⊤ g).sheafPushforwardContinuous
        CommRingCat.{u + 1} Y.smallEtaleTopology X.smallEtaleTopology).obj
        ((constantSheaf X.smallEtaleTopology CommRingCat.{u + 1}).obj A) :=
  ((sheafificationAdjunction Y.smallEtaleTopology CommRingCat.{u + 1}).homEquiv _ _).symm
    (Functor.whiskerLeft (MorphismProperty.Over.pullback @Etale ⊤ g).op
      (toSheafify X.smallEtaleTopology ((Functor.const X.Etaleᵒᵖ).obj A)))

private theorem constantDirect_unit {X Y : Scheme.{u}} (g : X ⟶ Y)
    (A : CommRingCat.{u + 1}) (U : Y.Etaleᵒᵖ) :
    (toSheafify Y.smallEtaleTopology ((Functor.const Y.Etaleᵒᵖ).obj A)).app U ≫
      (constantDirect g A).hom.app U =
        (toSheafify X.smallEtaleTopology ((Functor.const X.Etaleᵒᵖ).obj A)).app
          ((MorphismProperty.Over.pullback @Etale ⊤ g).op.obj U) := by
  have h := ((sheafificationAdjunction Y.smallEtaleTopology CommRingCat.{u + 1}).homEquiv
    ((Functor.const Y.Etaleᵒᵖ).obj A)
    (((MorphismProperty.Over.pullback @Etale ⊤ g).sheafPushforwardContinuous
      CommRingCat.{u + 1} Y.smallEtaleTopology X.smallEtaleTopology).obj
      ((constantSheaf X.smallEtaleTopology CommRingCat.{u + 1}).obj A))).apply_symm_apply
      (Functor.whiskerLeft (MorphismProperty.Over.pullback @Etale ⊤ g).op
        (toSheafify X.smallEtaleTopology ((Functor.const X.Etaleᵒᵖ).obj A)))
  exact congrArg (fun k ↦ k.app U) h

private theorem constantDirect_naturality {X Y : Scheme.{u}} (g : X ⟶ Y)
    {A D : CommRingCat.{u + 1}} (a : A ⟶ D) :
    (constantSheaf Y.smallEtaleTopology CommRingCat.{u + 1}).map a ≫ constantDirect g D =
      constantDirect g A ≫
        ((MorphismProperty.Over.pullback @Etale ⊤ g).sheafPushforwardContinuous
          CommRingCat.{u + 1} Y.smallEtaleTopology X.smallEtaleTopology).map
          ((constantSheaf X.smallEtaleTopology CommRingCat.{u + 1}).map a) := by
  apply ((sheafificationAdjunction Y.smallEtaleTopology CommRingCat.{u + 1}).homEquiv
    ((Functor.const Y.Etaleᵒᵖ).obj A) _).injective
  change ((sheafificationAdjunction Y.smallEtaleTopology CommRingCat.{u + 1}).homEquiv
    _ _) ((presheafToSheaf Y.smallEtaleTopology CommRingCat.{u + 1}).map
      ((Functor.const Y.Etaleᵒᵖ).map a) ≫ _) = _
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]
  simp only [constantDirect, Equiv.apply_symm_apply]
  apply NatTrans.ext
  funext U
  exact congrArg
    (fun t ↦ t.app ((MorphismProperty.Over.pullback @Etale ⊤ g).op.obj U))
    ((toSheafification X.smallEtaleTopology CommRingCat.{u + 1}).naturality
      ((Functor.const X.Etaleᵒᵖ).map a))

set_option maxHeartbeats 1200000 in
-- The slice comparison unfolds the concrete ringed-site functors.
private def structuralLevel {X Y : Scheme.{u}} {g : X ⟶ Y}
    {B : ℕᵒᵖ ⥤ CommRingCat.{u + 1}} (d : DirectImage g B) (n : ℕ) :
    coefficients Y B n ⟶
      ((MorphismProperty.Over.pullback @Etale ⊤ g).sheafPushforwardContinuous
        CommRingCat.{u + 1} Y.smallEtaleTopology X.smallEtaleTopology).obj
        (coefficients X B n) :=
  ⟨{ app U := d.structural.hom.app (op (n, U.unop))
     naturality := by
       intro U V f
       have h := d.structural.hom.naturality (Prod.mkHom (𝟙 n) f.unop).op
       change
         (((SemilinearSections.rings Y.smallEtaleTopology (coefficients Y B)
           (transitions Y B)).map (𝟙 (op n))).hom.app U ≫
           (coefficients Y B n).obj.map f) ≫ d.structural.hom.app (op (n, V.unop)) =
         d.structural.hom.app (op (n, U.unop)) ≫
           (((SemilinearSections.rings X.smallEtaleTopology (coefficients X B)
             (transitions X B)).map (𝟙 (op n))).hom.app
               ((MorphismProperty.Over.pullback @Etale ⊤ g).op.obj U) ≫
             (coefficients X B n).obj.map
               ((MorphismProperty.Over.pullback @Etale ⊤ g).op.map f)) at h
       simp only [CategoryTheory.Functor.map_id,
         ObjectProperty.FullSubcategory.id_hom, NatTrans.id_app] at h
       erw [Category.id_comp, Category.id_comp] at h
       exact h }⟩

private theorem structuralLevel_eq {X Y : Scheme.{u}} {g : X ⟶ Y}
    {B : ℕᵒᵖ ⥤ CommRingCat.{u + 1}} (d : DirectImage g B) (n : ℕ) :
    structuralLevel d n = constantDirect g (B.obj (op n)) := by
  apply ((sheafificationAdjunction Y.smallEtaleTopology CommRingCat.{u + 1}).homEquiv
    ((Functor.const Y.Etaleᵒᵖ).obj (B.obj (op n))) _).injective
  apply NatTrans.ext
  funext U
  ext x
  exact (d.constants n U x).trans
    (ConcreteCategory.congr_hom (constantDirect_unit g (B.obj (op n)) U) x).symm

private theorem ringMap_app (W : Scheme.{u})
    {B C : ℕᵒᵖ ⥤ CommRingCat.{u + 1}} (a : B ⟶ C)
    (n : ℕ) (U : W.Etaleᵒᵖ) :
    (ringMap W a).hom.app (op (n, U.unop)) =
      ((constantSheaf W.smallEtaleTopology CommRingCat.{u + 1}).map
        (a.app (op n))).hom.app U := by
  exact (systemMap_existsUnique W.smallEtaleTopology
    (coefficients W B) (transitions W B) (coefficients W C) (transitions W C)
    (fun n ↦ (constantSheaf W.smallEtaleTopology CommRingCat.{u + 1}).map
      (a.app (op n))) (fun n ↦ by
        rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
        exact congrArg
          (fun h ↦ (constantSheaf W.smallEtaleTopology CommRingCat.{u + 1}).map h)
          (a.naturality (homOfLE (Nat.le_succ n)).op).symm)).exists.choose_spec n U

attribute [local irreducible] ringMap

set_option maxHeartbeats 1200000 in
-- The coefficient square compares concrete sheafification morphisms.
private theorem structural_naturality {X Y : Scheme.{u}} {g : X ⟶ Y}
    {B C : ℕᵒᵖ ⥤ CommRingCat.{u + 1}} (a : B ⟶ C)
    (d : DirectImage g B) (e : DirectImage g C) :
    let := d.continuous
    ringMap Y a ≫ e.structural = d.structural ≫
      ((siteMap g).sheafPushforwardContinuous CommRingCat.{u + 1}
        (coefficientSequenceTopology Y.smallEtaleTopology)
        (coefficientSequenceTopology X.smallEtaleTopology)).map (ringMap X a) := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  let n := U.unop.1
  let V := U.unop.2
  have h := constantDirect_naturality g (a.app (op n))
  rw [← structuralLevel_eq d n, ← structuralLevel_eq e n] at h
  change (ringMap Y a).hom.app (op (n, V)) ≫
      e.structural.hom.app (op (n, V)) =
    d.structural.hom.app (op (n, V)) ≫
      (ringMap X a).hom.app (op (n, (MorphismProperty.Over.pullback @Etale ⊤ g).obj V))
  erw [ringMap_app Y a n (op V),
    ringMap_app X a n (op ((MorphismProperty.Over.pullback @Etale ⊤ g).obj V))]
  exact congrArg (fun k ↦ k.hom.app (op V)) h

set_option maxHeartbeats 1200000 in
-- The linearity proof unfolds the two concrete module actions.
private def ordinaryRestriction {X Y : Scheme.{u}} {g : X ⟶ Y}
    {B C : ℕᵒᵖ ⥤ CommRingCat.{u + 1}} (a : B ⟶ C)
    (d : DirectImage g B) (e : DirectImage g C) :
    res (ringMap X a) ⋙ d.push ≅ e.push ⋙ res (ringMap Y a) := by
  refine NatIso.ofComponents (fun M ↦ (SheafOfModules.fullyFaithfulForget _).preimageIso
    (PresheafOfModules.isoMk
      (fun U ↦ ModuleCat.isoMk (Iso.refl _) (fun r ↦ ?_)) ?_)) ?_
  · ext x
    change (e.structural.hom.app U) ((ringMap Y a).hom.app U r) •
        (show M.val.obj ((siteMap g).op.obj U) from x) =
      (ringMap X a).hom.app ((siteMap g).op.obj U) ((d.structural.hom.app U) r) •
        (show M.val.obj ((siteMap g).op.obj U) from x)
    have h := congrArg (fun k ↦ k.hom.app U) (structural_naturality a d e)
    exact congrArg (fun r ↦ r • (show M.val.obj ((siteMap g).op.obj U) from x))
      (ConcreteCategory.congr_hom h r)
  · intro U V f
    ext x
    rfl
  · intro M N f
    ext U x
    rfl

private theorem ordinaryRestriction_sections {X Y : Scheme.{u}} {g : X ⟶ Y}
    {B C : ℕᵒᵖ ⥤ CommRingCat.{u + 1}} (a : B ⟶ C)
    (d : DirectImage g B) (e : DirectImage g C)
    (M : Modules X C) (n : ℕ) (U : Y.Etaleᵒᵖ)
    (x : M.val.obj ((siteMap g).op.obj (op (n, U.unop)))) :
    HEq (((ordinaryRestriction a d e).hom.app M).val.app (op (n, U.unop)) x) x := by
  rfl

private theorem level_smul (W : Scheme.{u}) (B : ℕᵒᵖ ⥤ CommRingCat.{u + 1})
    (n : ℕ) (M : Modules W B) (U : W.Etaleᵒᵖ) (r : B.obj (op n))
    (x : M.val.obj (op (n, U.unop))) :
    @SMul.smul _ _ (((level W B n).obj M).obj.obj U).isModule.toSMul r x =
      (toSheafify W.smallEtaleTopology
        ((Functor.const W.Etaleᵒᵖ).obj (B.obj (op n)))).app U r • x := by
  change @SMul.smul _ _ (M.val.obj (op (n, U.unop))).isModule.toSMul
    (((eqToHom (evaluation_ring W.smallEtaleTopology (coefficients W B)
      (transitions W B) n).symm).hom.app U)
      ((toSheafify W.smallEtaleTopology
        ((Functor.const W.Etaleᵒᵖ).obj (B.obj (op n)))).app U r)) x = _
  rw [ObjectProperty.eqToHom_hom, eqToHom_app]
  rfl

set_option maxHeartbeats 1200000 in
-- Evaluation transports the concrete ring action through sheafification.
private def ordinaryScalarEvaluation (W : Scheme.{u})
    {B C : ℕᵒᵖ ⥤ CommRingCat.{u + 1}} (a : B ⟶ C) (n : ℕ) :
    res (ringMap W a) ⋙ level W B n ≅
      level W C n ⋙ Sheaf.restrictScalars W.smallEtaleTopology (a.app (op n)).hom := by
  refine NatIso.ofComponents (fun M ↦ ObjectProperty.isoMk _
    (NatIso.ofComponents (fun U ↦ ModuleCat.isoMk (Iso.refl _) (fun r ↦ ?_)) ?_)) ?_
  · ext x
    change
      @SMul.smul _ _ (((level W C n).obj M).obj.obj U).isModule.toSMul
          ((a.app (op n)).hom r) x =
        @SMul.smul _ _
          (((level W B n).obj ((res (ringMap W a)).obj M)).obj.obj U).isModule.toSMul r x
    rw [level_smul, level_smul]
    change (toSheafify W.smallEtaleTopology ((Functor.const W.Etaleᵒᵖ).obj
        (C.obj (op n)))).app U ((a.app (op n)).hom r) •
          (show M.val.obj (op (n, U.unop)) from x) =
      (ringMap W a).hom.app (op (n, U.unop))
        ((toSheafify W.smallEtaleTopology ((Functor.const W.Etaleᵒᵖ).obj
          (B.obj (op n)))).app U r) • (show M.val.obj (op (n, U.unop)) from x)
    rw [ringMap_app]
    have h := congrArg (fun k ↦ k.app U)
      ((toSheafification W.smallEtaleTopology CommRingCat.{u + 1}).naturality
        ((Functor.const W.Etaleᵒᵖ).map (a.app (op n))))
    exact congrArg (fun r ↦ r • (show M.val.obj (op (n, U.unop)) from x))
      (ConcreteCategory.congr_hom h r)
  · intro U V f
    ext x
    rfl
  · intro M N f
    ext U x
    rfl

set_option maxHeartbeats 1200000 in
-- Comparing evaluated carriers unfolds module-sheaf forgetful functors.
private theorem isIso_of_levels (W : Scheme.{u})
    (B : ℕᵒᵖ ⥤ CommRingCat.{u + 1}) {M N : Modules W B} (f : M ⟶ N)
    (hf : ∀ n, IsIso ((level W B n).map f)) : IsIso f := by
  let T := SheafOfModules.forget
    (ring (coefficientSequenceTopology W.smallEtaleTopology) (rings W B)) ⋙
      PresheafOfModules.toPresheaf _
  have hU (U : (ℕ × W.Etale)ᵒᵖ) : IsIso ((T.map f).app U) := by
    have := hf U.unop.1
    let E := sheafToPresheaf W.smallEtaleTopology
        (ModuleCat.{u + 1} (B.obj (op U.unop.1))) ⋙
      (CategoryTheory.evaluation W.Etaleᵒᵖ
        (ModuleCat.{u + 1} (B.obj (op U.unop.1)))).obj (op U.unop.2) ⋙
      forget₂ (ModuleCat.{u + 1} (B.obj (op U.unop.1))) AddCommGrpCat.{u + 1}
    exact E.map_isIso ((level W B U.unop.1).map f)
  have : IsIso (T.map f) := NatIso.isIso_of_isIso_app _
  exact isIso_of_reflects_iso f T

private theorem derived_isIso_of_levels (W : Scheme.{u})
    (B : ℕᵒᵖ ⥤ CommRingCat.{u + 1}) (E : ∀ n, Evaluation W B n)
    {M N : Derived W B} (f : M ⟶ N)
    (hf : ∀ n, IsIso ((E n).E.map f)) : IsIso f := by
  rw [_root_.DerivedCategory.isIso_iff]
  intro q
  apply isIso_of_levels W B
  intro n
  let := (E n).additive
  let := (E n).limits
  let := (E n).colimits
  have := hf n
  exact (NatIso.isIso_map_iff ((level W B n).mapDerivedCategoryHomologyFunctorIso q) f).mpr
    (by
      change IsIso ((_root_.DerivedCategory.homologyFunctor _ q).map ((E n).E.map f))
      infer_instance)

private def inverseRestrictionMap {X Y : Scheme.{u}} {g : X ⟶ Y}
    {B C : ℕᵒᵖ ⥤ CommRingCat.{u + 1}} (a : B ⟶ C)
    (d : Image g B) (e : Image g C) :
    res (ringMap Y a) ⋙ d.inverse ⟶ e.inverse ⋙ res (ringMap X a) :=
  ((mateEquiv e.adjunction d.adjunction).symm
    (TwoSquare.mk _ _ _ _
      (ordinaryRestriction a d.toDirectImage e.toDirectImage).inv)).natTrans

section EvaluationCube
variable {X Y : Scheme.{u}} {g : X ⟶ Y}
  {B C : ℕᵒᵖ ⥤ CommRingCat.{u + 1}} (a : B ⟶ C)
  (d : Image g B) (e : Image g C) (n : ℕ)
  (exB : Evaluation X B n) (exC : Evaluation X C n)
  (eyB : Evaluation Y B n) (eyC : Evaluation Y C n)
  (LB : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} (B.obj (op n))) ⥤
    Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (B.obj (op n))))
  (LC : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} (C.obj (op n))) ⥤
    Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (C.obj (op n))))
  [LB.Additive] [PreservesFiniteLimits LB] [PreservesFiniteColimits LB]
  [LC.Additive] [PreservesFiniteLimits LC] [PreservesFiniteColimits LC]
  (adB : LB ⊣ lowerStar (ModuleCat.{u + 1} (B.obj (op n))) g)
  (adC : LC ⊣ lowerStar (ModuleCat.{u + 1} (C.obj (op n))) g)
  (p : ImageEvaluation d n exB eyB LB adB)
  (q : ImageEvaluation e n exC eyC LC adC)
  (θ : Sheaf.restrictScalars Y.smallEtaleTopology (a.app (op n)).hom ⋙ LB ≅
    LC ⋙ Sheaf.restrictScalars X.smallEtaleTopology (a.app (op n)).hom)
  (hθ : (mateEquiv adC adB (TwoSquare.mk _ _ _ _ θ.hom)).natTrans =
    (lowerStarRestrictScalarsIso (a.app (op n)).hom g).hom)

set_option maxHeartbeats 1200000 in
-- The mate cube compares concrete system and coefficient-level carriers.
include hθ in
private theorem inverseRestriction_evaluation (M : Modules Y C) :
    LB.map ((ordinaryScalarEvaluation Y a n).inv.app M) ≫
        p.inverse.hom.app ((res (ringMap Y a)).obj M) ≫
        (level X B n).map ((inverseRestrictionMap a d e).app M) =
      θ.hom.app ((level Y C n).obj M) ≫
        (Sheaf.restrictScalars X.smallEtaleTopology (a.app (op n)).hom).map
          (q.inverse.hom.app M) ≫
        (ordinaryScalarEvaluation X a n).inv.app (e.inverse.obj M) := by
  have hp : (mateEquiv d.adjunction adB
      (TwoSquare.mk _ _ _ _ p.inverse.hom)).natTrans = p.ordinary.hom := by
    rw [p.inverse_mate]
    exact congrArg TwoSquare.natTrans ((mateEquiv d.adjunction adB).apply_symm_apply _)
  have hq : (mateEquiv e.adjunction adC
      (TwoSquare.mk _ _ _ _ q.inverse.hom)).natTrans = q.ordinary.hom := by
    rw [q.inverse_mate]
    exact congrArg TwoSquare.natTrans ((mateEquiv e.adjunction adC).apply_symm_apply _)
  have hr : (mateEquiv e.adjunction d.adjunction
      (TwoSquare.mk _ _ _ _ (inverseRestrictionMap a d e))).natTrans =
      (ordinaryRestriction a d.toDirectImage e.toDirectImage).inv :=
    congrArg TwoSquare.natTrans ((mateEquiv e.adjunction d.adjunction).apply_symm_apply _)
  apply mateEquiv_app_cube_converse e.adjunction d.adjunction adC adB
    (inverseRestrictionMap a d e) θ.hom q.inverse.hom p.inverse.hom
    (ordinaryScalarEvaluation Y a n).inv (ordinaryScalarEvaluation X a n).inv
  intro N
  change _ ≫ (level Y B n).map
      ((mateEquiv e.adjunction d.adjunction
        (TwoSquare.mk _ _ _ _ (inverseRestrictionMap a d e))).natTrans.app N) ≫
      (mateEquiv d.adjunction adB
        (TwoSquare.mk _ _ _ _ p.inverse.hom)).natTrans.app _ =
    _ ≫ (mateEquiv adC adB (TwoSquare.mk _ _ _ _ θ.hom)).natTrans.app _ ≫ _
  dsimp only [TwoSquare.mk, TwoSquare.natTrans] at hp hq hr hθ ⊢
  rw [hp, hq, hr, hθ]
  ext U x
  change (p.ordinary.hom.app ((res (ringMap X a)).obj N)).hom.app U x =
    (q.ordinary.hom.app N).hom.app U x
  exact (eq_of_heq (p.sections ((res (ringMap X a)).obj N) U x)).trans
    (eq_of_heq (q.sections N U x)).symm

end EvaluationCube

attribute [local irreducible] ordinaryRestriction ordinaryScalarEvaluation

private theorem singleOrdinaryRestriction_mate
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {X Y : Scheme.{u}} (g : X ⟶ Y) :
    (mateEquiv (upperStarLowerStarAdjunction (ModuleCat.{u + 1} B) g)
      (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) g)
      (TwoSquare.mk _ _ _ _ (upperStarRestrictScalarsIso φ g).hom)).natTrans =
        (lowerStarRestrictScalarsIso φ g).hom := by
  rw [← single_inverse_restriction_eq]
  exact underived_mate φ g

private theorem singleDerivedRestriction_isIso
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {X Y : Scheme.{u}} (g : X ⟶ Y) :
    IsIso (mateEquiv
      (Adjunction.mapDerivedCategoryRightDerivedAdjunction
        (upperStarLowerStarAdjunction (ModuleCat.{u + 1} B) g))
      (Adjunction.mapDerivedCategoryRightDerivedAdjunction
        (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) g))
      (TwoSquare.mk _ _ _ _ (Functor.mapDerivedCategorySquareIso
        (upperStarRestrictScalarsIso φ g)).hom)).natTrans := by
  have h := scalar_directImage_isIso φ g
  rw [restriction_exact_mate, single_inverse_restriction_eq] at h
  exact h

set_option maxHeartbeats 1200000 in
-- The dependent record carries exact functors and normalized adjunctions.
private structure RestrictionLevel {X Y : Scheme.{u}} {g : X ⟶ Y}
    {B C : ℕᵒᵖ ⥤ CommRingCat.{u + 1}} (a : B ⟶ C)
    (d : Image g B) (e : Image g C) (n : ℕ) where
  exB : Evaluation X B n
  exC : Evaluation X C n
  eyB : Evaluation Y B n
  eyC : Evaluation Y C n
  LB : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} (B.obj (op n))) ⥤
    Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (B.obj (op n)))
  LC : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} (C.obj (op n))) ⥤
    Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (C.obj (op n)))
  [addB : LB.Additive]
  [limB : PreservesFiniteLimits LB]
  [colimB : PreservesFiniteColimits LB]
  [addC : LC.Additive]
  [limC : PreservesFiniteLimits LC]
  [colimC : PreservesFiniteColimits LC]
  adjB : LB ⊣ lowerStar (ModuleCat.{u + 1} (B.obj (op n))) g
  adjC : LC ⊣ lowerStar (ModuleCat.{u + 1} (C.obj (op n))) g
  evalB : ImageEvaluation d n exB eyB LB adjB
  evalC : ImageEvaluation e n exC eyC LC adjC
  inverseSquare : Sheaf.restrictScalars Y.smallEtaleTopology (a.app (op n)).hom ⋙ LB ≅
    LC ⋙ Sheaf.restrictScalars X.smallEtaleTopology (a.app (op n)).hom
  mate : (mateEquiv adjC adjB (TwoSquare.mk _ _ _ _ inverseSquare.hom)).natTrans =
    (lowerStarRestrictScalarsIso (a.app (op n)).hom g).hom

attribute [local instance] RestrictionLevel.addB RestrictionLevel.limB RestrictionLevel.colimB
  RestrictionLevel.addC RestrictionLevel.limC RestrictionLevel.colimC

private abbrev RestrictionLevel.DerivedMate {X Y : Scheme.{u}} {g : X ⟶ Y}
    {B C : ℕᵒᵖ ⥤ CommRingCat.{u + 1}} {a : B ⟶ C}
    {d : Image g B} {e : Image g C} {n : ℕ} (r : RestrictionLevel a d e n) :=
  IsIso (mateEquiv r.adjC.mapDerivedCategoryRightDerivedAdjunction
    r.adjB.mapDerivedCategoryRightDerivedAdjunction
    (TwoSquare.mk _ _ _ _ (Functor.mapDerivedCategorySquareIso r.inverseSquare).hom)).natTrans


set_option maxHeartbeats 1200000 in
-- The reflected mate compares functors on the actual sequence sites.
private theorem inverseRestriction_isIso {X Y : Scheme.{u}} {g : X ⟶ Y}
    {B C : ℕᵒᵖ ⥤ CommRingCat.{u + 1}} (a : B ⟶ C)
    (d : Image g B) (e : Image g C) (r : ∀ n, RestrictionLevel a d e n) :
    IsIso (inverseRestrictionMap a d e) := by
  refine @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ ?_
  intro M
  apply isIso_of_levels X B
  intro n
  have h := inverseRestriction_evaluation a d e n (r n).exB (r n).exC
    (r n).eyB (r n).eyC (r n).LB (r n).LC (r n).adjB (r n).adjC
    (r n).evalB (r n).evalC (r n).inverseSquare (r n).mate M
  have hi : IsIso ((r n).LB.map ((ordinaryScalarEvaluation Y a n).inv.app M) ≫
      (r n).evalB.inverse.hom.app ((res (ringMap Y a)).obj M) ≫
      (level X B n).map ((inverseRestrictionMap a d e).app M)) := by
    rw [h]
    infer_instance
  simpa only [isIso_comp_left_iff] using hi

private theorem mapSquare_symm {A D E F : Type*} [Category A] [Category D] [Category E] [Category F]
    [Abelian A] [Abelian D] [Abelian E] [Abelian F]
    [HasDerivedCategory A] [HasDerivedCategory D]
    [HasDerivedCategory E] [HasDerivedCategory F]
    {H : A ⥤ D} {I : D ⥤ F} {J : A ⥤ E} {K : E ⥤ F}
    [H.Additive] [I.Additive] [J.Additive] [K.Additive]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    [PreservesFiniteLimits I] [PreservesFiniteColimits I]
    [PreservesFiniteLimits J] [PreservesFiniteColimits J]
    [PreservesFiniteLimits K] [PreservesFiniteColimits K]
    (z : H ⋙ I ≅ J ⋙ K) :
    (Functor.mapDerivedCategorySquareIso z.symm).hom =
      (Functor.mapDerivedCategorySquareIso z).inv := by
  simp only [Functor.mapDerivedCategorySquareIso, Iso.trans_hom, Iso.symm_hom,
    Iso.trans_inv, Iso.symm_inv, Functor.mapDerivedCategoryNatIso_symm, Category.assoc]

set_option maxHeartbeats 1200000 in
-- The derived mate cube has six exact functor comparisons.
private theorem restrictionImage_fromLevels {X Y : Scheme.{u}} {g : X ⟶ Y}
    {B C : ℕᵒᵖ ⥤ CommRingCat.{u + 1}} (a : B ⟶ C)
    (d : Image g B) (e : Image g C) (r : ∀ n, RestrictionLevel a d e n)
    (hr : ∀ n, (r n).DerivedMate) :
    Nonempty (RestrictionImage a d e) := by
  let := d.inverseAdditive
  let := d.inverseLimits
  let := d.inverseColimits
  let := d.pushAdditive
  let := d.kinjectives
  let := e.inverseAdditive
  let := e.inverseLimits
  let := e.inverseColimits
  let := e.pushAdditive
  let := e.kinjectives
  let := inverseRestriction_isIso a d e r
  let ρ := asIso (inverseRestrictionMap a d e)
  let ρD := Functor.mapDerivedCategorySquareIso ρ
  let τ := (mateEquiv e.derivedAdjunction d.derivedAdjunction
    (TwoSquare.mk _ _ _ _ ρD.hom)).natTrans
  have hτ : IsIso τ := by
    refine @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ ?_
    intro M
    apply derived_isIso_of_levels Y B (fun n ↦ (r n).eyB)
    intro n
    let rr := r n
    let := rr.exB.additive
    let := rr.exB.limits
    let := rr.exB.colimits
    let := rr.exC.additive
    let := rr.exC.limits
    let := rr.exC.colimits
    let := rr.eyB.additive
    let := rr.eyB.limits
    let := rr.eyB.colimits
    let := rr.eyC.additive
    let := rr.eyC.limits
    let := rr.eyC.colimits
    let γ := ordinaryScalarEvaluation Y a n
    let η := ordinaryScalarEvaluation X a n
    let γD := Functor.mapDerivedCategorySquareIso γ
    let ηD := Functor.mapDerivedCategorySquareIso η
    have hc := Functor.mapDerivedCategory_exactCube
      (level Y C n) (Sheaf.restrictScalars Y.smallEtaleTopology (a.app (op n)).hom)
      rr.LB (res (ringMap Y a)) (level Y B n) d.inverse (level X B n)
      e.inverse (res (ringMap X a)) rr.LC
      (Sheaf.restrictScalars X.smallEtaleTopology (a.app (op n)).hom) (level X C n)
      γ.symm rr.evalB.inverse ρ rr.inverseSquare rr.evalC.inverse η.symm
      (inverseRestriction_evaluation a d e n rr.exB rr.exC rr.eyB rr.eyC
        rr.LB rr.LC rr.adjB rr.adjC rr.evalB rr.evalC rr.inverseSquare rr.mate)
    have hleft (K : Derived Y C) :
        rr.LB.mapDerivedCategory.map (γD.inv.app K) ≫
            rr.evalB.derivedInverse.hom.app ((restriction Y a).obj K) ≫
            rr.exB.E.map (ρD.hom.app K) =
          (Functor.mapDerivedCategorySquareIso rr.inverseSquare).hom.app (rr.eyC.E.obj K) ≫
            (Sheaf.derivedRestrictScalars X.smallEtaleTopology (a.app (op n)).hom).map
              (rr.evalC.derivedInverse.hom.app K) ≫
            ηD.inv.app (e.P.obj K) := by
      have hh := congr_app hc K
      change rr.LB.mapDerivedCategory.map
          ((Functor.mapDerivedCategorySquareIso γ.symm).hom.app K) ≫
          (Functor.mapDerivedCategorySquareIso rr.evalB.inverse).hom.app
            ((restriction Y a).obj K) ≫ rr.exB.E.map (ρD.hom.app K) =
        (Functor.mapDerivedCategorySquareIso rr.inverseSquare).hom.app (rr.eyC.E.obj K) ≫
          (Sheaf.derivedRestrictScalars X.smallEtaleTopology (a.app (op n)).hom).map
            ((Functor.mapDerivedCategorySquareIso rr.evalC.inverse).hom.app K) ≫
          (Functor.mapDerivedCategorySquareIso η.symm).hom.app (e.P.obj K) at hh
      erw [mapSquare_symm γ, mapSquare_symm η] at hh
      rw [rr.evalB.derivedInverse_termwise, rr.evalC.derivedInverse_termwise]
      exact hh
    have hm := mateEquiv_app_cube e.derivedAdjunction d.derivedAdjunction
      rr.adjC.mapDerivedCategoryRightDerivedAdjunction
      rr.adjB.mapDerivedCategoryRightDerivedAdjunction
      ρD.hom (Functor.mapDerivedCategorySquareIso rr.inverseSquare).hom
      rr.evalC.derivedInverse.hom rr.evalB.derivedInverse.hom γD.inv ηD.inv hleft M
    have hp := rr.evalB.derived_mate
    have hq := rr.evalC.derived_mate
    dsimp only [TwoSquare.mk, TwoSquare.natTrans] at hp hq hm
    rw [← hp, ← hq] at hm
    let := hr n
    have hi : IsIso (γD.inv.app (e.R.obj M) ≫ rr.eyB.E.map (τ.app M) ≫
        rr.evalB.derived.hom.app ((restriction X a).obj M)) := by
      rw [hm]
      infer_instance
    simpa only [isIso_comp_left_iff, isIso_comp_right_iff] using hi
  let := hτ
  exact ⟨{
    ordinary := ordinaryRestriction a d.toDirectImage e.toDirectImage
    sections := ordinaryRestriction_sections a d.toDirectImage e.toDirectImage
    inverseImage := ρ
    inverseImage_mate := rfl
    derivedInverse := ρD
    derivedInverse_termwise := rfl
    derived := asIso τ
    derived_mate := rfl
  }⟩

set_option maxHeartbeats 1200000 in
-- The exact pullback is instantiated at the coefficient level.
private theorem properRestrictionLevel
    {X Y : Scheme.{u}} {f : X ⟶ Y} {c : Compactification f} {l : ℕ}
    (b : BasicData c l) {B C : Coefficients.{u} l}
    (a : B.rings ⟶ C.rings) (n : ℕ) :
    Nonempty { r : RestrictionLevel a (b.support B).proper (b.support C).proper n //
      r.DerivedMate } := by
  let p := (supportEvaluation_nonempty b B n).some
  let q := (supportEvaluation_nonempty b C n).some
  refine ⟨⟨{
    exB := b.evaluationZ B n
    exC := b.evaluationZ C n
    eyB := b.evaluationY B n
    eyC := b.evaluationY C n
    LB := upperStar (ModuleCat.{u + 1} (B.rings.obj (op n))) c.g
    LC := upperStar (ModuleCat.{u + 1} (C.rings.obj (op n))) c.g
    adjB := upperStarLowerStarAdjunction _ c.g
    adjC := upperStarLowerStarAdjunction _ c.g
    evalB := p.proper
    evalC := q.proper
    inverseSquare := upperStarRestrictScalarsIso (a.app (op n)).hom c.g
    mate := singleOrdinaryRestriction_mate (a.app (op n)).hom c.g
  }, ?_⟩⟩
  exact singleDerivedRestriction_isIso (a.app (op n)).hom c.g

set_option maxHeartbeats 1200000 in
-- The derived mate uses two exact left-adjoint models.
private theorem openRestrictionLevel
    {X Y : Scheme.{u}} {f : X ⟶ Y} {c : Compactification f} {l : ℕ}
    (b : BasicData c l) {B C : Coefficients.{u} l}
    (a : B.rings ⟶ C.rings) (n : ℕ) :
    Nonempty { r : RestrictionLevel a (b.support B).openImage.toImage
      (b.support C).openImage.toImage n // r.DerivedMate } := by
  let p := (supportEvaluation_nonempty b B n).some
  let q := (supportEvaluation_nonempty b C n).some
  let adB := openImmersionRestrictionLowerStarAdjunction
    (ModuleCat.{u + 1} (B.rings.obj (op n))) c.i
  let adC := openImmersionRestrictionLowerStarAdjunction
    (ModuleCat.{u + 1} (C.rings.obj (op n))) c.i
  let := adB.isLeftAdjoint
  let := adC.isLeftAdjoint
  let θ : Sheaf.restrictScalars c.Z.smallEtaleTopology (a.app (op n)).hom ⋙
      openImmersionRestriction (ModuleCat.{u + 1} (B.rings.obj (op n))) c.i ≅
    openImmersionRestriction (ModuleCat.{u + 1} (C.rings.obj (op n))) c.i ⋙
      Sheaf.restrictScalars X.smallEtaleTopology (a.app (op n)).hom := Iso.refl _
  have hθ : (mateEquiv adC adB (TwoSquare.mk _ _ _ _ θ.hom)).natTrans =
      (lowerStarRestrictScalarsIso (a.app (op n)).hom c.i).hom := by
    apply congrArg TwoSquare.natTrans
    apply mateEquiv_eq_of_unit
    intro M
    change (Sheaf.restrictScalars c.Z.smallEtaleTopology (a.app (op n)).hom).map
        (adC.unit.app M) ≫ 𝟙 _ =
      adB.unit.app _ ≫
        (lowerStar (ModuleCat.{u + 1} (B.rings.obj (op n))) c.i).map (𝟙 _)
    erw [Category.comp_id]
  refine ⟨⟨{
    exB := b.evaluationX B n
    exC := b.evaluationX C n
    eyB := b.evaluationZ B n
    eyC := b.evaluationZ C n
    LB := openImmersionRestriction (ModuleCat.{u + 1} (B.rings.obj (op n))) c.i
    LC := openImmersionRestriction (ModuleCat.{u + 1} (C.rings.obj (op n))) c.i
    adjB := adB
    adjC := adC
    evalB := p.openImage.image
    evalC := q.openImage.image
    inverseSquare := θ
    mate := hθ
  }, ?_⟩⟩
  apply rightDerivedMate_isIso_of_ordinaryMate_isIso _ _ adC adB
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} (C.rings.obj (op n))) c.i)
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} (B.rings.obj (op n))) c.i)
    θ (upperStarRestrictScalarsIso (a.app (op n)).hom c.i)
  · rw [hθ]
    infer_instance
  · rw [singleOrdinaryRestriction_mate]
    infer_instance
  · exact singleDerivedRestriction_isIso (a.app (op n)).hom c.i

private theorem openExtension_mate
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j] :
    (mateEquiv (openImmersionLowerShriekAdjunction (ModuleCat.{u + 1} B) j)
      (openImmersionLowerShriekAdjunction (ModuleCat.{u + 1} A) j)
      (TwoSquare.mk _ _ _ _
        (openImmersionLowerShriekRestrictScalarsIso φ j).hom)).natTrans = 𝟙 _ := by
  apply congrArg TwoSquare.natTrans
  apply mateEquiv_eq_of_unit
  intro M
  change (Sheaf.restrictScalars X.smallEtaleTopology φ).map
      ((openImmersionLowerShriekAdjunction (ModuleCat.{u + 1} B) j).unit.app M) ≫ 𝟙 _ =
    (openImmersionLowerShriekAdjunction (ModuleCat.{u + 1} A) j).unit.app _ ≫
      (openImmersionRestriction (ModuleCat.{u + 1} A) j).map
        ((openImmersionLowerShriekRestrictScalarsIso φ j).hom.app M)
  rw [Category.comp_id]
  exact (openImmersionLowerShriekAdjunction_unit_app_comp_openImmersionRestrictionMap
    φ j M).symm

set_option maxHeartbeats 1200000 in
-- The sectionwise comparison crosses concrete restriction functors.
private theorem ordinaryRestriction_unique {X Y : Scheme.{u}} {g : X ⟶ Y}
    {B C : ℕᵒᵖ ⥤ CommRingCat.{u + 1}} (a : B ⟶ C)
    (d : Image g B) (e : Image g C) (r : RestrictionImage a d e) :
    r.ordinary = ordinaryRestriction a d.toDirectImage e.toDirectImage := by
  apply Iso.ext
  ext M U x
  exact (eq_of_heq (r.sections M U.unop.1 (op U.unop.2) x)).trans
    (eq_of_heq (ordinaryRestriction_sections a d.toDirectImage e.toDirectImage
      M U.unop.1 (op U.unop.2) x)).symm

private theorem invert_comparison_cube {D : Type*} [Category D]
    {A B C E F : D} (f : A ⟶ B) (p : B ≅ C) (t : C ≅ E) (q : A ≅ F)
    (γ : F ⟶ E) (h : f ≫ p.hom ≫ t.hom = q.hom ≫ γ) :
    γ ≫ t.inv ≫ p.inv = q.inv ≫ f := by
  apply (cancel_epi q.hom).mp
  calc
    q.hom ≫ (γ ≫ t.inv ≫ p.inv) = (q.hom ≫ γ) ≫ t.inv ≫ p.inv := by
      simp only [Category.assoc]
    _ = (f ≫ p.hom ≫ t.hom) ≫ t.inv ≫ p.inv := by rw [← h]
    _ = f := by
      simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id]
    _ = q.hom ≫ (q.inv ≫ f) := by rw [Iso.hom_inv_id_assoc]

set_option maxHeartbeats 1200000 in
-- The open mate cube uses concrete restriction and extension functors.
private theorem restrictionOpen_fromEvaluation
    {X Y : Scheme.{u}} {f : X ⟶ Y} {c : Compactification f} {l : ℕ}
    (b : BasicData c l) {B C : Coefficients.{u} l} (a : B.rings ⟶ C.rings)
    (r : RestrictionImage a (b.support B).openImage.toImage
      (b.support C).openImage.toImage) :
    Nonempty (RestrictionOpen a (b.support B).openImage (b.support C).openImage) := by
  let d := (b.support B).openImage
  let e := (b.support C).openImage
  have hρ : r.inverseImage.hom = inverseRestrictionMap a d.toImage e.toImage := by
    rw [r.inverseImage_mate, ordinaryRestriction_unique a d.toImage e.toImage r]
    rfl
  let τ := ((mateEquiv e.openAdjunction d.openAdjunction).symm
    (TwoSquare.mk _ _ _ _ r.inverseImage.inv)).natTrans
  have hτ : IsIso τ := by
    refine @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ ?_
    intro M
    apply isIso_of_levels c.Z B.rings
    intro n
    let p := (supportEvaluation_nonempty b B n).some.openImage
    let q := (supportEvaluation_nonempty b C n).some.openImage
    let adB := openImmersionLowerShriekAdjunction
      (ModuleCat.{u + 1} (B.rings.obj (op n))) c.i
    let adC := openImmersionLowerShriekAdjunction
      (ModuleCat.{u + 1} (C.rings.obj (op n))) c.i
    let γ := ordinaryScalarEvaluation X a n
    let η := ordinaryScalarEvaluation c.Z a n
    let β := openImmersionLowerShriekRestrictScalarsIso (a.app (op n)).hom c.i
    have hp : (mateEquiv d.openAdjunction adB
        (TwoSquare.mk _ _ _ _ p.ordinary.inv)).natTrans = p.image.inverse.inv := by
      rw [p.mate]
      exact congrArg TwoSquare.natTrans
        ((mateEquiv d.openAdjunction adB).apply_symm_apply _)
    have hq : (mateEquiv e.openAdjunction adC
        (TwoSquare.mk _ _ _ _ q.ordinary.inv)).natTrans = q.image.inverse.inv := by
      rw [q.mate]
      exact congrArg TwoSquare.natTrans
        ((mateEquiv e.openAdjunction adC).apply_symm_apply _)
    have hr : (mateEquiv e.openAdjunction d.openAdjunction
        (TwoSquare.mk _ _ _ _ τ)).natTrans = r.inverseImage.inv :=
      congrArg TwoSquare.natTrans
        ((mateEquiv e.openAdjunction d.openAdjunction).apply_symm_apply _)
    have hiθ : (mateEquiv
        (openImmersionRestrictionLowerStarAdjunction
          (ModuleCat.{u + 1} (C.rings.obj (op n))) c.i)
        (openImmersionRestrictionLowerStarAdjunction
          (ModuleCat.{u + 1} (B.rings.obj (op n))) c.i)
        (TwoSquare.mk _ _ _ _ (Iso.refl _).hom)).natTrans =
        (lowerStarRestrictScalarsIso (a.app (op n)).hom c.i).hom := by
      apply congrArg TwoSquare.natTrans
      apply mateEquiv_eq_of_unit
      intro N
      change (Sheaf.restrictScalars c.Z.smallEtaleTopology (a.app (op n)).hom).map
          ((openImmersionRestrictionLowerStarAdjunction
            (ModuleCat.{u + 1} (C.rings.obj (op n))) c.i).unit.app N) ≫ 𝟙 _ =
        (openImmersionRestrictionLowerStarAdjunction
          (ModuleCat.{u + 1} (B.rings.obj (op n))) c.i).unit.app _ ≫
          (lowerStar (ModuleCat.{u + 1} (B.rings.obj (op n))) c.i).map (𝟙 _)
      erw [Category.comp_id]
    have hc (K : Modules c.Z C.rings) :
        γ.inv.app (e.inverse.obj K) ≫
            (level X B.rings n).map (r.inverseImage.inv.app K) ≫
            p.image.inverse.inv.app ((res (ringMap c.Z a)).obj K) =
          (Sheaf.restrictScalars X.smallEtaleTopology (a.app (op n)).hom).map
              (q.image.inverse.inv.app K) ≫
            (openImmersionRestriction (ModuleCat.{u + 1} (B.rings.obj (op n))) c.i).map
              (η.inv.app K) := by
      have hh := inverseRestriction_evaluation a d.toImage e.toImage n
        (b.evaluationX B n) (b.evaluationX C n)
        (b.evaluationZ B n) (b.evaluationZ C n) _ _ _ _
        p.image q.image (Iso.refl _) hiθ K
      rw [← hρ] at hh
      exact invert_comparison_cube
        ((openImmersionRestriction (ModuleCat.{u + 1} (B.rings.obj (op n))) c.i).map
          (η.inv.app K))
        (p.image.inverse.app ((res (ringMap c.Z a)).obj K))
        ((level X B.rings n).mapIso (r.inverseImage.app K))
        ((Sheaf.restrictScalars X.smallEtaleTopology (a.app (op n)).hom).mapIso
          (q.image.inverse.app K))
        (γ.inv.app (e.inverse.obj K))
        (by simpa only [γ, η, Iso.app_hom, CategoryTheory.Functor.mapIso_hom,
          Iso.refl_hom, NatTrans.id_app, Category.id_comp] using hh)
    have hl := mateEquiv_app_cube_converse e.openAdjunction d.openAdjunction adC adB
      τ β.hom q.ordinary.inv p.ordinary.inv γ.inv η.inv (fun K ↦ by
        change _ ≫ (level X B.rings n).map
            ((mateEquiv e.openAdjunction d.openAdjunction
              (TwoSquare.mk _ _ _ _ τ)).natTrans.app K) ≫
            (mateEquiv d.openAdjunction adB
              (TwoSquare.mk _ _ _ _ p.ordinary.inv)).natTrans.app _ =
          _ ≫ (mateEquiv adC adB (TwoSquare.mk _ _ _ _ β.hom)).natTrans.app _ ≫ _
        have hβ := openExtension_mate (a.app (op n)).hom c.i
        dsimp only [TwoSquare.mk, TwoSquare.natTrans] at hp hq hr hβ ⊢
        rw [hp, hq, hr, hβ]
        simpa only [NatTrans.id_app, Category.id_comp] using hc K) M
    have hz : IsIso ((openImmersionLowerShriek
          (ModuleCat.{u + 1} (B.rings.obj (op n))) c.i).map (γ.inv.app M) ≫
        p.ordinary.inv.app ((res (ringMap X a)).obj M) ≫
        (level c.Z B.rings n).map (τ.app M)) := by
      rw [hl]
      infer_instance
    simpa only [isIso_comp_left_iff] using hz
  let := hτ
  exact ⟨{ image := r, ordinary := asIso τ, mate := rfl }⟩

set_option maxHeartbeats 1200000 in
-- The proper and open comparisons instantiate concrete ringed-site records.
/-- The normalized restriction comparison exists for compactly supported systems.
Source: Zheng Lemma 5.16; Stacks 0GL6.
(blueprint: lem-pur-etale-system-projection-restriction-support-existence).

Proof: Restriction of the proper direct image is fixed on sections, and its inverse-image
mate is pasted with the exact open restriction mate. Localizing this ordinary square gives
the prescribed restriction comparison for compact support.
-/
theorem restrictionSupport_nonempty
    {X Y : Scheme.{u}} {f : X ⟶ Y} {c : Compactification f} {l : ℕ}
    (b : BasicData c l) {B C : Coefficients.{u} l}
    (a : B.rings ⟶ C.rings) :
    Nonempty (RestrictionSupport a (b.support B) (b.support C)) := by
  classical
  let rp := fun n ↦ (properRestrictionLevel b a n).some
  let ro := fun n ↦ (openRestrictionLevel b a n).some
  let p := (restrictionImage_fromLevels a (b.support B).proper (b.support C).proper
    (fun n ↦ (rp n).val) (fun n ↦ (rp n).property)).some
  let o := (restrictionImage_fromLevels a (b.support B).openImage.toImage
    (b.support C).openImage.toImage (fun n ↦ (ro n).val) (fun n ↦ (ro n).property)).some
  exact ⟨{ proper := p, openImage := (restrictionOpen_fromEvaluation b a o).some }⟩

end AlgebraicGeometry.Etale.SystemProjection
