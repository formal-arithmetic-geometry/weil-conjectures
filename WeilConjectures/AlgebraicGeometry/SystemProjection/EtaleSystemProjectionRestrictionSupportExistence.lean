/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SystemProjection.EtaleSystemProjectionBasicData
import WeilConjectures.CategoryTheory.Adjunction.MateCube
import WeilConjectures.CategoryTheory.Derived.DerivedExactCube
import WeilConjectures.AlgebraicGeometry.SystemProjection.EtaleSystemProjectionBasicData
import all WeilConjectures.AlgebraicGeometry.SystemProjection.EtaleSingleCoefficientProjection
import all WeilConjectures.AlgebraicGeometry.Etale.Proper.EtaleProperCoefficientTensorUnit
import all WeilConjectures.AlgebraicGeometry.Finite.Coefficient.FiniteCoefficientDirectImage
import WeilConjectures.CategoryTheory.Right.RightDerivedMateIndependence
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
end EvaluationCube

attribute [local irreducible] ordinaryRestriction ordinaryScalarEvaluation

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
set_option maxHeartbeats 1200000 in
-- The derived mate cube has six exact functor comparisons.
set_option maxHeartbeats 1200000 in
-- The exact pullback is instantiated at the coefficient level.
set_option maxHeartbeats 1200000 in
-- The derived mate uses two exact left-adjoint models.
set_option maxHeartbeats 1200000 in
-- The sectionwise comparison crosses concrete restriction functors.
set_option maxHeartbeats 1200000 in
-- The open mate cube uses concrete restriction and extension functors.
set_option maxHeartbeats 1200000 in
-- The proper and open comparisons instantiate concrete ringed-site records.
end AlgebraicGeometry.Etale.SystemProjection
