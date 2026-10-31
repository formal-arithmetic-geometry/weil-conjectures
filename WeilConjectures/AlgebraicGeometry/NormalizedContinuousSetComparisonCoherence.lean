/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ContinuousSetConstructions
public import WeilConjectures.AlgebraicGeometry.ProfinitePointPullback
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.CategoryTheory.Sites.Equivalence
public import WeilConjectures.CategoryTheory.SiteInverseImageTensor
public import WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
public import Mathlib.CategoryTheory.Monoidal.CommGrp_
public import Mathlib.CategoryTheory.Monoidal.Ring
public import Mathlib.CategoryTheory.Adjunction.Limits
public import WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
public import WeilConjectures.CategoryTheory.Monoidal.Conjugate
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
public import WeilConjectures.CategoryTheory.Sites.MonObj
public import WeilConjectures.AlgebraicGeometry.RelativeProfiniteTestLabels
public import Mathlib.AlgebraicGeometry.Scheme

import Mathlib.CategoryTheory.Sites.Pullback
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

/-! # Coherence of arbitrary normalized continuous-set comparisons

Source: Hemo--Richarz--Scholbach, Example 3.1 and the following scheme-pullback
paragraph, p. 6; Stacks Project, Tags 0037, 0DV0, 0B65 and 00X6
(blueprint: lem-sfb-normalized-continuous-set-comparison-coherence).

The normalization is the existing composite-adjunction test-function formula.
The scheme comparison is the existing adjunct of restriction along the fibre-product
projection. No invertibility hypothesis on the supplied family is imposed.
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale

private lemma normalized_natural (X : Scheme.{u}) {D E : Type (u + 1)}
    [TopologicalSpace D] [TopologicalSpace E]
    (σD : (profinitePointSetSchemeInverseImage X).obj (continuousSetProfiniteSheaf D) ⟶
      continuousSetSheaf X D)
    (σE : (profinitePointSetSchemeInverseImage X).obj (continuousSetProfiniteSheaf E) ⟶
      continuousSetSheaf X E)
    (hD : IsContinuousSetRealization X D σD) (hE : IsContinuousSetRealization X E σE)
    (h : C(D, E)) :
    σD ≫ continuousSetSheafMap X h =
      (profinitePointSetSchemeInverseImage X).map
        (continuousSetProfiniteFunctor.map (TopCat.ofHom h)) ≫ σE := by
  apply (continuousSetPointAdjunction X).homEquiv _ _ |>.injective
  rw [Adjunction.homEquiv_naturality_right, Adjunction.homEquiv_naturality_left]
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext S
  apply ConcreteCategory.hom_ext
  intro b
  change h.comp ((((continuousSetPointAdjunction X).homEquiv _ _ σD).hom.app S) b) =
    (((continuousSetPointAdjunction X).homEquiv _ _ σE).hom.app S) (h.comp b)
  rw [hD S.unop b, hE S.unop (h.comp b)]
  rfl

set_option backward.isDefEq.respectTransparency false in
private def functionProductLimit {C : Type v} [Category.{w} C]
    (G : C ⥤ TopCat.{u}) (I : Type u) (D : I → Type (u + 1))
    [∀ i, TopologicalSpace (D i)] :
    IsLimit (Fan.mk (ContinuousMap.yonedaPresheaf G (∀ i, D i))
      (fun i ↦ (show ContinuousMap.yonedaPresheaf G (∀ i, D i) ⟶
        ContinuousMap.yonedaPresheaf G (D i) from
          { app := fun _ ↦ ↾fun b ↦ (⟨fun d ↦ d i, continuous_apply i⟩ :
                C((∀ j, D j), D i)).comp b
            naturality := fun _ _ _ ↦ rfl }))) := by
  refine Fan.IsLimit.mk _ (fun s ↦
    { app := fun U ↦ ↾fun x ↦
        (⟨fun z i ↦ (show C(G.obj U.unop, D i) from (s.proj i).app U x).toFun z,
          continuous_pi fun i ↦ (show C(G.obj U.unop, D i) from (s.proj i).app U x).continuous⟩ :
            C(G.obj U.unop, ∀ i, D i))
      naturality := ?_ }) ?_ ?_
  · intro U V f
    apply ConcreteCategory.hom_ext
    intro x
    apply ContinuousMap.ext
    intro z
    funext i
    exact congrArg (fun k ↦ (show C(G.obj V.unop, D i) from k x).toFun z) ((s.proj i).naturality f)
  · intro s i
    apply NatTrans.ext
    funext U
    rfl
  · intro s m hm
    apply NatTrans.ext
    funext U
    apply ConcreteCategory.hom_ext
    intro x
    apply ContinuousMap.ext
    intro z
    funext i
    exact congrArg (fun h ↦ (show C(G.obj U.unop, D i) from h.app U x).toFun z) (hm i)

private noncomputable def profinite_products (I : Type u) (D : I → Type (u + 1))
    [∀ i, TopologicalSpace (D i)] :
    IsLimit (Fan.mk (continuousSetProfiniteSheaf (∀ i, D i))
      (fun i ↦ continuousSetProfiniteFunctor.map (TopCat.ofHom
        (⟨fun d ↦ d i, continuous_apply i⟩ : C((∀ j, D j), D i))))) := by
  apply isLimitOfIsLimitFanMkObj
    (sheafToPresheaf (coherentTopology Profinite.{u}) (Type (u + 1)))
  exact functionProductLimit (CompHausLike.compHausLikeToTop
    (fun T ↦ TotallyDisconnectedSpace T)) I D

private noncomputable def scheme_products (X : Scheme.{u}) (I : Type u) (D : I → Type (u + 1))
    [∀ i, TopologicalSpace (D i)] :
    IsLimit (Fan.mk (continuousSetSheaf X (∀ i, D i))
      (fun i ↦ continuousSetSheafMap X
        (⟨fun d ↦ d i, continuous_apply i⟩ : C((∀ j, D j), D i)))) := by
  apply isLimitOfIsLimitFanMkObj
    (sheafToPresheaf (Scheme.ProEt.topology X) (Type (u + 1)))
  exact functionProductLimit
    (Scheme.ProEt.forget X ⋙ Over.forget X ⋙ Scheme.forgetToTop) I D

private lemma transpose_comp
    {C D E : Type*} [Category C] [Category D] [Category E]
    {L : C ⥤ D} {R : D ⥤ C} {F : D ⥤ E} {G : E ⥤ D}
    (a : L ⊣ R) (b : F ⊣ G) (A : C) (B : E) (q : F.obj (L.obj A) ⟶ B) :
    (a.comp b).homEquiv A B q = a.homEquiv A (G.obj B) (b.homEquiv (L.obj A) B q) := by
  rw [Adjunction.comp_homEquiv]
  rfl

private lemma transpose_conjugate
    {C D : Type*} [Category C] [Category D]
    {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (α : R₁ ⟶ R₂)
    (A : C) (B : D) (q : L₁.obj A ⟶ B) :
    adj₂.homEquiv A B (((conjugateEquiv adj₁ adj₂).symm α).app A ≫ q) =
      adj₁.homEquiv A B q ≫ α.app B := by
  rw [Adjunction.homEquiv_apply, Functor.map_comp, ← Category.assoc,
    ← unit_conjugateEquiv_symm, Category.assoc, ← α.naturality]
  rw [Adjunction.homEquiv_apply, Category.assoc]

private lemma pullback_identity (X : Scheme.{u}) (D : Type (u + 1))
    [TopologicalSpace D] :
    continuousSetPullbackMap (𝟙 X) D =
      (profinitePointSetIdentity X).hom.app (continuousSetSheaf X D) := by
  apply (Scheme.proEtaleSheafAdjunction (𝟙 X) (Type (u + 1))).homEquiv _ _ |>.injective
  change _ = (Scheme.proEtaleSheafAdjunction (𝟙 X) (Type (u + 1))).homEquiv _ _
    (((conjugateEquiv Adjunction.id
      (Scheme.proEtaleSheafAdjunction (𝟙 X) (Type (u + 1)))).symm
        (lowerStarId (Type (u + 1)) X).inv).app _)
  rw [← Category.comp_id (((conjugateEquiv Adjunction.id
    (Scheme.proEtaleSheafAdjunction (𝟙 X) (Type (u + 1)))).symm
      (lowerStarId (Type (u + 1)) X).inv).app _), transpose_conjugate]
  simp only [continuousSetPullbackMap, Equiv.apply_symm_apply,
    Adjunction.homEquiv_apply, Adjunction.id_unit, NatTrans.id_app, Functor.id_map]
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  rfl

private lemma pullback_composition {X Y Z : Scheme.{u}} (f : Y ⟶ X) (g : Z ⟶ Y)
    (D : Type (u + 1)) [TopologicalSpace D] :
    continuousSetPullbackMap (g ≫ f) D =
      (profinitePointSetComp g f).hom.app (continuousSetSheaf X D) ≫
        (Scheme.proEtaleSheafInverseImage g (Type (u + 1))).map
          (continuousSetPullbackMap f D) ≫ continuousSetPullbackMap g D := by
  apply (Scheme.proEtaleSheafAdjunction (g ≫ f) (Type (u + 1))).homEquiv _ _ |>.injective
  change _ = (Scheme.proEtaleSheafAdjunction (g ≫ f) (Type (u + 1))).homEquiv _ _
    ((((conjugateEquiv
      ((Scheme.proEtaleSheafAdjunction f (Type (u + 1))).comp
        (Scheme.proEtaleSheafAdjunction g (Type (u + 1)))))
      (Scheme.proEtaleSheafAdjunction (g ≫ f) (Type (u + 1)))).symm
        (lowerStarComp (Type (u + 1)) g f).hom).app _ ≫ _)
  rw [transpose_conjugate]
  rw [transpose_comp]
  rw [Adjunction.homEquiv_naturality_left]
  simp only [continuousSetPullbackMap, Equiv.apply_symm_apply]
  rw [Adjunction.homEquiv_naturality_right, Equiv.apply_symm_apply]
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  apply ConcreteCategory.hom_ext
  intro s
  change s.comp (pullback.fst U.unop.hom (g ≫ f)).base.hom =
    ((s.comp (pullback.fst U.unop.hom f).base.hom).comp
      (pullback.fst (pullback.snd U.unop.hom f) g).base.hom).comp
        (((MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) (Q := ⊤) g f).hom.app
          U.unop).left.base.hom)
  apply ContinuousMap.ext
  intro z
  exact congrArg (fun k : _ ⟶ U.unop.left ↦ (show C(U.unop.left, D) from s).toFun (k z))
    (MorphismProperty.Over.pullbackComp_left_fst_fst (P := @WeaklyEtale) (Q := ⊤)
      g f U.unop).symm

private lemma normalized_pullback_aux {X Y : Scheme.{u}} (f : Y ⟶ X)
    (kX : X ⟶ specZ) (kY : Y ⟶ specZ) (w : f ≫ kX = kY)
    (D : Type (u + 1)) [TopologicalSpace D]
    (σX : (Scheme.proEtaleSheafInverseImage kX (Type (u + 1))).obj
      (profinitePointSetInverseImage.obj (continuousSetProfiniteSheaf D)) ⟶
        continuousSetSheaf X D)
    (σY : (Scheme.proEtaleSheafInverseImage kY (Type (u + 1))).obj
      (profinitePointSetInverseImage.obj (continuousSetProfiniteSheaf D)) ⟶
        continuousSetSheaf Y D)
    (hX : ∀ (S : Profinite.{u}) (b : C(S, D)),
      ((((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous profiniteToProEt
        (Type (u + 1)) (coherentTopology Profinite.{u}) (Scheme.ProEt.topology specZ)).comp
        (Scheme.proEtaleSheafAdjunction kX (Type (u + 1)))).homEquiv _ _ σX).hom.app
          (op S)) b = b.comp ((continuousSetTestProjection S).comp
            (pullback.fst (profiniteToProEt.obj S).hom kX).base.hom))
    (hY : ∀ (S : Profinite.{u}) (b : C(S, D)),
      ((((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous profiniteToProEt
        (Type (u + 1)) (coherentTopology Profinite.{u}) (Scheme.ProEt.topology specZ)).comp
        (Scheme.proEtaleSheafAdjunction kY (Type (u + 1)))).homEquiv _ _ σY).hom.app
          (op S)) b = b.comp ((continuousSetTestProjection S).comp
            (pullback.fst (profiniteToProEt.obj S).hom kY).base.hom)) :
    (Scheme.proEtaleSheafInverseImage f (Type (u + 1))).map σX ≫
        continuousSetPullbackMap f D =
      ((profinitePointSetComp f kX).inv.app
        (profinitePointSetInverseImage.obj (continuousSetProfiniteSheaf D)) ≫
        (eqToHom (congrArg (fun k : Y ⟶ specZ ↦
          Scheme.proEtaleSheafInverseImage k (Type (u + 1))) w)).app _) ≫ σY := by
  subst kY
  simp only [eqToHom_refl, NatTrans.id_app, Category.comp_id]
  let adjA := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous profiniteToProEt
    (Type (u + 1)) (coherentTopology Profinite.{u}) (Scheme.ProEt.topology specZ)
  apply (adjA.comp ((Scheme.proEtaleSheafAdjunction kX (Type (u + 1))).comp
    (Scheme.proEtaleSheafAdjunction f (Type (u + 1))))).homEquiv _ _ |>.injective
  rw [transpose_comp]
  conv_lhs => rw [transpose_comp]
  rw [Adjunction.homEquiv_naturality_left]
  simp only [continuousSetPullbackMap, Equiv.apply_symm_apply]
  rw [Adjunction.homEquiv_naturality_right, Adjunction.homEquiv_naturality_right]
  change adjA.homEquiv _ _
    ((Scheme.proEtaleSheafAdjunction kX (Type (u + 1))).homEquiv _ _ σX) ≫ _ =
    adjA.homEquiv _ _ (((Scheme.proEtaleSheafAdjunction kX (Type (u + 1))).comp
      (Scheme.proEtaleSheafAdjunction f (Type (u + 1)))).homEquiv _ _
      ((((conjugateEquiv (Scheme.proEtaleSheafAdjunction (f ≫ kX) (Type (u + 1)))
        ((Scheme.proEtaleSheafAdjunction kX (Type (u + 1))).comp
          (Scheme.proEtaleSheafAdjunction f (Type (u + 1))))).symm
            (lowerStarComp (Type (u + 1)) f kX).inv).app _ ≫ σY)))
  rw [transpose_conjugate, Adjunction.homEquiv_naturality_right]
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext S
  apply ConcreteCategory.hom_ext
  intro b
  change ((((adjA.comp (Scheme.proEtaleSheafAdjunction kX (Type (u + 1)))).homEquiv
    _ _ σX).hom.app S) b).comp
      (pullback.fst (pullback.snd (profiniteToProEt.obj S.unop).hom kX) f).base.hom =
    ((((adjA.comp (Scheme.proEtaleSheafAdjunction (f ≫ kX) (Type (u + 1)))).homEquiv
      _ _ σY).hom.app S) b).comp
        (((MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) (Q := ⊤) f kX).inv.app
          (profiniteToProEt.obj S.unop)).left.base.hom)
  rw [hX S.unop b, hY S.unop b]
  simp only [MorphismProperty.Over.pullbackComp_inv_app_left, pullback.map_id,
    Category.comp_id]
  apply ContinuousMap.ext
  intro z
  exact congrArg (fun k : _ ⟶ (profiniteToProEt.obj S.unop).left ↦
    (show C(S.unop, D) from b).toFun (continuousSetTestProjection S.unop (k z)))
      (pullbackLeftPullbackSndIso_hom_fst
        (profiniteToProEt.obj S.unop).hom kX f).symm

private lemma point_comparison_hom {X Y : Scheme.{u}} (f : Y ⟶ X) :
    (profinitePointSetSchemeComp f).hom =
      (Functor.associator profinitePointSetInverseImage
        (Scheme.proEtaleSheafInverseImage (toSpecZ X) (Type (u + 1)))
        (Scheme.proEtaleSheafInverseImage f (Type (u + 1)))).hom ≫
      Functor.whiskerLeft profinitePointSetInverseImage
        ((profinitePointSetComp f (toSpecZ X)).inv ≫
          eqToHom (congrArg
            (fun k : Y ⟶ specZ ↦ Scheme.proEtaleSheafInverseImage k (Type (u + 1)))
            (comp_toSpecZ f))) := by
  simp only [profinitePointSetSchemeComp, Iso.trans_hom, Functor.isoWhiskerLeft_hom,
    Iso.symm_hom, eqToIso.hom]

private lemma point_comparison_hom_app {X Y : Scheme.{u}} (f : Y ⟶ X)
    (F : Sheaf (coherentTopology Profinite.{u}) (Type (u + 1))) :
    (profinitePointSetSchemeComp f).hom.app F =
      (profinitePointSetComp f (toSpecZ X)).inv.app (profinitePointSetInverseImage.obj F) ≫
        (eqToHom (congrArg (fun k : Y ⟶ specZ ↦
          Scheme.proEtaleSheafInverseImage k (Type (u + 1))) (comp_toSpecZ f))).app
            (profinitePointSetInverseImage.obj F) := by
  have h := congrArg (fun η ↦ η.app F) (point_comparison_hom f)
  simpa only [NatTrans.comp_app, Functor.associator_hom_app, Functor.whiskerLeft_app,
    Category.id_comp] using h

private lemma normalized_pullback {X Y : Scheme.{u}} (f : Y ⟶ X)
    (D : Type (u + 1)) [TopologicalSpace D]
    (σX : (profinitePointSetSchemeInverseImage X).obj (continuousSetProfiniteSheaf D) ⟶
      continuousSetSheaf X D)
    (σY : (profinitePointSetSchemeInverseImage Y).obj (continuousSetProfiniteSheaf D) ⟶
      continuousSetSheaf Y D)
    (hX : IsContinuousSetRealization X D σX) (hY : IsContinuousSetRealization Y D σY) :
    (Scheme.proEtaleSheafInverseImage f (Type (u + 1))).map σX ≫
        continuousSetPullbackMap f D =
      (profinitePointSetSchemeComp f).hom.app (continuousSetProfiniteSheaf D) ≫ σY := by
  rw [point_comparison_hom_app]
  exact normalized_pullback_aux f (toSpecZ X) (toSpecZ Y) (comp_toSpecZ f)
    D σX σY hX hY

/-- Every test-function-normalized family respects coefficient maps, finite products
(including the empty product), and actual scheme inverse image. The scheme comparisons
also obey the inverse-image identity and composition laws.

Source: Hemo--Richarz--Scholbach, Example 3.1 and following paragraph, p. 6
(blueprint: lem-sfb-normalized-continuous-set-comparison-coherence).

Proof:
1. Transpose the coefficient square through `continuousSetPointAdjunction`. The two
normalizations evaluate to the same continuous map by associativity of composition.
2. Construct the product cone of continuous-function presheaves: a tuple of sections
is the continuous map with those coordinates. Reflect this limit through the inclusion
of sheaves into presheaves. This works for every index set, including the empty set.
3. The set point inverse image preserves finite limits by
`profinite_point_pullback_set_coherence`. Apply it to the profinite product cone.
The product equation follows from the coefficient equation at each projection.
4. Transpose the identity comparison using the unit equation for conjugate adjunctions.
Its transpose is restriction along the first projection of the identity pullback,
which is exactly `continuousSetDirectImageMap`.
5. Transpose composition successively through the two scheme adjunctions. The transpose
is the composite of the two restriction maps followed by the direct-image compositor.
The pullback-pasting projection equation identifies this with the composite restriction.
6. For scheme compatibility, first allow arbitrary structure maps kX and kY with
f ≫ kX = kY, and substitute that equality. Transpose through the two scheme adjunctions
and the point adjunction. Conjugation turns the point comparison into the inverse
of the direct-image compositor. Normalization reduces both sides to restriction of
b along the two projection composites. The pullback-pasting equation proves their
equality. Finally specialize to the structure maps to Spec Z. No inverse of sigma,
realization isomorphism, or realization coherence theorem is used. -/
theorem normalized_continuousSetComparison_coherence
    (σ : ∀ (X : Scheme.{u}) (D : Type (u + 1)) [TopologicalSpace D]
      [T2Space D] [TotallyDisconnectedSpace D],
      (profinitePointSetSchemeInverseImage X).obj (continuousSetProfiniteSheaf D) ⟶
        continuousSetSheaf X D)
    (hσ : ∀ (X : Scheme.{u}) (D : Type (u + 1)) [TopologicalSpace D]
      [T2Space D] [TotallyDisconnectedSpace D], IsContinuousSetRealization X D (σ X D)) :
    (∀ (X : Scheme.{u}) (D E : Type (u + 1))
      [TopologicalSpace D] [T2Space D] [TotallyDisconnectedSpace D]
      [TopologicalSpace E] [T2Space E] [TotallyDisconnectedSpace E] (h : C(D, E)),
      σ X D ≫ continuousSetSheafMap X h =
        (profinitePointSetSchemeInverseImage X).map
          (continuousSetProfiniteFunctor.map (TopCat.ofHom h)) ≫ σ X E) ∧
    (∀ (X : Scheme.{u}) (I : Type u) [Finite I] (D : I → Type (u + 1))
      [∀ i : I, TopologicalSpace (D i)] [∀ i : I, T2Space (D i)]
      [∀ i : I, TotallyDisconnectedSpace (D i)],
      IsIso (Pi.lift (fun i : I ↦ continuousSetProfiniteFunctor.map (TopCat.ofHom
        (⟨fun d : ∀ j : I, D j ↦ d i, continuous_apply i⟩)))) ∧
      IsIso (Pi.lift (fun i : I ↦ continuousSetSheafMap X
        (⟨fun d : ∀ j : I, D j ↦ d i, continuous_apply i⟩))) ∧
      IsIso (Pi.lift (fun i : I ↦ (profinitePointSetSchemeInverseImage X).map
        (continuousSetProfiniteFunctor.map (TopCat.ofHom
          (⟨fun d : ∀ j : I, D j ↦ d i, continuous_apply i⟩))))) ∧
      σ X (∀ i : I, D i) ≫ Pi.lift (fun i : I ↦ continuousSetSheafMap X
          (⟨fun d : ∀ j : I, D j ↦ d i, continuous_apply i⟩)) =
        Pi.lift (fun i : I ↦ (profinitePointSetSchemeInverseImage X).map
          (continuousSetProfiniteFunctor.map (TopCat.ofHom
            (⟨fun d : ∀ j : I, D j ↦ d i, continuous_apply i⟩))) ≫ σ X (D i))) ∧
    (∀ (X Y : Scheme.{u}) (f : Y ⟶ X) (D : Type (u + 1))
      [TopologicalSpace D] [T2Space D] [TotallyDisconnectedSpace D],
      (Scheme.proEtaleSheafInverseImage f (Type (u + 1))).map (σ X D) ≫
          continuousSetPullbackMap f D =
        (profinitePointSetSchemeComp f).hom.app (continuousSetProfiniteSheaf D) ≫ σ Y D) ∧
    (∀ (D : Type (u + 1)) [TopologicalSpace D] [T2Space D]
      [TotallyDisconnectedSpace D] (X : Scheme.{u}),
      continuousSetPullbackMap (𝟙 X) D =
        (profinitePointSetIdentity X).hom.app (continuousSetSheaf X D)) ∧
    (∀ (D : Type (u + 1)) [TopologicalSpace D] [T2Space D]
      [TotallyDisconnectedSpace D] (X Y Z : Scheme.{u}) (f : Y ⟶ X) (g : Z ⟶ Y),
      continuousSetPullbackMap (g ≫ f) D =
        (profinitePointSetComp g f).hom.app (continuousSetSheaf X D) ≫
          (Scheme.proEtaleSheafInverseImage g (Type (u + 1))).map
            (continuousSetPullbackMap f D) ≫ continuousSetPullbackMap g D) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro X D E _ _ _ _ _ _ h
    exact normalized_natural X (σ X D) (σ X E) (hσ X D) (hσ X E) h
  · intro X I _ D _ _ _
    have : PreservesFiniteLimits (profinitePointSetSchemeInverseImage X) :=
      profinite_point_pullback_set_coherence.1 X
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact (Fan.nonempty_isLimit_iff_isIso_piLift _).mp ⟨profinite_products I D⟩
    · exact (Fan.nonempty_isLimit_iff_isIso_piLift _).mp ⟨scheme_products X I D⟩
    · exact (Fan.nonempty_isLimit_iff_isIso_piLift _).mp
        ⟨isLimitFanMkObjOfIsLimit (profinitePointSetSchemeInverseImage X) _ _
          (profinite_products I D)⟩
    · apply Pi.hom_ext
      intro i
      simp only [Category.assoc, Pi.lift_π]
      exact normalized_natural X (σ X (∀ i, D i)) (σ X (D i))
        (hσ X (∀ i, D i)) (hσ X (D i)) _
  · intro X Y f D _ _ _
    exact normalized_pullback f D (σ X D) (σ Y D) (hσ X D) (hσ Y D)
  · intro D _ _ _ X
    exact pullback_identity X D
  · intro D _ _ _ X Y Z f g
    exact pullback_composition f g D

end AlgebraicGeometry.ProEtale
