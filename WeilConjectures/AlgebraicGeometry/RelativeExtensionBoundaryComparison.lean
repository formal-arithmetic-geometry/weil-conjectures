/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Relative.RelativeExtensionCohomologyNormalization
import all WeilConjectures.AlgebraicGeometry.Relative.RelativeExtensionCohomologyNormalization
import all WeilConjectures.AlgebraicGeometry.RelativeCone.PurityRelativeCone
import all WeilConjectures.Algebra.Homology.KernelShiftedMappingCone
import WeilConjectures.CategoryTheory.Abelian.ExtResolutionDerivedConnecting
import Mathlib.Algebra.Homology.ConcreteCategory

/-! # Relative supported Ext and coefficient boundaries

Source: Stacks Project, Tags 05TE and 06XR; the connecting-map paragraph of
blueprint lem-amb-cartier-kummer-map.
(blueprint: lem-pur-relative-extension-boundary-comparison)
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite HomologicalComplex

namespace AlgebraicGeometry.Etale

private local instance additiveSelfForget :
    HasForget₂ AddCommGrpCat.{u + 1} AddCommGrpCat.{u + 1} := ⟨𝟭 _, rfl⟩

private local instance additiveSelfForget_additive :
    (forget₂ AddCommGrpCat.{u + 1} AddCommGrpCat.{u + 1}).Additive :=
  inferInstanceAs (𝟭 AddCommGrpCat.{u + 1}).Additive

private local instance additiveSelfForget_homology :
    (forget₂ AddCommGrpCat.{u + 1} AddCommGrpCat.{u + 1}).PreservesHomology :=
  inferInstanceAs (𝟭 AddCommGrpCat.{u + 1}).PreservesHomology

variable {D T : Scheme.{u}} (i : D ⟶ T) [IsClosedImmersion i]

private abbrev supportedHomFunctor :=
  preadditiveCoyoneda.obj (op ((lowerStar AddCommGrpCat.{u + 1} i).obj
    (supportedIntegralConstant D)))

private def supportedHomEvaluation :
    supportedHomFunctor i ⟶ etaleSectionFunctor (Scheme.Etale.mk (𝟙 T)) where
  app F := AddCommGrpCat.ofHom
    { toFun k := integerSectionEquiv T F (supportedIntegralUnit i ≫ k)
      map_zero' := by simp
      map_add' k l := by
        change integerSectionEquiv T F (supportedIntegralUnit i ≫ (k + l)) = _
        rw [Preadditive.comp_add, map_add] }
  naturality F F' f := by
    ext k
    simp only [integerSectionEquiv_eval]
    rfl

private theorem supportedHomEvaluation_zero
    (F : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    (supportedHomEvaluation i).app F ≫ F.obj.map
      ((MorphismProperty.Over.mkIdTerminal @Etale T).from
        (Scheme.Etale.mk i.openComplement.ι)).op = 0 := by
  obtain ⟨e, he⟩ := integralSupportedHomIso i
  have h (k) : (supportedHomEvaluation i).app F k =
      kernel.ι (F.obj.map ((MorphismProperty.Over.mkIdTerminal @Etale T).from
        (Scheme.Etale.mk i.openComplement.ι)).op) (e.hom.app F k) := (he F k).symm
  ext k
  change F.obj.map _ ((supportedHomEvaluation i).app F k) = 0
  rw [h]
  exact ConcreteCategory.congr_hom (kernel.condition _) (e.hom.app F k)

private abbrev supportedHomComplex
    (C : CochainComplex (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) ℕ) :=
  (((supportedHomFunctor i).mapHomologicalComplex (.up ℕ)).obj C).extend
    ComplexShape.embeddingUpNat

private def supportedHomEvaluationComplex
    (C : CochainComplex (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) ℕ) :
    supportedHomComplex i C ⟶ relativeSections (Scheme.Etale.mk (𝟙 T)) C :=
  extendMap ((NatTrans.mapHomologicalComplex (supportedHomEvaluation i) _).app C)
    ComplexShape.embeddingUpNat

private theorem supportedHomEvaluationComplex_zero
    (C : CochainComplex (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) ℕ) :
    supportedHomEvaluationComplex i C ≫
      relativeSectionRestriction T (Scheme.Etale.mk i.openComplement.ι) C = 0 := by
  unfold supportedHomEvaluationComplex relativeSectionRestriction
  rw [← extendMap_comp]
  have h : (NatTrans.mapHomologicalComplex (supportedHomEvaluation i) _).app C ≫
      etaleSectionMap ((MorphismProperty.Over.mkIdTerminal @Etale T).from
        (Scheme.Etale.mk i.openComplement.ι)) C = 0 := by
    ext n : 1
    exact supportedHomEvaluation_zero i (C.X n)
  rw [h, extendMap_zero]

private def supportedHomConeMap
    (C : CochainComplex (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) ℕ) :
    supportedHomComplex i C ⟶
      relativeSectionComplex T (Scheme.Etale.mk i.openComplement.ι) C :=
  kernel.lift _ (supportedHomEvaluationComplex i C)
      (supportedHomEvaluationComplex_zero i C) ≫
    CochainComplex.comparison (relativeSectionRestriction T
      (Scheme.Etale.mk i.openComplement.ι) C)

private theorem supportedHomConeMap_fst
    (C : CochainComplex (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) ℕ)
    (p : ℤ) :
    (supportedHomConeMap i C).f p ≫
      (relativeForgetComplex T (Scheme.Etale.mk i.openComplement.ι) C).f p =
        (supportedHomEvaluationComplex i C).f p := by
  have h := (CochainComplex.comparison_projections
    (relativeSectionRestriction T (Scheme.Etale.mk i.openComplement.ι) C)
      p (p - 1) (by omega)).2
  unfold supportedHomConeMap
  change ((kernel.lift _ (supportedHomEvaluationComplex i C)
    (supportedHomEvaluationComplex_zero i C)).f p ≫
      (CochainComplex.comparison (relativeSectionRestriction T
        (Scheme.Etale.mk i.openComplement.ι) C)).f p) ≫
      (RelativeCone.projection (relativeSectionRestriction T
        (Scheme.Etale.mk i.openComplement.ι) C)).f p = _
  rw [Category.assoc, RelativeCone.projection_f, h]
  simpa only [comp_f] using congrArg (fun t ↦ t.f p)
    (kernel.lift_ι _ (supportedHomEvaluationComplex i C)
      (supportedHomEvaluationComplex_zero i C))

private theorem supportedHomConeMap_snd
    (C : CochainComplex (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) ℕ)
    (p : ℤ) :
    (supportedHomConeMap i C).f p ≫
      ((CochainComplex.mappingCone (relativeSectionRestriction T
        (Scheme.Etale.mk i.openComplement.ι) C)).shiftFunctorObjXIso
          (-1) p (p - 1) (by omega)).hom ≫
      homotopyCofiber.sndX (relativeSectionRestriction T
        (Scheme.Etale.mk i.openComplement.ι) C) (p - 1) = 0 := by
  have h := (CochainComplex.comparison_projections
    (relativeSectionRestriction T (Scheme.Etale.mk i.openComplement.ι) C)
      p (p - 1) (by omega)).1
  simp only [supportedHomConeMap, comp_f, Category.assoc, h, comp_zero]

private theorem supportedHomConeMap_natural
    {C C' : CochainComplex (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) ℕ}
    (f : C ⟶ C') :
    extendMap (((supportedHomFunctor i).mapHomologicalComplex (.up ℕ)).map f)
        ComplexShape.embeddingUpNat ≫ supportedHomConeMap i C' =
      supportedHomConeMap i C ≫
        relativeSectionMap T (Scheme.Etale.mk i.openComplement.ι) f := by
  ext p : 1
  apply (cancel_mono ((CochainComplex.mappingCone
    (relativeSectionRestriction T (Scheme.Etale.mk i.openComplement.ι) C')).shiftFunctorObjXIso
      (-1) p (p - 1) (by omega)).hom).1
  apply homotopyCofiber.ext_to_X
    (relativeSectionRestriction T (Scheme.Etale.mk i.openComplement.ι) C') (p - 1) p
      (by change p - 1 + 1 = p; omega)
  · have hfst (A) := supportedHomConeMap_fst i A p
    change ∀ A, (supportedHomConeMap i A).f p ≫
      (RelativeCone.projection (relativeSectionRestriction T
        (Scheme.Etale.mk i.openComplement.ι) A)).f p = _ at hfst
    simp only [cone_projection_f] at hfst
    simp only [comp_f, Category.assoc, relativeSectionMap, RelativeCone.fiberMap_fst]
    erw [hfst, reassoc_of% (hfst C)]
    have hn := (NatTrans.mapHomologicalComplex (supportedHomEvaluation i) (.up ℕ)).naturality f
    have h := congrArg (fun t ↦ (extendMap t ComplexShape.embeddingUpNat).f p) hn
    simpa only [supportedHomEvaluationComplex, extendMap_comp, comp_f] using h
  · simp only [comp_f, Category.assoc, relativeSectionMap, RelativeCone.fiberMap_snd]
    erw [supportedHomConeMap_snd, comp_zero,
      reassoc_of% (supportedHomConeMap_snd i C p), zero_comp]

private def supportedHomConeElement
    (C : CochainComplex (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) ℕ)
    (q : ℕ)
    (k : (lowerStar AddCommGrpCat.{u + 1} i).obj (supportedIntegralConstant D) ⟶ C.X q) :
    (relativeSectionComplex T (Scheme.Etale.mk i.openComplement.ι) C).X (q : ℤ) :=
  (supportedHomConeMap i C).f q
    (((((supportedHomFunctor i).mapHomologicalComplex (.up ℕ)).obj C).extendXIso
      ComplexShape.embeddingUpNat (rfl : ComplexShape.embeddingUpNat.f q = (q : ℤ))).inv k)

private theorem supportedHomConeElement_zero
    (C : CochainComplex (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) ℕ)
    (q : ℕ) : supportedHomConeElement i C q 0 = 0 := by
  simp only [supportedHomConeElement, map_zero]

private theorem supportedHomConeElement_natural
    {C C' : CochainComplex (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) ℕ}
    (f : C ⟶ C') (q : ℕ)
    (k : (lowerStar AddCommGrpCat.{u + 1} i).obj (supportedIntegralConstant D) ⟶ C.X q) :
    (relativeSectionMap T (Scheme.Etale.mk i.openComplement.ι) f).f q
        (supportedHomConeElement i C q k) =
      supportedHomConeElement i C' q (k ≫ f.f q) := by
  have h := ConcreteCategory.congr_hom
    (congrArg (fun t ↦ t.f (q : ℤ)) (supportedHomConeMap_natural i f))
      (((((supportedHomFunctor i).mapHomologicalComplex (.up ℕ)).obj C).extendXIso
        ComplexShape.embeddingUpNat (rfl : ComplexShape.embeddingUpNat.f q = (q : ℤ))).inv k)
  simp only [comp_f, ConcreteCategory.comp_apply] at h
  erw [extendMap_f _ _ (rfl : ComplexShape.embeddingUpNat.f q = (q : ℤ))] at h
  simp only [ConcreteCategory.comp_apply] at h
  erw [Iso.inv_hom_id_apply] at h
  exact h.symm

private theorem supportedHomConeElement_d
    (C : CochainComplex (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) ℕ)
    (q : ℕ)
    (k : (lowerStar AddCommGrpCat.{u + 1} i).obj (supportedIntegralConstant D) ⟶ C.X q) :
    (relativeSectionComplex T (Scheme.Etale.mk i.openComplement.ι) C).d
        (q : ℤ) ((q + 1 : ℕ) : ℤ) (supportedHomConeElement i C q k) =
      supportedHomConeElement i C (q + 1) (k ≫ C.d q (q + 1)) := by
  have h := ConcreteCategory.congr_hom
    ((supportedHomConeMap i C).comm (q : ℤ) ((q + 1 : ℕ) : ℤ))
      (((((supportedHomFunctor i).mapHomologicalComplex (.up ℕ)).obj C).extendXIso
        ComplexShape.embeddingUpNat (rfl : ComplexShape.embeddingUpNat.f q = (q : ℤ))).inv k)
  simp only [ConcreteCategory.comp_apply] at h
  erw [extend_d_eq _ _ (rfl : ComplexShape.embeddingUpNat.f q = (q : ℤ))
    (rfl : ComplexShape.embeddingUpNat.f (q + 1) = ((q + 1 : ℕ) : ℤ))] at h
  simp only [ConcreteCategory.comp_apply] at h
  erw [Iso.inv_hom_id_apply] at h
  exact h

private theorem supportedHomConeElement_closed
    (C : CochainComplex (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) ℕ)
    (q : ℕ)
    (k : (lowerStar AddCommGrpCat.{u + 1} i).obj (supportedIntegralConstant D) ⟶ C.X q)
    (hk : k ≫ C.d q (q + 1) = 0) :
    (relativeSectionComplex T (Scheme.Etale.mk i.openComplement.ι) C).d
        (q : ℤ) ((q + 1 : ℕ) : ℤ) (supportedHomConeElement i C q k) = 0 := by
  rw [supportedHomConeElement_d, hk, supportedHomConeElement_zero]

private def supportedHomConeCycle
    (C : CochainComplex (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) ℕ)
    (q : ℕ)
    (k : (lowerStar AddCommGrpCat.{u + 1} i).obj (supportedIntegralConstant D) ⟶ C.X q)
    (hk : k ≫ C.d q (q + 1) = 0) :
    (relativeSectionComplex T (Scheme.Etale.mk i.openComplement.ι) C).cycles (q : ℤ) :=
  (relativeSectionComplex T (Scheme.Etale.mk i.openComplement.ι) C).cyclesMk
    (supportedHomConeElement i C q k) ((q + 1 : ℕ) : ℤ) (by simp)
      (supportedHomConeElement_closed i C q k hk)

private theorem supportedHomConeCycle_i
    (C : CochainComplex (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) ℕ)
    (q : ℕ)
    (k : (lowerStar AddCommGrpCat.{u + 1} i).obj (supportedIntegralConstant D) ⟶ C.X q)
    (hk : k ≫ C.d q (q + 1) = 0) :
    (relativeSectionComplex T (Scheme.Etale.mk i.openComplement.ι) C).iCycles q
        (supportedHomConeCycle i C q k hk) = supportedHomConeElement i C q k :=
  HomologicalComplex.i_cyclesMk.{u + 1, u + 2}
    (relativeSectionComplex T (Scheme.Etale.mk i.openComplement.ι) C) _ _ _ _

private theorem relativeExtensionComparison_on_cycle
    (G : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) (I : InjectiveResolution G)
    (q : ℕ)
    (k : (lowerStar AddCommGrpCat.{u + 1} i).obj (supportedIntegralConstant D) ⟶
      I.cocomplex.X q) (hk : k ≫ I.cocomplex.d q (q + 1) = 0) :
    relativeExtensionComparison i G I q (I.extMk k (q + 1) rfl hk) =
      (relativeSectionComplex T (Scheme.Etale.mk i.openComplement.ι)
        I.cocomplex).homologyπ q (supportedHomConeCycle i I.cocomplex q k hk) := by
  apply (Classical.choose_spec (relativeExtensionComparison_existsUnique i G I)).1.onCocycle
  · rw [supportedHomConeCycle_i]
    unfold supportedHomConeElement
    rw [← ConcreteCategory.comp_apply]
    erw [supportedHomConeMap_fst]
    unfold supportedHomEvaluationComplex
    erw [extendMap_f _ _ (rfl : ComplexShape.embeddingUpNat.f q = (q : ℤ))]
    simp only [ConcreteCategory.comp_apply]
    erw [Iso.inv_hom_id_apply]
    congr 1
  · rw [supportedHomConeCycle_i]
    have h := (CochainComplex.comparison_projections
      (relativeSectionRestriction T (Scheme.Etale.mk i.openComplement.ι) I.cocomplex)
        (q : ℤ) ((q : ℤ) + -1) rfl).1
    have hz : (supportedHomConeMap i I.cocomplex).f q ≫
        ((CochainComplex.mappingCone (relativeSectionRestriction T
          (Scheme.Etale.mk i.openComplement.ι) I.cocomplex)).shiftFunctorObjXIso
            (-1) (q : ℤ) ((q : ℤ) + -1) rfl).hom ≫
        homotopyCofiber.sndX (relativeSectionRestriction T
          (Scheme.Etale.mk i.openComplement.ι) I.cocomplex) ((q : ℤ) + -1) = 0 := by
      simp only [supportedHomConeMap, comp_f, Category.assoc, h, comp_zero]
    have he := ConcreteCategory.congr_hom hz
      (((((supportedHomFunctor i).mapHomologicalComplex (.up ℕ)).obj I.cocomplex).extendXIso
        ComplexShape.embeddingUpNat (rfl : ComplexShape.embeddingUpNat.f q = (q : ℤ))).inv k)
    simp only [ConcreteCategory.comp_apply, supportedHomConeElement,
      AddCommGrpCat.hom_zero, AddMonoidHom.zero_apply] at he ⊢
    convert he using 1
    congr! 10

private theorem relativeExtensionComparison_coefficient
    {G G' : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (g : G ⟶ G') (I : InjectiveResolution G) (J : InjectiveResolution G')
    (f : I.Hom J g) (q : ℕ)
    (x : Ext ((lowerStar AddCommGrpCat.{u + 1} i).obj
      (supportedIntegralConstant D)) G q) :
    relativeExtensionComparison i G' J q (x.comp (Ext.mk₀ g) (add_zero q)) =
      homologyMap (relativeSectionMap T (Scheme.Etale.mk i.openComplement.ι) f.hom) q
        (relativeExtensionComparison i G I q x) := by
  obtain ⟨k, hk, rfl⟩ := I.extMk_surjective x (q + 1) rfl
  rw [InjectiveResolution.extMk_comp_mk₀ k (q + 1) rfl hk f,
    relativeExtensionComparison_on_cycle, relativeExtensionComparison_on_cycle]
  rw [← ConcreteCategory.comp_apply, homologyπ_naturality,
    ConcreteCategory.comp_apply]
  congr 1
  apply (AddCommGrpCat.mono_iff_injective
    ((relativeSectionComplex T (Scheme.Etale.mk i.openComplement.ι)
      J.cocomplex).iCycles q)).mp inferInstance
  rw [← ConcreteCategory.comp_apply, cyclesMap_i, ConcreteCategory.comp_apply,
    supportedHomConeCycle_i, supportedHomConeCycle_i,
    supportedHomConeElement_natural]

omit [IsClosedImmersion i] in
private theorem ext_boundary_cocycle
    {S : ShortComplex (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})}
    (hS : S.ShortExact)
    (I : InjectiveResolution S.X₁) (J : InjectiveResolution S.X₂)
    (K : InjectiveResolution S.X₃)
    (a : I.cocomplex ⟶ J.cocomplex) (b : J.cocomplex ⟶ K.cocomplex)
    (hab : a ≫ b = 0)
    (ha : I.ι ≫ a = (CochainComplex.single₀ _).map S.f ≫ J.ι)
    (hb : J.ι ≫ b = (CochainComplex.single₀ _).map S.g ≫ K.ι)
    (hs : ∀ k : ℕ, ((ShortComplex.mk a b hab).map
      (HomologicalComplex.eval _ (.up ℕ) k)).ShortExact)
    (q : ℕ)
    (c : (lowerStar AddCommGrpCat.{u + 1} i).obj (supportedIntegralConstant D) ⟶
      K.cocomplex.X q) (hc : c ≫ K.cocomplex.d q (q + 1) = 0)
    (v : (lowerStar AddCommGrpCat.{u + 1} i).obj (supportedIntegralConstant D) ⟶
      J.cocomplex.X q) (hv : v ≫ b.f q = c)
    (w : (lowerStar AddCommGrpCat.{u + 1} i).obj (supportedIntegralConstant D) ⟶
      I.cocomplex.X (q + 1))
    (hw : w ≫ I.cocomplex.d (q + 1) (q + 1 + 1) = 0)
    (hvw : v ≫ J.cocomplex.d q (q + 1) = w ≫ a.f (q + 1)) :
    (K.extMk c (q + 1) rfl hc).comp hS.extClass rfl =
      I.extMk w (q + 1 + 1) rfl hw := by
  let C := Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}
  let := HasDerivedCategory.standard C
  have : HasExt.{u + 2} C := HasExt.standard C
  have h := InjectiveResolution.extMk_resolution_connecting_eq_triangle hS
    ((lowerStar AddCommGrpCat.{u + 1} i).obj (supportedIntegralConstant D))
      I J K a b hab ha hb hs q c hc v hv w hw hvw
  rw [Ext.preadditiveCoyoneda_homologySequenceδ_singleTriangle_apply hS _ rfl] at h
  apply Ext.ext
  simpa only [Ext.comp_hom, ShortComplex.ShortExact.extClass_hom,
    InjectiveResolution.extMk_hom] using h

private theorem relativeExtensionComparison_connecting
    {S : ShortComplex (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})}
    (hS : S.ShortExact)
    (I : InjectiveResolution S.X₁) (J : InjectiveResolution S.X₂)
    (K : InjectiveResolution S.X₃)
    (a : I.cocomplex ⟶ J.cocomplex) (b : J.cocomplex ⟶ K.cocomplex)
    (hab : a ≫ b = 0)
    (ha : I.ι ≫ a = (CochainComplex.single₀ _).map S.f ≫ J.ι)
    (hb : J.ι ≫ b = (CochainComplex.single₀ _).map S.g ≫ K.ι)
    (hs : ∀ k : ℕ, Nonempty (((ShortComplex.mk a b hab).map
      (HomologicalComplex.eval _ (.up ℕ) k)).Splitting))
    (q : ℕ)
    (x : Ext ((lowerStar AddCommGrpCat.{u + 1} i).obj
      (supportedIntegralConstant D)) S.X₃ q) :
    relativeExtensionComparison i S.X₁ I (q + 1) (x.comp hS.extClass rfl) =
      relativeConnecting T (Scheme.Etale.mk i.openComplement.ι)
        (ShortComplex.mk a b hab) hs q (relativeExtensionComparison i S.X₃ K q x) := by
  classical
  obtain ⟨c, hc, rfl⟩ := K.extMk_surjective x (q + 1) rfl
  let σ (k : ℕ) := (hs k).some
  have hrows (k : ℕ) := (σ k).shortExact
  let v := c ≫ (σ q).s
  have hv : v ≫ b.f q = c := by
    have hsplit : (σ q).s ≫ b.f q = 𝟙 (K.cocomplex.X q) := (σ q).s_g
    dsimp only [v]
    rw [Category.assoc, hsplit, Category.comp_id]
  have hdv : (v ≫ J.cocomplex.d q (q + 1)) ≫ b.f (q + 1) = 0 := by
    rw [Category.assoc, ← b.comm, ← Category.assoc, hv, hc]
  have : Mono (((ShortComplex.mk a b hab).map
    (HomologicalComplex.eval _ (.up ℕ) (q + 1))).f) := (hrows (q + 1)).mono_f
  let w := (hrows (q + 1)).exact.lift (v ≫ J.cocomplex.d q (q + 1)) hdv
  have hwv : w ≫ a.f (q + 1) = v ≫ J.cocomplex.d q (q + 1) :=
    (hrows (q + 1)).exact.lift_f _ hdv
  have hw : w ≫ I.cocomplex.d (q + 1) (q + 1 + 1) = 0 := by
    have : Mono (a.f (q + 1 + 1)) := (hrows (q + 1 + 1)).mono_f
    rw [← cancel_mono (a.f (q + 1 + 1)), Category.assoc, ← a.comm,
      ← Category.assoc, hwv, Category.assoc, HomologicalComplex.d_comp_d,
      comp_zero, zero_comp]
  rw [ext_boundary_cocycle i hS I J K a b hab ha hb hrows q c hc v hv w hw hwv.symm,
    relativeExtensionComparison_on_cycle, relativeExtensionComparison_on_cycle]
  have hxv : (relativeSectionMap T (Scheme.Etale.mk i.openComplement.ι) b).f q
      (supportedHomConeElement i J.cocomplex q v) =
        supportedHomConeElement i K.cocomplex q c := by
    rw [supportedHomConeElement_natural, hv]
  have hxw : (relativeSectionMap T (Scheme.Etale.mk i.openComplement.ι) a).f
      ((q + 1 : ℕ) : ℤ) (supportedHomConeElement i I.cocomplex (q + 1) w) =
        (relativeSectionComplex T (Scheme.Etale.mk i.openComplement.ι) J.cocomplex).d
          (q : ℤ) ((q + 1 : ℕ) : ℤ) (supportedHomConeElement i J.cocomplex q v) := by
    rw [supportedHomConeElement_natural, supportedHomConeElement_d, hwv]
  have hδ := (relativeShortComplex_shortExact T (Scheme.Etale.mk i.openComplement.ι)
    (ShortComplex.mk a b hab) hs).δ_apply.{u + 1, u + 2}
      (q : ℤ) ((q + 1 : ℕ) : ℤ) (by simp)
      (supportedHomConeElement i K.cocomplex q c)
      (supportedHomConeElement_closed i K.cocomplex q c hc)
      (supportedHomConeElement i J.cocomplex q v) hxv
      (supportedHomConeElement i I.cocomplex (q + 1) w) hxw
      ((q + 1 + 1 : ℕ) : ℤ) (by simp)
  exact hδ.symm

/-- The normalized integral support comparison carries a Yoneda coefficient boundary,
followed by a coefficient morphism, to the positive signed relative connecting map
followed by that coefficient morphism. All horseshoe resolutions and lifts are arbitrary.
Source: Stacks Project, Tags 05TE and 06XR; blueprint lem-amb-cartier-kummer-map,
connecting-map paragraph.
(blueprint: lem-pur-relative-extension-boundary-comparison).

Proof: evaluate Hom from the integral closed constant sheaf at supported one and insert
it into the shifted cone with zero open coordinate. This is a chain map, natural for
all morphisms of sheaf complexes. Its image on each cocycle is the specified normalized
comparison. Represent x by a resolution cocycle c, lift it to v in the middle row using
the degreewise splitting, and factor dv through the first row as w. The next differential
of w is zero by monicity. The resolution Ext boundary formula sends c to w with a plus
sign. The concrete homology boundary formula for the relative short exact sequence
sends the evaluated cone cycle of c to that of w. Finally coefficient naturality follows
by applying the same chain map to a lift of the coefficient morphism. -/
theorem relativeExtensionBoundaryComparison
    {S : ShortComplex (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})}
    (hS : S.ShortExact)
    (I : InjectiveResolution S.X₁) (J : InjectiveResolution S.X₂)
    (K : InjectiveResolution S.X₃)
    (a : I.cocomplex ⟶ J.cocomplex) (b : J.cocomplex ⟶ K.cocomplex)
    (hab : a ≫ b = 0)
    (ha : I.ι ≫ a = (CochainComplex.single₀ _).map S.f ≫ J.ι)
    (hb : J.ι ≫ b = (CochainComplex.single₀ _).map S.g ≫ K.ι)
    (hs : ∀ k : ℕ, Nonempty (((ShortComplex.mk a b hab).map
      (HomologicalComplex.eval _ (.up ℕ) k)).Splitting))
    {G : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}} (g : S.X₁ ⟶ G)
    (M : InjectiveResolution G) (f : I.Hom M g) (q : ℕ)
    (x : Ext ((lowerStar AddCommGrpCat.{u + 1} i).obj
      (supportedIntegralConstant D)) S.X₃ q) :
    relativeExtensionComparison i G M (q + 1)
        ((x.comp hS.extClass rfl).comp (Ext.mk₀ g) (add_zero (q + 1))) =
      homologyMap (relativeSectionMap T (Scheme.Etale.mk i.openComplement.ι) f.hom)
        ((q + 1 : ℕ) : ℤ)
        (relativeConnecting T (Scheme.Etale.mk i.openComplement.ι)
          (ShortComplex.mk a b hab) hs q (relativeExtensionComparison i S.X₃ K q x)) := by
  rw [relativeExtensionComparison_coefficient,
    relativeExtensionComparison_connecting i hS I J K a b hab ha hb hs]

end AlgebraicGeometry.Etale
