module
public import WeilConjectures.AlgebraicGeometry.FiniteSplitEtaleHypercover
import Sheaf.AlgebraicGeometry.FiniteCoproductLfpQcqs
import Mathlib.AlgebraicGeometry.LimitsOver
import WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit
import Sheaf.Paper.EtaleFiniteDataDescent
@[expose] public section
universe w
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry
private theorem pullbackComp_inv_fst {X Y Z : Scheme.{w}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (W : Over Z) :
    ((Over.pullbackComp f g).inv.app W).left ≫ pullback.fst W.hom (f ≫ g) =
      pullback.fst (pullback.snd W.hom g) f ≫ pullback.fst W.hom g := by
  have H := conjugateEquiv_counit ((Over.mapPullbackAdj f).comp (Over.mapPullbackAdj g))
    (Over.mapPullbackAdj (f ≫ g)) (Over.mapComp f g).hom W
  simpa [Over.pullbackComp, Adjunction.comp_counit_app] using
    congrArg (fun k ↦ k.left) H

private theorem comparison_fst {X Y Z : Scheme.{w}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (k : X ⟶ Z) (h : f ≫ g = k) (W : Over Z) :
    ((((Over.pullbackComp f g).symm ≪≫
      eqToIso (congrArg (fun t : X ⟶ Z ↦ Over.pullback t) h)).app W).hom).left ≫
        pullback.fst W.hom k =
      pullback.fst (pullback.snd W.hom g) f ≫ pullback.fst W.hom g := by
  subst k
  simpa using pullbackComp_inv_fst f g W

private theorem finite_etale_cofan_qcqs
    {X : Scheme.{w}} {A : Type*} [Finite A] (V : A → X.Etale)
    (W : X.Etale) (ι : ∀ a, V a ⟶ W) (h : IsColimit (Cofan.mk W ι))
    (hV : ∀ a, CompactSpace (V a).left ∧ QuasiSeparatedSpace (V a).left) :
    CompactSpace W.left ∧ QuasiSeparatedSpace W.left := by
  let F := Scheme.Etale.forget X ⋙ Over.forget X
  have : Small.{w} A := inferInstance
  have : IsZariskiLocalAtSource @Etale := inferInstance
  have : CreatesColimitsOfShape (Discrete A)
      (MorphismProperty.Over.forget @Etale ⊤ X) := inferInstance
  have : PreservesColimitsOfShape (Discrete A) (Scheme.Etale.forget X) := by
    unfold Scheme.Etale.forget
    infer_instance
  have : PreservesColimit (Discrete.functor V) F := by
    dsimp [F]
    infer_instance
  have h' := isColimitCofanMkObjOfIsColimit F V ι h
  let e : W.left ≅ ∐ (fun a ↦ (V a).left) :=
    h'.coconePointUniqueUpToIso (coproductIsCoproduct _)
  obtain ⟨hc, hs, _⟩ := finite_coproduct_lfp_qcqs (fun a ↦ (V a).left) X
    (fun a ↦ (V a).hom)
  have : CompactSpace ↥(∐ (fun a ↦ (V a).left)) := hc (fun a ↦ (hV a).1)
  have : QuasiSeparatedSpace ↥(∐ (fun a ↦ (V a).left)) := hs (fun a ↦ (hV a).2)
  let he := TopCat.homeoOfIso (Scheme.forgetToTop.mapIso e).symm
  exact ⟨@Homeomorph.compactSpace _ _ _ _ ‹_› he,
    (quasiSeparatedSpace_congr he).mp ‹_›⟩

private theorem truncated_terms_qcqs {X : Scheme.{w}} {r : ℕ}
    (U : TruncatedFiniteSplitEtaleHypercover X r)
    (Δ : (SimplexCategory.Truncated r)ᵒᵖ) :
    CompactSpace (U.simplicial.obj Δ).left ∧
      QuasiSeparatedSpace (U.simplicial.obj Δ).left := by
  have hN (n : Fin (r + 1)) :
      CompactSpace (U.N n).left ∧ QuasiSeparatedSpace (U.N n).left := by
    obtain ⟨k, V, ι, ⟨hι⟩, hV⟩ := U.finite_each_degree n
    exact finite_etale_cofan_qcqs V (U.N n) ι hι (fun a ↦ ⟨(hV a).1, (hV a).2.1⟩)
  let A := Σ m : Fin (r + 1),
    {α : Δ.unop.obj ⟶ SimplexCategory.mk m.val // Epi α}
  exact finite_etale_cofan_qcqs (fun a : A ↦ U.N a.1) (U.simplicial.obj Δ)
    _ (U.splitting Δ) (fun a ↦ hN a.1)

private theorem truncated_finite (r : ℕ) : Finite (SimplexCategory.Truncated r) := by
  apply Finite.of_injective
    (fun Δ : SimplexCategory.Truncated r ↦
      (⟨Δ.obj.len, Nat.lt_succ_of_le Δ.property⟩ : Fin (r + 1)))
  intro a b hab
  apply ObjectProperty.FullSubcategory.ext
  exact SimplexCategory.ext (congrArg Fin.val hab)

private theorem truncated_terms_finitePresentation
    {X : Scheme.{w}} [QuasiSeparatedSpace X] {r : ℕ}
    (U : TruncatedFiniteSplitEtaleHypercover X r)
    (Δ : (SimplexCategory.Truncated r)ᵒᵖ) :
    LocallyOfFinitePresentation (U.diagram.obj Δ).hom ∧
      QuasiCompact (U.diagram.obj Δ).hom ∧ QuasiSeparated (U.diagram.obj Δ).hom := by
  obtain ⟨hcU, hsU⟩ := truncated_terms_qcqs U Δ
  dsimp [TruncatedFiniteSplitEtaleHypercover.diagram]
  exact ⟨inferInstance, inferInstance, inferInstance⟩

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem finite_morphism_equalities_lift
    {I : Type w} [SmallCategory I] [IsFiltered I]
    (D : Iᵒᵖ ⥤ Scheme.{w})
    [∀ {i j : Iᵒᵖ} (f : i ⟶ j), IsAffineHom (D.map f)]
    [∀ i : Iᵒᵖ, CompactSpace (D.obj i)]
    [∀ i : Iᵒᵖ, QuasiSeparatedSpace (D.obj i)]
    (c : Cone D) (hc : IsLimit c)
    (R : Type*) [Finite R] (i : Iᵒᵖ) (V W : R → Over (D.obj i))
    (hV : ∀ r, LocallyOfFinitePresentation (V r).hom ∧
      QuasiCompact (V r).hom ∧ QuasiSeparated (V r).hom)
    (hW : ∀ r, LocallyOfFinitePresentation (W r).hom ∧
      QuasiCompact (W r).hom ∧ QuasiSeparated (W r).hom)
    (x y : ∀ r, V r ⟶ W r)
    (hxy : ∀ r, (Over.pullback (c.π.app i)).map (x r) =
      (Over.pullback (c.π.app i)).map (y r)) :
    ∃ (j : Iᵒᵖ) (h : j ⟶ i), ∀ r,
      (Over.pullback (D.map h)).map (x r) =
        (Over.pullback (D.map h)).map (y r) := by
  classical
  have hex : ∀ r, ∃ (j : Iᵒᵖ) (h : j ⟶ i),
      (Over.pullback (D.map h)).map (x r) =
        (Over.pullback (D.map h)).map (y r) := by
    intro r
    have := (hV r).1
    have := (hV r).2.1
    have := (hV r).2.2
    have := (hW r).1
    have := (hW r).2.1
    have := (hW r).2.2
    have hfst : pullback.fst (V r).hom (c.π.app i) ≫ (x r).left =
        pullback.fst (V r).hom (c.π.app i) ≫ (y r).left := by
      have hh := congrArg
        (fun f ↦ f.left ≫ pullback.fst (W r).hom (c.π.app i)) (hxy r)
      simpa using hh
    obtain ⟨j, h, hh⟩ := Scheme.exists_pullback_fst_comp_eq_of_isLimit
      hc (V r).hom (W r).hom (x r).left (y r).left
      (Over.w (x r)) (Over.w (y r)) hfst
    refine ⟨j, h, ?_⟩
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · simpa using hh
    · simp
  choose js fs hfs using hex
  obtain ⟨j, h, g, hg⟩ := IsCofiltered.wideCospan fs
  refine ⟨j, h, fun r ↦ ?_⟩
  let E : Over.pullback (D.map h) ≅
      Over.pullback (D.map (fs r)) ⋙ Over.pullback (D.map (g r)) :=
    eqToIso (congrArg (fun f : j ⟶ i ↦ Over.pullback (D.map f)) (hg r).symm) ≪≫
      eqToIso (congrArg (fun f ↦ Over.pullback f) (D.map_comp (g r) (fs r))) ≪≫
      Over.pullbackComp (D.map (g r)) (D.map (fs r))
  apply (cancel_mono (E.hom.app (W r))).mp
  rw [E.hom.naturality, E.hom.naturality]
  exact congrArg (E.hom.app (V r) ≫ ·)
    (congrArg (fun f ↦ (Over.pullback (D.map (g r))).map f) (hfs r))


set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem finite_components_lift
    {I : Type w} [SmallCategory I] [IsFiltered I]
    (D : Iᵒᵖ ⥤ Scheme.{w})
    [∀ {i j : Iᵒᵖ} (f : i ⟶ j), IsAffineHom (D.map f)]
    [∀ i : Iᵒᵖ, CompactSpace (D.obj i)]
    [∀ i : Iᵒᵖ, QuasiSeparatedSpace (D.obj i)]
    (c : Cone D) (hc : IsLimit c)
    (R : Type*) [Finite R] (i : Iᵒᵖ) (V W : R → Over (D.obj i))
    (hV : ∀ r, LocallyOfFinitePresentation (V r).hom ∧
      QuasiCompact (V r).hom ∧ QuasiSeparated (V r).hom)
    (hW : ∀ r, LocallyOfFinitePresentation (W r).hom ∧
      QuasiCompact (W r).hom ∧ QuasiSeparated (W r).hom)
    (ψ : ∀ r, (Over.pullback (c.π.app i)).obj (V r) ⟶
      (Over.pullback (c.π.app i)).obj (W r)) :
    ∃ (j : Iᵒᵖ) (h : j ⟶ i)
      (ψj : ∀ r, (Over.pullback (D.map h)).obj (V r) ⟶
        (Over.pullback (D.map h)).obj (W r)),
      ∀ r, (Over.pullback (c.π.app j)).map (ψj r) ≫
          (((Over.pullbackComp (c.π.app j) (D.map h)).symm ≪≫
            eqToIso (congrArg (fun f : c.pt ⟶ D.obj i ↦ Over.pullback f)
              (c.w h))).app (W r)).hom =
        (((Over.pullbackComp (c.π.app j) (D.map h)).symm ≪≫
          eqToIso (congrArg (fun f : c.pt ⟶ D.obj i ↦ Over.pullback f)
            (c.w h))).app (V r)).hom ≫ ψ r := by
  classical
  let θ (f : R) := (ψ f).left ≫ pullback.fst (W f).hom (c.π.app i)
  have hθ (f : R) : θ f ≫ (W f).hom =
      pullback.fst (V f).hom (c.π.app i) ≫ (V f).hom := by
    dsimp [θ]
    rw [Category.assoc, pullback.condition, ← Category.assoc]
    change ((ψ f).left ≫ ((Over.pullback (c.π.app i)).obj (W f)).hom) ≫
      c.π.app i = _
    rw [Over.w, pullback.condition]
    rfl
  have hex (f : R) : ∃ (j : Iᵒᵖ) (h : j ⟶ i)
      (θj : pullback (V f).hom (D.map h) ⟶ (W f).left),
      θj ≫ (W f).hom = pullback.fst (V f).hom (D.map h) ≫ (V f).hom ∧
      pullback.map (V f).hom (c.π.app i) (V f).hom (D.map h)
        (𝟙 _) (c.π.app j) (𝟙 _) (by simp) (by simp) ≫ θj = θ f := by
    have := (hV f).1
    have := (hV f).2.1
    have := (hV f).2.2
    have := (hW f).1
    have := (hW f).2.1
    have := (hW f).2.2
    exact Scheme.exists_pullback_hom_of_isLimit hc (V f).hom (W f).hom (θ f) (hθ f)
  choose js fs θs hθs hdesc using hex
  obtain ⟨j, h, m, hm⟩ := IsCofiltered.wideCospan fs
  have hmap (f : R) : D.map h = D.map (m f) ≫ D.map (fs f) := by
    rw [← D.map_comp, hm]
  let M (f : R) := pullback.map (V f).hom (D.map h) (V f).hom (D.map (fs f))
    (𝟙 _) (D.map (m f)) (𝟙 _) (by simp) (by simp [hmap f])
  let θj (f : R) := M f ≫ θs f
  have hθj (f : R) : θj f ≫ (W f).hom =
      pullback.fst (V f).hom (D.map h) ≫ (V f).hom := by
    simp [θj, M, hθs f]
  have hj (f : R) : pullback.map (V f).hom (c.π.app i) (V f).hom (D.map h)
      (𝟙 _) (c.π.app j) (𝟙 _) (by simp) (by simp) ≫ θj f = θ f := by
    have hM : pullback.map (V f).hom (c.π.app i) (V f).hom (D.map h)
        (𝟙 _) (c.π.app j) (𝟙 _) (by simp) (by simp) ≫ M f =
        pullback.map (V f).hom (c.π.app i) (V f).hom (D.map (fs f))
          (𝟙 _) (c.π.app (js f)) (𝟙 _) (by simp) (by simp) := by
      apply pullback.hom_ext
      · simp [M]
      · simp [M, c.w (m f)]
    dsimp [θj]
    rw [← Category.assoc, hM]
    exact hdesc f
  let ej (f : R) : (Over.pullback (D.map h)).obj (V f) ⟶
      (Over.pullback (D.map h)).obj (W f) :=
    Over.homMk (pullback.lift (θj f) (pullback.snd (V f).hom (D.map h))
      ((hθj f).trans pullback.condition)) (by simp)
  let K := (Over.pullbackComp (c.π.app j) (D.map h)).symm ≪≫
    eqToIso (congrArg (fun f : c.pt ⟶ D.obj i ↦ Over.pullback f) (c.w h))
  have hK (W : Over (D.obj i)) :
      (K.hom.app W).left ≫ pullback.fst W.hom (c.π.app i) =
        pullback.fst (pullback.snd W.hom (D.map h)) (c.π.app j) ≫
          pullback.fst W.hom (D.map h) :=
    by
      have hcomp (k : c.pt ⟶ D.obj i) (hk : c.π.app j ≫ D.map h = k) :
          ((((Over.pullbackComp (c.π.app j) (D.map h)).symm ≪≫
            eqToIso (congrArg (fun t : c.pt ⟶ D.obj i ↦ Over.pullback t) hk)).app W).hom).left ≫
              pullback.fst W.hom k =
            pullback.fst (pullback.snd W.hom (D.map h)) (c.π.app j) ≫
              pullback.fst W.hom (D.map h) := by
        subst k
        have H := conjugateEquiv_counit
          ((Over.mapPullbackAdj (c.π.app j)).comp (Over.mapPullbackAdj (D.map h)))
          (Over.mapPullbackAdj (c.π.app j ≫ D.map h))
          (Over.mapComp (c.π.app j) (D.map h)).hom W
        simpa [Over.pullbackComp, Adjunction.comp_counit_app] using
          congrArg (fun k ↦ k.left) H
      simpa [K] using hcomp (c.π.app i) (c.w h)
  have he (f : R) : (Over.pullback (c.π.app j)).map (ej f) ≫ K.hom.app (W f) =
      K.hom.app (V f) ≫ ψ f := by
    have hM : (K.hom.app (V f)).left ≫
        pullback.map (V f).hom (c.π.app i) (V f).hom (D.map h)
          (𝟙 _) (c.π.app j) (𝟙 _) (by simp) (by simp) =
        pullback.fst (pullback.snd (V f).hom (D.map h)) (c.π.app j) := by
      apply pullback.hom_ext
      · simpa using hK (V f)
      · simp only [Category.assoc, pullback.map, pullback.lift_snd, Category.comp_id]
        change (K.hom.app (V f)).left ≫
          ((Over.pullback (c.π.app i)).obj (V f)).hom ≫ c.π.app j = _
        rw [← Category.assoc, Over.w]
        exact pullback.condition.symm
    ext1
    apply pullback.hom_ext
    · change (((Over.pullback (c.π.app j)).map (ej f)).left ≫
          (K.hom.app (W f)).left) ≫ pullback.fst (W f).hom (c.π.app i) =
        ((K.hom.app (V f)).left ≫ (ψ f).left) ≫
          pullback.fst (W f).hom (c.π.app i)
      rw [Category.assoc, hK (W f)]
      have hmapp : ((Over.pullback (c.π.app j)).map (ej f)).left ≫
          pullback.fst (pullback.snd (W f).hom (D.map h)) (c.π.app j) =
          pullback.fst (pullback.snd (V f).hom (D.map h)) (c.π.app j) ≫ (ej f).left := by
        simp
      rw [← Category.assoc, hmapp, Category.assoc]
      change pullback.fst _ _ ≫ (ej f).left ≫ pullback.fst (W f).hom (D.map h) =
        (K.hom.app (V f)).left ≫ θ f
      rw [show (ej f).left ≫ pullback.fst (W f).hom (D.map h) = θj f by simp [ej]]
      exact (congrArg (· ≫ θj f) hM).symm.trans
        ((Category.assoc _ _ _).trans (congrArg ((K.hom.app (V f)).left ≫ ·) (hj f)))
    · exact (Over.w (((Over.pullback (c.π.app j)).map (ej f)) ≫ K.hom.app (W f))).trans
        (Over.w (K.hom.app (V f) ≫ ψ f)).symm
  exact ⟨j, h, ej, he⟩

/-- Finite hypercover objects descend; this is the object and covering part of the
finite-data descent argument. Source: blueprint
lemma-weil-pbc-finite-hypercover-descent,
Detailed form proof, first two paragraphs.
(blueprint: lemma-weil-pbc-finite-hypercover-descent-objects) -/
theorem finite_hypercover_descent_objects
    {I : Type w} [SmallCategory I] [IsFiltered I]
    (D : Iᵒᵖ ⥤ Scheme.{w})
    [∀ {i j : Iᵒᵖ} (f : i ⟶ j), IsAffineHom (D.map f)]
    [∀ i : Iᵒᵖ, CompactSpace (D.obj i)]
    [∀ i : Iᵒᵖ, QuasiSeparatedSpace (D.obj i)]
    (c : Cone D) (hc : IsLimit c) :
    ∀ (r : ℕ) (U : TruncatedFiniteSplitEtaleHypercover c.pt r),
      ∃ (i : Iᵒᵖ) (Ui : TruncatedFiniteSplitEtaleHypercover (D.obj i) r),
        Ui.IsBaseChange (c.π.app i) U ∧
          ∀ (j : Iᵒᵖ) (h : j ⟶ i) (n : Fin (r + 1)),
            Surjective ((Over.pullback (D.map h)).map
              ((Scheme.Etale.forget (D.obj i)).map (Ui.matchingMap n))).left := by
  sorry
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Morphisms of finite hypercover truncations descend. Source: blueprint
lemma-weil-pbc-finite-hypercover-descent, Detailed form proof, final paragraph.
(blueprint: lemma-weil-pbc-finite-hypercover-descent-morphisms) -/
theorem finite_hypercover_descent_morphisms
    {I : Type w} [SmallCategory I] [IsFiltered I]
    (D : Iᵒᵖ ⥤ Scheme.{w})
    [∀ {i j : Iᵒᵖ} (f : i ⟶ j), IsAffineHom (D.map f)]
    [∀ i : Iᵒᵖ, CompactSpace (D.obj i)]
    [∀ i : Iᵒᵖ, QuasiSeparatedSpace (D.obj i)]
    (c : Cone D) (hc : IsLimit c) :
    ∀ (r : ℕ) (i : Iᵒᵖ)
      (U V : TruncatedFiniteSplitEtaleHypercover (D.obj i) r)
      (φ : U.diagram ⋙ Over.pullback (c.π.app i) ⟶
        V.diagram ⋙ Over.pullback (c.π.app i)),
      ∃ (j : Iᵒᵖ) (h : j ⟶ i)
        (ψ : U.diagram ⋙ Over.pullback (D.map h) ⟶
          V.diagram ⋙ Over.pullback (D.map h)),
        ∀ Δ : (SimplexCategory.Truncated r)ᵒᵖ,
          (Over.pullback (c.π.app j)).map (ψ.app Δ) ≫
              (((Over.pullbackComp (c.π.app j) (D.map h)).symm ≪≫
                eqToIso (congrArg (fun f : c.pt ⟶ D.obj i ↦ Over.pullback f)
                  (c.w h))).app (V.diagram.obj Δ)).hom =
            (((Over.pullbackComp (c.π.app j) (D.map h)).symm ≪≫
              eqToIso (congrArg (fun f : c.pt ⟶ D.obj i ↦ Over.pullback f)
                (c.w h))).app (U.diagram.obj Δ)).hom ≫ φ.app Δ := by
  classical
  intro r i U V φ
  have := truncated_finite r
  have : Finite (SimplexCategory.Truncated r)ᵒᵖ :=
    Finite.of_injective Opposite.unop Opposite.unop_injective
  let C := (SimplexCategory.Truncated r)ᵒᵖ
  obtain ⟨j, h, ψj, hj⟩ := finite_components_lift D c hc C i
    U.diagram.obj V.diagram.obj (truncated_terms_finitePresentation U)
    (truncated_terms_finitePresentation V) φ.app
  let F := U.diagram ⋙ Over.pullback (D.map h)
  let G := V.diagram ⋙ Over.pullback (D.map h)
  let K := (Over.pullbackComp (c.π.app j) (D.map h)).symm ≪≫
    eqToIso (congrArg (fun f : c.pt ⟶ D.obj i ↦ Over.pullback f) (c.w h))
  let R := Σ a b : C, a ⟶ b
  have : ∀ a b : C, Finite (a ⟶ b) := by
    intro a b
    apply Finite.of_injective (fun f : a ⟶ b ↦ f.unop.hom)
    intro f g hfg
    apply Quiver.Hom.unop_inj
    exact SimplexCategory.Truncated.Hom.ext _ _
      (congrArg SimplexCategory.Hom.toOrderHom hfg)
  have : Finite R := inferInstance
  change ∀ a, (Over.pullback (c.π.app j)).map (ψj a) ≫ K.hom.app (V.diagram.obj a) =
    K.hom.app (U.diagram.obj a) ≫ φ.app a at hj
  have hF (a : C) : LocallyOfFinitePresentation (F.obj a).hom ∧
      QuasiCompact (F.obj a).hom ∧ QuasiSeparated (F.obj a).hom := by
    obtain ⟨hp, hq, hs⟩ := truncated_terms_finitePresentation U a
    dsimp [F]
    exact ⟨inferInstance, inferInstance, inferInstance⟩
  have hG (a : C) : LocallyOfFinitePresentation (G.obj a).hom ∧
      QuasiCompact (G.obj a).hom ∧ QuasiSeparated (G.obj a).hom := by
    obtain ⟨hp, hq, hs⟩ := truncated_terms_finitePresentation V a
    dsimp [G]
    exact ⟨inferInstance, inferInstance, inferInstance⟩
  have hn (a b : C) (f : a ⟶ b) :
      (Over.pullback (c.π.app j)).map (F.map f ≫ ψj b) =
        (Over.pullback (c.π.app j)).map (ψj a ≫ G.map f) := by
    apply (cancel_mono (K.hom.app (V.diagram.obj b))).mp
    simp only [Functor.map_comp, Category.assoc]
    rw [hj b]
    have hKU := K.hom.naturality (U.diagram.map f)
    have hKV := K.hom.naturality (V.diagram.map f)
    simp only [Functor.comp_map] at hKU hKV
    change (Over.pullback (c.π.app j)).map ((Over.pullback (D.map h)).map
      (U.diagram.map f)) ≫ K.hom.app (U.diagram.obj b) ≫ φ.app b = _
    rw [← Category.assoc, hKU, Category.assoc]
    have hφ := φ.naturality f
    simp only [Functor.comp_map] at hφ
    rw [hφ]
    rw [← Category.assoc, ← Category.assoc, ← hj a]
    exact congrArg ((Over.pullback (c.π.app j)).map (ψj a) ≫ ·) hKV.symm
  obtain ⟨k, l, hl⟩ := finite_morphism_equalities_lift D c hc R j
    (fun f ↦ F.obj f.1) (fun f ↦ G.obj f.2.1)
    (fun f ↦ hF f.1) (fun f ↦ hG f.2.1)
    (fun f ↦ F.map f.2.2 ≫ ψj f.2.1)
    (fun f ↦ ψj f.1 ≫ G.map f.2.2) (fun f ↦ hn f.1 f.2.1 f.2.2)
  let χ : F ⋙ Over.pullback (D.map l) ⟶ G ⋙ Over.pullback (D.map l) :=
    { app := fun a ↦ (Over.pullback (D.map l)).map (ψj a)
      naturality := fun {a b} f ↦ by
        simpa only [Functor.comp_map, ← Functor.map_comp] using hl ⟨a, b, f⟩ }
  let T : Over.pullback (D.map (l ≫ h)) ≅
      Over.pullback (D.map h) ⋙ Over.pullback (D.map l) :=
    eqToIso (congrArg (fun f ↦ Over.pullback f) (D.map_comp l h)) ≪≫
      Over.pullbackComp (D.map l) (D.map h)
  let ψ : U.diagram ⋙ Over.pullback (D.map (l ≫ h)) ⟶
      V.diagram ⋙ Over.pullback (D.map (l ≫ h)) :=
    (Functor.isoWhiskerLeft U.diagram T).hom ≫ χ ≫
      (Functor.isoWhiskerLeft V.diagram T).inv
  let L := (Over.pullbackComp (c.π.app k) (D.map l)).symm ≪≫
    eqToIso (congrArg (fun f : c.pt ⟶ D.obj j ↦ Over.pullback f) (c.w l))
  let M := (Over.pullbackComp (c.π.app k) (D.map (l ≫ h))).symm ≪≫
    eqToIso (congrArg (fun f : c.pt ⟶ D.obj i ↦ Over.pullback f) (c.w (l ≫ h)))
  have hT (W : Over (D.obj i)) :
      (T.hom.app W).left ≫ pullback.fst (pullback.snd W.hom (D.map h)) (D.map l) ≫
          pullback.fst W.hom (D.map h) = pullback.fst W.hom (D.map (l ≫ h)) := by
    have hInv : (T.inv.app W).left ≫ pullback.fst W.hom (D.map (l ≫ h)) =
        pullback.fst (pullback.snd W.hom (D.map h)) (D.map l) ≫
          pullback.fst W.hom (D.map h) := by
      simpa [T] using comparison_fst (D.map l) (D.map h) (D.map (l ≫ h))
        (D.map_comp l h).symm W
    rw [← hInv, ← Category.assoc, ← Over.comp_left, T.hom_inv_id_app]
    simp
  have coherence (W : Over (D.obj i)) :
      (Over.pullback (c.π.app k)).map (T.hom.app W) ≫
          L.hom.app ((Over.pullback (D.map h)).obj W) ≫ K.hom.app W = M.hom.app W := by
    ext1
    apply pullback.hom_ext
    · simp only [Over.comp_left, Category.assoc]
      have hK := comparison_fst _ _ _ (c.w h) W
      have hL := comparison_fst _ _ _ (c.w l) ((Over.pullback (D.map h)).obj W)
      have hM := comparison_fst _ _ _ (c.w (l ≫ h)) W
      change ((Over.pullback (c.π.app k)).map (T.hom.app W)).left ≫
        (L.hom.app ((Over.pullback (D.map h)).obj W)).left ≫
        (K.hom.app W).left ≫ pullback.fst W.hom (c.π.app i) = _
      change (K.hom.app W).left ≫ pullback.fst W.hom (c.π.app i) = _ at hK
      change (L.hom.app ((Over.pullback (D.map h)).obj W)).left ≫
        pullback.fst (pullback.snd W.hom (D.map h)) (c.π.app j) = _ at hL
      change (M.hom.app W).left ≫ pullback.fst W.hom (c.π.app i) = _ at hM
      rw [hK, ← Category.assoc (L.hom.app _).left, hL]
      simp only [Category.assoc]
      have hmapp : ((Over.pullback (c.π.app k)).map (T.hom.app W)).left ≫
          pullback.fst ((Over.pullback (D.map l)).obj
            ((Over.pullback (D.map h)).obj W)).hom (c.π.app k) =
        pullback.fst ((Over.pullback (D.map (l ≫ h))).obj W).hom (c.π.app k) ≫
          (T.hom.app W).left := by
        simp
      simp only [Over.pullback_obj_hom] at hmapp ⊢
      rw [← Category.assoc ((Over.pullback (c.π.app k)).map (T.hom.app W)).left,
        hmapp]
      simpa only [Category.assoc, hT] using hM.symm
    · exact (Over.w _).trans (Over.w _).symm
  refine ⟨k, l ≫ h, ψ, ?_⟩
  intro Δ
  change (Over.pullback (c.π.app k)).map (ψ.app Δ) ≫ M.hom.app (V.diagram.obj Δ) =
    M.hom.app (U.diagram.obj Δ) ≫ φ.app Δ
  rw [← coherence (V.diagram.obj Δ), ← coherence (U.diagram.obj Δ)]
  simp only [ψ, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerLeft_inv, Functor.whiskerLeft_app, Functor.map_comp, Category.assoc]
  rw [← Category.assoc
    ((Over.pullback (c.π.app k)).map (T.inv.app (V.diagram.obj Δ)))
    ((Over.pullback (c.π.app k)).map (T.hom.app (V.diagram.obj Δ))),
    ← Functor.map_comp, T.inv_hom_id_app]
  rw [(Over.pullback (c.π.app k)).map_id]
  simp only [Category.id_comp]
  have heq : (Over.pullback (c.π.app k)).map (χ.app Δ) ≫
      L.hom.app ((Over.pullback (D.map h)).obj (V.diagram.obj Δ)) =
    L.hom.app ((Over.pullback (D.map h)).obj (U.diagram.obj Δ)) ≫
      (Over.pullback (c.π.app j)).map (ψj Δ) := L.hom.naturality (ψj Δ)
  rw [← Category.assoc ((Over.pullback (c.π.app k)).map (χ.app Δ)), heq]
  simp only [Category.assoc]
  rw [hj Δ]

/-- Equalities of finite hypercover morphisms descend. Source: blueprint
lemma-weil-pbc-finite-hypercover-descent, Detailed form proof, final paragraph.
(blueprint: lemma-weil-pbc-finite-hypercover-descent-equalities) -/
theorem finite_hypercover_descent_equalities
    {I : Type w} [SmallCategory I] [IsFiltered I]
    (D : Iᵒᵖ ⥤ Scheme.{w})
    [∀ {i j : Iᵒᵖ} (f : i ⟶ j), IsAffineHom (D.map f)]
    [∀ i : Iᵒᵖ, CompactSpace (D.obj i)]
    [∀ i : Iᵒᵖ, QuasiSeparatedSpace (D.obj i)]
    (c : Cone D) (hc : IsLimit c) :
    ∀ (r : ℕ) (i : Iᵒᵖ)
      (U V : TruncatedFiniteSplitEtaleHypercover (D.obj i) r)
      (φ ψ : U.diagram ⟶ V.diagram),
      Functor.whiskerRight φ (Over.pullback (c.π.app i)) =
        Functor.whiskerRight ψ (Over.pullback (c.π.app i)) →
      ∃ (j : Iᵒᵖ) (h : j ⟶ i),
        Functor.whiskerRight φ (Over.pullback (D.map h)) =
          Functor.whiskerRight ψ (Over.pullback (D.map h)) := by
  classical
  intro r i U V φ ψ hφψ
  have := truncated_finite r
  have : Finite (SimplexCategory.Truncated r)ᵒᵖ :=
    Finite.of_injective Opposite.unop Opposite.unop_injective
  obtain ⟨j, h, hj⟩ := finite_morphism_equalities_lift D c hc
    ((SimplexCategory.Truncated r)ᵒᵖ) i U.diagram.obj V.diagram.obj
    (truncated_terms_finitePresentation U) (truncated_terms_finitePresentation V)
    φ.app ψ.app (fun Δ ↦ NatTrans.congr_app hφψ Δ)
  refine ⟨j, h, ?_⟩
  exact NatTrans.ext (funext hj)
end AlgebraicGeometry
