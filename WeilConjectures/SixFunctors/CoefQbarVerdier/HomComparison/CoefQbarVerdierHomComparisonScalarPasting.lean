/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.CoefQbarVerdier.HomComparison.CoefQbarVerdierHomComparisonComponents
import WeilConjectures.SixFunctors.CoefQbarVerdier.HomComparison.CoefQbarHomInclusionScalar
import WeilConjectures.SixFunctors.CoefQbarVerdier.HomComparison.CoefQbarFiniteHomScalarSquare

/-! # Pasting the finite Hom scalar square into the common-stage component square

Source: blueprint thm-coef-qbar-verdier, retained proof step 5.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option Elab.async false
set_option linter.auxLemma false

attribute [local irreducible] WeilConjectures.rationalDerivedInternalHom
  WeilConjectures.rationalDerivedTensor WeilConjectures.sfRationalScalarExtension
  WeilConjectures.rationalTensorScalarComparison WeilConjectures.rationalHomScalarComparison
  WeilConjectures.integralCoefficientLinear HasDerivedCategory.standard
  WeilConjectures.sfRationalConstructibleLocalization
  WeilConjectures.commonStageDerivedInternalHom
set_option allowUnsafeReducibility true in
attribute [local reducible] WeilConjectures.GeneralAlgebraicallyClosedCoefficients.stageCategory
  WeilConjectures.GeneralAlgebraicallyClosedCoefficients.stageCategory._aux_1
  WeilConjectures.GeneralAlgebraicallyClosedCoefficients.stageCategory._aux_3
  WeilConjectures.GeneralAlgebraicallyClosedCoefficients.stageCategory._aux_5
  WeilConjectures.GeneralAlgebraicallyClosedCoefficients.pairCategory
  CategoryTheory.ObjectProperty.FullSubcategory.category

attribute [local implicit_reducible]
  WeilConjectures.GeneralAlgebraicallyClosedCoefficients.Stage
  WeilConjectures.CoefQbarVerdier.Duality
  CategoryTheory.StageSystem.ι
universe u v
open CategoryTheory Opposite AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures.CoefQbarVerdier.HomComparison
open AlgebraicallyClosedCoefficients (Index Coefficient)
open GeneralAlgebraicallyClosedCoefficients (inclusion stageSystem)

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
  (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]

private theorem comparison_pasting
    {C D A : Type*} [Category C] [Category D] [Category A]
    (S : C ⥤ D) (I : C ⥤ A) (J : D ⥤ A) (t : S ⋙ J ≅ I)
    (H : Cᵒᵖ × C ⥤ C) (H' : Dᵒᵖ × D ⥤ D) (G : Aᵒᵖ × A ⥤ A)
    (n : H ⋙ I ≅ I.op.prod I ⋙ G) (n' : H' ⋙ J ≅ J.op.prod J ⋙ G)
    (K w d : C) (z e : D) (o a b : A)
    (r : I.obj w ≅ o) (s : J.obj z ≅ o) (ω : S.obj w ≅ z)
    (α : I.obj d ≅ a) (β : J.obj e ≅ b) (f : b ⟶ a)
    (p : d ⟶ H.obj (op K, w)) (q : e ⟶ H'.obj (op (S.obj K), z))
    (v : S.obj d ≅ e) (c : S.obj (H.obj (op K, w)) ⟶
      H'.obj (op (S.obj K), S.obj w))
    (hd : J.map v.hom ≫ β.hom ≫ f = t.hom.app d ≫ α.hom)
    (hw : J.map ω.hom ≫ s.hom = t.hom.app w ≫ r.hom)
    (hp : S.map p ≫ c ≫ H'.map (Prod.mkHom (𝟙 (op (S.obj K))) ω.hom) =
      v.hom ≫ q)
    (hc : J.map c ≫ n'.hom.app (op (S.obj K), S.obj w) ≫
        G.map (Prod.mkHom (t.inv.app K).op (t.hom.app w)) =
      t.hom.app (H.obj (op K, w)) ≫ n.hom.app (op K, w)) :
    f ≫ α.inv ≫ I.map p ≫ n.hom.app (op K, w) ≫
        G.map (Prod.mkHom (𝟙 (op (I.obj K))) r.hom) =
      β.inv ≫ J.map q ≫ n'.hom.app (op (S.obj K), z) ≫
        G.map (Prod.mkHom (𝟙 (op (J.obj (S.obj K)))) s.hom) ≫
        G.map (Prod.mkHom (t.inv.app K).op (𝟙 o)) := by
  apply (cancel_epi (J.map v.hom ≫ β.hom)).mp
  simp only [← Category.assoc] at hd ⊢
  rw [hd]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [← J.map_comp_assoc, ← hp, J.map_comp, J.map_comp]
  simp only [Category.assoc]
  have hn := n'.hom.naturality (Prod.mkHom (𝟙 (op (S.obj K))) ω.hom)
  simp only [Functor.comp_map, Functor.prod_map, Functor.op_map, op_id,
    CategoryTheory.Functor.map_id, unop_id] at hn
  rw [reassoc_of% hn]
  have hG : G.map (Prod.mkHom (𝟙 (op (J.obj (S.obj K)))) (J.map ω.hom)) ≫
      G.map (Prod.mkHom (𝟙 (op (J.obj (S.obj K)))) s.hom) ≫
      G.map (Prod.mkHom (t.inv.app K).op (𝟙 o)) =
    G.map (Prod.mkHom (t.inv.app K).op (t.hom.app w)) ≫
      G.map (Prod.mkHom (𝟙 (op (I.obj K))) r.hom) := by
    simp only [← G.map_comp]
    congr 1
    ext <;> simp [hw]
  simp only [Functor.comp_obj]
  rw [hG]
  rw [reassoc_of% hc]
  have ht := t.hom.naturality p
  dsimp only [Functor.comp_map] at ht
  rw [reassoc_of% ht]

private theorem comparison_pasting_lift
    {C D A : Type*} [Category C] [Category D] [Category A]
    (P : ObjectProperty (Aᵒᵖ × A)) (G : P.FullSubcategory ⥤ A)
    (hP : ∀ K M : A, P (op K, M))
    (GG : Aᵒᵖ × A ⥤ A)
    (hGG : GG = P.lift (𝟭 _) (fun Q ↦ hP Q.1.unop Q.2) ⋙ G)
    (S : C ⥤ D) (I : C ⥤ A) (J : D ⥤ A) (t : S ⋙ J ≅ I)
    (H : Cᵒᵖ × C ⥤ C) (H' : Dᵒᵖ × D ⥤ D)
    (n : H ⋙ I ≅ I.op.prod I ⋙ GG) (n' : H' ⋙ J ≅ J.op.prod J ⋙ GG)
    (K w d : C) (z e : D) (o a b : A)
    (r : I.obj w ≅ o) (s : J.obj z ≅ o) (ω : S.obj w ≅ z)
    (α : I.obj d ≅ a) (β : J.obj e ≅ b) (f : b ⟶ a)
    (p : d ⟶ H.obj (op K, w)) (q : e ⟶ H'.obj (op (S.obj K), z))
    (v : S.obj d ≅ e) (c : S.obj (H.obj (op K, w)) ⟶
      H'.obj (op (S.obj K), S.obj w))
    (hd : J.map v.hom ≫ β.hom ≫ f = t.hom.app d ≫ α.hom)
    (hw : J.map ω.hom ≫ s.hom = t.hom.app w ≫ r.hom)
    (hp : S.map p ≫ c ≫ H'.map (Prod.mkHom (𝟙 (op (S.obj K))) ω.hom) =
      v.hom ≫ q)
    (hc : J.map c ≫ n'.hom.app (op (S.obj K), S.obj w) ≫
        GG.map
          (Prod.mkHom (t.inv.app K).op (t.hom.app w)) =
      t.hom.app (H.obj (op K, w)) ≫ n.hom.app (op K, w)) :
    f ≫ α.inv ≫ I.map p ≫ n.hom.app (op K, w) ≫
        GG.map
          (Prod.mkHom (𝟙 (op (I.obj K))) r.hom) =
      β.inv ≫ J.map q ≫ n'.hom.app (op (S.obj K), z) ≫
        GG.map
          (Prod.mkHom (𝟙 (op (J.obj (S.obj K)))) s.hom) ≫
        GG.map
          (Prod.mkHom (t.inv.app K).op (𝟙 o)) := by
  subst GG
  exact comparison_pasting S I J t H H'
    (P.lift (𝟭 _) (fun Q ↦ hP Q.1.unop Q.2) ⋙ G)
    n n' K w d z e o a b r s ω α β f p q v c hd hw hp hc

private theorem square_of_transition_eq
    {C D A : Type*} [Category C] [Category D] [Category A]
    (U V : C ⥤ D) (h : U = V) (I : C ⥤ A) (J : D ⥤ A)
    (t : U ⋙ J ≅ I) (F G : Aᵒᵖ ⥤ A)
    (a : I.op ⋙ F ≅ I.op ⋙ G) (b : J.op ⋙ F ≅ J.op ⋙ G)
    (hc : ∀ K,
      F.map (((eqToIso (congrArg (fun S : C ⥤ D ↦ S ⋙ J) h.symm) ≪≫ t).inv.app K).op) ≫
          a.hom.app (op K) =
        b.hom.app (op (V.obj K)) ≫
          G.map (((eqToIso (congrArg (fun S : C ⥤ D ↦ S ⋙ J) h.symm) ≪≫ t).inv.app K).op))
    (K : C) :
    F.map (t.inv.app K).op ≫ a.hom.app (op K) =
      b.hom.app (op (U.obj K)) ≫ G.map (t.inv.app K).op := by
  subst V
  simpa using hc K

private theorem stage_square_of_transition_eq
    {I : Type*} [Preorder I] [IsDirectedOrder I]
    {C : I → Type*} [∀ i, Category (C i)] (S : StageSystem C)
    (V : ∀ {i j}, i ≤ j → C i ⥤ C j) (hV : ∀ (i j : I) (h : i ≤ j), S.T h = V h)
    (F G : S.PairCategoryᵒᵖ ⥤ S.PairCategory)
    (a : ∀ i, (S.ι i).op ⋙ F ≅ (S.ι i).op ⋙ G)
    (K : S.PairCategory) (L : I) (h : K.stage ≤ L)
    (hc : ∀ M,
      F.map (((eqToIso (congrArg (fun T : C K.stage ⥤ C L ↦ T ⋙ S.ι L)
        (hV K.stage L h).symm) ≪≫ S.transIso h).inv.app M).op) ≫
          (a K.stage).hom.app (op M) =
        (a L).hom.app (op ((V h).obj M)) ≫
          G.map (((eqToIso (congrArg (fun T : C K.stage ⥤ C L ↦ T ⋙ S.ι L)
            (hV K.stage L h).symm) ≪≫ S.transIso h).inv.app M).op)) :
    F.map (S.isoToStage K h).hom.op ≫ (a K.stage).hom.app (op K.obj) =
      (a L).hom.app (op (K.toStage h)) ≫ G.map (S.isoToStage K h).hom.op := by
  simpa only [StageSystem.transIso_inv_app] using
    square_of_transition_eq (S.T h) (V h) (hV K.stage L h)
      (S.ι K.stage) (S.ι L) (S.transIso h) F G (a K.stage) (a L)
      hc K.obj

private theorem stage_square_iso
    {I : Type*} [Preorder I] [IsDirectedOrder I]
    {C : I → Type*} [∀ i, Category (C i)] (S : StageSystem C)
    (V : ∀ {i j}, i ≤ j → C i ⥤ C j) (hV : ∀ (i j : I) (h : i ≤ j), S.T h = V h)
    (F G : S.PairCategoryᵒᵖ ⥤ S.PairCategory)
    (a : ∀ i, (S.ι i).op ⋙ F ≅ (S.ι i).op ⋙ G)
    (K : S.PairCategory) (L : I) (h : K.stage ≤ L)
    (hc : ∀ M,
      F.mapIso (((eqToIso (congrArg (fun T : C K.stage ⥤ C L ↦ T ⋙ S.ι L)
        (hV K.stage L h).symm) ≪≫ S.transIso h).app M).symm.op) ≪≫
          (a K.stage).app (op M) =
        (a L).app (op ((V h).obj M)) ≪≫
          G.mapIso (((eqToIso (congrArg (fun T : C K.stage ⥤ C L ↦ T ⋙ S.ι L)
            (hV K.stage L h).symm) ≪≫ S.transIso h).app M).symm.op)) :
    F.mapIso ((S.isoToStage K h).op) ≪≫ (a K.stage).app (op K.obj) =
      (a L).app (op (K.toStage h)) ≪≫ G.mapIso ((S.isoToStage K h).op) := by
  apply Iso.ext
  exact stage_square_of_transition_eq S V hV F G a K L h (fun M ↦
    congrArg Iso.hom (hc M))

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local implicit_reducible] homDual stageHom stagePairs RationalOperations.homDual
  RationalOperations.homRight RationalOperations.homPair

attribute [local irreducible] commonStageHomComparison StageSystem.PairCategory.mkHom
  stageHomInclusion stageToSelf homToStage

private theorem fullHom_const_naturality
    {C A : Type*} [Category C] [Category A]
    (I : C ⥤ A) (P : ObjectProperty (Aᵒᵖ × A)) (G : P.FullSubcategory ⥤ A)
    (w : C) (o : A) (s : I.obj w ≅ o)
    (h₀ : ∀ Q : Cᵒᵖ × C, P ((I.op.prod I).obj Q))
    (h₁ : ∀ K : Aᵒᵖ, P (K, o))
    {K M : Cᵒᵖ} (f : K ⟶ M) :
    let U := ((𝟭 _).prod' ((Functor.const _).obj w)) ⋙ P.lift (I.op.prod I) h₀
    let V := I.op ⋙ P.lift ((𝟭 _).prod' ((Functor.const _).obj o)) h₁
    let e : ∀ N, U.obj N ≅ V.obj N := fun _ ↦ P.isoMk (Iso.prod (Iso.refl _) s)
    (U ⋙ G).map f ≫ (G.mapIso (e M)).hom =
      (G.mapIso (e K)).hom ≫ (V ⋙ G).map f := by
  dsimp only [Functor.comp_map, ObjectProperty.lift_map,
    Functor.prod_map, Functor.op_map, Functor.prod'_map, Functor.id_map,
    Functor.const_obj_map, Functor.comp_obj, Functor.op_obj, Functor.prod_obj,
    Functor.prod'_obj, Functor.id_obj, Functor.const_obj_obj,
    Functor.mapIso_hom, ObjectProperty.isoMk_hom, Iso.prod_hom, Iso.refl_hom]
  rw [← G.map_comp, ← G.map_comp]
  congr 1
  apply ObjectProperty.hom_ext
  ext <;> simp only [CategoryTheory.Functor.map_id, Category.id_comp,
    Category.comp_id, Prod.mkHom, prod_comp,
    ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.homMk_hom,
    ObjectProperty.isoMk_hom, Iso.prod_hom, Iso.refl_hom]

/-- Transport a fixed second input through a functor on permitted pairs.
Source: blueprint thm-coef-qbar-verdier, retained step 5.
(blueprint: lem-coef-qbar-verdier-hom-comparison-scalar-pasting-expanded). -/
private def fullHom_constIso {C A : Type*} [Category C] [Category A]
    (I : C ⥤ A) (P : ObjectProperty (Aᵒᵖ × A)) (G : P.FullSubcategory ⥤ A)
    (w : C) (o : A) (s : I.obj w ≅ o)
    (h₀ : ∀ Q : Cᵒᵖ × C, P ((I.op.prod I).obj Q))
    (h₁ : ∀ K : Aᵒᵖ, P (K, o)) :
    ((𝟭 Cᵒᵖ).prod' ((Functor.const Cᵒᵖ).obj w)) ⋙
        P.lift (I.op.prod I) h₀ ⋙ G ≅
      I.op ⋙ P.lift ((𝟭 Aᵒᵖ).prod' ((Functor.const Aᵒᵖ).obj o)) h₁ ⋙ G :=
  NatIso.ofComponents
    (fun _ ↦ G.mapIso (P.isoMk (Iso.prod (Iso.refl _) s)))
    (fun {_ _} f ↦ fullHom_const_naturality I P G w o s h₀ h₁ f)

/-- Naturality of four explicitly composed components.
Source: the four-factor comparison of blueprint thm-coef-qbar-verdier, step 5.
(blueprint: lem-coef-qbar-verdier-hom-comparison-scalar-pasting-expanded). -/
private theorem iso_four_naturality {C D : Type*} [Category C] [Category D]
    {F₀ F₁ F₂ F₃ F₄ : C ⥤ D}
    (a : F₀ ≅ F₁) (b : F₁ ≅ F₂) (c : F₂ ≅ F₃) (d : F₃ ≅ F₄)
    {K M : C} (f : K ⟶ M) :
    F₀.map f ≫ (a.app M ≪≫ b.app M ≪≫ c.app M ≪≫ d.app M).hom =
      (a.app K ≪≫ b.app K ≪≫ c.app K ≪≫ d.app K).hom ≫ F₄.map f := by
  simpa only [Iso.trans_hom, Iso.app_hom, NatTrans.comp_app, Category.assoc] using
    (a ≪≫ b ≪≫ c ≪≫ d).hom.naturality f

/-- Compose four natural isomorphisms using their literal components.
Source: the four-factor comparison of blueprint thm-coef-qbar-verdier, step 5.
(blueprint: lem-coef-qbar-verdier-hom-comparison-scalar-pasting-expanded). -/
private def iso_four {C D : Type*} [Category C] [Category D]
    {F₀ F₁ F₂ F₃ F₄ : C ⥤ D}
    (a : F₀ ≅ F₁) (b : F₁ ≅ F₂) (c : F₂ ≅ F₃) (d : F₃ ≅ F₄) : F₀ ≅ F₄ :=
  NatIso.ofComponents (fun K ↦ a.app K ≪≫ b.app K ≪≫ c.app K ≪≫ d.app K)
    (fun {_ _} f ↦ iso_four_naturality a b c d f)

/-- The four Hom comparison factors, assembled before specializing the categories.
Source: blueprint thm-coef-qbar-verdier, retained proof step 5.
(blueprint: lem-coef-qbar-verdier-hom-comparison-scalar-pasting-expanded). -/
private def finiteHomComparison {C A : Type*} [Category C] [Category A]
    (I : C ⥤ A) (P : ObjectProperty (Aᵒᵖ × A)) (G : P.FullSubcategory ⥤ A)
    (H : Cᵒᵖ × C ⥤ C) (d : Cᵒᵖ ⥤ C) (g : Aᵒᵖ ⥤ A)
    (w : C) (o : A) (s : I.obj w ≅ o)
    (h₀ : ∀ Q : Cᵒᵖ × C, P ((I.op.prod I).obj Q))
    (h₁ : ∀ K : Aᵒᵖ, P (K, o))
    (a : d ⋙ I ≅ I.op ⋙ g)
    (b : d ≅ ((𝟭 _).prod' ((Functor.const _).obj w)) ⋙ H)
    (c : H ⋙ I ≅ P.lift (I.op.prod I) h₀ ⋙ G) :
    I.op ⋙ g ≅ I.op ⋙ P.lift ((𝟭 _).prod' ((Functor.const _).obj o)) h₁ ⋙ G :=
  iso_four a.symm (Functor.isoWhiskerRight b I)
    (Functor.isoWhiskerLeft ((𝟭 _).prod' ((Functor.const _).obj w)) c)
    (fullHom_constIso I P G w o s h₀ h₁)

/-- The literal components of finiteHomComparison.
Source: blueprint thm-coef-qbar-verdier, retained proof step 5.
(blueprint: lem-coef-qbar-verdier-hom-comparison-scalar-pasting-expanded). -/
private theorem finiteHomComparison_hom {C A : Type*} [Category C] [Category A]
    (I : C ⥤ A) (P : ObjectProperty (Aᵒᵖ × A)) (G : P.FullSubcategory ⥤ A)
    (H : Cᵒᵖ × C ⥤ C) (d : Cᵒᵖ ⥤ C) (g : Aᵒᵖ ⥤ A)
    (w : C) (o : A) (s : I.obj w ≅ o)
    (h₀ : ∀ Q : Cᵒᵖ × C, P ((I.op.prod I).obj Q))
    (h₁ : ∀ K : Aᵒᵖ, P (K, o))
    (a : d ⋙ I ≅ I.op ⋙ g)
    (b : d ≅ ((𝟭 _).prod' ((Functor.const _).obj w)) ⋙ H)
    (c : H ⋙ I ≅ P.lift (I.op.prod I) h₀ ⋙ G) (K : C) :
    (finiteHomComparison I P G H d g w o s h₀ h₁ a b c).hom.app (op K) =
      a.inv.app (op K) ≫ I.map (b.hom.app (op K)) ≫ c.hom.app (op K, w) ≫
        G.map (ObjectProperty.homMk
          (X := ⟨(op (I.obj K), I.obj w), h₀ (op K, w)⟩)
          (Y := ⟨(op (I.obj K), o), h₁ (op (I.obj K))⟩)
          (Prod.mkHom (𝟙 (op (I.obj K))) s.hom)) := rfl

private theorem iso_four_eq {C A : Type*} [Category C] [Category A]
    {F₀ F₁ F₂ F₃ F₄ : C ⥤ A}
    (a : F₀ ≅ F₁) (b : F₁ ≅ F₂) (c : F₂ ≅ F₃) (d : F₃ ≅ F₄) :
    iso_four a b c d = a ≪≫ b ≪≫ c ≪≫ d := by
  ext K
  rfl

private def fastComparison (B : Duality D l hl Ω X) (E : Index l Ω) :
    (inclusion (Y := X) E).op ⋙ B.duality.dual ≅
      (inclusion (Y := X) E).op ⋙ homDual l Ω X B.omega
        (fun K ↦ allPairs l Ω X D hl B.finite K B.omega)  :=
  finiteHomComparison (inclusion (Y := X) E)
    (commonStageHomPairs l Ω X) (commonStageDerivedInternalHom l Ω X)
    (stageHom l Ω X D hl B.finite E) (B.finite.datum E).dual B.duality.dual
    ((sfRationalConstructibleLocalization l (Coefficient.{u} l Ω E) X).obj
      (B.finite.omega E).omega) B.omega (B.omegaComparison E)
    (fun Q ↦ allPairs l Ω X D hl B.finite
      ((inclusion (Y := X) E).obj Q.1.unop) ((inclusion (Y := X) E).obj Q.2))
    (fun N ↦ allPairs l Ω X D hl B.finite N.unop B.omega)
    (B.comparison E) (B.finite.hom E).duality
    (stageHomInclusion l Ω X D hl B.finite E)

private theorem comparison_eq_fast (B : Duality D l hl Ω X) (E : Index l Ω) :
    localComparison l Ω X D hl B E = fastComparison D l hl Ω X B E := by
  rw [localComparison.eq_1]
  unfold fastComparison finiteHomComparison
  exact (iso_four_eq _ _ _ _).symm

private abbrev fullHom (F : Finite D l hl Ω X) :
    (generalAlgebraicallyClosedConstructibleCategory l Ω X)ᵒᵖ ×
      generalAlgebraicallyClosedConstructibleCategory l Ω X ⥤
      generalAlgebraicallyClosedConstructibleCategory l Ω X :=
  (commonStageHomPairs l Ω X).lift (𝟭 _)
    (fun P ↦ allPairs l Ω X D hl F P.1.unop P.2) ⋙
      commonStageDerivedInternalHom l Ω X

private theorem homDual_map_fullHom (F : Finite D l hl Ω X)
    (omega K M : generalAlgebraicallyClosedConstructibleCategory l Ω X)
    (f : op K ⟶ op M) :
    (homDual l Ω X omega (fun N ↦ allPairs l Ω X D hl F N omega)).map f =
      (fullHom D l hl Ω X F).map
          (Prod.mkHom f (𝟙 omega)) := rfl

private theorem localComparison_hom_explicit (B : Duality D l hl Ω X) (E : Index l Ω)
    (K : GeneralAlgebraicallyClosedCoefficients.Stage l Ω X E) :
    (localComparison l Ω X D hl B E).hom.app (op K) =
      (B.comparison E).inv.app (op K) ≫
        (inclusion (Y := X) E).map ((B.finite.hom E).duality.hom.app (op K)) ≫
        (stageHomInclusion l Ω X D hl B.finite E).hom.app
          (op K, (sfRationalConstructibleLocalization l (Coefficient.{u} l Ω E) X).obj
            (B.finite.omega E).omega) ≫
        (commonStageDerivedInternalHom l Ω X).map
          (ObjectProperty.homMk
            (X := (stagePairs l Ω X D hl B.finite E).obj
              (op K, (sfRationalConstructibleLocalization l (Coefficient.{u} l Ω E) X).obj
                (B.finite.omega E).omega))
            (Y := ⟨(op ((inclusion (Y := X) E).obj K), B.omega),
              allPairs l Ω X D hl B.finite ((inclusion (Y := X) E).obj K) B.omega⟩)
            (Prod.mkHom (𝟙 (op ((inclusion (Y := X) E).obj K)))
              (B.omegaComparison E).hom)) := by
  rw [comparison_eq_fast D l hl Ω X B E]
  unfold fastComparison
  exact finiteHomComparison_hom (inclusion (Y := X) E)
    (commonStageHomPairs l Ω X) (commonStageDerivedInternalHom l Ω X)
    (stageHom l Ω X D hl B.finite E) (B.finite.datum E).dual B.duality.dual
    ((sfRationalConstructibleLocalization l (Coefficient.{u} l Ω E) X).obj
      (B.finite.omega E).omega) B.omega (B.omegaComparison E)
    (fun Q ↦ allPairs l Ω X D hl B.finite
      ((inclusion (Y := X) E).obj Q.1.unop) ((inclusion (Y := X) E).obj Q.2))
    (fun N ↦ allPairs l Ω X D hl B.finite N.unop B.omega)
    (B.comparison E) (B.finite.hom E).duality
    (stageHomInclusion l Ω X D hl B.finite E) K

private theorem localComparison_hom_fullHom (B : Duality D l hl Ω X) (E : Index l Ω)
    (K : GeneralAlgebraicallyClosedCoefficients.Stage l Ω X E) :
    (localComparison l Ω X D hl B E).hom.app (op K) =
      (B.comparison E).inv.app (op K) ≫
        (inclusion E).map ((B.finite.hom E).duality.hom.app (op K)) ≫
        (stageHomInclusion l Ω X D hl B.finite E).hom.app
          (op K, (sfRationalConstructibleLocalization l (Coefficient.{u} l Ω E) X).obj
            (B.finite.omega E).omega) ≫
        (fullHom D l hl Ω X B.finite).map
          (Prod.mkHom (𝟙 (op ((inclusion E).obj K))) (B.omegaComparison E).hom) := by
  exact localComparison_hom_explicit D l hl Ω X B E K

private theorem localComparison_transition_of_factors
    (B : Duality D l hl Ω X) (E L : Index l Ω) (h : E ≤ L)
    (K : GeneralAlgebraicallyClosedCoefficients.Stage l Ω X E)
    (hp :
      B.duality.dual.map ((inclusionTransition l Ω X E L h).inv.app K).op ≫
        (B.comparison E).inv.app (op K) ≫
        (inclusion E).map ((B.finite.hom E).duality.hom.app (op K)) ≫
        (stageHomInclusion l Ω X D hl B.finite E).hom.app
          (op K, (sfRationalConstructibleLocalization l (Coefficient.{u} l Ω E) X).obj
            (B.finite.omega E).omega) ≫
        (fullHom D l hl Ω X B.finite).map
          (Prod.mkHom (𝟙 (op ((inclusion E).obj K))) (B.omegaComparison E).hom) =
      (B.comparison L).inv.app
          (op ((GeneralAlgebraicallyClosedCoefficients.transition l Ω X E L h).obj K)) ≫
        (inclusion L).map ((B.finite.hom L).duality.hom.app
          (op ((GeneralAlgebraicallyClosedCoefficients.transition l Ω X E L h).obj K))) ≫
        (stageHomInclusion l Ω X D hl B.finite L).hom.app
          (op ((GeneralAlgebraicallyClosedCoefficients.transition l Ω X E L h).obj K),
            (sfRationalConstructibleLocalization l (Coefficient.{u} l Ω L) X).obj
              (B.finite.omega L).omega) ≫
        (fullHom D l hl Ω X B.finite).map
          (Prod.mkHom (𝟙 (op ((inclusion L).obj
            ((GeneralAlgebraicallyClosedCoefficients.transition l Ω X E L h).obj K))))
            (B.omegaComparison L).hom) ≫
        (fullHom D l hl Ω X B.finite).map
          (Prod.mkHom ((inclusionTransition l Ω X E L h).inv.app K).op (𝟙 B.val.omega))) :
    B.duality.dual.map ((inclusionTransition l Ω X E L h).inv.app K).op ≫
        (localComparison l Ω X D hl B E).hom.app (op K) =
      (localComparison l Ω X D hl B L).hom.app
        (op ((GeneralAlgebraicallyClosedCoefficients.transition l Ω X E L h).obj K)) ≫
        (homDual l Ω X B.omega (fun M ↦ allPairs l Ω X D hl B.finite M B.omega)).map
          ((inclusionTransition l Ω X E L h).inv.app K).op := by
  rw [localComparison_hom_fullHom D l hl Ω X B E K,
    localComparison_hom_fullHom D l hl Ω X B L
      ((GeneralAlgebraicallyClosedCoefficients.transition l Ω X E L h).obj K),
    homDual_map_fullHom D l hl Ω X B.finite B.omega]
  dsimp only [Functor.comp_obj, Functor.op_obj, Quiver.Hom.unop_op,
    homDual, fullHom, Functor.prod'_obj,
    Functor.id_obj, Functor.const_obj_obj, Functor.prod_obj] at hp ⊢
  simpa (config := { dsimp := false, zetaDelta := false }) only [
    Iso.app_inv, Category.assoc] using hp

private theorem localComparison_transition
    (B : Duality D l hl Ω X) (E L : Index l Ω) (h : E ≤ L)
    (hs : RationalOperations.HomScalarCompatibility l
      (Coefficient.{u} l Ω E) X D hl (Coefficient.{u} l Ω L)
      (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω E L h)
      (B.finite.omega E) (B.finite.omega L)
      (B.finite.datum E) (B.finite.datum L) (B.finite.hom E) (B.finite.hom L))
    (K : GeneralAlgebraicallyClosedCoefficients.Stage l Ω X E) :
    let S := GeneralAlgebraicallyClosedCoefficients.transition l Ω X E L h
    B.duality.dual.map ((inclusionTransition l Ω X E L h).inv.app K).op ≫
        (localComparison l Ω X D hl B E).hom.app (op K) =
      (localComparison l Ω X D hl B L).hom.app (op (S.obj K)) ≫
        (homDual l Ω X B.omega (fun M ↦ allPairs l Ω X D hl B.finite M B.omega)).map
          ((inclusionTransition l Ω X E L h).inv.app K).op := by
  dsimp only
  have hp := comparison_pasting_lift (commonStageHomPairs l Ω X)
    (commonStageDerivedInternalHom l Ω X) (allPairs l Ω X D hl B.finite)
    (fullHom D l hl Ω X B.finite) rfl
    (GeneralAlgebraicallyClosedCoefficients.transition l Ω X E L h) (inclusion E) (inclusion L)
    (inclusionTransition l Ω X E L h)
    (stageHom l Ω X D hl B.finite E) (stageHom l Ω X D hl B.finite L)
    (stageHomInclusion l Ω X D hl B.finite E)
    (stageHomInclusion l Ω X D hl B.finite L)
    K ((sfRationalConstructibleLocalization l (Coefficient.{u} l Ω E) X).obj (B.finite.omega
        E).omega) ((B.finite.datum E).dual.obj (op K)) ((sfRationalConstructibleLocalization l
        (Coefficient.{u} l Ω L) X).obj (B.finite.omega L).omega)
    ((B.finite.datum L).dual.obj (op ((GeneralAlgebraicallyClosedCoefficients.transition l Ω X E
        L h).obj K))) B.val.omega
    (B.duality.dual.obj (op ((inclusion E).obj K)))
    (B.duality.dual.obj (op (((GeneralAlgebraicallyClosedCoefficients.transition l Ω X E L h) ⋙
        inclusion L).obj K)))
    (B.omegaComparison E) (B.omegaComparison L) (B.finite.scalar E L h).omega
    ((B.comparison E).app (op K)) ((B.comparison L).app (op
        ((GeneralAlgebraicallyClosedCoefficients.transition l Ω X E L h).obj K)))
    (B.duality.dual.map ((inclusionTransition l Ω X E L h).inv.app K).op)
    ((B.finite.hom E).duality.hom.app (op K))
    ((B.finite.hom L).duality.hom.app (op ((GeneralAlgebraicallyClosedCoefficients.transition l Ω
        X E L h).obj K)))
    ((B.finite.beta E L h).app (op K))
    (rationalHomScalarComparison l (Coefficient.{u} l Ω E) (Coefficient.{u} l Ω L)
      (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω E L h) X
      ⟨(op K, ((sfRationalConstructibleLocalization l (Coefficient.{u} l Ω E) X).obj
        (B.finite.omega E).omega)), (B.finite.hom E).permitted K
        ((sfRationalConstructibleLocalization l (Coefficient.{u} l Ω E) X).obj (B.finite.omega
        E).omega)⟩).hom
    (B.property.2.2.2.2.2.2.1 E L h K)
    (B.property.2.2.2.2.2.2.2.2.1 E L h)
    (finite_scalar_hom_square D l hl Ω X B.finite E L h hs K)
    (stageHomInclusion_scalar D l hl Ω X B.finite E L h K ((sfRationalConstructibleLocalization l
        (Coefficient.{u} l Ω E) X).obj (B.finite.omega E).omega))
  apply localComparison_transition_of_factors D l hl Ω X B E L h K
  simpa (config := { dsimp := false, zetaDelta := false }) only [Iso.app_inv] using hp

private theorem component_hom (B : Duality D l hl Ω X)
    (K : generalAlgebraicallyClosedConstructibleCategory l Ω X) :
    (component l Ω X D hl B K).hom =
      (localComparison l Ω X D hl B K.stage).hom.app (op K.obj) := by
  rewrite [component.eq_def]
  exact Iso.app_hom (localComparison l Ω X D hl B K.stage) (op K.obj)

private theorem component_hom_inclusion (B : Duality D l hl Ω X) (E : Index l Ω)
    (K : GeneralAlgebraicallyClosedCoefficients.Stage l Ω X E) :
    (component l Ω X D hl B ((inclusion E).obj K)).hom =
      (localComparison l Ω X D hl B E).hom.app (op K) := by
  simp only [component, GeneralAlgebraicallyClosedCoefficients.inclusion,
    StageSystem.ι_obj, Iso.app_hom]

private theorem component_stage_iso
    (B : Duality D l hl Ω X)
    (K : generalAlgebraicallyClosedConstructibleCategory l Ω X)
    (L : Index l Ω) (h : K.stage ≤ L)
    (hs : RationalOperations.HomScalarCompatibility l
      (Coefficient.{u} l Ω K.stage) X D hl (Coefficient.{u} l Ω L)
      (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω K.stage L h)
      (B.finite.omega K.stage) (B.finite.omega L)
      (B.finite.datum K.stage) (B.finite.datum L)
      (B.finite.hom K.stage) (B.finite.hom L)) :
    B.duality.dual.mapIso (((stageSystem l Ω X).isoToStage K h).op) ≪≫
        (localComparison l Ω X D hl B K.stage).app (op K.obj) =
      (localComparison l Ω X D hl B L).app (op (K.toStage h)) ≪≫
        (homDual l Ω X B.omega (fun M ↦
          allPairs l Ω X D hl B.finite M B.omega)).mapIso
          (((stageSystem l Ω X).isoToStage K h).op) := by
  exact stage_square_iso (stageSystem l Ω X)
    (fun {E L} h ↦ GeneralAlgebraicallyClosedCoefficients.transition l Ω X E L h)
    (GeneralAlgebraicallyClosedCoefficients.stageSystem_existsUnique l Ω X).exists.choose_spec.1
    B.duality.dual
    (homDual l Ω X B.omega (fun M ↦ allPairs l Ω X D hl B.finite M B.omega))
    (localComparison l Ω X D hl B) K L h
    (fun M ↦ Iso.ext (localComparison_transition D l hl Ω X B K.stage L h hs M))

private theorem component_stage_square
    (B : Duality D l hl Ω X)
    (K : generalAlgebraicallyClosedConstructibleCategory l Ω X)
    (L : Index l Ω) (h : K.stage ≤ L)
    (hs : RationalOperations.HomScalarCompatibility l
      (Coefficient.{u} l Ω K.stage) X D hl (Coefficient.{u} l Ω L)
      (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω K.stage L h)
      (B.finite.omega K.stage) (B.finite.omega L)
      (B.finite.datum K.stage) (B.finite.datum L)
      (B.finite.hom K.stage) (B.finite.hom L)) :
    B.duality.dual.map ((stageSystem l Ω X).isoToStage K h).hom.op ≫
        (localComparison l Ω X D hl B K.stage).hom.app (op K.obj) =
      (localComparison l Ω X D hl B L).hom.app (op (K.toStage h)) ≫
        (homDual l Ω X B.omega (fun M ↦
          allPairs l Ω X D hl B.finite M B.omega)).map
          ((stageSystem l Ω X).isoToStage K h).hom.op := by
  exact congrArg Iso.hom (component_stage_iso D l hl Ω X B K L h hs)

/-- Expanded scalar-pasting square for the chosen local comparison components.
Source: coefficient-transport paragraph of blueprint thm-coef-qbar-verdier,
retained proof step 5.
(blueprint: lem-coef-qbar-verdier-hom-comparison-scalar-pasting-expanded).

This is the component-level calculation obtained after expanding `component` to
`localComparison`; it is the finite-stage square that the outer theorem packages.
-/
theorem component_extension_expanded
    (B : Duality D l hl Ω X)
    (K : generalAlgebraicallyClosedConstructibleCategory l Ω X)
    (L : Index l Ω) (h : K.stage ≤ L)
    (hs : RationalOperations.HomScalarCompatibility l
      (Coefficient.{u} l Ω K.stage) X D hl (Coefficient.{u} l Ω L)
      (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω K.stage L h)
      (B.finite.omega K.stage) (B.finite.omega L)
      (B.finite.datum K.stage) (B.finite.datum L)
      (B.finite.hom K.stage) (B.finite.hom L)) :
    B.duality.dual.map ((stageSystem l Ω X).isoToStage K h).hom.op ≫
        (localComparison l Ω X D hl B K.stage).hom.app (op K.obj) =
      (component l Ω X D hl B ((inclusion L).obj (K.toStage h))).hom ≫
        (homDual l Ω X B.omega (fun M ↦
          allPairs l Ω X D hl B.finite M B.omega)).map
          ((stageSystem l Ω X).isoToStage K h).hom.op := by
  rewrite [component_hom_inclusion D l hl Ω X B L (K.toStage h)]
  exact component_stage_square D l hl Ω X B K L h hs

theorem component_extension_of_scalar_compatibility
    (B : Duality D l hl Ω X)
    (K : generalAlgebraicallyClosedConstructibleCategory l Ω X)
    (L : Index l Ω) (h : K.stage ≤ L)
    (hs : RationalOperations.HomScalarCompatibility l
      (Coefficient.{u} l Ω K.stage) X D hl (Coefficient.{u} l Ω L)
      (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω K.stage L h)
      (B.finite.omega K.stage) (B.finite.omega L)
      (B.finite.datum K.stage) (B.finite.datum L)
      (B.finite.hom K.stage) (B.finite.hom L)) :
    B.duality.dual.map ((stageSystem l Ω X).isoToStage K h).hom.op ≫
        (component l Ω X D hl B K).hom =
      (component l Ω X D hl B ((inclusion L).obj (K.toStage h))).hom ≫
        (homDual l Ω X B.omega (fun M ↦
          allPairs l Ω X D hl B.finite M B.omega)).map
          ((stageSystem l Ω X).isoToStage K h).hom.op := by
  rewrite [component_hom D l hl Ω X B K]
  exact component_extension_expanded D l hl Ω X B K L h hs

end WeilConjectures.CoefQbarVerdier.HomComparison
