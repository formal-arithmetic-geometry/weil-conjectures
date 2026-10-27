module

public import Sheaf.AlgebraicGeometry.AffineCohomologyComparisonData

import Sheaf.AlgebraicGeometry.AffineCohomologyRawRestriction
import Sheaf.AlgebraicGeometry.CoherentHigherImageModuleAction
import all WeilConjectures.AlgebraicGeometry.AbelianHigherDirectImageNaturalComparison
import WeilConjectures.AlgebraicGeometry.ModuleCohomologyScalarEndomorphism
import Mathlib.CategoryTheory.Sites.DenseSubsite.Basic
import Mathlib.Algebra.Group.InjSurj

/-! # Realization of affine coherent cohomology as an etale module higher image

Source: Stacks Project, Etale Cohomology, Tag 03Q8, lemma-higher-direct-images;
Tag 03P2 for the simultaneous coherent comparison.
(blueprint: lem-weil-pbc-affine-cohomology-etale-module-realization).
-/

@[expose] public section
universe u v w
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Scheme.Modules
noncomputable section
set_option autoImplicit false
set_option cleanup.letToHave false
set_option backward.defeqAttrib.useBackward false
attribute [local irreducible] RingedSpace.moduleCohomology
  Etale.sheafHDerivedEquiv Etale.sheafHToDerived
  CategoryTheory.derivedExtEvaluation coherentEtaleRestrictionIso
  moduleAbelianCohomologyLarge coherentEtaleMap
  moduleCohomologyFMap IsNormalizedCoherentEtaleComparison
  tensorPullback tensorPullbackObj tensorSectionsComp tensorSectionsUnit
  etaleTensorSectionsRestriction
  affineRealizationComparison affineRealizationAffineComparison affineRealizationRestriction
  affineRealizationRawEvaluation affineRealizationRawCoherentEquiv
  affineRealizationClass affineRealizationRawEquiv
  Etale.abelianHigherDirectImageClass Etale.rawRestrictedCohomologyComparison
attribute [local instance 2000]
  instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensCarrierAbPresheaf
-- Prefer the bundled module structure before searching for section presentations.
attribute [local instance 3000] ModuleCat.isModule
attribute [local instance] Etale.RawRestrictedComparison.etaleComposition
  Etale.RawRestrictedComparison.etaleIdentities Etale.RawRestrictedComparison.etalePullbacks
  Etale.RawRestrictedComparison.etaleBaseChange Etale.RawRestrictedComparison.sheafifyInstance
  Etale.RawRestrictedComparison.weakSheafifyInstance
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local instance 50]
  instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensCarrierAbPresheaf

private theorem dense_sheafification_iso {C D : Type*} [Category C] [Category D]
    (J : GrothendieckTopology D) (i : C ⥤ D)
    [i.IsCoverDense J] [i.IsLocallyFull J] [HasWeakSheafify J AddCommGrpCat.{w}]
    (P : Dᵒᵖ ⥤ AddCommGrpCat.{w}) (T : Sheaf J AddCommGrpCat.{w})
    (e : i.op ⋙ P ≅ i.op ⋙ T.obj) :
    ∃ Φ : (presheafToSheaf J AddCommGrpCat.{w}).obj P ≅ T,
      whiskerLeft i.op (toSheafify J P ≫ Φ.hom.hom) = e.hom := by
  let α : P ⟶ T.obj := Functor.IsCoverDense.restrictHomEquivHom e.hom
  have hα : whiskerLeft i.op α = e.hom :=
    Functor.IsCoverDense.restrictHomEquivHom.symm_apply_apply e.hom
  let Q := (presheafToSheaf J AddCommGrpCat.{w}).obj P
  let β : Q ⟶ T := ⟨sheafifyLift J α T.property⟩
  have hβ : toSheafify J P ≫ β.hom = α := toSheafify_sheafifyLift J α T.property
  let δ : T ⟶ Q :=
    ⟨Functor.IsCoverDense.restrictHomEquivHom
      (e.inv ≫ whiskerLeft i.op (toSheafify J P))⟩
  have hδ : whiskerLeft i.op δ.hom = e.inv ≫ whiskerLeft i.op (toSheafify J P) :=
    Functor.IsCoverDense.restrictHomEquivHom.symm_apply_apply _
  have hαδ : α ≫ δ.hom = toSheafify J P := by
    apply (Functor.IsCoverDense.restrictHomEquivHom (G := i) (ℱ' := Q)).symm.injective
    change whiskerLeft i.op (α ≫ δ.hom) = _
    rw [whiskerLeft_comp, hα, hδ, ← Category.assoc, e.hom_inv_id, Category.id_comp]
    rfl
  have hβδ : β ≫ δ = 𝟙 Q := by
    apply Sheaf.hom_ext
    apply sheafify_hom_ext J _ _ Q.property
    change toSheafify J P ≫ (β.hom ≫ δ.hom) = toSheafify J P ≫ 𝟙 Q.obj
    rw [← Category.assoc, hβ, hαδ, Category.comp_id]
  have hδβ : δ ≫ β = 𝟙 T := by
    apply Sheaf.hom_ext
    apply (Functor.IsCoverDense.restrictHomEquivHom (G := i) (ℱ' := T)).symm.injective
    change whiskerLeft i.op (δ.hom ≫ β.hom) = 𝟙 _
    rw [whiskerLeft_comp, hδ, Category.assoc, ← whiskerLeft_comp, hβ, hα, e.inv_hom_id]
  refine ⟨⟨β, δ, hβδ, hδβ⟩, ?_⟩
  change whiskerLeft i.op (toSheafify J P ≫ β.hom) = e.hom
  rw [hβ, hα]

private theorem dense_component {C D : Type*} [Category C] [Category D]
    {J : GrothendieckTopology D} (i : C ⥤ D)
    (P : Dᵒᵖ ⥤ AddCommGrpCat.{w}) {H T : Sheaf J AddCommGrpCat.{w}}
    (κ : P ⟶ H.obj) (φ : H ⟶ T) (e : i.op ⋙ P ≅ i.op ⋙ T.obj)
    (he : whiskerLeft i.op (κ ≫ φ.hom) = e.hom)
    (W : C) (z : P.obj (op (i.obj W))) :
    φ.hom.app (op (i.obj W)) (κ.app (op (i.obj W)) z) = e.hom.app (op W) z := by
  have hz := ConcreteCategory.congr_hom (congrArg (fun t ↦ t.app (op W)) he) z
  change φ.hom.app (op (i.obj W)) (κ.app (op (i.obj W)) z) = e.hom.app (op W) z at hz
  exact hz

private theorem dense_full_component {D : Type*} [Category D]
    {J : GrothendieckTopology D} (p : ObjectProperty D)
    (P : Dᵒᵖ ⥤ AddCommGrpCat.{w}) {H T : Sheaf J AddCommGrpCat.{w}}
    (κ : P ⟶ H.obj) (φ : H ⟶ T) (α : p.ι.op ⋙ P ≅ p.ι.op ⋙ T.obj)
    (he : whiskerLeft p.ι.op (κ ≫ φ.hom) = α.hom)
    (V : D) (hV : p V) (z : P.obj (op V)) :
    φ.hom.app (op V) (κ.app (op V) z) = α.hom.app (op ⟨V, hV⟩) z :=
  dense_component p.ι P κ φ α he ⟨V, hV⟩ z

private theorem canonical_dense_values {D : Type*} [Category D]
    (J : GrothendieckTopology D) (p : ObjectProperty D)
    [p.ι.IsCoverDense J] [HasWeakSheafify J AddCommGrpCat.{w}]
    (P : Dᵒᵖ ⥤ AddCommGrpCat.{w}) (H T : Sheaf J AddCommGrpCat.{w})
    (σ : (presheafToSheaf J AddCommGrpCat.{w}).obj P ≅ H)
    (c : ∀ V : D, P.obj (op V) → H.obj.obj (op V))
    (hσ : ∀ V z, (toSheafify J P ≫ σ.hom.hom).app (op V) z = c V z)
    (e : p.ι.op ⋙ P ≅ p.ι.op ⋙ T.obj)
    (t : ∀ V : D, p V → P.obj (op V) → T.obj.obj (op V))
    (he : ∀ (V : D) (hV : p V) (z : P.obj (op V)), e.hom.app (op ⟨V, hV⟩) z = t V hV z) :
    ∃ Φ : H ≅ T, ∀ (V : D) (hV : p V) z,
      Φ.hom.hom.app (op V) (c V z) = t V hV z := by
  obtain ⟨β, hβ⟩ := dense_sheafification_iso J p.ι P T e
  let Φ : H ≅ T := σ.symm ≪≫ β
  have hfac : toSheafify J P ≫ σ.hom.hom ≫ Φ.hom.hom =
      toSheafify J P ≫ β.hom.hom := by
    have hi : σ.hom.hom ≫ Φ.hom.hom = β.hom.hom := by
      change (σ.hom ≫ (σ.inv ≫ β.hom)).hom = β.hom.hom
      rw [← Category.assoc, σ.hom_inv_id, Category.id_comp]
    exact congrArg (fun k ↦ toSheafify J P ≫ k) hi
  refine ⟨Φ, ?_⟩
  intro V hV z
  have hz := dense_full_component p P (toSheafify J P) β.hom e hβ V hV z
  exact (congrArg (Φ.hom.hom.app (op V)) (hσ V z)).symm.trans
    ((ConcreteCategory.congr_hom (NatTrans.congr_app hfac (op V)) z).trans
      (hz.trans (he V hV z)))

private def sourceSheafificationIso {C : Type*} [Category C]
    (J : GrothendieckTopology C) [HasWeakSheafify J AddCommGrpCat.{w}]
    {B P : Cᵒᵖ ⥤ AddCommGrpCat.{w}} {H : Sheaf J AddCommGrpCat.{w}}
    (b : B ≅ P) (σ : (presheafToSheaf J AddCommGrpCat.{w}).obj P ≅ H) :
    (presheafToSheaf J AddCommGrpCat.{w}).obj B ≅ H :=
  (presheafToSheaf J AddCommGrpCat.{w}).mapIso b ≪≫ σ

private theorem sourceSheafificationIso_unit {C : Type*} [Category C]
    (J : GrothendieckTopology C) [HasWeakSheafify J AddCommGrpCat.{w}]
    {B P : Cᵒᵖ ⥤ AddCommGrpCat.{w}} {H : Sheaf J AddCommGrpCat.{w}}
    (b : B ≅ P) (σ : (presheafToSheaf J AddCommGrpCat.{w}).obj P ≅ H) :
    toSheafify J B ≫ (sourceSheafificationIso J b σ).hom.hom =
      b.hom ≫ toSheafify J P ≫ σ.hom.hom := by
  change toSheafify J B ≫ (sheafifyMap J b.hom ≫ σ.hom.hom) =
    b.hom ≫ (toSheafify J P ≫ σ.hom.hom)
  rw [← Category.assoc, ← toSheafify_naturality, Category.assoc]

private theorem sourceSheafificationIso_unit_apply {C : Type*} [Category C]
    (J : GrothendieckTopology C) [HasWeakSheafify J AddCommGrpCat.{w}]
    {B P : Cᵒᵖ ⥤ AddCommGrpCat.{w}} {H : Sheaf J AddCommGrpCat.{w}}
    (b : B ≅ P) (σ : (presheafToSheaf J AddCommGrpCat.{w}).obj P ≅ H)
    (V : Cᵒᵖ) (z : B.obj V) :
    (toSheafify J B ≫ (sourceSheafificationIso J b σ).hom.hom).app V z =
      (toSheafify J P ≫ σ.hom.hom).app V (b.hom.app V z) := by
  have h := ConcreteCategory.congr_hom
    (NatTrans.congr_app (sourceSheafificationIso_unit J b σ) V) z
  simpa only [NatTrans.comp_app, AddCommGrpCat.comp_apply] using h

private theorem coherent_class_factor {X S : Scheme.{u}} (f : X ⟶ S)
    (G : X.Modules) [G.IsQuasicoherent] (q : ℕ) (V : S.Etale) {T : Type*}
    (F : (affineRealizationHigherImage f G q).obj.obj (op V) → T)
    (t : Sheaf.H (liftedCoherentEtaleSheaf (affineRealizationCoefficient f G V)) q → T)
    (h : ∀ z : (Etale.abelianHigherDirectImageRawPresheaf f q
        (liftedCoherentEtaleSheaf G)).obj (op V),
      F (Etale.abelianHigherDirectImageClass f q (liftedCoherentEtaleSheaf G) V z) =
        t (affineRealizationRawEvaluation f G q V z)) :
    ∀ x, F (affineRealizationClass f G q V x) = t x := by
  intro x
  obtain ⟨z, hz⟩ := (affineRealizationRawEvaluation_bijective f G q V).2 x
  have he := (congrArg F (affineRealizationClass_rawEvaluation f G q V z)).trans (h z)
  simpa only [hz] using he

private def sectionEquiv {C : Type*} [Category C] {J : GrothendieckTopology C}
    {H T : Sheaf J AddCommGrpCat.{w}} (Φ : H ≅ T) (V : C) :
    H.obj.obj (op V) ≃+ T.obj.obj (op V) :=
  (((sheafToPresheaf J AddCommGrpCat.{w}).mapIso Φ).app (op V)).addCommGroupIsoToAddEquiv

private theorem linear_from_class {R A B C : Type*} (c : A → B)
    (e : A ≃ C) (φ : B ≃ C) (hφ : ∀ y, φ (c y) = e y)
    (sA : R → A → A) (sB : R → B → B) (sC : R → C → C)
    (hB : ∀ a y, sB a (c y) = c (sA a y))
    (he : ∀ a y, e (sA a y) = sC a (e y)) :
    ∀ a x, φ (sB a x) = sC a (φ x) := by
  intro a x
  let y := e.symm (φ x)
  have hy : c y = x := by
    apply φ.injective
    rw [hφ]
    exact e.apply_symm_apply (φ x)
  rw [← hy]
  exact (congrArg φ (hB a y)).trans
    ((hφ (sA a y)).trans ((he a y).trans (congrArg (sC a) (hφ y)).symm))

private theorem sections_ext {C D : Type*} [Category C] [Category D]
    {J : GrothendieckTopology D} (i : C ⥤ D) [i.IsCoverDense J]
    (H : Sheaf J AddCommGrpCat.{w}) (V : D) {x y : H.obj.obj (op V)}
    (h : ∀ (W : C) (f : i.obj W ⟶ V), H.obj.map f.op x = H.obj.map f.op y) :
    x = y :=
  Functor.IsCoverDense.ext i ((sheafCompose J (CategoryTheory.forget AddCommGrpCat.{w})).obj H) V
    (fun {W} f ↦ h W f)

private theorem dense_linear {C D : Type*} [Category C] [Category D]
    {J : GrothendieckTopology D} (i : C ⥤ D) [i.IsCoverDense J]
    (H T : Sheaf J AddCommGrpCat.{w}) (A : D → Type*)
    (res : ∀ {V V' : D}, (V' ⟶ V) → A V → A V')
    (sH : ∀ V, A V → H.obj.obj (op V) → H.obj.obj (op V))
    (sT : ∀ V, A V → T.obj.obj (op V) → T.obj.obj (op V)) (φ : H ⟶ T)
    (hH : ∀ {V V' : D} (h : V' ⟶ V) a x,
      H.obj.map h.op (sH V a x) = sH V' (res h a) (H.obj.map h.op x))
    (hT : ∀ {V V' : D} (h : V' ⟶ V) a x,
      T.obj.map h.op (sT V a x) = sT V' (res h a) (T.obj.map h.op x))
    (hlocal : ∀ (W : C) a x,
      φ.hom.app (op (i.obj W)) (sH (i.obj W) a x) =
        sT (i.obj W) a (φ.hom.app (op (i.obj W)) x)) :
    ∀ V a x, φ.hom.app (op V) (sH V a x) = sT V a (φ.hom.app (op V) x) := by
  intro V a x
  apply sections_ext i T V
  intro W h
  have hn (z : H.obj.obj (op V)) :
      φ.hom.app (op (i.obj W)) (H.obj.map h.op z) =
        T.obj.map h.op (φ.hom.app (op V) z) := by
    simpa only [AddCommGrpCat.comp_apply] using
      (ConcreteCategory.congr_hom (φ.hom.naturality h.op) z)
  calc
    _ = φ.hom.app (op (i.obj W)) (H.obj.map h.op (sH V a x)) := (hn _).symm
    _ = φ.hom.app (op (i.obj W))
        (sH (i.obj W) (res h a) (H.obj.map h.op x)) :=
      congrArg (φ.hom.app (op (i.obj W))) (hH h a x)
    _ = sT (i.obj W) (res h a)
        (φ.hom.app (op (i.obj W)) (H.obj.map h.op x)) := hlocal W _ _
    _ = sT (i.obj W) (res h a) (T.obj.map h.op (φ.hom.app (op V) x)) :=
      congrArg (sT (i.obj W) (res h a)) (hn x)
    _ = T.obj.map h.op (sT V a (φ.hom.app (op V) x)) := (hT h _ _).symm

private def rawBasePresheaf {X S : Scheme.{u}} (f : X ⟶ S) (G : X.Modules)
    [G.IsQuasicoherent] (q : ℕ) : S.Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1} :=
  Etale.abelianHigherDirectImageRawPresheaf f q (liftedCoherentEtaleSheaf G)

private def sectionBasePresheaf {S : Scheme.{u}} (E : S.Modules) :
    S.Etaleᵒᵖ ⥤ AddCommGrpCat.{u} := etaleTensorSectionsPresheaf E

private def tensorGroup {S : Scheme.{u}} (E : S.Modules) (V : S.Etale) :
    AddCommGrpCat.{u} := (sectionBasePresheaf E).obj (op V)

private abbrev catEquiv (A : AddCommGrpCat.{v}) (B : AddCommGrpCat.{w}) :=
  @AddEquiv A B A.str.toAdd B.str.toAdd

-- Keep the existing bundled groups when constructing component isomorphisms.
private def equivHom {A B : AddCommGrpCat.{w}} (e : catEquiv A B) : A ⟶ B :=
  ConcreteCategory.ofHom (C := AddCommGrpCat.{w}) e.toAddMonoidHom

private def equivIso {A B : AddCommGrpCat.{w}} (e : catEquiv A B) : A ≅ B where
  hom := equivHom e
  inv := equivHom e.symm
  hom_inv_id := by ext x; exact e.symm_apply_apply x
  inv_hom_id := by ext x; exact e.apply_symm_apply x

private def componentsIso {C : Type*} [Category C]
    {P Q : C ⥤ AddCommGrpCat.{w}} (e : ∀ V, catEquiv (P.obj V) (Q.obj V))
    (hn : ∀ {V V' : C} (h : V ⟶ V'),
      P.map h ≫ equivHom (e V') = equivHom (e V) ≫ Q.map h) : P ≅ Q :=
  NatIso.ofComponents (fun V ↦ equivIso (e V)) hn

-- A named carrier keeps generic component calculations from unfolding the derived
-- cohomology and tensor-pullback constructions. The value remains the literal section.
private structure PresheafSection {C : Type*} [Category C]
    (P : C ⥤ AddCommGrpCat.{w}) (V : C) where
  down : P.obj V

private def presheafSectionEquiv {C : Type*} [Category C]
    (P : C ⥤ AddCommGrpCat.{w}) (V : C) : PresheafSection P V ≃ P.obj V where
  toFun x := x.down
  invFun x := ⟨x⟩
  left_inv x := by cases x; rfl
  right_inv _ := rfl

private instance sectionZero {C : Type*} [Category C] (P : C ⥤ AddCommGrpCat.{w}) (V : C) :
    Zero (PresheafSection P V) := ⟨⟨0⟩⟩

private instance sectionAdd {C : Type*} [Category C] (P : C ⥤ AddCommGrpCat.{w}) (V : C) :
    Add (PresheafSection P V) := ⟨fun x y ↦ ⟨x.down + y.down⟩⟩

private instance sectionNeg {C : Type*} [Category C] (P : C ⥤ AddCommGrpCat.{w}) (V : C) :
    Neg (PresheafSection P V) := ⟨fun x ↦ ⟨-x.down⟩⟩

private instance sectionSub {C : Type*} [Category C] (P : C ⥤ AddCommGrpCat.{w}) (V : C) :
    Sub (PresheafSection P V) := ⟨fun x y ↦ ⟨x.down - y.down⟩⟩

private instance sectionNatSMul {C : Type*} [Category C] (P : C ⥤ AddCommGrpCat.{w}) (V : C) :
    SMul ℕ (PresheafSection P V) := ⟨fun n x ↦ ⟨n • x.down⟩⟩

private instance sectionIntSMul {C : Type*} [Category C] (P : C ⥤ AddCommGrpCat.{w}) (V : C) :
    SMul ℤ (PresheafSection P V) := ⟨fun n x ↦ ⟨n • x.down⟩⟩

private instance sectionAddCommGroup {C : Type*} [Category C] (P : C ⥤ AddCommGrpCat.{w}) (V : C) :
    AddCommGroup (PresheafSection P V) :=
  (presheafSectionEquiv P V).injective.addCommGroup (fun x ↦ x.down)
    rfl (fun _ _ ↦ rfl) (fun _ ↦ rfl) (fun _ _ ↦ rfl)
    (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)

private def presheafSectionAddEquiv {C : Type*} [Category C]
    (P : C ⥤ AddCommGrpCat.{w}) (V : C) : PresheafSection P V ≃+ P.obj V where
  toEquiv := presheafSectionEquiv P V
  map_add' _ _ := rfl

private def boxMap {C : Type*} [Category C] (P : C ⥤ AddCommGrpCat.{w})
    {V V' : C} (h : P.obj V ⟶ P.obj V') :
    AddCommGrpCat.of (PresheafSection P V) ⟶ AddCommGrpCat.of (PresheafSection P V') :=
  AddCommGrpCat.ofHom ((presheafSectionAddEquiv P V').symm.toAddMonoidHom.comp
    (h.hom.comp (presheafSectionAddEquiv P V).toAddMonoidHom))

private theorem boxMap_mk {C : Type*} [Category C] (P : C ⥤ AddCommGrpCat.{w})
    {V V' : C} (h : P.obj V ⟶ P.obj V') (x : P.obj V) :
    boxMap P h (PresheafSection.mk x) = PresheafSection.mk (h x) := by rfl

private def boxedPresheaf {C : Type*} [Category C] (P : C ⥤ AddCommGrpCat.{w}) :
    C ⥤ AddCommGrpCat.{w} where
  obj V := AddCommGrpCat.of (PresheafSection P V)
  map h := boxMap P (P.map h)
  map_id V := by
    ext x
    apply (presheafSectionEquiv P V).injective
    exact ConcreteCategory.congr_hom (P.map_id V) x.down
  map_comp h k := by
    ext x
    apply (presheafSectionEquiv P _).injective
    exact ConcreteCategory.congr_hom (P.map_comp h k) x.down

private def boxedPresheafIso {C : Type*} [Category C] (P : C ⥤ AddCommGrpCat.{w}) :
    boxedPresheaf P ≅ P :=
  componentsIso (fun V ↦ presheafSectionAddEquiv P V) (by intro V V' h; ext x; rfl)

private def rawSectionPresheaf {X S : Scheme.{u}} (f : X ⟶ S) (G : X.Modules)
    [G.IsQuasicoherent] (q : ℕ) : S.Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1} :=
  boxedPresheaf (rawBasePresheaf f G q)

private def sectionPresheaf {S : Scheme.{u}} (E : S.Modules) :
    S.Etaleᵒᵖ ⥤ AddCommGrpCat.{u} :=
  boxedPresheaf (sectionBasePresheaf E)

private def boxedRawRestriction {X S : Scheme.{u}} (f : X ⟶ S)
    (G : X.Modules) [G.IsQuasicoherent] (q : ℕ) {V V' : S.Etale} (h : V' ⟶ V) :
    (rawSectionPresheaf f G q).obj (op V) ⟶
      (rawSectionPresheaf f G q).obj (op V') :=
  @boxMap _ _ (rawBasePresheaf f G q) (op V) (op V')
    (@affineRealizationRawRestriction X S f G _ q V V' h)

private def boxedTensorRestriction {S : Scheme.{u}} (E : S.Modules)
    {V V' : S.Etale} (h : V' ⟶ V) :
    (sectionPresheaf E).obj (op V) ⟶ (sectionPresheaf E).obj (op V') :=
  @boxMap _ _ (sectionBasePresheaf E) (op V) (op V') (@etaleTensorSectionsRestriction S E V V' h)

private theorem boxedRawRestriction_down {X S : Scheme.{u}} (f : X ⟶ S)
    (G : X.Modules) [G.IsQuasicoherent] (q : ℕ) {V V' : S.Etale} (h : V' ⟶ V)
    (z : (rawSectionPresheaf f G q).obj (op V)) :
    (@boxedRawRestriction X S f G _ q V V' h z).down =
      @affineRealizationRawRestriction X S f G _ q V V' h z.down :=
  rfl

private theorem boxedTensorRestriction_up {S : Scheme.{u}} (E : S.Modules)
    {V V' : S.Etale} (h : V' ⟶ V) (x : tensorGroup E V) :
    @boxedTensorRestriction S E V V' h
        (PresheafSection.mk (P := sectionBasePresheaf E) (V := op V) x) =
      PresheafSection.mk (P := sectionBasePresheaf E) (V := op V')
        (@etaleTensorSectionsRestriction S E V V' h x) :=
  @boxMap_mk _ _ (sectionBasePresheaf E) (op V) (op V')
    (@etaleTensorSectionsRestriction S E V V' h) x

private def affineObjects (S : Scheme.{u}) : ObjectProperty S.Etale :=
  fun V ↦ IsAffine V.left

private instance affineObjects_coverDense (S : Scheme.{u}) :
    (affineObjects S).ι.IsCoverDense S.smallEtaleTopology := by
  constructor
  intro V
  apply S.smallEtaleTopology.superset_covering _
    ((AffineEtale.Spec S).is_cover_of_isCoverDense S.smallEtaleTopology V)
  rintro W h ⟨A, a, b, hab⟩
  exact ⟨⟨(AffineEtale.Spec S).obj A,
    (by change IsAffine (Spec A.left.unop); infer_instance)⟩, a, b, hab⟩

attribute [local instance 2000]
  instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensCarrierAbPresheaf

set_option backward.isDefEq.respectTransparency false in
private theorem comparison_scalar (Y : Scheme.{u}) [CompactSpace Y] [Y.IsSeparated]
    (M : Y.Modules) [M.IsQuasicoherent] (q : ℕ) (a : Γ(Y, ⊤))
    (x : Sheaf.H (liftedCoherentEtaleSheaf M) q) :
    affineRealizationComparison Y M q
        (Sheaf.H.map (coherentEtaleMap M M (M.smulHom a)) q x) =
      a • affineRealizationComparison Y M q x := by
  exact (affineRealizationComparison_natural Y M M (M.smulHom a) q x).trans
    (moduleCohomology_scalar_endomorphism M (M.smulHom a) a
      (fun U t ↦ smulHom_app_apply M a U t) q (affineRealizationComparison Y M q x))

set_option backward.isDefEq.respectTransparency false in
private theorem affineComparison_scalar {X S : Scheme.{u}} (f : X ⟶ S)
    [QuasiCompact f] [IsSeparated f] (G : X.Modules) [G.IsQuasicoherent]
    (q : ℕ) (V : S.Etale) [IsAffine V.left] (a : Γ(V.left, ⊤))
    (x : Sheaf.H (liftedCoherentEtaleSheaf (affineRealizationCoefficient f G V)) q) :
    affineRealizationAffineComparison f G q V (Sheaf.H.map
      (coherentEtaleMap _ _ ((affineRealizationCoefficient f G V).smulHom
        ((pullback.fst V.hom f).appTop a))) q x) =
      (pullback.fst V.hom f).appTop a • affineRealizationAffineComparison f G q V x := by
  let : IsAffine ((𝟭 Scheme).obj V.left) := ‹IsAffine V.left›
  let : CompactSpace ((𝟭 Scheme).obj V.left) := Scheme.compactSpace_of_isAffine V.left
  let : CompactSpace (Limits.pullback V.hom f : Scheme.{u}) :=
    QuasiCompact.compactSpace_of_compactSpace (Limits.pullback.fst V.hom f)
  let : Scheme.IsSeparated (Limits.pullback V.hom f : Scheme.{u}) :=
    (HasAffineProperty.iff_of_isAffine (P := @IsSeparated)
      (Q := fun Y _ _ _ ↦ Scheme.IsSeparated Y)
      (f := Limits.pullback.fst V.hom f)).mp inferInstance
  have he := affineRealizationAffineComparison_eq f G q V
  exact (DFunLike.congr_fun he _).trans
    ((comparison_scalar (Limits.pullback V.hom f : Scheme.{u})
      (affineRealizationCoefficient f G V) q
      ((pullback.fst V.hom f).appTop a) x).trans
      (congrArg (fun y ↦ (pullback.fst V.hom f).appTop a • y)
        (DFunLike.congr_fun he x).symm))

attribute [local instance 50]
  instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensCarrierAbPresheaf

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

private theorem square_apply {A B : AddCommGrpCat.{u}}
    (r : A ⟶ B) (m : A ⟶ A) (n : B ⟶ B) (sA : A → A) (sB : B → B)
    (hm : ∀ x, m x = sA x) (hn : ∀ x, n x = sB x)
    (hc : m ≫ r = r ≫ n) (x : A) : r (sA x) = sB (r x) := by
  have h := ConcreteCategory.congr_hom hc x
  simpa only [AddCommGrpCat.comp_apply, hm, hn] using h

private theorem lifted_smul_apply {Y : Scheme.{u}} (M : Y.Modules)
    (a : Γ(Y, ⊤)) (x : ULift.{u + 1} Γ(M, ⊤)) :
    (AddCommGrpCat.uliftFunctor.{u + 1, u}.map (M.smul a)) x =
      ULift.up (a • x.down) := by rfl

private theorem lifted_restriction_map {S : Scheme.{u}} (E : S.Modules)
    [E.IsQuasicoherent] {V V' : S.Etale} (h : V' ⟶ V) :
    (liftedCoherentEtaleSheaf E).obj.map h.op =
      AddCommGrpCat.uliftFunctor.{u + 1, u}.map (etaleTensorSectionsRestriction E h) := by
  rfl

private def tensorSectionSmul {S : Scheme.{u}} (E : S.Modules)
    [E.IsQuasicoherent] (V : S.Etale) (a : ULift.{u + 1} Γ(V.left, ⊤))
    (x : (liftedCoherentEtaleSheaf E).obj.obj (op V)) :
    (liftedCoherentEtaleSheaf E).obj.obj (op V) :=
  ULift.up (a.down • (@id Γ((tensorPullback V.hom).obj E, ⊤) x.down))

private theorem tensorSectionSmul_restrict {S : Scheme.{u}} (E : S.Modules)
    [E.IsQuasicoherent] {V V' : S.Etale} (h : V' ⟶ V)
    (a : ULift.{u + 1} Γ(V.left, ⊤))
    (x : (liftedCoherentEtaleSheaf E).obj.obj (op V)) :
    (liftedCoherentEtaleSheaf E).obj.map h.op (tensorSectionSmul E V a x) =
      tensorSectionSmul E V' (ULift.up (h.left.appTop a.down))
        ((liftedCoherentEtaleSheaf E).obj.map h.op x) := by
  let L := AddCommGrpCat.uliftFunctor.{u + 1, u}
  have hc : L.map (((tensorPullback V.hom).obj E).smul a.down) ≫
      (liftedCoherentEtaleSheaf E).obj.map h.op =
      (liftedCoherentEtaleSheaf E).obj.map h.op ≫
        L.map (((tensorPullback V'.hom).obj E).smul (h.left.appTop a.down)) := by
    let m := ((tensorPullback V.hom).obj E).smul a.down
    let n := ((tensorPullback V'.hom).obj E).smul (h.left.appTop a.down)
    let r := etaleTensorSectionsRestriction E h
    calc
      _ = L.map m ≫ L.map r :=
        congrArg (fun t ↦ L.map m ≫ t) (lifted_restriction_map E h)
      _ = L.map (m ≫ r) := (L.map_comp m r).symm
      _ = L.map (r ≫ n) :=
        congrArg L.map (etaleTensorSectionsRestriction_smul E h a.down)
      _ = L.map r ≫ L.map n := L.map_comp r n
      _ = _ := congrArg (fun t ↦ t ≫ L.map n) (lifted_restriction_map E h).symm
  exact square_apply ((liftedCoherentEtaleSheaf E).obj.map h.op)
    (L.map (((tensorPullback V.hom).obj E).smul a.down))
    (L.map (((tensorPullback V'.hom).obj E).smul (h.left.appTop a.down)))
    (tensorSectionSmul E V a) (tensorSectionSmul E V' (ULift.up (h.left.appTop a.down)))
    (lifted_smul_apply _ a.down) (lifted_smul_apply _ (h.left.appTop a.down)) hc x

private theorem lifted_square {A A' : AddCommGrpCat.{u + 1}}
    {B B' : AddCommGrpCat.{u}} (r : A ⟶ A') (s : B ⟶ B')
    (e : catEquiv A B) (e' : A' ≃+ B') (h : ∀ x, e' (r x) = s (e x)) :
    r ≫ equivHom (B := AddCommGrpCat.uliftFunctor.{u + 1, u}.obj B')
        (e'.trans AddEquiv.ulift.symm) =
      equivHom (B := AddCommGrpCat.uliftFunctor.{u + 1, u}.obj B)
        (e.trans AddEquiv.ulift.symm) ≫
        AddCommGrpCat.uliftFunctor.{u + 1, u}.map s := by
  ext x
  exact congrArg ULift.up (h x)

private def affine_component {X S : Scheme.{u}} (f : X ⟶ S)
    [QuasiCompact f] [IsSeparated f] (G : X.Modules) [G.IsQuasicoherent]
    (E : S.Modules) (q : ℕ) (V : S.Etale) [IsAffine V.left]
    (e : catEquiv (affineRealizationOrdinaryGroup f G q V) (tensorGroup E V)) :
    catEquiv ((rawSectionPresheaf f G q).obj (op V)) ((sectionPresheaf E).obj (op V)) :=
  (presheafSectionAddEquiv (rawBasePresheaf f G q) (op V)).trans
    ((affineRealizationRawCoherentEquiv f G q V).trans
      (e.trans (presheafSectionAddEquiv (sectionBasePresheaf E) (op V)).symm))

private theorem affine_component_apply {X S : Scheme.{u}} (f : X ⟶ S)
    [QuasiCompact f] [IsSeparated f] (G : X.Modules) [G.IsQuasicoherent]
    (E : S.Modules) (q : ℕ) (V : S.Etale) [IsAffine V.left]
    (e : catEquiv (affineRealizationOrdinaryGroup f G q V) (tensorGroup E V))
    (z : (rawSectionPresheaf f G q).obj (op V)) :
    affine_component f G E q V e z =
      PresheafSection.mk (P := sectionBasePresheaf E) (V := op V)
        (e (affineRealizationRawCoherentEquiv f G q V z.down)) := by rfl

private def restrictedLiftIso {C D : Type*} [Category C] [Category D]
    (i : C ⥤ D) (P : Dᵒᵖ ⥤ AddCommGrpCat.{u + 1})
    (Q : Dᵒᵖ ⥤ AddCommGrpCat.{u})
    (e : ∀ V, catEquiv (P.obj (op (i.obj V))) (Q.obj (op (i.obj V))))
    (hn : ∀ {V V' : C} (h : V' ⟶ V) x,
      e V' (P.map (i.map h).op x) = Q.map (i.map h).op (e V x)) :
    i.op ⋙ P ≅ i.op ⋙ (Q ⋙ AddCommGrpCat.uliftFunctor.{u + 1, u}) :=
  componentsIso (fun V ↦ (e V.unop).trans AddEquiv.ulift.symm)
    (fun {V V'} h ↦ lifted_square (P.map (i.map h.unop).op)
      (Q.map (i.map h.unop).op) (e V.unop) (e V'.unop) (hn h.unop))

private def fullLiftIso {D : Type*} [Category D] (p : ObjectProperty D)
    (P : Dᵒᵖ ⥤ AddCommGrpCat.{u + 1}) (Q : Dᵒᵖ ⥤ AddCommGrpCat.{u})
    (e : ∀ V : p.FullSubcategory, catEquiv (P.obj (op V.obj)) (Q.obj (op V.obj)))
    (hn : ∀ {V V' : p.FullSubcategory} (h : V' ⟶ V) x,
      e V' (P.map h.hom.op x) = Q.map h.hom.op (e V x)) :
    p.ι.op ⋙ P ≅ p.ι.op ⋙ (Q ⋙ AddCommGrpCat.uliftFunctor.{u + 1, u}) :=
  restrictedLiftIso p.ι P Q e hn

private def propertyLiftIso {D : Type*} [Category D] (p : ObjectProperty D)
    (P : Dᵒᵖ ⥤ AddCommGrpCat.{u + 1}) (Q : Dᵒᵖ ⥤ AddCommGrpCat.{u})
    (e : ∀ V, p V → catEquiv (P.obj (op V)) (Q.obj (op V)))
    (hn : ∀ V V' (hV : p V) (hV' : p V') (h : V' ⟶ V) x,
      e V' hV' (P.map h.op x) = Q.map h.op (e V hV x)) :
    p.ι.op ⋙ P ≅ p.ι.op ⋙ (Q ⋙ AddCommGrpCat.uliftFunctor.{u + 1, u}) :=
  fullLiftIso p P Q (fun V ↦ e V.obj V.property)
    (fun {V V'} h ↦ hn V.obj V'.obj V.property V'.property h.hom)

private theorem coefficient_presheaf_eq {S : Scheme.{u}} (E : S.Modules)
    [E.IsQuasicoherent] : (liftedCoherentEtaleSheaf E).obj =
      sectionBasePresheaf E ⋙ AddCommGrpCat.uliftFunctor.{u + 1, u} := by
  rfl

private theorem unop_op_hom {C : Type*} [Category C] {V V' : C} (h : V' ⟶ V) :
    h.op.unop = h := by rfl

private theorem tensor_base_map_eq {S : Scheme.{u}} (E : S.Modules)
    {V V' : S.Etale} (h : V' ⟶ V) :
    (sectionBasePresheaf E).map h.op = @etaleTensorSectionsRestriction S E V V' h  :=
  congrArg (fun t : V' ⟶ V ↦ @etaleTensorSectionsRestriction S E V V' t)
    (unop_op_hom h)

private theorem raw_base_map_eq {X S : Scheme.{u}} (f : X ⟶ S)
    (G : X.Modules) [G.IsQuasicoherent] (q : ℕ) {V V' : S.Etale} (h : V' ⟶ V) :
    (rawBasePresheaf f G q).map h.op =
      @affineRealizationRawRestriction X S f G _ q V V' h := by rfl

private theorem naturality_of_maps_eq
    {A A' : AddCommGrpCat.{u + 1}} {B B' : AddCommGrpCat.{u}}
    (r r' : A ⟶ A') (s s' : B ⟶ B') (e : A → B) (e' : A' → B')
    (hr : r = r') (hs : s = s')
    (hn : ∀ x, e' (r' x) = s' (e x)) (x : A) : e' (r x) = s (e x) := by
  subst r'
  subst s'
  exact hn x

private theorem native_evaluation_natural {X S : Scheme.{u}} (f : X ⟶ S)
    [QuasiCompact f] [IsSeparated f] (G : X.Modules) [G.IsQuasicoherent]
    (E : S.Modules) (q : ℕ) (V V' : S.Etale) [IsAffine V.left] [IsAffine V'.left]
    (h : V' ⟶ V)
    (e : catEquiv (affineRealizationOrdinaryGroup f G q V) (tensorGroup E V))
    (e' : catEquiv (affineRealizationOrdinaryGroup f G q V') (tensorGroup E V'))
    (hn : ∀ x : ((RingedSpace.moduleCohomology (Limits.pullback V.hom f).toRingedSpace q).obj
        (affineRealizationCoefficient f G V)),
      e' (@affineRealizationRestriction X S f G q V V' h x) =
        @etaleTensorSectionsRestriction S E V V' h (e x))
    (z : (rawSectionPresheaf f G q).obj (op V)) :
    e' (affineRealizationRawCoherentEquiv f G q V'
      (@affineRealizationRawRestriction X S f G _ q V V' h z.down)) =
      @etaleTensorSectionsRestriction S E V V' h
        (e (affineRealizationRawCoherentEquiv f G q V z.down)) := by
  exact (congrArg e' (affineRealizationRawCoherentEquiv_natural f G q V V' h z.down)).trans
    (hn _)

private theorem affine_component_wrapped_natural {X S : Scheme.{u}} (f : X ⟶ S)
    [QuasiCompact f] [IsSeparated f] (G : X.Modules) [G.IsQuasicoherent]
    (E : S.Modules) (q : ℕ) (V V' : S.Etale) [IsAffine V.left] [IsAffine V'.left]
    (h : V' ⟶ V)
    (e : catEquiv (affineRealizationOrdinaryGroup f G q V) (tensorGroup E V))
    (e' : catEquiv (affineRealizationOrdinaryGroup f G q V') (tensorGroup E V'))
    (hn : ∀ x : ((RingedSpace.moduleCohomology (Limits.pullback V.hom f).toRingedSpace q).obj
        (affineRealizationCoefficient f G V)),
      e' (@affineRealizationRestriction X S f G q V V' h x) =
        @etaleTensorSectionsRestriction S E V V' h (e x))
    (z : (rawSectionPresheaf f G q).obj (op V)) :
    affine_component f G E q V' e' (@boxedRawRestriction X S f G _ q V V' h z) =
      @boxedTensorRestriction S E V V' h (affine_component f G E q V e z) := by
  exact (affine_component_apply f G E q V' e' _).trans
    ((congrArg (fun t ↦ PresheafSection.mk (P := sectionBasePresheaf E) (V := op V')
      (e' (affineRealizationRawCoherentEquiv f G q V' t)))
      (boxedRawRestriction_down f G q h z)).trans
      ((congrArg (PresheafSection.mk (P := sectionBasePresheaf E) (V := op V'))
        (native_evaluation_natural f G E q V V' h e e' hn z)).trans
        ((congrArg (@boxedTensorRestriction S E V V' h)
          (affine_component_apply f G E q V e z)).trans
          (boxedTensorRestriction_up E h _)).symm))

private theorem raw_presheaf_map_eq {X S : Scheme.{u}} (f : X ⟶ S)
    (G : X.Modules) [G.IsQuasicoherent] (q : ℕ) {V V' : S.Etale} (h : V' ⟶ V) :
    (rawSectionPresheaf f G q).map h.op = @boxedRawRestriction X S f G _ q V V' h :=
  congrArg (@boxMap _ _ (rawBasePresheaf f G q) (op V) (op V')) (raw_base_map_eq f G q h)

private theorem tensor_presheaf_map_eq {S : Scheme.{u}} (E : S.Modules)
    {V V' : S.Etale} (h : V' ⟶ V) :
    (sectionPresheaf E).map h.op = @boxedTensorRestriction S E V V' h :=
  congrArg (@boxMap _ _ (sectionBasePresheaf E) (op V) (op V')) (tensor_base_map_eq E h)

private def propertyLiftIsoWithMaps {D : Type*} [Category D] (p : ObjectProperty D)
    (P : Dᵒᵖ ⥤ AddCommGrpCat.{u + 1}) (Q : Dᵒᵖ ⥤ AddCommGrpCat.{u})
    (r : ∀ {V V' : D}, (V' ⟶ V) → (P.obj (op V) ⟶ P.obj (op V')))
    (s : ∀ {V V' : D}, (V' ⟶ V) → (Q.obj (op V) ⟶ Q.obj (op V')))
    (hr : ∀ {V V' : D} (h : V' ⟶ V), P.map h.op = r h)
    (hs : ∀ {V V' : D} (h : V' ⟶ V), Q.map h.op = s h)
    (e : ∀ V, p V → catEquiv (P.obj (op V)) (Q.obj (op V)))
    (hn : ∀ V V' (hV : p V) (hV' : p V') (h : V' ⟶ V) x,
      e V' hV' (r h x) = s h (e V hV x)) :
    p.ι.op ⋙ P ≅ p.ι.op ⋙ (Q ⋙ AddCommGrpCat.uliftFunctor.{u + 1, u}) :=
  propertyLiftIso p P Q e (fun V V' hV hV' h x ↦
    naturality_of_maps_eq (P.map h.op) (r h) (Q.map h.op) (s h)
      (e V hV) (e V' hV') (hr h) (hs h) (hn V V' hV hV' h) x)

private theorem propertyLiftIsoWithMaps_apply {D : Type*} [Category D] (p : ObjectProperty D)
    (P : Dᵒᵖ ⥤ AddCommGrpCat.{u + 1}) (Q : Dᵒᵖ ⥤ AddCommGrpCat.{u})
    (r : ∀ {V V' : D}, (V' ⟶ V) → (P.obj (op V) ⟶ P.obj (op V')))
    (s : ∀ {V V' : D}, (V' ⟶ V) → (Q.obj (op V) ⟶ Q.obj (op V')))
    (hr : ∀ {V V' : D} (h : V' ⟶ V), P.map h.op = r h)
    (hs : ∀ {V V' : D} (h : V' ⟶ V), Q.map h.op = s h)
    (e : ∀ V, p V → catEquiv (P.obj (op V)) (Q.obj (op V)))
    (hn : ∀ V V' (hV : p V) (hV' : p V') (h : V' ⟶ V) x,
      e V' hV' (r h x) = s h (e V hV x))
    (V : D) (hV : p V) (x : P.obj (op V)) :
    (propertyLiftIsoWithMaps p P Q r s hr hs e hn).hom.app (op ⟨V, hV⟩) x =
      ULift.up (e V hV x) := by rfl

private def natIsoEqTarget {C : Type*} [Category C] {P Q R : C ⥤ AddCommGrpCat.{w}}
    (e : P ≅ Q) (h : Q = R) : P ≅ R := e ≪≫ eqToIso h

private theorem natIsoEqTarget_apply {C : Type*} [Category C]
    {P Q R : C ⥤ AddCommGrpCat.{w}} (e : P ≅ Q) (h : Q = R)
    (V : C) (x : P.obj V) :
    HEq ((natIsoEqTarget e h).hom.app V x) (e.hom.app V x) := by subst h; rfl

private def unboxThenLiftIso {C : Type*} [Category C] (P : C ⥤ AddCommGrpCat.{u}) :
    boxedPresheaf P ⋙ AddCommGrpCat.uliftFunctor.{u + 1, u} ≅
      P ⋙ AddCommGrpCat.uliftFunctor.{u + 1, u} :=
  isoWhiskerRight (boxedPresheafIso P) AddCommGrpCat.uliftFunctor.{u + 1, u}

private theorem unboxThenLiftIso_apply {C : Type*} [Category C]
    (P : C ⥤ AddCommGrpCat.{u}) (V : C)
    (x : (boxedPresheaf P ⋙ AddCommGrpCat.uliftFunctor.{u + 1, u}).obj V) :
    (unboxThenLiftIso P).hom.app V x = ULift.up x.down.down := by rfl

private def coefficientIso {S : Scheme.{u}} (E : S.Modules) [E.IsQuasicoherent] :
    sectionPresheaf E ⋙ AddCommGrpCat.uliftFunctor.{u + 1, u} ≅
      (liftedCoherentEtaleSheaf E).obj :=
  natIsoEqTarget (unboxThenLiftIso (sectionBasePresheaf E)) (coefficient_presheaf_eq E).symm

private theorem coefficientIso_up {S : Scheme.{u}} (E : S.Modules) [E.IsQuasicoherent]
    (V : S.Etale) (x : tensorGroup E V) :
    (coefficientIso E).hom.app (op V)
      (ULift.up (PresheafSection.mk (P := sectionBasePresheaf E) (V := op V) x)) =
        ULift.up x := by
  exact (eq_of_heq (natIsoEqTarget_apply (unboxThenLiftIso (sectionBasePresheaf E))
    (coefficient_presheaf_eq E).symm (op V)
    (ULift.up (PresheafSection.mk (P := sectionBasePresheaf E) (V := op V) x)))).trans
      (unboxThenLiftIso_apply (sectionBasePresheaf E) (op V)
        (ULift.up (PresheafSection.mk (P := sectionBasePresheaf E) (V := op V) x)))

private theorem boxedPresheafIso_hom_down {C : Type*} [Category C]
    (P : C ⥤ AddCommGrpCat.{w}) (V : C) (z : (boxedPresheaf P).obj V) :
    (boxedPresheafIso P).hom.app V z = z.down := by rfl

private def rawBoxIso {X S : Scheme.{u}} (f : X ⟶ S) (G : X.Modules)
    [G.IsQuasicoherent] (q : ℕ) : rawSectionPresheaf f G q ≅
      Etale.abelianHigherDirectImageRawPresheaf f q (liftedCoherentEtaleSheaf G) :=
  boxedPresheafIso (rawBasePresheaf f G q)

private theorem rawBoxIso_hom_down {X S : Scheme.{u}} (f : X ⟶ S)
    (G : X.Modules) [G.IsQuasicoherent] (q : ℕ) (V : S.Etale)
    (z : (rawSectionPresheaf f G q).obj (op V)) :
    (rawBoxIso f G q).hom.app (op V) z = z.down :=
  boxedPresheafIso_hom_down (rawBasePresheaf f G q) (op V) z

private def changeTargetIso {C D : Type*} [Category C] [Category D]
    (i : C ⥤ D) {P Q R : D ⥤ AddCommGrpCat.{w}}
    (e : i ⋙ P ≅ i ⋙ Q) (h : Q ≅ R) : i ⋙ P ≅ i ⋙ R :=
  e ≪≫ isoWhiskerLeft i h

private theorem changeTargetIso_apply {C D : Type*} [Category C] [Category D]
    (i : C ⥤ D) {P Q R : D ⥤ AddCommGrpCat.{w}}
    (e : i ⋙ P ≅ i ⋙ Q) (h : Q ≅ R) (V : C) (x : P.obj (i.obj V)) :
    (changeTargetIso i e h).hom.app V x = h.hom.app (i.obj V) (e.hom.app V x) := by rfl

private def affine_components {X S : Scheme.{u}} (f : X ⟶ S)
    [QuasiCompact f] [IsSeparated f] (G : X.Modules) [G.IsQuasicoherent]
    (E : S.Modules) (q : ℕ)
    (e : ∀ (V : S.Etale) [IsAffine V.left],
      catEquiv (affineRealizationOrdinaryGroup f G q V) (tensorGroup E V)) :
    ∀ V, affineObjects S V →
      catEquiv ((rawSectionPresheaf f G q).obj (op V)) ((sectionPresheaf E).obj (op V)) :=
  fun V hV ↦ @affine_component X S f _ _ G _ E q V hV (@e V hV)

private theorem affine_components_apply {X S : Scheme.{u}} (f : X ⟶ S)
    [QuasiCompact f] [IsSeparated f] (G : X.Modules) [G.IsQuasicoherent]
    (E : S.Modules) (q : ℕ)
    (e : ∀ (V : S.Etale) [IsAffine V.left],
      catEquiv (affineRealizationOrdinaryGroup f G q V) (tensorGroup E V))
    (V : S.Etale) (hV : affineObjects S V)
    (z : (rawSectionPresheaf f G q).obj (op V)) :
    affine_components f G E q e V hV z =
      @affine_component X S f _ _ G _ E q V hV (@e V hV) z := by rfl

private def chartNaturality {X S : Scheme.{u}} (f : X ⟶ S)
    (G : X.Modules) (E : S.Modules) (q : ℕ)
    (e : ∀ (V : S.Etale) [IsAffine V.left],
      catEquiv (affineRealizationOrdinaryGroup f G q V) (tensorGroup E V)) : Prop :=
  ∀ (V V' : S.Etale) [IsAffine V.left] [IsAffine V'.left]
      (h : V' ⟶ V)
      (x : ((RingedSpace.moduleCohomology (Limits.pullback V.hom f).toRingedSpace q).obj
        (affineRealizationCoefficient f G V))),
      e V' (@affineRealizationRestriction X S f G q V V' h x) =
        @etaleTensorSectionsRestriction S E V V' h (e V x)

private theorem affine_components_natural {X S : Scheme.{u}} (f : X ⟶ S)
    [QuasiCompact f] [IsSeparated f] (G : X.Modules) [G.IsQuasicoherent]
    (E : S.Modules) (q : ℕ)
    (e : ∀ (V : S.Etale) [IsAffine V.left],
      catEquiv (affineRealizationOrdinaryGroup f G q V) (tensorGroup E V))
    (hn : chartNaturality f G E q e) :
    ∀ (V V' : S.Etale) (hV : affineObjects S V) (hV' : affineObjects S V')
      (h : V' ⟶ V) (z : (rawSectionPresheaf f G q).obj (op V)),
      affine_components f G E q e V' hV' (@boxedRawRestriction X S f G _ q V V' h z) =
        @boxedTensorRestriction S E V V' h (affine_components f G E q e V hV z) := by
  intro V V' hV hV' h z
  exact (affine_components_apply f G E q e V' hV' _).trans
    ((@affine_component_wrapped_natural X S f _ _ G _ E q V V' hV hV' h
      (@e V hV) (@e V' hV') (@hn V V' hV hV' h) z).trans
      (congrArg (@boxedTensorRestriction S E V V' h)
        (affine_components_apply f G E q e V hV z).symm))

private def affine_boxedIso {X S : Scheme.{u}} (f : X ⟶ S)
    [QuasiCompact f] [IsSeparated f] (G : X.Modules) [G.IsQuasicoherent]
    (E : S.Modules) [E.IsQuasicoherent] (q : ℕ)
    (e : ∀ (V : S.Etale) [IsAffine V.left],
      catEquiv (affineRealizationOrdinaryGroup f G q V) (tensorGroup E V))
    (hn : chartNaturality f G E q e) :
    (affineObjects S).ι.op ⋙
        rawSectionPresheaf f G q ≅
      (affineObjects S).ι.op ⋙
        (sectionPresheaf E ⋙ AddCommGrpCat.uliftFunctor.{u + 1, u}) := by
  exact propertyLiftIsoWithMaps (affineObjects S) (rawSectionPresheaf f G q) (sectionPresheaf E)
      (fun {V V'} h ↦ @boxedRawRestriction X S f G _ q V V' h)
      (fun {V V'} h ↦ @boxedTensorRestriction S E V V' h)
      (fun {V V'} h ↦ @raw_presheaf_map_eq X S f G _ q V V' h)
      (fun {V V'} h ↦ @tensor_presheaf_map_eq S E V V' h)
      (affine_components f G E q e) (affine_components_natural f G E q e hn)

private def affine_nativeIso {X S : Scheme.{u}} (f : X ⟶ S)
    [QuasiCompact f] [IsSeparated f] (G : X.Modules) [G.IsQuasicoherent]
    (E : S.Modules) [E.IsQuasicoherent] (q : ℕ)
    (e : ∀ (V : S.Etale) [IsAffine V.left],
      catEquiv (affineRealizationOrdinaryGroup f G q V) (tensorGroup E V))
    (hn : chartNaturality f G E q e) :
    (affineObjects S).ι.op ⋙
        rawSectionPresheaf f G q ≅
      (affineObjects S).ι.op ⋙ (liftedCoherentEtaleSheaf E).obj :=
  changeTargetIso (affineObjects S).ι.op (affine_boxedIso f G E q e hn) (coefficientIso E)

private theorem affine_nativeIso_apply {X S : Scheme.{u}} (f : X ⟶ S)
    [QuasiCompact f] [IsSeparated f] (G : X.Modules) [G.IsQuasicoherent]
    (E : S.Modules) [E.IsQuasicoherent] (q : ℕ)
    (e : ∀ (V : S.Etale) [IsAffine V.left],
      catEquiv (affineRealizationOrdinaryGroup f G q V) (tensorGroup E V))
    (hn : chartNaturality f G E q e)
    (V : S.Etale) [IsAffine V.left]
    (z : (rawSectionPresheaf f G q).obj (op V)) :
    (affine_nativeIso f G E q e hn).hom.app
      (op (⟨V, ‹IsAffine V.left›⟩ : (affineObjects S).FullSubcategory)) z =
      ULift.up (e V (affineRealizationAffineComparison f G q V
        (affineRealizationRawEvaluation f G q V z.down))) := by
  let W : (affineObjects S).FullSubcategory := ⟨V, ‹IsAffine V.left›⟩
  let β : (affineObjects S).ι.op ⋙ rawSectionPresheaf f G q ≅
      (affineObjects S).ι.op ⋙
        (sectionPresheaf E ⋙ AddCommGrpCat.uliftFunctor.{u + 1, u}) :=
    propertyLiftIsoWithMaps (affineObjects S) (rawSectionPresheaf f G q) (sectionPresheaf E)
      (fun {V V'} h ↦ @boxedRawRestriction X S f G _ q V V' h)
      (fun {V V'} h ↦ @boxedTensorRestriction S E V V' h)
      (fun {V V'} h ↦ @raw_presheaf_map_eq X S f G _ q V V' h)
      (fun {V V'} h ↦ @tensor_presheaf_map_eq S E V V' h)
      (affine_components f G E q e) (affine_components_natural f G E q e hn)
  have hβ : β.hom.app (op W) z = ULift.up (affine_component f G E q V (e V) z) :=
    propertyLiftIsoWithMaps_apply (affineObjects S) (rawSectionPresheaf f G q) (sectionPresheaf E)
      (fun {V V'} h ↦ @boxedRawRestriction X S f G _ q V V' h)
      (fun {V V'} h ↦ @boxedTensorRestriction S E V V' h)
      (fun {V V'} h ↦ @raw_presheaf_map_eq X S f G _ q V V' h)
      (fun {V V'} h ↦ @tensor_presheaf_map_eq S E V V' h)
      (affine_components f G E q e) (affine_components_natural f G E q e hn) V ‹IsAffine V.left› z
  have ht := changeTargetIso_apply (affineObjects S).ι.op β (coefficientIso E) (op W) z
  exact ht.trans ((congrArg ((coefficientIso E).hom.app (op V))
    (hβ.trans (congrArg ULift.up (affine_component_apply f G E q V (e V) z)))).trans
      ((coefficientIso_up E V _).trans (congrArg ULift.up
        (congrArg (e V) (affineRealizationRawCoherentEquiv_apply f G q V z.down)))))

private def nativeComparisonView {X S : Scheme.{u}} (f : X ⟶ S)
    (G : X.Modules) (E : S.Modules) (q : ℕ)
    (e : ∀ (V : S.Etale) [IsAffine V.left],
      ((RingedSpace.moduleCohomology (Limits.pullback V.hom f).toRingedSpace q).obj
        (affineRealizationCoefficient f G V)) ≃+ Γ((tensorPullback V.hom).obj E, ⊤)) :
    ∀ (V : S.Etale) [IsAffine V.left],
      catEquiv (affineRealizationOrdinaryGroup f G q V) (tensorGroup E V) :=
  fun V _ ↦ {
    toFun := fun x ↦ e V x
    invFun := fun y ↦ (e V).symm y
    left_inv := fun x ↦ (e V).symm_apply_apply x
    right_inv := fun y ↦ (e V).apply_symm_apply y
    map_add' := fun x y ↦ (e V).map_add x y }

private theorem nativeComparisonView_apply {X S : Scheme.{u}} (f : X ⟶ S)
    (G : X.Modules) (E : S.Modules) (q : ℕ)
    (e : ∀ (V : S.Etale) [IsAffine V.left],
      ((RingedSpace.moduleCohomology (Limits.pullback V.hom f).toRingedSpace q).obj
        (affineRealizationCoefficient f G V)) ≃+ Γ((tensorPullback V.hom).obj E, ⊤))
    (V : S.Etale) [IsAffine V.left]
    (x : ((RingedSpace.moduleCohomology (Limits.pullback V.hom f).toRingedSpace q).obj
        (affineRealizationCoefficient f G V))) :
    nativeComparisonView f G E q e V x = e V x := by rfl

private theorem nativeComparisonView_natural {X S : Scheme.{u}} (f : X ⟶ S)
    (G : X.Modules) (E : S.Modules) (q : ℕ)
    (e : ∀ (V : S.Etale) [IsAffine V.left],
      ((RingedSpace.moduleCohomology (Limits.pullback V.hom f).toRingedSpace q).obj
        (affineRealizationCoefficient f G V)) ≃+ Γ((tensorPullback V.hom).obj E, ⊤))
    (hn : ∀ (V V' : S.Etale) [IsAffine V.left] [IsAffine V'.left]
      (h : V' ⟶ V)
      (x : (RingedSpace.moduleCohomology (Limits.pullback V.hom f).toRingedSpace q).obj
        (affineRealizationCoefficient f G V)),
      e V' (affineRealizationRestriction f G q h x) =
        etaleTensorSectionsRestriction E h (e V x)) :
    chartNaturality f G E q (nativeComparisonView f G E q e) := by
  intro V V' hV hV' h x
  exact (nativeComparisonView_apply f G E q e V' _).trans
    ((@hn V V' hV hV' h x).trans
      (congrArg (@etaleTensorSectionsRestriction S E V V' h)
        (nativeComparisonView_apply f G E q e V x).symm))

private theorem boxed_affine_iso_apply {X S : Scheme.{u}} (f : X ⟶ S)
    [QuasiCompact f] [IsSeparated f] (G : X.Modules) [G.IsQuasicoherent]
    (E : S.Modules) [E.IsQuasicoherent] (q : ℕ)
    (e : ∀ (V : S.Etale) [IsAffine V.left],
      ((RingedSpace.moduleCohomology (Limits.pullback V.hom f).toRingedSpace q).obj
        (affineRealizationCoefficient f G V)) ≃+ Γ((tensorPullback V.hom).obj E, ⊤))
    (hn : ∀ (V V' : S.Etale) [IsAffine V.left] [IsAffine V'.left]
      (h : V' ⟶ V)
      (x : (RingedSpace.moduleCohomology (Limits.pullback V.hom f).toRingedSpace q).obj
        (affineRealizationCoefficient f G V)),
      e V' (affineRealizationRestriction f G q h x) =
        etaleTensorSectionsRestriction E h (e V x))
    (V : S.Etale) [IsAffine V.left]
    (z : (rawSectionPresheaf f G q).obj (op V)) :
    (affine_nativeIso f G E q (nativeComparisonView f G E q e)
      (nativeComparisonView_natural f G E q e hn)).hom.app
        (op (⟨V, ‹IsAffine V.left›⟩ : (affineObjects S).FullSubcategory)) z =
      ULift.up (e V (affineRealizationAffineComparison f G q V
        (affineRealizationRawEvaluation f G q V z.down))) := by
  exact (affine_nativeIso_apply f G E q (nativeComparisonView f G E q e)
    (nativeComparisonView_natural f G E q e hn) V z).trans
      (congrArg ULift.up (nativeComparisonView_apply f G E q e V _))

-- The concrete section operations are only needed while constructing the boxed functors.
-- Keep them out of later searches over arbitrary cohomology carriers.
attribute [-instance] sectionZero sectionAdd sectionNeg sectionSub
  sectionNatSMul sectionIntSMul sectionAddCommGroup

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem extend_affine_realization {X S : Scheme.{u}} (f : X ⟶ S)
    [QuasiCompact f] [IsSeparated f] (G : X.Modules) [G.IsQuasicoherent]
    (E : S.Modules) [E.IsQuasicoherent] (q : ℕ)
    (t : ∀ (V : S.Etale) [IsAffine V.left],
      (rawSectionPresheaf f G q).obj (op V) →
        (liftedCoherentEtaleSheaf E).obj.obj (op V))
    (α : (affineObjects S).ι.op ⋙
        rawSectionPresheaf f G q ≅
      (affineObjects S).ι.op ⋙ (liftedCoherentEtaleSheaf E).obj)
    (hα : ∀ (V : S.Etale) [IsAffine V.left]
      (z : (rawSectionPresheaf f G q).obj (op V)),
      α.hom.app (op (⟨V, ‹IsAffine V.left›⟩ : (affineObjects S).FullSubcategory)) z =
        t V z) :
    ∃ Φ : affineRealizationHigherImage f G q ≅ liftedCoherentEtaleSheaf E,
      ∀ (V : S.Etale) [IsAffine V.left]
        (z : (rawSectionPresheaf f G q).obj (op V)),
        Φ.hom.hom.app (op V)
          (Etale.abelianHigherDirectImageClass f q (liftedCoherentEtaleSheaf G) V z.down) =
          t V z := by
  let σ := sourceSheafificationIso S.smallEtaleTopology (rawBoxIso f G q)
    (Etale.canonicalComparison f q (liftedCoherentEtaleSheaf G))
  apply canonical_dense_values S.smallEtaleTopology (affineObjects S)
    (rawSectionPresheaf f G q) (affineRealizationHigherImage f G q)
    (liftedCoherentEtaleSheaf E) σ
    (fun V z ↦ Etale.abelianHigherDirectImageClass f q
      (liftedCoherentEtaleSheaf G) V z.down) _ α
    (fun V hV z ↦ @t V hV z) (fun V hV z ↦ @hα V hV z)
  intro V z
  have h := (sourceSheafificationIso_unit_apply S.smallEtaleTopology (rawBoxIso f G q)
    (Etale.canonicalComparison f q (liftedCoherentEtaleSheaf G)) (op V) z).trans
      (Etale.canonicalComparison_class f q (liftedCoherentEtaleSheaf G) V
        ((rawBoxIso f G q).hom.app (op V) z))
  simpa only [rawBoxIso_hom_down] using h

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem exists_realizationIso {X S : Scheme.{u}} (f : X ⟶ S)
    [QuasiCompact f] [IsSeparated f] (G : X.Modules) [G.IsQuasicoherent]
    (E : S.Modules) [E.IsQuasicoherent] (q : ℕ)
    (e : ∀ (V : S.Etale) [IsAffine V.left],
      ((RingedSpace.moduleCohomology (Limits.pullback V.hom f).toRingedSpace q).obj
        (affineRealizationCoefficient f G V)) ≃+ Γ((tensorPullback V.hom).obj E, ⊤))
    (hn : ∀ (V V' : S.Etale) [IsAffine V.left] [IsAffine V'.left]
      (h : V' ⟶ V)
      (x : (RingedSpace.moduleCohomology (Limits.pullback V.hom f).toRingedSpace q).obj
        (affineRealizationCoefficient f G V)),
      e V' (affineRealizationRestriction f G q h x) =
        etaleTensorSectionsRestriction E h (e V x)) :
    ∃ Φ : affineRealizationHigherImage f G q ≅ liftedCoherentEtaleSheaf E,
      (∀ (V : S.Etale) [IsAffine V.left]
    (x : Sheaf.H (liftedCoherentEtaleSheaf (affineRealizationCoefficient f G V)) q),
      Φ.hom.hom.app (op V) (affineRealizationClass f G q V x) =
        ULift.up (e V (affineRealizationAffineComparison f G q V x))) := by
  obtain ⟨Φ, hΦ⟩ := extend_affine_realization f G E q
    (fun V hV z ↦ ULift.up (@e V hV
      (@affineRealizationAffineComparison X S f _ _ G _ q V hV
        (affineRealizationRawEvaluation f G q V z.down))))
    (affine_nativeIso f G E q (nativeComparisonView f G E q e)
      (nativeComparisonView_natural f G E q e hn))
    (boxed_affine_iso_apply f G E q e hn)
  refine ⟨Φ, ?_⟩
  intro V hV x
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
    exact coherent_class_factor f G q V
      (fun y ↦ Φ.hom.hom.app (op V) y)
      (fun y ↦ ULift.up (e V (affineRealizationAffineComparison f G q V y)))
      (fun z ↦ hΦ V ⟨z⟩) x

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false


private theorem realization_raw_normalization {X S : Scheme.{u}} (f : X ⟶ S)
    [QuasiCompact f] [IsSeparated f] (G : X.Modules) [G.IsQuasicoherent]
    (E : S.Modules) [E.IsQuasicoherent] (q : ℕ)
    (e : ∀ (V : S.Etale) [IsAffine V.left],
      ((RingedSpace.moduleCohomology (Limits.pullback V.hom f).toRingedSpace q).obj
        (affineRealizationCoefficient f G V)) ≃+ Γ((tensorPullback V.hom).obj E, ⊤))
    (Φ : affineRealizationHigherImage f G q ≅ liftedCoherentEtaleSheaf E)
    (hclass : ∀ (V : S.Etale) [IsAffine V.left]
    (x : Sheaf.H (liftedCoherentEtaleSheaf (affineRealizationCoefficient f G V)) q),
      Φ.hom.hom.app (op V) (affineRealizationClass f G q V x) =
        ULift.up (e V (affineRealizationAffineComparison f G q V x))) :
    ∀ (V : S.Etale) [IsAffine V.left]
        (z : (Etale.abelianHigherDirectImageRawPresheaf f q
          (liftedCoherentEtaleSheaf G)).obj (op V)),
        Φ.hom.hom.app (op V)
          (Etale.abelianHigherDirectImageClass f q (liftedCoherentEtaleSheaf G) V z) =
          ULift.up (e V (affineRealizationAffineComparison f G q V
          (affineRealizationRawEvaluation f G q V z))) := by
  intro V hV z
  exact (congrArg (Φ.hom.hom.app (op V))
    (affineRealizationClass_rawEvaluation f G q V z).symm).trans
      (hclass V (affineRealizationRawEvaluation f G q V z))

private theorem finish_realization {X S : Scheme.{u}} (f : X ⟶ S)
    [QuasiCompact f] [IsSeparated f] (G : X.Modules) [G.IsQuasicoherent]
    (E : S.Modules) [E.IsQuasicoherent] (q : ℕ)
    (H : Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1})
    (classMap : ∀ V : S.Etale,
      Sheaf.H (liftedCoherentEtaleSheaf (affineRealizationCoefficient f G V)) q →
        H.obj.obj (op V))
    (e : ∀ (V : S.Etale) [IsAffine V.left],
      ((RingedSpace.moduleCohomology (Limits.pullback V.hom f).toRingedSpace q).obj
        (affineRealizationCoefficient f G V)) ≃+ Γ((tensorPullback V.hom).obj E, ⊤))
    (e_linear : ∀ (V : S.Etale) [IsAffine V.left] (a : Γ(V.left, ⊤))
      (x : (RingedSpace.moduleCohomology (Limits.pullback V.hom f).toRingedSpace q).obj
        (affineRealizationCoefficient f G V)),
      e V ((Limits.pullback.fst V.hom f).appTop a • x) = a • e V x)
    (action : ∀ V : S.Etale,
        Module (ULift.{u + 1} Γ(V.left, ⊤))
          ((H).obj.obj (op V)))
      (Φ : H ≅ liftedCoherentEtaleSheaf E)
    (hrestriction : ∀ (V V' : S.Etale) (h : V' ⟶ V) (a : ULift.{u + 1} Γ(V.left, ⊤))
        (x : (H).obj.obj (op V)),
        (H).obj.map h.op
          (affineRealizationSmul (action V) a x) =
        affineRealizationSmul (action V') (ULift.up (h.left.appTop a.down))
          ((H).obj.map h.op x))
    (haction : ∀ (V : S.Etale) (a : Γ(V.left, ⊤))
        (x : Sheaf.H (liftedCoherentEtaleSheaf (affineRealizationCoefficient f G V)) q),
        affineRealizationSmul (action V) (ULift.up a) (classMap V x) =
          classMap V (Sheaf.H.map
            (coherentEtaleMap _ _
              ((affineRealizationCoefficient f G V).smulHom
                ((Limits.pullback.fst V.hom f).appTop a)))
            q x))
    (hclass : ∀ (V : S.Etale) [IsAffine V.left]
    (x : Sheaf.H (liftedCoherentEtaleSheaf (affineRealizationCoefficient f G V)) q),
      Φ.hom.hom.app (op V) (classMap V x) =
        ULift.up (e V (affineRealizationAffineComparison f G q V x)))
    : (∀ (V : S.Etale) (a : ULift.{u + 1} Γ(V.left, ⊤))
        (x : (H).obj.obj (op V)),
        Φ.hom.hom.app (op V) (affineRealizationSmul (action V) a x) =
          ULift.up (a.down • (@id Γ((tensorPullback V.hom).obj E, ⊤)
            (Φ.hom.hom.app (op V) x).down))) := by
  have hlinear_affine (V : S.Etale) [IsAffine V.left]
      (a : ULift.{u + 1} Γ(V.left, ⊤))
      (x : (H).obj.obj (op V)) :
      Φ.hom.hom.app (op V) (affineRealizationSmul (action V) a x) =
        ULift.up (a.down • (@id Γ((tensorPullback V.hom).obj E, ⊤)
          (Φ.hom.hom.app (op V) x).down)) := by
    let c := ((affineRealizationAffineComparison f G q V).trans (e V)).trans
      AddEquiv.ulift.symm
    let sA (a : ULift.{u + 1} Γ(V.left, ⊤)) y := Sheaf.H.map
      (coherentEtaleMap _ _ ((affineRealizationCoefficient f G V).smulHom
        ((pullback.fst V.hom f).appTop a.down))) q y
    have he (a : ULift.{u + 1} Γ(V.left, ⊤)) y :
        c (sA a y) = tensorSectionSmul E V a (c y) := by
      change ULift.up (e V (affineRealizationAffineComparison f G q V (sA a y))) =
        ULift.up (a.down • e V (affineRealizationAffineComparison f G q V y))
      exact congrArg ULift.up ((congrArg (e V)
        (affineComparison_scalar f G q V a.down y)).trans (e_linear V a.down _))
    exact linear_from_class (classMap V) c.toEquiv
      (sectionEquiv Φ V).toEquiv (hclass V) sA
      (affineRealizationSmul (action V)) (tensorSectionSmul E V)
      (fun a y ↦ haction V a.down y) he a x
  exact dense_linear (affineObjects S).ι (H)
    (liftedCoherentEtaleSheaf E) (fun V ↦ ULift.{u + 1} Γ(V.left, ⊤))
    (fun h a ↦ ULift.up (h.left.appTop a.down))
    (fun V ↦ affineRealizationSmul (action V)) (tensorSectionSmul E) Φ.hom
    (fun h a x ↦ hrestriction _ _ h a x) (tensorSectionSmul_restrict E)
    (by intro W; have : IsAffine ((affineObjects S).ι.obj W).left := W.property
        exact hlinear_affine ((affineObjects S).ι.obj W))


private theorem combine_realization_parts {A B : Type*}
    {P Q : A → Prop} {R : A → B → Prop} {U V : B → Prop}
    (ha : ∃ a, P a ∧ Q a) (hb : ∃ b, U b)
    (h : ∀ a b, P a → Q a → U b → R a b) (hw : ∀ b, U b → V b) :
    ∃ a b, P a ∧ Q a ∧ R a b ∧ U b ∧ V b := by
  obtain ⟨a, hp, hq⟩ := ha
  obtain ⟨b, hu⟩ := hb
  have hr := h a b hp hq hu
  exact ⟨a, b, hp, hq, hr, hu, hw b hu⟩

/-- Compatible affine linear comparisons realize the abelian higher direct image as
an etale module sheaf, with its induced local scalar action and both class normalizations.
The sectionwise Module structures, their semilinear restrictions, and the linearity
of the abelian sheaf isomorphism are precisely an isomorphism of module sheaves.
Source: Stacks Project, Tag 03Q8, lemma-higher-direct-images; Tag 03P2
(blueprint: lem-weil-pbc-affine-cohomology-etale-module-realization).

Proof:
1. Quasi-compactness and separatedness survive base change. Over an affine base the
fibre product is quasi-compact and separated, and its pulled-back coefficient is
quasi-coherent. Apply the simultaneous canonical coherent comparison there.
2. Etale inverse image is restriction. The normalized tensor-pullback composition
identifies its coefficient with the tensor-section sheaf of the pulled-back module.
3. On the full etale site take the restricted cohomology presheaf. Multiplication
by pullbacks of base functions defines its sectionwise module actions. Functoriality
and coefficient naturality make restrictions semilinear. Module sheafification has
the prescribed underlying abelian higher direct image, by Tag 03Q8.
4. Compose the affine comparisons with the given e. The assumed square gives
naturality; the scalar comparison and scalar-endomorphism lemma give linearity.
5. Affine objects cover every etale object. The full affine subsite, with induced
sieve topology, is dense; restriction is therefore fully faithful on abelian sheaves
in the common coefficient universe.
6. Extend the affine map from the raw presheaf to the target sheaf by cover-density
and factor through sheafification. Extend its inverse after the raw unit; verify the
inverse identities by restriction and the sheafification universal property. The
normalized raw class lift identifies this sheafification with the actual higher image.
7. The unit is linear, as are the affine comparisons. On an arbitrary etale object
restrict to affine opens and use sheaf uniqueness. This proves the stated linearity
for every local scalar, including on non-affine objects.
8. The defining equation gives the cohomology-class normalization. The actual raw
evaluation and raw-restricted-class normalization identify its raw class with that
cohomology class; substitution gives the second formula. -/
theorem exists_affineCohomologyEtaleModuleRealization {X S : Scheme.{u}} (f : X ⟶ S)
    [QuasiCompact f] [IsSeparated f] (G : X.Modules) [G.IsQuasicoherent]
    (E : S.Modules) [E.IsQuasicoherent] (q : ℕ)
    (e : ∀ (V : S.Etale) [IsAffine V.left],
      ((RingedSpace.moduleCohomology (Limits.pullback V.hom f).toRingedSpace q).obj
        (affineRealizationCoefficient f G V)) ≃+ Γ((tensorPullback V.hom).obj E, ⊤))
    (e_linear : ∀ (V : S.Etale) [IsAffine V.left] (a : Γ(V.left, ⊤))
      (x : (RingedSpace.moduleCohomology (Limits.pullback V.hom f).toRingedSpace q).obj
        (affineRealizationCoefficient f G V)),
      e V ((Limits.pullback.fst V.hom f).appTop a • x) = a • e V x)
    (e_natural : ∀ (V V' : S.Etale) [IsAffine V.left] [IsAffine V'.left]
      (h : V' ⟶ V)
      (x : (RingedSpace.moduleCohomology (Limits.pullback V.hom f).toRingedSpace q).obj
        (affineRealizationCoefficient f G V)),
      e V' (affineRealizationRestriction f G q h x) =
        etaleTensorSectionsRestriction E h (e V x)) :
    ∃ (action : ∀ V : S.Etale,
        Module (ULift.{u + 1} Γ(V.left, ⊤))
          ((affineRealizationHigherImage f G q).obj.obj (op V)))
      (Φ : affineRealizationHigherImage f G q ≅ liftedCoherentEtaleSheaf E),
      (∀ (V V' : S.Etale) (h : V' ⟶ V) (a : ULift.{u + 1} Γ(V.left, ⊤))
        (x : (affineRealizationHigherImage f G q).obj.obj (op V)),
        (affineRealizationHigherImage f G q).obj.map h.op
          (affineRealizationSmul (action V) a x) =
        affineRealizationSmul (action V') (ULift.up (h.left.appTop a.down))
          ((affineRealizationHigherImage f G q).obj.map h.op x)) ∧
      (∀ (V : S.Etale) (a : Γ(V.left, ⊤))
        (x : Sheaf.H (liftedCoherentEtaleSheaf (affineRealizationCoefficient f G V)) q),
        affineRealizationSmul (action V) (ULift.up a) (affineRealizationClass f G q V x) =
          affineRealizationClass f G q V (Sheaf.H.map
            (coherentEtaleMap _ _
              ((affineRealizationCoefficient f G V).smulHom
                ((Limits.pullback.fst V.hom f).appTop a)))
            q x)) ∧
      (∀ (V : S.Etale) (a : ULift.{u + 1} Γ(V.left, ⊤))
        (x : (affineRealizationHigherImage f G q).obj.obj (op V)),
        Φ.hom.hom.app (op V) (affineRealizationSmul (action V) a x) =
          ULift.up (a.down • (@id Γ((tensorPullback V.hom).obj E, ⊤)
            (Φ.hom.hom.app (op V) x).down))) ∧
      (∀ (V : S.Etale) [IsAffine V.left]
        (x : Sheaf.H (liftedCoherentEtaleSheaf (affineRealizationCoefficient f G V)) q),
        Φ.hom.hom.app (op V) (affineRealizationClass f G q V x) =
          ULift.up (e V (affineRealizationAffineComparison f G q V x))) ∧
      (∀ (V : S.Etale) [IsAffine V.left]
        (z : (Etale.abelianHigherDirectImageRawPresheaf f q
          (liftedCoherentEtaleSheaf G)).obj (op V)),
        Φ.hom.hom.app (op V)
          (Etale.abelianHigherDirectImageClass f q (liftedCoherentEtaleSheaf G) V z) =
          ULift.up (e V (affineRealizationAffineComparison f G q V
            (affineRealizationRawEvaluation f G q V z)))) := by
  exact combine_realization_parts (exists_coherentHigherImageModuleAction f G q)
    (exists_realizationIso f G E q e e_natural)
    (finish_realization f G E q (affineRealizationHigherImage f G q)
      (affineRealizationClass f G q)
      e e_linear) (realization_raw_normalization f G E q e)


end
end AlgebraicGeometry.Scheme.Modules
