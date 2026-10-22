/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E8
-/
module

public import Sheaf.Paper.CompletedTensorUnitInsertionData
import all Sheaf.Paper.ReflectiveCompletedMonoidal
import Mathlib.CategoryTheory.Localization.Monoidal.Functor

/-! # Coherence of the normalized completed pullback -/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096

universe uB vB uE vE u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace CategoryTheory.ConstantCompletion

variable {B : Type uB} [Category.{vB} B] [MonoidalCategory B] [SymmetricCategory B]
variable {E : Type uE} [Category.{vE} E] [MonoidalCategory E] [SymmetricCategory E]

@[instance_reducible]
private def braided_of_oplax
    {C D : Type*} [Category C] [Category D] [MonoidalCategory C] [MonoidalCategory D]
    [BraidedCategory C] [BraidedCategory D] (F : C ⥤ D) [F.Monoidal]
    (h : ∀ X Y : C, Functor.OplaxMonoidal.δ F X Y ≫
      (β_ (F.obj X) (F.obj Y)).hom =
      F.map (β_ X Y).hom ≫ Functor.OplaxMonoidal.δ F Y X) : F.Braided := by
  refine { braided := fun X Y ↦ ?_ }
  apply (cancel_mono (Functor.OplaxMonoidal.δ F Y X)).1
  simp only [Category.assoc, Functor.Monoidal.μ_δ, Category.comp_id]
  rw [← h]
  simp only [← Category.assoc, Functor.Monoidal.μ_δ, Category.id_comp]

private theorem cast_hom_of_heq {C : Type*} [Category C]
    {X X' Y Y' : C} (ex : X = X') (ey : Y = Y')
    (f : X ⟶ Y) (g : X' ⟶ Y') (h : HEq f g) :
    f = eqToHom ex ≫ g ≫ eqToHom ey.symm := by
  cases ex
  cases ey
  simpa only [eqToHom_refl, Category.id_comp, Category.comp_id] using eq_of_heq h

private theorem cast_hom_heq {C : Type*} [Category C]
    {X X' Y Y' : C} (ex : X = X') (ey : Y = Y') (g : X' ⟶ Y') :
    HEq (eqToHom ex ≫ g ≫ eqToHom ey.symm) g := by
  cases ex
  cases ey
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  rfl

private theorem monoidal_nat_delta
    {C D : Type*} [Category C] [Category D] [MonoidalCategory C] [MonoidalCategory D]
    {F G : C ⥤ D} [F.Monoidal] [G.Monoidal] (τ : F ⟶ G) [τ.IsMonoidal]
    (X Y : C) : Functor.OplaxMonoidal.δ F X Y ≫ (τ.app X ⊗ₘ τ.app Y) =
      τ.app (X ⊗ Y) ≫ Functor.OplaxMonoidal.δ G X Y := by
  apply (cancel_epi (Functor.LaxMonoidal.μ F X Y)).1
  simp only [← Category.assoc, Functor.Monoidal.μ_δ, Category.id_comp]
  rw [NatTrans.IsMonoidal.tensor]
  simp only [Category.assoc, Functor.Monoidal.μ_δ, Category.comp_id]

private theorem monoidal_nat_unit
    {C D : Type*} [Category C] [Category D] [MonoidalCategory C] [MonoidalCategory D]
    {F G : C ⥤ D} [F.Monoidal] [G.Monoidal] (τ : F ⟶ G) [τ.IsMonoidal] :
    τ.app (𝟙_ C) ≫ Functor.OplaxMonoidal.η G = Functor.OplaxMonoidal.η F := by
  apply (cancel_epi (Functor.LaxMonoidal.ε F)).1
  rw [← Category.assoc, NatTrans.IsMonoidal.unit]
  simp only [Functor.Monoidal.ε_η]

private theorem oplax_braid_transport
    {C D : Type*} [Category C] [Category D] [MonoidalCategory C] [MonoidalCategory D]
    [BraidedCategory C] [BraidedCategory D] (F : C ⥤ D) [F.OplaxMonoidal]
    {X X' Y Y' : C} (a : X ≅ X') (b : Y ≅ Y')
    (h : Functor.OplaxMonoidal.δ F X' Y' ≫ (β_ (F.obj X') (F.obj Y')).hom =
      F.map (β_ X' Y').hom ≫ Functor.OplaxMonoidal.δ F Y' X') :
    Functor.OplaxMonoidal.δ F X Y ≫ (β_ (F.obj X) (F.obj Y)).hom =
      F.map (β_ X Y).hom ≫ Functor.OplaxMonoidal.δ F Y X := by
  apply (cancel_mono (F.map b.hom ⊗ₘ F.map a.hom)).1
  calc
    _ = Functor.OplaxMonoidal.δ F X Y ≫ (F.map a.hom ⊗ₘ F.map b.hom) ≫
        (β_ (F.obj X') (F.obj Y')).hom := by
      rw [Category.assoc, ← BraidedCategory.braiding_naturality]
    _ = F.map (a.hom ⊗ₘ b.hom) ≫ Functor.OplaxMonoidal.δ F X' Y' ≫
        (β_ (F.obj X') (F.obj Y')).hom := by
      rw [← Category.assoc, Functor.OplaxMonoidal.δ_natural, Category.assoc]
    _ = F.map (a.hom ⊗ₘ b.hom) ≫ F.map (β_ X' Y').hom ≫
        Functor.OplaxMonoidal.δ F Y' X' := by rw [h]
    _ = F.map (β_ X Y).hom ≫ F.map (b.hom ⊗ₘ a.hom) ≫
        Functor.OplaxMonoidal.δ F Y' X' := by
      rw [← Category.assoc, ← F.map_comp,
        BraidedCategory.braiding_naturality, F.map_comp, Category.assoc]
    _ = _ := by
      simp only [Category.assoc, Functor.OplaxMonoidal.δ_natural]

private theorem lifted_braid_on_images
    {C D E : Type*} [Category C] [Category D] [Category E]
    [MonoidalCategory C] [MonoidalCategory D] [MonoidalCategory E]
    [BraidedCategory C] [BraidedCategory D] [BraidedCategory E]
    (R : C ⥤ D) (F : D ⥤ E) (G : C ⥤ E)
    [R.Braided] [F.Monoidal] [G.Braided]
    (γ : G ⟶ R ⋙ F) [IsIso γ] [γ.IsMonoidal] (X Y : C) :
    Functor.OplaxMonoidal.δ F (R.obj X) (R.obj Y) ≫
        (β_ (F.obj (R.obj X)) (F.obj (R.obj Y))).hom =
      F.map (β_ (R.obj X) (R.obj Y)).hom ≫
        Functor.OplaxMonoidal.δ F (R.obj Y) (R.obj X) := by
  have hd (U V : C) : γ.app (U ⊗ V) ≫ F.map (Functor.OplaxMonoidal.δ R U V) ≫
      Functor.OplaxMonoidal.δ F (R.obj U) (R.obj V) =
      Functor.OplaxMonoidal.δ G U V ≫ (γ.app U ⊗ₘ γ.app V) := by
    simpa only [Functor.OplaxMonoidal.comp_δ] using (monoidal_nat_delta γ U V).symm
  have hr : Functor.OplaxMonoidal.δ R X Y ≫ (β_ (R.obj X) (R.obj Y)).hom =
      R.map (β_ X Y).hom ≫ Functor.OplaxMonoidal.δ R Y X := by
    rw [Functor.map_braiding]
    simp only [Category.assoc, Functor.Monoidal.μ_δ, Category.comp_id]
  have hg : Functor.OplaxMonoidal.δ G X Y ≫ (β_ (G.obj X) (G.obj Y)).hom =
      G.map (β_ X Y).hom ≫ Functor.OplaxMonoidal.δ G Y X := by
    rw [Functor.map_braiding]
    simp only [Category.assoc, Functor.Monoidal.μ_δ, Category.comp_id]
  apply (cancel_epi (γ.app (X ⊗ Y) ≫ F.map (Functor.OplaxMonoidal.δ R X Y))).1
  calc
    _ = (Functor.OplaxMonoidal.δ G X Y ≫ (γ.app X ⊗ₘ γ.app Y)) ≫
        (β_ (F.obj (R.obj X)) (F.obj (R.obj Y))).hom := by
      simpa only [Category.assoc] using
        congrArg (fun f ↦ f ≫ (β_ (F.obj (R.obj X)) (F.obj (R.obj Y))).hom) (hd X Y)
    _ = Functor.OplaxMonoidal.δ G X Y ≫ (β_ (G.obj X) (G.obj Y)).hom ≫
        (γ.app Y ⊗ₘ γ.app X) := by
      simpa only [Functor.comp_obj, Category.assoc] using
        congrArg (fun f ↦ Functor.OplaxMonoidal.δ G X Y ≫ f)
          (BraidedCategory.braiding_naturality (γ.app X) (γ.app Y))
    _ = G.map (β_ X Y).hom ≫ Functor.OplaxMonoidal.δ G Y X ≫
        (γ.app Y ⊗ₘ γ.app X) := by
      simpa only [Category.assoc] using congrArg (fun f ↦ f ≫ (γ.app Y ⊗ₘ γ.app X)) hg
    _ = G.map (β_ X Y).hom ≫ γ.app (Y ⊗ X) ≫
        F.map (Functor.OplaxMonoidal.δ R Y X) ≫
        Functor.OplaxMonoidal.δ F (R.obj Y) (R.obj X) := by
      simpa only [Category.assoc] using
        congrArg (fun f ↦ G.map (β_ X Y).hom ≫ f) (hd Y X).symm
    _ = γ.app (X ⊗ Y) ≫ F.map (R.map (β_ X Y).hom) ≫
        F.map (Functor.OplaxMonoidal.δ R Y X) ≫
        Functor.OplaxMonoidal.δ F (R.obj Y) (R.obj X) := by
      simpa only [Functor.comp_map, Category.assoc] using
        congrArg (fun f ↦ f ≫ F.map (Functor.OplaxMonoidal.δ R Y X) ≫
          Functor.OplaxMonoidal.δ F (R.obj Y) (R.obj X))
          (γ.naturality (β_ X Y).hom)
    _ = γ.app (X ⊗ Y) ≫ F.map (Functor.OplaxMonoidal.δ R X Y) ≫
        F.map (β_ (R.obj X) (R.obj Y)).hom ≫
        Functor.OplaxMonoidal.δ F (R.obj Y) (R.obj X) := by
      have hh := congrArg (fun f ↦ F.map f) hr
      simp only [F.map_comp] at hh
      simpa only [Category.assoc] using
        congrArg (fun f ↦ γ.app (X ⊗ Y) ≫ f ≫
          Functor.OplaxMonoidal.δ F (R.obj Y) (R.obj X)) hh.symm
    _ = _ := by simp only [Category.assoc]

/-- A normalized completed comparison inherits ordinary symmetric monoidal coherence.
Source: Stacks Project, algebraization.tex, remark-completed-tensor-product (Tag 099G),
and sites-cohomology.tex, lemma-pullback-tensor-product (Tag 07A4).
(blueprint: lem-pur-reflective-completed-pullback-coherence).

Proof: use the supplied strong symmetric monoidal reflectors R : B -> P and
R' : E -> P', with their normalized cotensorators and units. The Hom bijections
exhibit R as a localization at the arrows it inverts. The ordinary oplax structure,
whose comparison and unit are invertible, makes L strong symmetric monoidal.
Thus G = L followed by R' is strong symmetric monoidal. The hypothesis hPull
makes gamma_X = G(eta_X) invertible. Naturality of eta gives a natural isomorphism
gamma : G -> R followed by F, where F is the displayed completed restriction.
Monoidal localization supplies F with its strong monoidal structure and makes
gamma monoidal.

For local V,W, let a_V : V -> R(V) be the invertible unit, and let
c_(V,W) : V tensor W -> R(V tensor W) be the isomorphism of objects given by
the completed tensor model. The cotensorator of R on V,W equals inverse c_(V,W)
followed by a_V tensor a_W. This follows from its specified cotensorator and the
model's tensor-map equation. Naturality of F's cotensorator at a_V,a_W and
monoidality of gamma therefore give
 gamma_(V tensor W) ; F(inverse c_(V,W)) ; delta_F = delta_G.
The normalization hc gives the same equation for mu_c, transported across the
model's two object equalities. Cancel the invertible prefix to identify delta_F
with that transported mu_c. The corresponding unit model and monoidality of
gamma give the same argument for eta_F and e_c, using hec. Heterogeneous equality
removes precisely those object transports.

For braiding, first work on objects R(X),R(Y). Precompose the desired square by
gamma_(X tensor Y) followed by F(delta_R). Monoidality of gamma, its naturality,
the ordinary braiding equation for G, and the braiding equation for R identify
both paths. Cancel the prefix. Every local V is isomorphic to R(V) via a_V;
naturality of the cotensorator and the braiding transports this square to V,W.
The oplax part of F's strong structure, with the identified maps, is the result. -/
theorem reflectiveCompletedPullbackCoherence
    (P : ObjectProperty B) (P' : ObjectProperty E)
    (L : B ⥤ E) (T : B ⥤ B) (T' : E ⥤ E)
    (η : 𝟭 B ⟶ T) (η' : 𝟭 E ⟶ T')
    (hT : ∀ X : B, P (T.obj X)) (hT' : ∀ X : E, P' (T'.obj X))
    (hbij : ∀ (X Z : B), P Z →
      Function.Bijective (fun f : T.obj X ⟶ Z ↦ η.app X ≫ f))
    (_hbij' : ∀ (X Z : E), P' Z →
      Function.Bijective (fun f : T'.obj X ⟶ Z ↦ η'.app X ≫ f))
    (hη : ∀ X : P.FullSubcategory, IsIso (η.app X.obj))
    (hη' : ∀ X : P'.FullSubcategory, IsIso (η'.app X.obj))
    (hLeft : ∀ X W : B, IsIso (tensorInsertLeft T η X W))
    (hRight : ∀ X W : B, IsIso (tensorInsertRight T η X W))
    (hLeft' : ∀ X W : E, IsIso (tensorInsertLeft T' η' X W))
    (hRight' : ∀ X W : E, IsIso (tensorInsertRight T' η' X W))
    (hPull : ∀ X : B, IsIso (T'.map (L.map (η.app X))))
    (μ : tensor B ⋙ L ≅ (L.prod L) ⋙ tensor E)
    (e : L.obj (𝟙_ B) ≅ 𝟙_ E) (o : L.OplaxMonoidal)
    (ho : ∀ X W : B, o.δ X W = μ.hom.app (X, W)) (he : o.η = e.hom)
    (hβ : ∀ X W : B, μ.hom.app (X, W) ≫ (β_ (L.obj X) (L.obj W)).hom =
      L.map (β_ X W).hom ≫ μ.hom.app (W, X))
    (μc : tensor B ⋙ T ⋙ L ⋙ T' ≅ ((L ⋙ T').prod (L ⋙ T')) ⋙ tensor E ⋙ T')
    (hc : ∀ X W : B, T'.map (L.map (η.app (X ⊗ W))) ≫ μc.hom.app (X, W) =
      T'.map (μ.hom.app (X, W) ≫ (η'.app (L.obj X) ⊗ₘ η'.app (L.obj W))))
    (ec : (L ⋙ T').obj (T.obj (𝟙_ B)) ≅ T'.obj (𝟙_ E))
    (hec : T'.map (L.map (η.app (𝟙_ B))) ≫ ec.hom = T'.map e.hom)
    (m : MonoidalCategory P.FullSubcategory)
    (m' : MonoidalCategory P'.FullSubcategory)
    (s : @SymmetricCategory P.FullSubcategory _ m)
    (s' : @SymmetricCategory P'.FullSubcategory _ m')
    (hm : CompletedConstraintModel P T η hLeft hRight hη m s)
    (hm' : CompletedConstraintModel P' T' η' hLeft' hRight' hη' m' s') :
    letI := m
    letI := m'
    letI := s
    letI := s'
    ∀ (mr : (ObjectProperty.lift P T hT).Monoidal)
      (mr' : (ObjectProperty.lift P' T' hT').Monoidal),
      (letI := mr
       (∀ X Y : B, HEq
         (Functor.OplaxMonoidal.δ (ObjectProperty.lift P T hT) X Y).hom
         (T.map (η.app X ⊗ₘ η.app Y))) ∧
       HEq (Functor.OplaxMonoidal.η (ObjectProperty.lift P T hT)).hom
         (𝟙 (T.obj (𝟙_ B))) ∧
       (∀ X Y : B, Functor.OplaxMonoidal.δ (ObjectProperty.lift P T hT) X Y ≫
         (β_ ((ObjectProperty.lift P T hT).obj X)
           ((ObjectProperty.lift P T hT).obj Y)).hom =
         (ObjectProperty.lift P T hT).map (β_ X Y).hom ≫
           Functor.OplaxMonoidal.δ (ObjectProperty.lift P T hT) Y X)) →
      (letI := mr'
       (∀ X Y : E, HEq
         (Functor.OplaxMonoidal.δ (ObjectProperty.lift P' T' hT') X Y).hom
         (T'.map (η'.app X ⊗ₘ η'.app Y))) ∧
       HEq (Functor.OplaxMonoidal.η (ObjectProperty.lift P' T' hT')).hom
         (𝟙 (T'.obj (𝟙_ E))) ∧
       (∀ X Y : E, Functor.OplaxMonoidal.δ (ObjectProperty.lift P' T' hT') X Y ≫
         (β_ ((ObjectProperty.lift P' T' hT').obj X)
           ((ObjectProperty.lift P' T' hT').obj Y)).hom =
         (ObjectProperty.lift P' T' hT').map (β_ X Y).hom ≫
           Functor.OplaxMonoidal.δ (ObjectProperty.lift P' T' hT') Y X)) →
      CompletedPullbackCoherence P P' L T T' hT' μc ec m m' s s' := by
  classical
  intro mr mr' hr hr'
  let := m
  let := m'
  let := s
  let := s'
  let R := ObjectProperty.lift P T hT
  let R' := ObjectProperty.lift P' T' hT'
  let F := completeInverse P P' L T' hT'
  let : R.Monoidal := mr
  let : R'.Monoidal := mr'
  obtain ⟨hδR, hηR, hβR⟩ := hr
  obtain ⟨hδR', hηR', hβR'⟩ := hr'
  let : R.Braided := braided_of_oplax R hβR
  let : R'.Braided := braided_of_oplax R' hβR'
  let : L.OplaxMonoidal := o
  let : IsIso (Functor.OplaxMonoidal.η L) := by rw [he]; infer_instance
  let (X Y : B) : IsIso (Functor.OplaxMonoidal.δ L X Y) := by
    rw [ho]
    infer_instance
  let : L.Monoidal := Functor.Monoidal.ofOplaxMonoidal L
  let : L.Braided := braided_of_oplax L (by
    intro X Y
    simpa only [ho] using hβ X Y)
  let G : B ⥤ P'.FullSubcategory := L ⋙ R'
  let : G.Monoidal := inferInstance
  let : G.Braided := inferInstance
  let (X : B) : IsIso (G.map (η.app X)) :=
    (ObjectProperty.isIso_hom_iff _).1 (hPull X)
  let γ : G ⟶ R ⋙ F := {
    app X := G.map (η.app X)
    naturality X Y f := by
      change G.map f ≫ G.map (η.app Y) = G.map (η.app X) ≫ G.map (T.map f)
      simpa only [Functor.id_obj, Functor.id_map, ← G.map_comp] using
        congrArg (fun f ↦ G.map f) (η.naturality f) }
  let (X : B) : IsIso (γ.app X) := inferInstance
  let : IsIso γ := NatIso.isIso_of_isIso_app γ
  let χ : R ⋙ F ≅ G := (asIso γ).symm
  let W := (MorphismProperty.isomorphisms P.FullSubcategory).inverseImage R
  let a := reflectorAdjunction P T η hT hbij
  let : R.IsLocalization W := a.isLocalization_leftAdjoint'
  let : Localization.Lifting R W G F := ⟨χ⟩
  let fm : F.Monoidal := Localization.Monoidal.functorMonoidalOfComp R W F G
  let : χ.hom.IsMonoidal := Localization.Monoidal.lifting_isMonoidal R W F G
  let : γ.IsMonoidal := inferInstanceAs χ.inv.IsMonoidal
  let av (V : P.FullSubcategory) : V ≅ R.obj V.obj := by
    let := hη V
    exact P.isoMk (asIso (η.app V.obj))
  let cv (V W : P.FullSubcategory) : V ⊗ W ≅ R.obj (V.obj ⊗ W.obj) :=
    P.isoMk (eqToIso (hm.1 V W))
  have hav (V : P.FullSubcategory) : F.map (av V).hom = γ.app V.obj := rfl
  have hdrl (V W : P.FullSubcategory) :
      Functor.OplaxMonoidal.δ R V.obj W.obj =
        (cv V W).inv ≫ ((av V).hom ⊗ₘ (av W).hom) := by
    apply ObjectProperty.hom_ext
    change (Functor.OplaxMonoidal.δ R V.obj W.obj).hom =
      eqToHom (hm.1 V W).symm ≫ ((av V).hom ⊗ₘ (av W).hom).hom
    have ht := (hδR V.obj W.obj).trans
      (hm.2.1 V W (R.obj V.obj) (R.obj W.obj) (av V).hom (av W).hom).symm
    simpa only [eqToHom_refl, Category.comp_id] using
      cast_hom_of_heq (hm.1 V W).symm rfl _ _ ht
  have hn (V W : P.FullSubcategory) :
      γ.app (V.obj ⊗ W.obj) ≫ F.map (cv V W).inv ≫
        Functor.OplaxMonoidal.δ F V W = Functor.OplaxMonoidal.δ G V.obj W.obj := by
    have hh := monoidal_nat_delta γ V.obj W.obj
    change Functor.OplaxMonoidal.δ G V.obj W.obj ≫
        (γ.app V.obj ⊗ₘ γ.app W.obj) =
      γ.app (V.obj ⊗ W.obj) ≫ F.map (Functor.OplaxMonoidal.δ R V.obj W.obj) ≫
        Functor.OplaxMonoidal.δ F (R.obj V.obj) (R.obj W.obj) at hh
    rw [hdrl, F.map_comp] at hh
    simp only [Category.assoc] at hh
    rw [← Functor.OplaxMonoidal.δ_natural F (av V).hom (av W).hom] at hh
    rw [hav, hav] at hh
    apply (cancel_mono (γ.app V.obj ⊗ₘ γ.app W.obj)).1
    simpa only [Category.assoc] using hh.symm
  have hg (X Y : B) :
      (Functor.OplaxMonoidal.δ G X Y).hom =
        (γ.app (X ⊗ Y)).hom ≫ μc.hom.app (X, Y) ≫
          eqToHom (hm'.1 (G.obj X) (G.obj Y)).symm := by
    have hh := cast_hom_of_heq rfl (hm'.1 (R'.obj (L.obj X)) (R'.obj (L.obj Y)))
      (Functor.OplaxMonoidal.δ R' (L.obj X) (L.obj Y)).hom
      (T'.map (η'.app (L.obj X) ⊗ₘ η'.app (L.obj Y)))
      (hδR' (L.obj X) (L.obj Y))
    change T'.map (o.δ X Y) ≫
        (Functor.OplaxMonoidal.δ R' (L.obj X) (L.obj Y)).hom = _
    rw [ho, hh]
    simp only [eqToHom_refl, Category.id_comp]
    rw [← Category.assoc, ← T'.map_comp, ← hc]
    simp only [Category.assoc]
    rfl
  let ex (V W : P.FullSubcategory) : (F.obj (V ⊗ W)).obj =
      T'.obj (L.obj (T.obj (V.obj ⊗ W.obj))) :=
    congrArg (fun Z ↦ T'.obj (L.obj Z)) (hm.1 V W)
  let ey (V W : P.FullSubcategory) : (F.obj V ⊗ F.obj W).obj =
      T'.obj (T'.obj (L.obj V.obj) ⊗ T'.obj (L.obj W.obj)) :=
    hm'.1 (F.obj V) (F.obj W)
  let dc (V W : P.FullSubcategory) : F.obj (V ⊗ W) ⟶ F.obj V ⊗ F.obj W :=
    ObjectProperty.homMk
      (eqToHom (ex V W) ≫ μc.hom.app (V.obj, W.obj) ≫ eqToHom (ey V W).symm)
  have hcv (V W : P.FullSubcategory) : (F.map (cv V W).inv).hom =
      eqToHom (ex V W).symm := by
    change T'.map (L.map (eqToHom (hm.1 V W).symm)) = _
    simp only [eqToHom_map]
  have hdc (V W : P.FullSubcategory) :
      γ.app (V.obj ⊗ W.obj) ≫ F.map (cv V W).inv ≫ dc V W =
        Functor.OplaxMonoidal.δ G V.obj W.obj := by
    apply ObjectProperty.hom_ext
    change (γ.app (V.obj ⊗ W.obj)).hom ≫ (F.map (cv V W).inv).hom ≫
      (eqToHom (ex V W) ≫ μc.hom.app (V.obj, W.obj) ≫ eqToHom (ey V W).symm) = _
    rw [hcv]
    simp only [eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
    exact (hg V.obj W.obj).symm
  have hδf (V W : P.FullSubcategory) : Functor.OplaxMonoidal.δ F V W = dc V W := by
    apply (cancel_epi (γ.app (V.obj ⊗ W.obj) ≫ F.map (cv V W).inv)).1
    simpa only [Category.assoc] using (hn V W).trans (hdc V W).symm
  let c0 : 𝟙_ P.FullSubcategory ≅ R.obj (𝟙_ B) :=
    P.isoMk (eqToIso hm.2.2.1)
  have hηr : Functor.OplaxMonoidal.η R = c0.inv := by
    apply ObjectProperty.hom_ext
    change (Functor.OplaxMonoidal.η R).hom = eqToHom hm.2.2.1.symm
    simpa only [eqToHom_refl, Category.id_comp, Category.comp_id] using
      cast_hom_of_heq rfl hm.2.2.1 _ (𝟙 (T.obj (𝟙_ B))) hηR
  have hu : γ.app (𝟙_ B) ≫ F.map c0.inv ≫ Functor.OplaxMonoidal.η F =
      Functor.OplaxMonoidal.η G := by
    have hh := monoidal_nat_unit γ
    change γ.app (𝟙_ B) ≫ F.map (Functor.OplaxMonoidal.η R) ≫
      Functor.OplaxMonoidal.η F = Functor.OplaxMonoidal.η G at hh
    rw [hηr] at hh
    exact hh
  have hgu : (Functor.OplaxMonoidal.η G).hom =
      T'.map e.hom ≫ eqToHom hm'.2.2.1.symm := by
    have hh : (Functor.OplaxMonoidal.η R').hom = eqToHom hm'.2.2.1.symm := by
      simpa only [eqToHom_refl, Category.id_comp, Category.comp_id] using
        cast_hom_of_heq rfl hm'.2.2.1 _ (𝟙 (T'.obj (𝟙_ E))) hηR'
    change T'.map o.η ≫ (Functor.OplaxMonoidal.η R').hom = _
    rw [he, hh]
  let ex0 : (F.obj (𝟙_ P.FullSubcategory)).obj = T'.obj (L.obj (T.obj (𝟙_ B))) :=
    congrArg (fun Z ↦ T'.obj (L.obj Z)) hm.2.2.1
  let uc : F.obj (𝟙_ P.FullSubcategory) ⟶ 𝟙_ P'.FullSubcategory :=
    ObjectProperty.homMk (eqToHom ex0 ≫ ec.hom ≫ eqToHom hm'.2.2.1.symm)
  have hc0 : (F.map c0.inv).hom = eqToHom ex0.symm := by
    change T'.map (L.map (eqToHom hm.2.2.1.symm)) = _
    simp only [eqToHom_map]
  have huc : γ.app (𝟙_ B) ≫ F.map c0.inv ≫ uc = Functor.OplaxMonoidal.η G := by
    apply ObjectProperty.hom_ext
    change (γ.app (𝟙_ B)).hom ≫ (F.map c0.inv).hom ≫
      (eqToHom ex0 ≫ ec.hom ≫ eqToHom hm'.2.2.1.symm) = _
    rw [hc0]
    simp only [eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
    change T'.map (L.map (η.app (𝟙_ B))) ≫ ec.hom ≫ _ = _
    rw [← Category.assoc, hec]
    exact hgu.symm
  have hηf : Functor.OplaxMonoidal.η F = uc := by
    apply (cancel_epi (γ.app (𝟙_ B) ≫ F.map c0.inv)).1
    simpa only [Category.assoc] using hu.trans huc.symm
  refine ⟨fm.toOplaxMonoidal, ?_, ?_, ?_⟩
  · intro V W
    rw [hδf]
    exact cast_hom_heq (ex V W) (ey V W) (μc.hom.app (V.obj, W.obj))
  · rw [hηf]
    exact cast_hom_heq ex0 hm'.2.2.1 ec.hom
  · intro V W
    exact oplax_braid_transport F (av V) (av W)
      (lifted_braid_on_images R F G γ V.obj W.obj)

end CategoryTheory.ConstantCompletion
