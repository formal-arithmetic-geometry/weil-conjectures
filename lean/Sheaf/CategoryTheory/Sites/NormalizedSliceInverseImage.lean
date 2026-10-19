/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group X8
-/
module

public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.Pullback
import Mathlib.CategoryTheory.Sites.Limits
import WeilConjectures.Mathlib.CategoryTheory.Functor.Flat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Types
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts

/-!
# The unit-normalized inverse image on a slice site

Source: Stacks Project, Sites, Tag 03CF, lemma-localize-morphism
(blueprint: lem-pur-unit-normalized-slice-inverse-image).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem sigma_ext {C : Type u} [SmallCategory C] {U X : C}
    (H : (Over U)ᵒᵖ ⥤ Type (u + 1)) {a b : X ⟶ U}
    {s : H.obj (op (Over.mk a))} {t : H.obj (op (Over.mk b))}
    (h : a = b) (hs : H.map (eqToHom (by rw [h])).op t = s) :
    (⟨a, s⟩ : Σ a : X ⟶ U, H.obj (op (Over.mk a))) = ⟨b, t⟩ := by
  subst b
  simpa using congrArg
    (fun t : H.obj (op (Over.mk a)) ↦
      (⟨a, t⟩ : Σ a : X ⟶ U, H.obj (op (Over.mk a)))) hs.symm

private def sigmaRestriction {C : Type u} [SmallCategory C] {U X Y : C}
    (H : (Over U)ᵒᵖ ⥤ Type (u + 1)) (b : Y ⟶ X)
    (z : Σ a : X ⟶ U, H.obj (op (Over.mk a))) :
    Σ a : Y ⟶ U, H.obj (op (Over.mk a)) :=
  ⟨b ≫ z.1, H.map (Over.homMk b rfl).op z.2⟩

private def sigmaPresheaf {C : Type u} [SmallCategory C] {U : C}
    (H : (Over U)ᵒᵖ ⥤ Type (u + 1)) : Cᵒᵖ ⥤ Type (u + 1) where
  obj X := Σ a : X.unop ⟶ U, H.obj (op (Over.mk a))
  map b := ↾(sigmaRestriction H b.unop)
  map_id X := by
    apply ConcreteCategory.hom_ext
    intro z
    rcases z with ⟨a, s⟩
    dsimp [sigmaRestriction]
    apply sigma_ext H (Category.id_comp _)
    congr 2
    congr 1
    apply Quiver.Hom.unop_inj
    ext
    simp

  map_comp b c := by
    apply ConcreteCategory.hom_ext
    intro z
    rcases z with ⟨a, s⟩
    dsimp [sigmaRestriction]
    apply sigma_ext H (Category.assoc _ _ _)
    simp only [← Functor.map_comp_apply]
    congr 2
    congr 1
    apply Quiver.Hom.unop_inj
    ext
    simp

private def sigmaProjection {C : Type u} [SmallCategory C] {U : C}
    (H : (Over U)ᵒᵖ ⥤ Type (u + 1)) : sigmaPresheaf H ⟶ uliftYoneda.{u + 1}.obj U where
  app _ := ↾fun z ↦ ⟨z.1⟩
  naturality _ _ _ := rfl

private def sigmaMap {C : Type u} [SmallCategory C] {U : C}
    {H H' : (Over U)ᵒᵖ ⥤ Type (u + 1)} (f : H ⟶ H') : sigmaPresheaf H ⟶ sigmaPresheaf H' where
  app _ := ↾fun z ↦ ⟨z.1, f.app _ z.2⟩
  naturality X Y b := by
    apply ConcreteCategory.hom_ext
    rintro ⟨a, s⟩
    dsimp [sigmaPresheaf, sigmaRestriction]
    congr 1
    exact f.naturality_apply
      (Over.homMk b.unop rfl : Over.mk (b.unop ≫ a) ⟶ Over.mk a).op s

private def sigmaFunctor {C : Type u} [SmallCategory C]
    (K : GrothendieckTopology C) (U : C) :
    Sheaf (K.over U) (Type (u + 1)) ⥤ Over (uliftYoneda.{u + 1}.obj U) where
  obj H := Over.mk (sigmaProjection H.obj)
  map f := Over.homMk (sigmaMap f.hom) (by rfl)
  map_id H := by
    apply Over.OverMorphism.ext
    rfl
  map_comp f g := by
    apply Over.OverMorphism.ext
    rfl

private def pairSection {C : Type u} [SmallCategory C] {U : C}
    (H : (Over U)ᵒᵖ ⥤ Type (u + 1)) (X : Over U) (s : H.obj (op X)) :
    (sigmaPresheaf H).obj (op X.left) :=
  ⟨X.hom, H.map (Over.homMk (𝟙 X.left) (by simp) : Over.mk X.hom ⟶ X).op s⟩

private theorem pairSection_naturality {C : Type u} [SmallCategory C] {U : C}
    (H : (Over U)ᵒᵖ ⥤ Type (u + 1)) {X Y : Over U} (b : X ⟶ Y) (s : H.obj (op Y)) :
    (sigmaPresheaf H).map b.left.op (pairSection H Y s) =
      pairSection H X (H.map b.op s) := by
  dsimp [sigmaPresheaf, sigmaRestriction, pairSection]
  apply sigma_ext H (Over.w b)
  simp only [← Functor.map_comp_apply]
  congr 2
  congr 1
  apply Quiver.Hom.unop_inj
  ext
  simp


private noncomputable abbrev bigPull {D : Type u} [SmallCategory D]
    (K : GrothendieckTopology D) (U : C ⥤ D) :=
  U.op.lan ⋙ presheafToSheaf K (Type (u + 1))

private noncomputable def bigUnit {D : Type u} [SmallCategory D]
    (K : GrothendieckTopology D) (U : C ⥤ D) (F : Cᵒᵖ ⥤ Type (u + 1)) :
    F ⟶ U.op ⋙ ((bigPull K U).obj F).obj :=
  U.op.lanUnit.app F ≫ Functor.whiskerLeft U.op (toSheafify K (U.op.lan.obj F))

private theorem bigUnit_naturality {D : Type u} [SmallCategory D]
    (K : GrothendieckTopology D) (U : C ⥤ D)
    {F G : Cᵒᵖ ⥤ Type (u + 1)} (f : F ⟶ G) :
    f ≫ bigUnit K U G = bigUnit K U F ≫
      Functor.whiskerLeft U.op ((bigPull K U).map f).hom := by
  ext X x
  have h₁ := ConcreteCategory.congr_hom (congr_app (U.op.lanUnit.naturality f) X) x
  have h₂ := ConcreteCategory.congr_hom
    (congr_app (toSheafify_naturality K (U.op.lan.map f)) (U.op.obj X))
    ((U.op.lanUnit.app F).app X x)
  change (toSheafify K (U.op.lan.obj G)).app (U.op.obj X)
    ((U.op.lanUnit.app G).app X (f.app X x)) = _
  change (U.op.lanUnit.app G).app X (f.app X x) =
    (U.op.lan.map f).app (U.op.obj X) ((U.op.lanUnit.app F).app X x) at h₁
  rw [h₁]
  exact h₂

private def normalizedFibre {D : Type u} [SmallCategory D]
    {K : GrothendieckTopology D} (V : D) (B : Sheaf K (Type (u + 1)))
    (z : B.obj.obj (op V)) (F : Over B) : Subfunctor (F.left.over V).obj where
  obj X := {s | F.hom.hom.app (op X.unop.left) s = B.obj.map X.unop.hom.op z}
  map {X Y} b s hs := by
    change F.hom.hom.app _ (F.left.obj.map b.unop.left.op s) = _
    rw [NatTrans.naturality_apply, hs, ← Functor.map_comp_apply, ← op_comp, Over.w]

private theorem normalizedFibre_isSheaf {D : Type u} [SmallCategory D]
    {K : GrothendieckTopology D} (V : D) (B : Sheaf K (Type (u + 1)))
    (z : B.obj.obj (op V)) (F : Over B) :
    Presheaf.IsSheaf (K.over V) (normalizedFibre V B z F).toFunctor := by
  apply (isSheaf_iff_isSheaf_of_type _ _).mpr
  apply (Subfunctor.isSheaf_iff _
    ((isSheaf_iff_isSheaf_of_type _ _).mp (F.left.over V).property)).mpr
  intro X s hs
  change F.hom.hom.app _ s = _
  apply (((isSheaf_iff_isSheaf_of_type _ _).mp (B.over V).property).isSeparated _ hs).ext
  intro Y b hb
  change B.obj.map b.left.op (F.hom.hom.app _ s) = _
  rw [← NatTrans.naturality_apply]
  change F.hom.hom.app _ (F.left.obj.map b.left.op s) = _
  change F.hom.hom.app _ (F.left.obj.map b.left.op s) =
    B.obj.map b.left.op (B.obj.map X.unop.hom.op z)
  rw [← Functor.map_comp_apply, ← op_comp, Over.w]
  exact hb

private noncomputable def normalizedFibreFunctor {D : Type u} [SmallCategory D]
    {K : GrothendieckTopology D} (V : D) (B : Sheaf K (Type (u + 1)))
    (z : B.obj.obj (op V)) : Over B ⥤ Sheaf (K.over V) (Type (u + 1)) where
  obj F := ⟨(normalizedFibre V B z F).toFunctor, normalizedFibre_isSheaf V B z F⟩
  map {F G} f := ⟨{
    app X := ↾fun s ↦ ⟨f.left.hom.app _ s.val, by
      have h := congrArg (fun t ↦ t.hom.app (op X.unop.left) s.val) (Over.w f)
      exact h.trans s.property⟩
    naturality X Y b := by
      apply ConcreteCategory.hom_ext
      intro s
      apply Subtype.ext
      exact f.left.hom.naturality_apply b.unop.left.op s.val }⟩

private def sigmaSecond (V : C) (F : Sheaf J (Type (u + 1))) :
    sigmaPresheaf (F.over V).obj ⟶ F.obj where
  app _ := ↾fun x ↦ x.2
  naturality _ _ _ := rfl


private noncomputable def sigmaFanIsLimit (V : C) (F : Sheaf J (Type (u + 1))) :
    IsLimit (BinaryFan.mk (sigmaProjection (F.over V).obj) (sigmaSecond V F)) := by
  refine BinaryFan.isLimitMk (fun s ↦ ?_) ?_ ?_ ?_
  · exact {
      app X := ↾fun z ↦ ⟨(s.fst.app X z).down, s.snd.app X z⟩
      naturality X Y f := by
        apply ConcreteCategory.hom_ext
        intro z
        apply Sigma.ext (congrArg ULift.down (s.fst.naturality_apply f z))
        have hn : s.snd.app Y (s.pt.map f z) = F.obj.map f (s.snd.app X z) :=
          s.snd.naturality_apply f z
        exact heq_of_eq hn }
  · intro s
    ext X z
    rfl
  · intro s
    ext X z
    rfl
  · intro s m h₁ h₂
    ext X z
    have h₁' := ConcreteCategory.congr_hom (congr_app h₁ X) z
    have h₂' := ConcreteCategory.congr_hom (congr_app h₂ X) z
    dsimp at h₁' h₂' ⊢
    apply Sigma.ext (congrArg ULift.down h₁')
    exact heq_of_eq h₂'

private noncomputable abbrev normalizedSlice
    {D : Type u} [SmallCategory D] (K : GrothendieckTopology D) (U : C ⥤ D) (V : C) :=
  sigmaFunctor J V ⋙ Over.post (bigPull K U) ⋙
    normalizedFibreFunctor (U.obj V) ((bigPull K U).obj (uliftYoneda.{u + 1}.obj V))
      ((bigUnit K U (uliftYoneda.{u + 1}.obj V)).app (op V) ⟨𝟙 V⟩)

private noncomputable def normalizedSliceUnit
    {D : Type u} [SmallCategory D] (K : GrothendieckTopology D) (U : C ⥤ D) (V : C)
    (F : Sheaf (J.over V) (Type (u + 1))) :
    F.obj ⟶ (Over.post U).op ⋙ ((normalizedSlice K U V).obj F).obj where
  app X := ↾fun x ↦ ⟨(bigUnit K U (sigmaPresheaf F.obj)).app (op X.unop.left)
    (pairSection F.obj X.unop x), by
      have hn := ConcreteCategory.congr_hom
        (congr_app (bigUnit_naturality K U (sigmaProjection F.obj)) (op X.unop.left))
        (pairSection F.obj X.unop x)
      have hb := (bigUnit K U (uliftYoneda.{u + 1}.obj V)).naturality_apply
        X.unop.hom.op ⟨𝟙 V⟩
      exact hn.symm.trans (by simpa [uliftYoneda, pairSection, sigmaProjection] using hb)⟩
  naturality X Y f := by
    apply ConcreteCategory.hom_ext
    intro x
    apply Subtype.ext
    symm
    exact ((bigUnit K U (sigmaPresheaf F.obj)).naturality_apply f.unop.left.op
      (pairSection F.obj X.unop x)).symm.trans
        (congrArg ((bigUnit K U (sigmaPresheaf F.obj)).app (op Y.unop.left))
          (pairSection_naturality F.obj f.unop x))

private theorem normalizedSliceUnit_naturality
    {D : Type u} [SmallCategory D] (K : GrothendieckTopology D) (U : C ⥤ D) (V : C)
    {F G : Sheaf (J.over V) (Type (u + 1))} (f : F ⟶ G) :
    f.hom ≫ normalizedSliceUnit K U V G = normalizedSliceUnit K U V F ≫
      Functor.whiskerLeft (Over.post U).op ((normalizedSlice K U V).map f).hom := by
  ext X x
  apply Subtype.ext
  have h := ConcreteCategory.congr_hom
    (congr_app (bigUnit_naturality K U (sigmaMap f.hom)) (op X.unop.left))
    (pairSection F.obj X.unop x)
  change (bigUnit K U (sigmaPresheaf G.obj)).app (op X.unop.left)
    (pairSection G.obj X.unop (f.hom.app X x)) =
      ((bigPull K U).map (sigmaMap f.hom)).hom.app (op (U.obj X.unop.left))
        ((bigUnit K U (sigmaPresheaf F.obj)).app (op X.unop.left)
          (pairSection F.obj X.unop x))
  refine (congrArg ((bigUnit K U (sigmaPresheaf G.obj)).app (op X.unop.left)) ?_).trans h
  dsimp [sigmaMap, pairSection]
  congr 1
  exact (f.hom.naturality_apply _ x).symm

private noncomputable def normalizedSliceComparison
    {D : Type u} [SmallCategory D] (K : GrothendieckTopology D) (U : C ⥤ D) (V : C) :
    J.overPullback (Type (u + 1)) V ⋙ normalizedSlice K U V ⟶
      Functor.sheafPullbackConstruction.sheafPullback U (Type (u + 1)) J K ⋙
        K.overPullback (Type (u + 1)) (U.obj V) where
  app F := ⟨{
    app X := ↾fun x ↦ ((bigPull K U).map (sigmaSecond V F)).hom.app (op X.unop.left) x.val
    naturality X Y f := by
      apply ConcreteCategory.hom_ext
      intro x
      exact (((bigPull K U).map (sigmaSecond V F)).hom.naturality_apply
        f.unop.left.op x.val) }⟩
  naturality {F G} f := by
    ext X x
    have h : sigmaMap ((J.overPullback (Type (u + 1)) V).map f).hom ≫
        sigmaSecond V G = sigmaSecond V F ≫ f.hom := by
      ext Y y
      rfl
    have hh := congrArg (fun t ↦ ((bigPull K U).map t).hom.app (op X.unop.left) x.val) h
    simp only [Functor.map_comp] at hh
    change ((bigPull K U).map (sigmaSecond V G)).hom.app (op X.unop.left)
      (((bigPull K U).map (sigmaMap
        ((J.overPullback (Type (u + 1)) V).map f).hom)).hom.app (op X.unop.left) x.val) =
      ((bigPull K U).map f.hom).hom.app (op X.unop.left)
        (((bigPull K U).map (sigmaSecond V F)).hom.app (op X.unop.left) x.val)
    exact hh

private theorem normalizedSliceComparison_unit
    {D : Type u} [SmallCategory D] (K : GrothendieckTopology D) (U : C ⥤ D) (V : C)
    (F : Sheaf J (Type (u + 1))) (W : C) (q : W ⟶ V) (x : F.obj.obj (op W)) :
    ((normalizedSliceComparison K U V).app F).hom.app (op (Over.mk (U.map q)))
        ((normalizedSliceUnit K U V (F.over V)).app (op (Over.mk q)) x) =
      (bigUnit K U F.obj).app (op W) x := by
  have h := (ConcreteCategory.congr_hom
    (congr_app (bigUnit_naturality K U (sigmaSecond V F)) (op W)) ⟨q, x⟩).symm
  simpa [normalizedSliceComparison, normalizedSliceUnit, sigmaSecond, pairSection] using h

private theorem fibre_snd_bijective {A B P : Type (u + 1)}
    (f : P ⟶ A) (g : P ⟶ B) (h : IsLimit (BinaryFan.mk f g)) (a : A) :
    Function.Bijective (fun x : {x : P | f x = a} ↦ g x.val) := by
  constructor
  · intro x y hxy
    have he : (↾fun _ : PUnit.{u + 2} ↦ x.val) = (↾fun _ ↦ y.val) := by
      apply BinaryFan.IsLimit.hom_ext h
      · ext t
        exact x.property.trans y.property.symm
      · ext t
        exact hxy
    exact Subtype.ext (ConcreteCategory.congr_hom he PUnit.unit)
  · intro b
    let c := BinaryFan.mk (↾fun _ : PUnit.{u + 2} ↦ a) (↾fun _ ↦ b)
    refine ⟨⟨h.lift c PUnit.unit, ?_⟩, ?_⟩
    · exact ConcreteCategory.congr_hom (h.fac c ⟨WalkingPair.left⟩) PUnit.unit
    · exact ConcreteCategory.congr_hom (h.fac c ⟨WalkingPair.right⟩) PUnit.unit

private theorem normalizedSliceComparison_isIso
    {D : Type u} [SmallCategory D] (K : GrothendieckTopology D) (U : C ⥤ D)
    [RepresentablyFlat U] (V : C) : IsIso (normalizedSliceComparison (J := J) K U V) := by
  have : AB5OfSize.{u, u} (Type (u + 1)) :=
    AB5OfSize_shrink.{u, u, u + 1, u + 1} _
  have : PreservesFiniteLimits (bigPull K U) := inferInstance
  have hi (F : Sheaf J (Type (u + 1))) :
      IsIso ((normalizedSliceComparison K U V).app F).hom := by
    have ha (X : (Over (U.obj V))ᵒᵖ) :
        IsIso (((normalizedSliceComparison K U V).app F).hom.app X) := by
      apply (isIso_iff_bijective _).2
      let E := bigPull K U ⋙ sheafToPresheaf K (Type (u + 1)) ⋙
        (evaluation Dᵒᵖ (Type (u + 1))).obj (op X.unop.left)
      exact fibre_snd_bijective _ _
        (mapIsLimitOfPreservesOfIsLimit E _ _ (sigmaFanIsLimit V F)) _
    exact NatIso.isIso_of_isIso_app _
  have ha (F : Sheaf J (Type (u + 1))) :
      IsIso ((normalizedSliceComparison K U V).app F) := by
    let : IsIso ((sheafToPresheaf _ _).map
      ((normalizedSliceComparison K U V).app F)) := hi F
    exact isIso_of_reflects_iso _ (sheafToPresheaf _ _)
  exact NatIso.isIso_of_isIso_app _

/-- The slice comparison for the actual Kan-extension/sheafification inverse image,
normalized on the actual Kan-extension/sheafification units.

Source: Stacks Project, `sites.tex`, Tag 03CF, lemma-localize-morphism, the diagram
of inverse images and the final product calculation.

Proof: For a slice sheaf A, form the presheaf S(A)(W) = Σ(q : W → V), A(q),
with its projection to the lifted representable hV. Apply P = Lan(U.op) followed
by sheafification. Define H(A) over an arrow r : Y → U(V) as the fibre of
P(S(A))(Y) → P(hV)(Y) at the restriction along r of the image of idV under
the actual unit. Naturality and separatedness of P(hV) make these fibres a sheaf.
The actual unit on the pair (q,x) defines η; unit naturality proves both its
fibre condition and its naturality in A. For a global F, S(F.over V) is a binary
product of hV and F.obj, with the explicit first and second projections.
Representable flatness makes P preserve this binary product. Its fibre over
any base section is therefore isomorphic to P(F.obj), by the second projection.
These isomorphisms are natural in F. Unit naturality for the second projection
says exactly that the isomorphism takes η(q,x) to the actual global unit on x.
All data are constructed explicitly; no existence theorem chooses them.
(blueprint: lem-pur-unit-normalized-slice-inverse-image). -/
theorem unit_normalized_slice_inverse_image
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (U : C ⥤ D) [U.IsContinuous J K] [RepresentablyFlat U] (V : C) :
    ∃ (H : Sheaf (J.over V) (Type (u + 1)) ⥤
          Sheaf (K.over (U.obj V)) (Type (u + 1)))
      (η : ∀ F : Sheaf (J.over V) (Type (u + 1)),
        F.obj ⟶ (Over.post U).op ⋙ (H.obj F).obj)
      (e : J.overPullback (Type (u + 1)) V ⋙ H ≅
        Functor.sheafPullbackConstruction.sheafPullback U (Type (u + 1)) J K ⋙
          K.overPullback (Type (u + 1)) (U.obj V)),
      (∀ {F G : Sheaf (J.over V) (Type (u + 1))} (f : F ⟶ G),
        f.hom ≫ η G = η F ≫ Functor.whiskerLeft (Over.post U).op (H.map f).hom) ∧
      ∀ (F : Sheaf J (Type (u + 1))) (W : C) (q : W ⟶ V) (x : F.obj.obj (op W)),
        (e.hom.app F).hom.app (op (Over.mk (U.map q)))
            ((η (F.over V)).app (op (Over.mk q)) x) =
          ((U.op.lanAdjunction (Type (u + 1))).unit.app F.obj ≫
            Functor.whiskerLeft U.op (toSheafify K (U.op.lan.obj F.obj))).app (op W) x := by
  let := normalizedSliceComparison_isIso (J := J) K U V
  let e := asIso (normalizedSliceComparison (J := J) K U V)
  exact ⟨normalizedSlice K U V, normalizedSliceUnit K U V, e,
    fun f ↦ normalizedSliceUnit_naturality K U V f,
    fun F W q x ↦ normalizedSliceComparison_unit K U V F W q x⟩

end CategoryTheory
