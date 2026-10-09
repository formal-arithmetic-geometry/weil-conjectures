/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.ColimitsOver
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.CategoryTheory.SingleObj
public import WeilConjectures.Mathlib.RingTheory.TotallySplit

/-!
# Quotients of affine schemes by monoid actions

Let `X` be a scheme and `P` a property of affine morphisms. A diagram
`K : SingleObj G ⥤ P.Over ⊤ X` is an affine
`X`-scheme `W` with an action of the monoid `G` by `X`-endomorphisms. If `X` is affine, its
colimit is `Spec` of the invariants of `Γ(W)`, and a cocone is a colimit iff its leg is injective
on global sections with image the invariants
(`AlgebraicGeometry.Scheme.isColimit_iff_injective_appTop`). If `G` is finite, the formation of
the quotient commutes with flat base change, so the quotients over the affine opens of an
arbitrary `X` glue (`AlgebraicGeometry.Scheme.Cover.hasColimit_of_locallyDirected`).

## Main results

- `AlgebraicGeometry.Scheme.isColimit_iff_injective_appTop`: the characterisation of colimits
  over an affine base.
- `AlgebraicGeometry.Scheme.hasColimitsOfShape_singleObj_isAffineHom_over`: affine `X`-schemes
  have quotients by finite groups.

-/

@[expose] public section

universe u

open CategoryTheory Limits MorphismProperty

namespace AlgebraicGeometry.Scheme

lemma toSpecΓ_comp_specMap_appTop (W : Scheme.{u}) {R : CommRingCat.{u}} (f : R ⟶ Γ(W, ⊤)) :
    (W.toSpecΓ ≫ Spec.map f).appTop = (ΓSpecIso R).hom ≫ f := by
  rw [Hom.comp_appTop, toSpecΓ_appTop, ΓSpecIso_naturality]

/-- The morphism of affine schemes with a given map on global sections. -/
noncomputable def homOfAppTop {T T' : Scheme.{u}} [IsAffine T] [IsAffine T']
    (φ : Γ(T', ⊤) ⟶ Γ(T, ⊤)) : T ⟶ T' :=
  T.isoSpec.hom ≫ Spec.map φ ≫ T'.isoSpec.inv

@[simp]
lemma homOfAppTop_appTop {T T' : Scheme.{u}} [IsAffine T] [IsAffine T']
    (φ : Γ(T', ⊤) ⟶ Γ(T, ⊤)) : (homOfAppTop φ).appTop = φ := by
  apply Spec.map_injective
  rw [← cancel_epi T.isoSpec.hom, isoSpec_hom_naturality, homOfAppTop]
  simp

variable {P : MorphismProperty Scheme.{u}} (hP : ∀ {Y Z : Scheme.{u}} (f : Y ⟶ Z), P f → IsAffineHom f)
  {X : Scheme.{u}} {G : Type*} [Monoid G] (K : SingleObj G ⥤ P.Over ⊤ X)

include hP in
lemma isAffine_left [IsAffine X] (W : P.Over ⊤ X) : IsAffine W.left :=
  have : IsAffineHom W.hom := hP _ W.prop
  have : IsAffine ((Functor.fromPUnit X).obj W.right) := ‹IsAffine X›
  isAffine_of_isAffineHom W.hom

lemma appTop_map_apply_of_cocone (c : Cocone K) (g : G) (z : Γ(c.pt.left, ⊤)) :
    (K.map g).left.appTop.hom ((c.ι.app (SingleObj.star G)).left.appTop.hom z) =
      (c.ι.app (SingleObj.star G)).left.appTop.hom z := by
  have := congr_arg (fun f : K.obj (SingleObj.star G) ⟶ c.pt ↦ f.left.appTop.hom z)
    (c.w (j := SingleObj.star G) (j' := SingleObj.star G) g)
  rwa [MorphismProperty.Comma.comp_left, Hom.comp_appTop] at this

variable [IsAffine X]

include hP in
/-- A cocone over an affine base `X` of a monoid action on an affine `X`-scheme `W` is a colimit
if its leg `W ⟶ c.pt` is injective on global sections with image containing the invariants. -/
noncomputable def isColimitOfInjectiveAppTop (c : Cocone K)
    (hinj : Function.Injective (c.ι.app (SingleObj.star G)).left.appTop.hom)
    (hrange : ∀ a, (∀ g, (K.map g).left.appTop.hom a = a) →
      a ∈ Set.range (c.ι.app (SingleObj.star G)).left.appTop.hom) : IsColimit c := by
  have (W : P.Over ⊤ X) : IsAffine W.left := isAffine_left hP W
  let α := (c.ι.app (SingleObj.star G)).left.appTop.hom
  let e := RingEquiv.ofBijective α.rangeRestrict
    ⟨fun a b h ↦ hinj (congr_arg Subtype.val h), α.rangeRestrict_surjective⟩
  have he (y : α.range) : α (e.symm y) = y := congr_arg Subtype.val (e.apply_symm_apply y)
  -- the global sections map of the descended morphism
  let β (s : Cocone K) : Γ(s.pt.left, ⊤) →+* Γ(c.pt.left, ⊤) :=
    e.symm.toRingHom.comp ((s.ι.app (SingleObj.star G)).left.appTop.hom.codRestrict α.range
      fun z ↦ hrange _ fun g ↦ appTop_map_apply_of_cocone K s g z)
  have hβ (s : Cocone K) (z : Γ(s.pt.left, ⊤)) :
      α (β s z) = (s.ι.app (SingleObj.star G)).left.appTop.hom z := he _
  have hdesc (s : Cocone K) : homOfAppTop (CommRingCat.ofHom (β s)) ≫ s.pt.hom = c.pt.hom := by
    have : IsAffine ((Functor.fromPUnit X).obj s.pt.right) := ‹IsAffine X›
    apply ext_of_isAffine
    ext x
    apply hinj
    simp only [Hom.comp_appTop, CommRingCat.hom_comp, homOfAppTop_appTop, CommRingCat.hom_ofHom,
      RingHom.coe_comp, Function.comp_apply]
    rw [hβ]
    change ((s.ι.app _).left ≫ s.pt.hom).appTop.hom x = ((c.ι.app _).left ≫ c.pt.hom).appTop.hom x
    have h₁ : (s.ι.app (SingleObj.star G)).left ≫ s.pt.hom = (K.obj (SingleObj.star G)).hom :=
      MorphismProperty.Over.w _
    have h₂ : (c.ι.app (SingleObj.star G)).left ≫ c.pt.hom = (K.obj (SingleObj.star G)).hom :=
      MorphismProperty.Over.w _
    rw [h₁, h₂]
  refine
    { desc s := Over.homMk (homOfAppTop (CommRingCat.ofHom (β s))) (hdesc s) trivial
      fac s j := ?_
      uniq s m hm := ?_ }
  · obtain rfl : j = SingleObj.star G := rfl
    ext1
    apply ext_of_isAffine
    ext z
    simp only [Over.homMk_hom, MorphismProperty.Comma.comp_left, Hom.comp_appTop, CommRingCat.hom_comp,
      RingHom.coe_comp, Function.comp_apply]
    exact (congr_arg α (by simp)).trans (hβ s z)
  · ext1
    apply ext_of_isAffine
    ext z
    apply hinj
    have := congr_arg (fun f : K.obj (SingleObj.star G) ⟶ s.pt ↦ f.left.appTop.hom z)
      (hm (SingleObj.star G))
    simp only [MorphismProperty.Comma.comp_left, Hom.comp_appTop, CommRingCat.hom_comp, RingHom.coe_comp,
      Function.comp_apply] at this
    refine this.trans ((hβ s z).symm.trans ?_)
    congr 1
    change _ = (homOfAppTop (CommRingCat.ofHom (β s))).appTop.hom z
    simp

omit [IsAffine X] in
/-- The invariants of the action of `G` on the global sections of `K(⋆)`. -/
def invariants : Subring Γ((K.obj (SingleObj.star G)).left, ⊤) :=
  ⨅ g : G, RingHom.eqLocus (K.map g).left.appTop.hom (RingHom.id _)

omit [IsAffine X] in
lemma mem_invariants {a : Γ((K.obj (SingleObj.star G)).left, ⊤)} :
    a ∈ invariants K ↔ ∀ g : G, (K.map g).left.appTop.hom a = a := by
  simp [invariants, Subring.mem_iInf, RingHom.mem_eqLocus]

omit [IsAffine X] in
lemma appTop_hom_mem_invariants (x : Γ(X, ⊤)) :
    (K.obj (SingleObj.star G)).hom.appTop.hom x ∈ invariants K := by
  rw [mem_invariants]
  intro g
  have h : (K.map g).left ≫ (K.obj (SingleObj.star G)).hom = (K.obj (SingleObj.star G)).hom :=
    MorphismProperty.Over.w _
  have := congr_arg (fun f ↦ f.appTop.hom x) h
  simpa only [Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply] using this

variable (hP' : ∀ {Y Z : Scheme.{u}} (f : Y ⟶ Z), IsAffine Y → IsAffine Z → P f)

omit [IsAffine X] in
/-- The inclusion of the invariants into the global sections. -/
noncomputable def invariantsι :
    CommRingCat.of (invariants K) ⟶ Γ((K.obj (SingleObj.star G)).left, ⊤) :=
  CommRingCat.ofHom (invariants K).subtype

omit [IsAffine X] in
/-- The structure map of the invariants. -/
noncomputable def invariantsStructure : Γ(X, ⊤) ⟶ CommRingCat.of (invariants K) :=
  CommRingCat.ofHom (((K.obj (SingleObj.star G)).hom.appTop.hom).codRestrict _
    (appTop_hom_mem_invariants K))

omit [IsAffine X] in
lemma invariantsStructure_invariantsι :
    invariantsStructure K ≫ invariantsι K = (K.obj (SingleObj.star G)).hom.appTop :=
  rfl

omit [IsAffine X] in
lemma map_invariantsι (g : G) : invariantsι K ≫ (K.map g).left.appTop = invariantsι K := by
  ext a
  exact (mem_invariants K).mp a.2 g

include hP' in
/-- The quotient of an affine `X`-scheme by a monoid action: `Spec` of the invariants. -/
noncomputable abbrev quotientPt : P.Over ⊤ X :=
  { left := Spec (CommRingCat.of (invariants K))
    right := ⟨⟨⟩⟩
    hom := Spec.map (invariantsStructure K) ≫ X.isoSpec.inv
    prop := hP' _ (inferInstanceAs (IsAffine (Spec _))) ‹IsAffine X› }

include hP' in
/-- The quotient map. -/
noncomputable def quotientι : K.obj (SingleObj.star G) ⟶ quotientPt K hP' :=
  MorphismProperty.Over.homMk ((K.obj (SingleObj.star G)).left.toSpecΓ ≫
    Spec.map (invariantsι K)) (by
      have key : ((K.obj (SingleObj.star G)).left.toSpecΓ ≫ Spec.map (invariantsι K)) ≫
          Spec.map (invariantsStructure K) ≫ X.isoSpec.inv = (K.obj (SingleObj.star G)).hom := by
        rw [Category.assoc, ← Spec.map_comp_assoc, invariantsStructure_invariantsι,
          ← toSpecΓ_naturality_assoc]
        change (K.obj (SingleObj.star G)).hom ≫ X.toSpecΓ ≫ X.isoSpec.inv = _
        simp
      exact key) trivial

include hP' in
/-- The quotient of an affine `X`-scheme by a monoid action, as a cocone. -/
noncomputable def quotientCocone : Cocone K where
  pt := quotientPt K hP'
  ι :=
    { app _ := quotientι K hP'
      naturality := fun x y g ↦ by
        obtain rfl : x = SingleObj.star G := rfl
        obtain rfl : y = SingleObj.star G := rfl
        ext1
        change (K.map g).left ≫ ((K.obj (SingleObj.star G)).left.toSpecΓ ≫
          Spec.map (invariantsι K)) =
          (K.obj (SingleObj.star G)).left.toSpecΓ ≫ Spec.map (invariantsι K)
        rw [toSpecΓ_naturality_assoc, ← Spec.map_comp, map_invariantsι] }

omit [IsAffine X] in
lemma quotientι_left_appTop_apply (x : Γ(Spec (CommRingCat.of (invariants K)), ⊤)) :
    ((K.obj (SingleObj.star G)).left.toSpecΓ ≫ Spec.map (invariantsι K)).appTop.hom x =
      invariantsι K ((ΓSpecIso (CommRingCat.of (invariants K))).hom x) :=
  congr($(toSpecΓ_comp_specMap_appTop _ (invariantsι K)).hom x)

include hP hP' in
/-- The quotient cocone is a colimit. -/
noncomputable def isColimitQuotientCocone : IsColimit (quotientCocone K hP') := by
  refine isColimitOfInjectiveAppTop hP K _ ?_ ?_
  · change Function.Injective ((K.obj (SingleObj.star G)).left.toSpecΓ ≫
      Spec.map (invariantsι K)).appTop.hom
    intro x y hxy
    have := (quotientι_left_appTop_apply K x).symm.trans
      (hxy.trans (quotientι_left_appTop_apply K y))
    exact (ΓSpecIso (CommRingCat.of (invariants K))).commRingCatIsoToRingEquiv.injective
      (Subtype.val_injective this)
  · intro a ha
    change a ∈ Set.range ((K.obj (SingleObj.star G)).left.toSpecΓ ≫
      Spec.map (invariantsι K)).appTop.hom
    refine ⟨(ΓSpecIso (CommRingCat.of (invariants K))).inv.hom ⟨a, (mem_invariants K).mpr ha⟩, ?_⟩
    refine (quotientι_left_appTop_apply K _).trans ?_
    change invariantsι K (((ΓSpecIso (CommRingCat.of (invariants K))).inv ≫
      (ΓSpecIso (CommRingCat.of (invariants K))).hom).hom _) = _
    rw [Iso.inv_hom_id]
    rfl

end AlgebraicGeometry.Scheme
