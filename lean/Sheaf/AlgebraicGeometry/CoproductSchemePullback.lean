/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q56
-/
module

public import Sheaf.AlgebraicGeometry.FppfSheafCoproductPartition
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.Gluing

/-!
# Scheme-test pullbacks over coproducts of fppf sheaves

Source: Stacks Project, Spaces, Tags 02WQ, 0F15 and 02WO
(blueprint: lem-trf-coproduct-scheme-pullback).

A pullback square of presheaves expresses the representing bijections, including
their naturality. All scheme morphisms are over the fixed base. Coproducts of schemes
are specified by their universal property, so no bound on the number of empty
summands is imposed by a global coproduct instance.
-/

@[expose] public section

universe u v

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

/-- Even for a large indexing type, a specified scheme coproduct has open injections. -/
private theorem cofan_open {J : Type*} (X : J → Scheme.{u}) (Y : Scheme.{u})
    (j : ∀ i, X i ⟶ Y) (h : IsColimit (Cofan.mk Y j)) (i : J) :
    IsOpenImmersion (j i) := by
  classical
  let k : ∀ a, X a ⟶ X i ⨿ Y := fun a ↦
    if e : a = i then eqToHom (congrArg X e) ≫ coprod.inl else j a ≫ coprod.inr
  let δ : Y ⟶ X i ⨿ Y := Cofan.IsColimit.desc h k
  have fac (a : J) : j a ≫ δ = k a := Cofan.IsColimit.fac h k a
  have hi : j i ≫ δ = coprod.inl := by simpa [k] using fac i
  have hr : δ ≫ coprod.desc (j i) (𝟙 Y) = 𝟙 Y := by
    apply Cofan.IsColimit.hom_ext h
    intro a
    change j a ≫ δ ≫ coprod.desc (j i) (𝟙 Y) = j a ≫ 𝟙 Y
    rw [← Category.assoc, fac]
    by_cases e : a = i
    · subst a; simp [k]
    · simp [k, e, Category.assoc]
  have pb : IsPullback (𝟙 (X i)) (j i) coprod.inl δ := by
    apply IsPullback.mk' (by simpa using hi.symm)
    · intro W f g hf _
      simpa using hf
    · intro W a b hab
      refine ⟨a, by simp, ?_⟩
      have hh := congrArg (fun t ↦ t ≫ coprod.desc (j i) (𝟙 Y)) hab
      simpa [Category.assoc, hr] using hh
  exact MorphismProperty.of_isPullback pb inferInstance

private theorem cofan_covers {J : Type*} (X : J → Scheme.{u}) (Y : Scheme.{u})
    (j : ∀ i, X i ⟶ Y) (h : IsColimit (Cofan.mk Y j)) :
    ∀ y : Y, ∃ i x, j i x = y := by
  let : ∀ i, IsOpenImmersion (j i) := cofan_open X Y j h
  let W : Y.Opens := ⨆ i, (j i).opensRange
  let k : ∀ i, X i ⟶ W.toScheme := fun i ↦
    IsOpenImmersion.lift W.ι (j i) (by
      rintro _ ⟨x, rfl⟩
      exact ⟨⟨j i x, le_iSup (fun i ↦ (j i).opensRange) i ⟨x, rfl⟩⟩, rfl⟩)
  let t := Cofan.IsColimit.desc h k
  have ht : t ≫ W.ι = 𝟙 Y := by
    apply Cofan.IsColimit.hom_ext h
    intro i
    change j i ≫ t ≫ W.ι = j i ≫ 𝟙 Y
    have hf : j i ≫ t = k i := Cofan.IsColimit.fac h k i
    rw [← Category.assoc, hf]
    exact (IsOpenImmersion.lift_fac _ _ _).trans (Category.comp_id _).symm
  intro y
  have hy : y ∈ W := by
    have he := congrArg (fun f : Y ⟶ Y ↦ f y) ht
    change W.ι (t y) = y at he
    exact he ▸ (t y).property
  obtain ⟨i, x, hx⟩ := TopologicalSpace.Opens.mem_iSup.mp hy
  exact ⟨i, x, hx⟩

private theorem cofan_disjoint {J : Type*} (X : J → Scheme.{u}) (Y : Scheme.{u})
    (j : ∀ i, X i ⟶ Y) (h : IsColimit (Cofan.mk Y j))
    {i k : J} (hik : i ≠ k) (x : X i) (y : X k) : j i x ≠ j k y := by
  classical
  let f : ∀ a, X a ⟶ Y ⨿ Y := fun a ↦
    j a ≫ if a = i then coprod.inl else coprod.inr
  let t := Cofan.IsColimit.desc h f
  have hi : j i ≫ t = j i ≫ coprod.inl := by
    simpa [f] using Cofan.IsColimit.fac h f i
  have hk : j k ≫ t = j k ≫ coprod.inr := by
    simpa [f, Ne.symm hik] using Cofan.IsColimit.fac h f k
  intro he
  apply inl_ne_inr Y Y (j i x) (j k y)
  calc
    (coprod.inl : Y ⟶ Y ⨿ Y) (j i x) = t (j i x) :=
      (congrArg (fun f : X i ⟶ Y ⨿ Y ↦ f x) hi).symm
    _ = t (j k y) := congrArg t he
    _ = (coprod.inr : Y ⟶ Y ⨿ Y) (j k y) := congrArg (fun f : X k ⟶ Y ⨿ Y ↦ f y) hk

private theorem exists_cofan_of_small_support {J : Type*} (X : J → Scheme.{u})
    [Small.{u} {i : J // Nonempty (X i)}] :
    ∃ (Y : Scheme.{u}) (j : ∀ i, X i ⟶ Y), Nonempty (IsColimit (Cofan.mk Y j)) := by
  classical
  let K := {i : J // Nonempty (X i)}
  let Y := ∐ fun i : K ↦ X i.1
  let j : ∀ i, X i ⟶ Y := fun i ↦
    if hi : Nonempty (X i) then Sigma.ι (fun i : K ↦ X i.1) ⟨i, hi⟩ else
      @isInitialOfIsEmpty (X i) (not_nonempty_iff.mp hi) |>.to Y
  refine ⟨Y, j, ⟨Cofan.IsColimit.mk _
    (fun c ↦ Sigma.desc (fun i : K ↦ c.inj i.1)) ?_ ?_⟩⟩
  · intro c i
    by_cases hi : Nonempty (X i)
    · simp [j, hi]
    · let : IsEmpty (X i) := not_nonempty_iff.mp hi
      exact isInitialOfIsEmpty.hom_ext _ _
  · intro c m hm
    apply Sigma.hom_ext (f := fun i : K ↦ X i.1)
    intro i
    simpa [j, i.2] using hm i.1

private noncomputable def over_cofan {S : Scheme.{u}} {J : Type*} (X : J → Over S)
    (Y : Over S) (j : ∀ i, X i ⟶ Y)
    (h : IsColimit (Cofan.mk Y.left (fun i ↦ (j i).left))) :
    IsColimit (Cofan.mk Y j) := by
  refine Cofan.IsColimit.mk _ (fun c ↦ Over.homMk
    (Cofan.IsColimit.desc h (fun i ↦ (c.inj i).left)) ?_) ?_ ?_
  · apply Cofan.IsColimit.hom_ext h
    intro i
    change (j i).left ≫ _ ≫ c.pt.hom = (j i).left ≫ Y.hom
    rw [← Category.assoc]
    have hf := Cofan.IsColimit.fac h (fun i ↦ (c.inj i).left) i
    change (j i).left ≫ Cofan.IsColimit.desc h (fun i ↦ (c.inj i).left) =
      (c.inj i).left at hf
    rw [hf, Over.w, Over.w]
  · intro c i
    apply Over.OverMorphism.ext
    exact Cofan.IsColimit.fac h _ i
  · intro c m hm
    apply Over.OverMorphism.ext
    apply Cofan.IsColimit.hom_ext h
    intro i
    have hf := Cofan.IsColimit.fac h (fun i ↦ (c.inj i).left) i
    exact (congrArg CommaMorphism.left (hm i)).trans hf.symm

private theorem lift_representable {S : Scheme.{u}} {A B D : Over S}
    {F : (Over S)ᵒᵖ ⥤ Type (max u v)} (q : D ⟶ A) (r : D ⟶ B)
    (a : uliftYoneda.{v}.obj A ⟶ F) (b : uliftYoneda.{v}.obj B ⟶ F)
    (h : IsPullback (uliftYoneda.{v}.map q) (uliftYoneda.{v}.map r) a b)
    {Z : Over S} (f : Z ⟶ A) (g : Z ⟶ B)
    (w : uliftYoneda.{v}.map f ≫ a = uliftYoneda.{v}.map g ≫ b) :
    ∃ l : Z ⟶ D, l ≫ q = f ∧ l ≫ r = g := by
  let t := h.lift (uliftYoneda.{v}.map f) (uliftYoneda.{v}.map g) w
  refine ⟨uliftYoneda.{v}.preimage t, ?_, ?_⟩
  · apply uliftYoneda.{v}.map_injective
    simp [Functor.map_comp, t]
  · apply uliftYoneda.{v}.map_injective
    simp [Functor.map_comp, t]

private theorem hom_ext_representable {S : Scheme.{u}} {A B D : Over S}
    {F : (Over S)ᵒᵖ ⥤ Type (max u v)} (q : D ⟶ A) (r : D ⟶ B)
    (a : uliftYoneda.{v}.obj A ⟶ F) (b : uliftYoneda.{v}.obj B ⟶ F)
    (h : IsPullback (uliftYoneda.{v}.map q) (uliftYoneda.{v}.map r) a b)
    {Z : Over S} {f g : Z ⟶ D} (hq : f ≫ q = g ≫ q) (hr : f ≫ r = g ≫ r) : f = g := by
  apply uliftYoneda.{v}.map_injective
  apply h.hom_ext
  · simpa only [← Functor.map_comp] using congrArg (uliftYoneda.{v}.map) hq
  · simpa only [← Functor.map_comp] using congrArg (uliftYoneda.{v}.map) hr

private theorem coproduct_squares {S : Scheme.{u}} {I : Type (max u v)}
    (G : I → Sheaf (fppfTopology.over S) (Type (max u v)))
    (C : Sheaf (fppfTopology.over S) (Type (max u v)))
    (c : ∀ i, G i ⟶ C) (hc : IsColimit (Cofan.mk C c))
    (U : I → Over S) (W : Over S) (j : ∀ i, U i ⟶ W)
    (h : IsColimit (Cofan.mk W.left (fun i ↦ (j i).left)))
    (b : ∀ i, uliftYoneda.{v}.obj (U i) ⟶ (G i).obj)
    (p : uliftYoneda.{v}.obj W ⟶ C.obj)
    (hp : ∀ i, uliftYoneda.{v}.map (j i) ≫ p = b i ≫ (c i).hom) :
    ∀ i, IsPullback (uliftYoneda.{v}.map (j i)) (b i) p (c i).hom := by
  classical
  obtain ⟨D, hD, _⟩ := (fppfSheaf_coproduct_partition G).2 C c hc |>.2.1
    W (uliftYonedaEquiv.{v} p)
  have squares := ((fppfSheaf_coproduct_partition G).2 C c hc).2.2.1
    W (uliftYonedaEquiv.{v} p) D hD |>.2.1
  have hs (i : I) : IsPullback
      (uliftYoneda.{v}.map (fppfPartitionInclusion W (D.opens i)))
      (uliftYonedaEquiv.{v}.symm (D.sections i)) p (c i).hom := by
    simpa using squares i
  let t (i : I) := (hs i).lift (uliftYoneda.{v}.map (j i)) (b i) (hp i)
  let l (i : I) : U i ⟶ fppfPartitionOpen W (D.opens i) := uliftYoneda.{v}.preimage (t i)
  have hl (i : I) : l i ≫ fppfPartitionInclusion W (D.opens i) = j i := by
    apply uliftYoneda.{v}.map_injective
    simp [l, Functor.map_comp, t]
  have range_le (i : I) : Set.range (j i).left ⊆ (D.opens i : Set W.left) := by
    rintro _ ⟨x, rfl⟩
    have he := congrArg (fun f : U i ⟶ W ↦ f.left x) (hl i)
    change ((l i).left x).val = (j i).left x at he
    exact he ▸ ((l i).left x).property
  have range_eq (i : I) : Set.range (j i).left =
      Set.range (D.opens i).ι := by
    ext x
    rw [(D.opens i).range_ι]
    refine ⟨fun hx ↦ range_le i hx, ?_⟩
    intro hx
    obtain ⟨k, y, rfl⟩ := cofan_covers (fun i ↦ (U i).left) W.left
      (fun i ↦ (j i).left) h x
    have hik : i = k := by
      by_contra hn
      exact (D.disjoint hn).le_bot ⟨hx, range_le k ⟨y, rfl⟩⟩
    subst k
    exact ⟨y, rfl⟩
  intro i
  let : IsOpenImmersion (j i).left := cofan_open _ _ _ h i
  let e₀ := IsOpenImmersion.isoOfRangeEq (j i).left (D.opens i).ι (range_eq i)
  let e : U i ≅ fppfPartitionOpen W (D.opens i) := Over.isoMk e₀ (by
    change e₀.hom ≫ (D.opens i).ι ≫ W.hom = (U i).hom
    rw [← Category.assoc, IsOpenImmersion.isoOfRangeEq_hom_fac, Over.w])
  have he : e.hom ≫ fppfPartitionInclusion W (D.opens i) = j i := by
    apply Over.OverMorphism.ext
    exact IsOpenImmersion.isoOfRangeEq_hom_fac _ _ (range_eq i)
  have he' : e.hom = l i := by
    apply Over.OverMorphism.ext
    apply (cancel_mono (D.opens i).ι).mp
    exact congrArg CommaMorphism.left (he.trans (hl i).symm)
  have hb : uliftYoneda.{v}.map e.hom ≫
      uliftYonedaEquiv.{v}.symm (D.sections i) = b i := by
    rw [he']
    simp [l, t]
  exact (hs i).of_iso (uliftYoneda.{v}.mapIso e.symm) (Iso.refl _) (Iso.refl _)
    (Iso.refl _) (by
      simp only [Functor.mapIso_hom, Iso.symm_hom]
      rw [← he, Functor.map_comp, ← Category.assoc, ← Functor.map_comp]
      simp) (by
      simp only [Functor.mapIso_hom, Iso.symm_hom]
      rw [← hb, ← Category.assoc, ← Functor.map_comp]
      simp) (by simp) (by simp)

private noncomputable def over_open_lift {S : Scheme.{u}} {X Y Z : Over S}
    (j : X ⟶ Z) (f : Y ⟶ Z) [IsOpenImmersion j.left]
    (h : Set.range f.left ⊆ Set.range j.left) : Y ⟶ X :=
  Over.homMk (IsOpenImmersion.lift j.left f.left h) (by
    rw [← Over.w j, ← Category.assoc, IsOpenImmersion.lift_fac, Over.w])

private theorem over_open_lift_fac {S : Scheme.{u}} {X Y Z : Over S}
    (j : X ⟶ Z) (f : Y ⟶ Z) [IsOpenImmersion j.left]
    (h : Set.range f.left ⊆ Set.range j.left) : over_open_lift j f h ≫ j = f := by
  apply Over.OverMorphism.ext
  exact IsOpenImmersion.lift_fac _ _ _

private theorem cofan_preimage {S : Scheme.{u}} {I : Type*}
    (V U : I → Over S) (V₀ U₀ : Over S) (j : ∀ i, V i ⟶ V₀) (k : ∀ i, U i ⟶ U₀)
    (hj : IsColimit (Cofan.mk V₀.left (fun i ↦ (j i).left)))
    (hk : IsColimit (Cofan.mk U₀.left (fun i ↦ (k i).left)))
    (r : ∀ i, V i ⟶ U i) (R : V₀ ⟶ U₀) (hR : ∀ i, j i ≫ R = r i ≫ k i)
    (i : I) :
    Set.range (j i).left = R.left ⁻¹' Set.range (k i).left := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    refine ⟨(r i).left y, ?_⟩
    exact (congrArg (fun f : V i ⟶ U₀ ↦ f.left y) (hR i)).symm
  · intro hx
    obtain ⟨a, y, rfl⟩ := cofan_covers _ _ _ hj x
    obtain ⟨z, hz⟩ := hx
    have he := congrArg (fun f : V a ⟶ U₀ ↦ f.left y) (hR a)
    have hai : a = i := by
      by_contra hn
      exact cofan_disjoint _ _ _ hk hn ((r a).left y) z (he.symm.trans hz.symm)
    subst a
    exact ⟨y, rfl⟩

private theorem sheaf_cofan_ext {S : Scheme.{u}} {I : Type*}
    (X : I → Over S) (Y : Over S) (j : ∀ i, X i ⟶ Y)
    (h : IsColimit (Cofan.mk Y.left (fun i ↦ (j i).left)))
    (F : Sheaf (fppfTopology.over S) (Type (max u v)))
    {a b : uliftYoneda.{v}.obj Y ⟶ F.obj}
    (hab : ∀ i, uliftYoneda.{v}.map (j i) ≫ a = uliftYoneda.{v}.map (j i) ≫ b) :
    a = b := by
  let : ∀ i, IsOpenImmersion (j i).left := cofan_open _ _ _ h
  let cov : Y.left.OpenCover := Cover.mkOfCovers I (fun i ↦ (X i).left)
    (fun i ↦ (j i).left) (cofan_covers _ _ _ h)
  have mem : Sieve.ofArrows X j ∈ (fppfTopology.over S) Y := by
    rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows]
    exact Precoverage.toGrothendieck_mono zariskiPrecoverage_le_fppfPrecoverage _
      cov.mem_grothendieckTopology
  apply uliftYonedaEquiv.{v}.injective
  apply (F.property.isSheafFor _ mem).isSeparatedFor.ext
  rintro Z f ⟨A, g, _, ⟨i⟩, rfl⟩
  have he := congrArg (uliftYonedaEquiv.{v}) (hab i)
  have he₁ := uliftYonedaEquiv_naturality a (j i).op
  have he₂ := uliftYonedaEquiv_naturality b (j i).op
  simp only [Quiver.Hom.unop_op] at he₁ he₂
  have he' := he₁.trans (he.trans he₂.symm)
  simpa [Functor.map_comp, types_comp_apply] using congrArg (F.obj.map g.op) he'

private theorem clopen_cofan {I : Type*} (Z : Scheme.{u}) (D : I → Z.Opens)
    (hd : Pairwise (fun i j ↦ Disjoint (D i) (D j))) (hc : iSup D = ⊤) :
    Nonempty (IsColimit (Cofan.mk Z (fun i ↦ (D i).ι))) := by
  classical
  let cov : Z.OpenCover := Cover.mkOfCovers I (fun i ↦ (D i).toScheme)
    (fun i ↦ (D i).ι) (fun z ↦ by
      have hz : z ∈ iSup D := by rw [hc]; trivial
      obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hz
      exact ⟨i, ⟨z, hi⟩, rfl⟩)
  have compat (c : Cofan (fun i ↦ (D i).toScheme)) (i j : I) :
      pullback.fst (D i).ι (D j).ι ≫ c.inj i =
        pullback.snd (D i).ι (D j).ι ≫ c.inj j := by
    by_cases he : i = j
    · subst j
      rw [(cancel_mono (D i).ι).mp (pullback.condition)]
    · let : IsEmpty (pullback (D i).ι (D j).ι : Scheme.{u}) := ⟨fun x ↦ by
        have hx := congrArg (fun f : pullback (D i).ι (D j).ι ⟶ Z ↦ f x)
          (pullback.condition)
        change (pullback.fst (D i).ι (D j).ι x).val =
          (pullback.snd (D i).ι (D j).ι x).val at hx
        exact (hd he).le_bot ⟨(pullback.fst (D i).ι (D j).ι x).property,
          hx.symm ▸ (pullback.snd (D i).ι (D j).ι x).property⟩⟩
      exact isInitialOfIsEmpty.hom_ext _ _
  refine ⟨Cofan.IsColimit.mk _ (fun c ↦ cov.glueMorphisms c.inj (compat c))
    (fun c i ↦ cov.ι_glueMorphisms _ _ i) ?_⟩
  intro c m hm
  apply cov.hom_ext
  intro i
  exact (hm i).trans (cov.ι_glueMorphisms _ _ i).symm

private theorem cofan_inverse_partition {S : Scheme.{u}} {I : Type*}
    (U : I → Over S) (W : Over S) (j : ∀ i, U i ⟶ W)
    (h : IsColimit (Cofan.mk W.left (fun i ↦ (j i).left)))
    (hj : ∀ i, IsOpenImmersion (j i).left) {Z : Over S} (b : Z ⟶ W) :
    let D := fun i ↦ b.left ⁻¹ᵁ (@Hom.opensRange _ _ (j i).left (hj i))
    Nonempty (IsColimit (Cofan.mk Z.left (fun i ↦ (D i).ι))) := by
  apply clopen_cofan
  · intro i k hik
    rw [disjoint_iff]
    apply bot_unique
    intro z hz
    obtain ⟨x, hx⟩ := hz.1
    obtain ⟨y, hy⟩ := hz.2
    exact cofan_disjoint _ _ _ h hik x y (hx.trans hy.symm)
  · apply top_unique
    intro z _
    obtain ⟨i, x, hx⟩ := cofan_covers _ _ _ h (b.left z)
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨i, x, hx⟩

private theorem lift_section {S : Scheme.{u}} {A B Z : Over S}
    {F G : (Over S)ᵒᵖ ⥤ Type (max u v)} (j : A ⟶ B)
    (a : uliftYoneda.{v}.obj A ⟶ F) (b : uliftYoneda.{v}.obj B ⟶ G) (c : F ⟶ G)
    (h : IsPullback (uliftYoneda.{v}.map j) a b c)
    (f : Z ⟶ B) (t : uliftYoneda.{v}.obj Z ⟶ F)
    (w : uliftYoneda.{v}.map f ≫ b = t ≫ c) :
    ∃ l : Z ⟶ A, l ≫ j = f ∧ uliftYoneda.{v}.map l ≫ a = t := by
  let k := h.lift (uliftYoneda.{v}.map f) t w
  refine ⟨uliftYoneda.{v}.preimage k, ?_, ?_⟩
  · apply uliftYoneda.{v}.map_injective
    simp [Functor.map_comp, k]
  · simp [k]

private theorem preimage_le_of_square {S : Scheme.{u}} {A B T U Z : Over S}
    {F G : (Over S)ᵒᵖ ⥤ Type (max u v)}
    (j : A ⟶ T) (k : B ⟶ U) [IsOpenImmersion j.left] [IsOpenImmersion k.left]
    (α : uliftYoneda.{v}.obj A ⟶ F) (β : uliftYoneda.{v}.obj B ⟶ F)
    (a : uliftYoneda.{v}.obj T ⟶ G) (b : uliftYoneda.{v}.obj U ⟶ G) (c : F ⟶ G)
    (hj : IsPullback (uliftYoneda.{v}.map j) α a c)
    (hk : IsPullback (uliftYoneda.{v}.map k) β b c)
    (f : Z ⟶ T) (g : Z ⟶ U)
    (w : uliftYoneda.{v}.map f ≫ a = uliftYoneda.{v}.map g ≫ b) :
    g.left ⁻¹ᵁ k.left.opensRange ≤ f.left ⁻¹ᵁ j.left.opensRange := by
  let D := g.left ⁻¹ᵁ k.left.opensRange
  let inc := fppfPartitionInclusion Z D
  let r : fppfPartitionOpen Z D ⟶ B := over_open_lift k (inc ≫ g) (by
    rintro _ ⟨x, rfl⟩
    exact x.property)
  have hr : r ≫ k = inc ≫ g := over_open_lift_fac _ _ _
  obtain ⟨l, hl, _⟩ := lift_section j α a c hj (inc ≫ f)
    (uliftYoneda.{v}.map r ≫ β) (by
      rw [Functor.map_comp, Category.assoc, w, ← Category.assoc, ← Functor.map_comp,
        ← hr, Functor.map_comp, Category.assoc, hk.w, Category.assoc])
  intro z hz
  refine ⟨l.left ⟨z, hz⟩, ?_⟩
  exact congrArg (fun t : fppfPartitionOpen Z D ⟶ T ↦ t.left ⟨z, hz⟩) hl

private theorem pullback_from_lifts {S : Scheme.{u}} {V T U : Over S}
    {F : (Over S)ᵒᵖ ⥤ Type (max u v)} (Q : V ⟶ T) (R : V ⟶ U)
    (a : uliftYoneda.{v}.obj T ⟶ F) (b : uliftYoneda.{v}.obj U ⟶ F)
    (w : uliftYoneda.{v}.map Q ≫ a = uliftYoneda.{v}.map R ≫ b)
    (hex : ∀ (Z : Over S) (f : Z ⟶ T) (g : Z ⟶ U),
      uliftYoneda.{v}.map f ≫ a = uliftYoneda.{v}.map g ≫ b →
        ∃ l : Z ⟶ V, l ≫ Q = f ∧ l ≫ R = g)
    (hext : ∀ (Z : Over S) (f g : Z ⟶ V),
      f ≫ Q = g ≫ Q → f ≫ R = g ≫ R → f = g) :
    IsPullback (uliftYoneda.{v}.map Q) (uliftYoneda.{v}.map R) a b := by
  apply IsPullback.of_forall_isPullback_app
  intro Z
  apply (Types.isPullback_iff _ _ _ _).2
  refine ⟨NatTrans.congr_app w Z, ?_, ?_⟩
  · intro x y hxy
    apply ULift.ext
    exact hext Z.unop x.down y.down (congrArg ULift.down hxy.1)
      (congrArg ULift.down hxy.2)
  · intro f g hfg
    obtain ⟨l, hl, hr⟩ := hex Z.unop f.down g.down (by
      apply uliftYonedaEquiv.{v}.injective
      simpa [uliftYonedaEquiv, ← NatTrans.naturality_apply] using hfg)
    exact ⟨ULift.up l, congrArg ULift.up hl, congrArg ULift.up hr⟩

/-- The coproduct of component scheme pullbacks represents the scheme-test pullback
over a coproduct of arbitrary fppf sheaves. The projections have their prescribed
restrictions, and a compatible pair of test maps has identical inverse-image opens.
Source: Stacks, Spaces, Tag 02WQ, final atlas assertion, expanded using Tags 0F15
and 02WO (blueprint: lem-trf-coproduct-scheme-pullback).

Proof:
1. Form the scheme coproduct of the V_i (lem-weil-pbc-scheme-coproduct-family).
   For a larger index universe, first omit the empty V_i: choosing a point of each
   remaining V_i and mapping it to T gives an injection of their indices into T,
   since the T_i are disjoint. Thus this subfamily has a small index type, its
   coproduct exists in the scheme universe, and adding the empty schemes changes
   no mapping property. The coproduct gives Q and R with the stated restrictions.
   On the inverse images of its
   summands, the component pullback squares give aQ = pR. The sheaf condition,
   or the uniqueness in lem-trf-fppf-sheaf-coproduct-partition, gives equality globally.
2. For a pair (f,u) with af = pu, the clopen-partition lemma identifies the partitions
   of the two equal sections with the inverse images of T_i and U_i. Its uniqueness
   gives equality of these opens. Its injectivity of each coprojection then gives
   the equality of component sections on this common inverse-image open W_i.
3. The component pullback square gives a unique map W_i to V_i. Compose with the
   coproduct inclusions and glue using lem-weil-pbc-scheme-morphism-gluing; overlaps
   are empty. Gluing uniqueness proves that its two projections are f and u.
4. This construction inverts v mapped to (Qv,Rv). For the other composite, the
   inverse image of U_i under Rv is the inverse image of V_i under v, by disjointness
   of the coproduct summands. On each such open, uniqueness in the component
   pullback identifies the recovered map with v; morphism-gluing uniqueness finishes.
5. Associativity makes the forward bijections natural in every test morphism, so
   their inverses are natural too. This is the asserted presheaf pullback square.
   The empty-index case forces T and U to be empty and gives the empty representing
   scheme. Empty summands have empty inverse images and unique lifts.

The open-immersion witnesses in the conclusion are consequences of the given
scheme coproduct, included only to form its image opens without extra hypotheses.
Equality of opens is equality of their associated open subscheme structures. -/
theorem fppfSheaf_coproduct_scheme_pullback {S : Scheme.{u}} {I : Type (max u v)}
    (G : I → Sheaf (fppfTopology.over S) (Type (max u v)))
    (C : Sheaf (fppfTopology.over S) (Type (max u v)))
    (c : ∀ i, G i ⟶ C) (hc : IsColimit (Cofan.mk C c))
    (U : I → Over S) (Ucop : Over S) (ιU : ∀ i, U i ⟶ Ucop)
    (hU : IsColimit (Cofan.mk Ucop.left (fun i ↦ (ιU i).left)))
    (pᵢ : ∀ i, uliftYoneda.{v}.obj (U i) ⟶ (G i).obj)
    (p : uliftYoneda.{v}.obj Ucop ⟶ C.obj)
    (hp : ∀ i, uliftYoneda.{v}.map (ιU i) ≫ p = pᵢ i ≫ (c i).hom)
    (T : Over S) (a : C.obj.obj (op T)) (d : FppfCoproductPartition G T)
    (hd : d.MapsTo c a) (V : I → Over S)
    (q : ∀ i, V i ⟶ fppfPartitionOpen T (d.opens i)) (r : ∀ i, V i ⟶ U i)
    (hV : ∀ i, IsPullback (uliftYoneda.{v}.map (q i))
      (uliftYoneda.{v}.map (r i)) (uliftYonedaEquiv.{v}.symm (d.sections i)) (pᵢ i)) :
    ∃ (hιU : ∀ i, IsOpenImmersion (ιU i).left)
      (Vcop : Over S) (ιV : ∀ i, V i ⟶ Vcop),
      Nonempty (IsColimit (Cofan.mk Vcop.left (fun i ↦ (ιV i).left))) ∧
      ∃ (Q : Vcop ⟶ T) (R : Vcop ⟶ Ucop),
        (∀ i, ιV i ≫ Q = q i ≫ fppfPartitionInclusion T (d.opens i)) ∧
        (∀ i, ιV i ≫ R = r i ≫ ιU i) ∧
        IsPullback (uliftYoneda.{v}.map Q) (uliftYoneda.{v}.map R)
          (uliftYonedaEquiv.{v}.symm a) p ∧
        ∀ (Z : Over S) (f : Z ⟶ T) (b : Z ⟶ Ucop),
          uliftYoneda.{v}.map f ≫ uliftYonedaEquiv.{v}.symm a =
            uliftYoneda.{v}.map b ≫ p →
          ∀ i, b.left ⁻¹ᵁ (@Scheme.Hom.opensRange _ _ (ιU i).left (hιU i)) =
            f.left ⁻¹ᵁ d.opens i := by
  classical
  let hιU : ∀ i, IsOpenImmersion (ιU i).left := cofan_open _ _ _ hU
  let : ∀ i, IsOpenImmersion (ιU i).left := hιU
  have hTi := ((fppfSheaf_coproduct_partition G).2 C c hc).2.2.1 T a d hd |>.2.1
  have hUi := coproduct_squares G C c hc U Ucop ιU hU pᵢ p hp
  let K := {i : I // Nonempty ((V i).left)}
  let point (i : K) : T.left := ((q i.1).left (Classical.choice i.2)).val
  have point_mem (i : K) : point i ∈ d.opens i.1 :=
    ((q i.1).left (Classical.choice i.2)).property
  have point_inj : Function.Injective point := by
    intro i j he
    apply Subtype.ext
    by_contra hn
    exact (d.disjoint hn).le_bot ⟨point_mem i, he ▸ point_mem j⟩
  let : Small.{u} K := small_of_injective point_inj
  obtain ⟨W, j, ⟨hj⟩⟩ := exists_cofan_of_small_support (fun i ↦ (V i).left)
  let base : W ⟶ S := Cofan.IsColimit.desc hj (fun i ↦ (V i).hom)
  let Vcop : Over S := Over.mk base
  let ιV : ∀ i, V i ⟶ Vcop := fun i ↦ Over.homMk (j i)
    (Cofan.IsColimit.fac hj (fun i ↦ (V i).hom) i)
  have hVc : IsColimit (Cofan.mk Vcop.left (fun i ↦ (ιV i).left)) := hj
  let hVo := over_cofan V Vcop ιV hVc
  let Q : Vcop ⟶ T := Cofan.IsColimit.desc hVo
    (fun i ↦ q i ≫ fppfPartitionInclusion T (d.opens i))
  let R : Vcop ⟶ Ucop := Cofan.IsColimit.desc hVo (fun i ↦ r i ≫ ιU i)
  have hQ (i : I) : ιV i ≫ Q = q i ≫ fppfPartitionInclusion T (d.opens i) :=
    Cofan.IsColimit.fac hVo _ i
  have hR (i : I) : ιV i ≫ R = r i ≫ ιU i := Cofan.IsColimit.fac hVo _ i
  have w : uliftYoneda.{v}.map Q ≫ uliftYonedaEquiv.{v}.symm a =
      uliftYoneda.{v}.map R ≫ p := by
    apply sheaf_cofan_ext V Vcop ιV hVc C
    intro i
    rw [← Category.assoc, ← Functor.map_comp, hQ, Functor.map_comp, Category.assoc,
      (hTi i).w, ← Category.assoc, (hV i).w, Category.assoc, ← hp i,
      ← Category.assoc, ← Functor.map_comp, ← hR, Functor.map_comp, Category.assoc]
  have hex (Z : Over S) (f : Z ⟶ T) (b : Z ⟶ Ucop)
      (hab : uliftYoneda.{v}.map f ≫ uliftYonedaEquiv.{v}.symm a =
        uliftYoneda.{v}.map b ≫ p) :
      ∃ l : Z ⟶ Vcop, l ≫ Q = f ∧ l ≫ R = b := by
    let D : I → Z.left.Opens := fun i ↦ b.left ⁻¹ᵁ (ιU i).left.opensRange
    let E : I → Over S := fun i ↦ fppfPartitionOpen Z (D i)
    let inc : ∀ i, E i ⟶ Z := fun i ↦ fppfPartitionInclusion Z (D i)
    obtain ⟨hD⟩ := cofan_inverse_partition U Ucop ιU hU hιU b
    let hE := over_cofan E Z inc hD
    let bi : ∀ i, E i ⟶ U i := fun i ↦ over_open_lift (ιU i) (inc i ≫ b) (by
      rintro _ ⟨x, rfl⟩; exact x.property)
    have hbi (i : I) : bi i ≫ ιU i = inc i ≫ b := over_open_lift_fac _ _ _
    have local_lift (i : I) : ∃ l : E i ⟶ V i,
        l ≫ q i ≫ fppfPartitionInclusion T (d.opens i) = inc i ≫ f ∧
        l ≫ r i = bi i := by
      obtain ⟨fi, hfi, hsec⟩ := lift_section
        (fppfPartitionInclusion T (d.opens i))
        (uliftYonedaEquiv.{v}.symm (d.sections i))
        (uliftYonedaEquiv.{v}.symm a) (c i).hom (hTi i)
        (inc i ≫ f) (uliftYoneda.{v}.map (bi i) ≫ pᵢ i) (by
          rw [Functor.map_comp, Category.assoc, hab, ← Category.assoc,
            ← Functor.map_comp, ← hbi, Functor.map_comp, Category.assoc,
            hp, Category.assoc])
      obtain ⟨l, hl, hr⟩ := lift_representable (q i) (r i)
        (uliftYonedaEquiv.{v}.symm (d.sections i)) (pᵢ i) (hV i) fi (bi i) hsec
      exact ⟨l, by rw [← Category.assoc, hl, hfi], hr⟩
    choose li hli hri using local_lift
    let l : Z ⟶ Vcop := Cofan.IsColimit.desc hE (fun i ↦ li i ≫ ιV i)
    have hl (i : I) : inc i ≫ l = li i ≫ ιV i := Cofan.IsColimit.fac hE _ i
    refine ⟨l, ?_, ?_⟩
    · apply Cofan.IsColimit.hom_ext hE
      intro i
      change inc i ≫ l ≫ Q = inc i ≫ f
      rw [← Category.assoc, hl, Category.assoc, hQ]
      exact hli i
    · apply Cofan.IsColimit.hom_ext hE
      intro i
      change inc i ≫ l ≫ R = inc i ≫ b
      rw [← Category.assoc, hl, Category.assoc, hR, ← Category.assoc, hri, hbi]
  have hext (Z : Over S) (f g : Z ⟶ Vcop)
      (hq : f ≫ Q = g ≫ Q) (hr : f ≫ R = g ≫ R) : f = g := by
    let : ∀ i, IsOpenImmersion (ιV i).left := cofan_open _ _ _ hVc
    let D : I → Z.left.Opens := fun i ↦ (f ≫ R).left ⁻¹ᵁ (ιU i).left.opensRange
    let E : I → Over S := fun i ↦ fppfPartitionOpen Z (D i)
    let inc : ∀ i, E i ⟶ Z := fun i ↦ fppfPartitionInclusion Z (D i)
    obtain ⟨hD⟩ := cofan_inverse_partition U Ucop ιU hU hιU (f ≫ R)
    let hE := over_cofan E Z inc hD
    have range_f (i : I) : Set.range (inc i ≫ f).left ⊆ Set.range (ιV i).left := by
      rw [cofan_preimage V U Vcop Ucop ιV ιU hVc hU r R hR i]
      rintro _ ⟨x, rfl⟩
      exact x.property
    have range_g (i : I) : Set.range (inc i ≫ g).left ⊆ Set.range (ιV i).left := by
      rw [cofan_preimage V U Vcop Ucop ιV ιU hVc hU r R hR i]
      rintro _ ⟨x, rfl⟩
      have he := congrArg (fun t : Z ⟶ Ucop ↦ t.left x.val) hr
      change R.left (g.left x.val) ∈ Set.range (ιU i).left
      change R.left (f.left x.val) = R.left (g.left x.val) at he
      have hx : R.left (f.left x.val) ∈ Set.range (ιU i).left := x.property
      exact he ▸ hx
    let fi : ∀ i, E i ⟶ V i := fun i ↦ over_open_lift (ιV i) (inc i ≫ f) (range_f i)
    let gi : ∀ i, E i ⟶ V i := fun i ↦ over_open_lift (ιV i) (inc i ≫ g) (range_g i)
    have hfi (i : I) : fi i ≫ ιV i = inc i ≫ f := over_open_lift_fac _ _ _
    have hgi (i : I) : gi i ≫ ιV i = inc i ≫ g := over_open_lift_fac _ _ _
    apply Cofan.IsColimit.hom_ext hE
    intro i
    change inc i ≫ f = inc i ≫ g
    rw [← hfi, ← hgi]
    congr 1
    apply hom_ext_representable (q i) (r i)
      (uliftYonedaEquiv.{v}.symm (d.sections i)) (pᵢ i) (hV i)
    · apply Over.OverMorphism.ext
      apply (cancel_mono (d.opens i).ι).mp
      have hh : fi i ≫ q i ≫ fppfPartitionInclusion T (d.opens i) =
          gi i ≫ q i ≫ fppfPartitionInclusion T (d.opens i) := by
        rw [← hQ, ← Category.assoc, hfi, Category.assoc, hq,
          ← Category.assoc, ← hgi, Category.assoc, hQ]
      exact congrArg CommaMorphism.left hh
    · apply Over.OverMorphism.ext
      apply (cancel_mono (ιU i).left).mp
      have hh : fi i ≫ r i ≫ ιU i = gi i ≫ r i ≫ ιU i := by
        rw [← hR, ← Category.assoc, hfi, Category.assoc, hr,
          ← Category.assoc, ← hgi, Category.assoc, hR]
      exact congrArg CommaMorphism.left hh
  refine ⟨hιU, Vcop, ιV, ⟨hVc⟩, Q, R, hQ, hR,
    pullback_from_lifts Q R _ p w hex hext, ?_⟩
  intro Z f b hab i
  let : IsOpenImmersion (fppfPartitionInclusion T (d.opens i)).left :=
    inferInstanceAs (IsOpenImmersion (d.opens i).ι)
  have h₁ := preimage_le_of_square (fppfPartitionInclusion T (d.opens i)) (ιU i)
    _ _ _ _ (c i).hom (hTi i) (hUi i) f b hab
  have h₂ := preimage_le_of_square (ιU i) (fppfPartitionInclusion T (d.opens i))
    _ _ _ _ (c i).hom (hUi i) (hTi i) b f hab.symm
  simpa [fppfPartitionInclusion] using le_antisymm h₁ h₂

end AlgebraicGeometry.Scheme
