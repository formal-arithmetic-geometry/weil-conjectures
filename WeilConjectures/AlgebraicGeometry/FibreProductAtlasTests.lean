/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AlgebraicSpace
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.CategoryTheory.Yoneda
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts

/-!
# Scheme atlases of sheaf fibre products and their scheme tests

Source: Stacks Project, Spaces, Tag 04T9, last paragraph
(blueprint: lem-trf-fibre-product-atlas-tests).

Presheaf pullbacks are computed pointwise. The slice product `prod U V` is the
scheme `U ×_S V`, and its Yoneda maps specify the diagonal test. Projection
equations specify the canonical test isomorphism, including its map to the test scheme.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- The atlas map sends a compatible pair `(u,v)` to `(a(u),b(v))`.
Source: Stacks Project, Spaces, Tag 04T9, last paragraph
(blueprint: lem-trf-fibre-product-atlas-tests). -/
noncomputable def fibreProductAtlasMap {S : Scheme.{u}}
    {F G H : (Over S)ᵒᵖ ⥤ Type u} (f : F ⟶ H) (g : G ⟶ H)
    {U V : Over S} (a : yoneda.obj U ⟶ F) (b : yoneda.obj V ⟶ G) :
    Limits.pullback (a ≫ f) (b ≫ g) ⟶ Limits.pullback f g :=
  Limits.pullback.map (a ≫ f) (b ≫ g) f g a b (𝟙 H)
    (Category.comp_id _) (Category.comp_id _)

private theorem property_of_test {S : Scheme.{u}}
    (P : MorphismProperty Scheme.{u}) [P.RespectsIso]
    {F G : (Over S)ᵒᵖ ⥤ Type u} {a : F ⟶ G}
    (ha : IsRepresentableWith (P.inverseImage (Over.forget S)) a) {T A : Over S}
    {t : yoneda.obj T ⟶ G} {q : yoneda.obj A ⟶ F} {p : A ⟶ T}
    (h : IsPullback q (yoneda.map p) a t) : P p.left := by
  obtain ⟨B, b, r, hb, hp⟩ := ha T t
  let e : A ≅ B := Yoneda.fullyFaithful.preimageIso (h.isoIsPullback _ _ hb)
  have he : e.hom ≫ b = p := by
    apply yoneda.map_injective
    simp [e, yoneda.map_comp, IsPullback.isoIsPullback_hom_snd]
  rw [← he]
  exact (P.cancel_left_of_respectsIso e.hom.left b.left).2 hp

private theorem diagonal_square {C : Type*} [Category C]
    {X Y H Z : C} {l : Z ⟶ X} {r : Z ⟶ Y}
    (hz : IsLimit (BinaryFan.mk l r)) (f : X ⟶ H) (g : Y ⟶ H)
    [HasPullback f g] [HasBinaryProduct H H] :
    IsPullback (Limits.pullback.fst f g ≫ f)
      (hz.lift (BinaryFan.mk (Limits.pullback.fst f g) (Limits.pullback.snd f g)))
      (prod.lift (𝟙 H) (𝟙 H)) (prod.lift (l ≫ f) (r ≫ g)) := by
  let k := hz.lift (BinaryFan.mk (Limits.pullback.fst f g) (Limits.pullback.snd f g))
  have kl : k ≫ l = Limits.pullback.fst f g := hz.fac _ ⟨WalkingPair.left⟩
  have kr : k ≫ r = Limits.pullback.snd f g := hz.fac _ ⟨WalkingPair.right⟩
  have w : (Limits.pullback.fst f g ≫ f) ≫ prod.lift (𝟙 H) (𝟙 H) =
      k ≫ prod.lift (l ≫ f) (r ≫ g) := by
    apply prod.hom_ext <;> simp [← Category.assoc, kl, kr, Limits.pullback.condition]
  apply IsPullback.of_isLimit (PullbackCone.IsLimit.mk w
    (fun s ↦ Limits.pullback.lift (s.snd ≫ l) (s.snd ≫ r) (by
      have h₁ := s.condition =≫ (prod.fst : H ⨯ H ⟶ H)
      have h₂ := s.condition =≫ (prod.snd : H ⨯ H ⟶ H)
      simp only [Category.assoc, prod.lift_fst, prod.lift_snd, Category.comp_id] at h₁ h₂
      simpa only [Category.assoc] using h₁.symm.trans h₂)) ?_ ?_ ?_)
  · intro s
    have h₁ := s.condition =≫ (prod.fst : H ⨯ H ⟶ H)
    simpa using h₁.symm
  · intro s
    apply hz.hom_ext
    intro j
    rcases j with ⟨j⟩
    cases j
    · simpa only [BinaryFan.mk_fst, Category.assoc, kl] using
        Limits.pullback.lift_fst (s.snd ≫ l) (s.snd ≫ r) _
    · simpa only [BinaryFan.mk_snd, Category.assoc, kr] using
        Limits.pullback.lift_snd (s.snd ≫ l) (s.snd ≫ r) _
  · intro s m h₁ h₂
    apply Limits.pullback.hom_ext
    · have := h₂ =≫ l
      simpa [Category.assoc, kl] using this
    · have := h₂ =≫ r
      simpa [Category.assoc, kr] using this

private theorem test_square {S : Scheme.{u}}
    {F G H : (Over S)ᵒᵖ ⥤ Type u} (f : F ⟶ H) (g : G ⟶ H)
    {U V : Over S} (a : yoneda.obj U ⟶ F) (b : yoneda.obj V ⟶ G)
    {T A B : Over S} (t : yoneda.obj T ⟶ Limits.pullback f g)
    (α : A ⟶ T) (β : B ⟶ T)
    (qA : yoneda.obj A ⟶ yoneda.obj U) (qB : yoneda.obj B ⟶ yoneda.obj V)
    (hA : IsPullback qA (yoneda.map α) a (t ≫ Limits.pullback.fst f g))
    (hB : IsPullback qB (yoneda.map β) b (t ≫ Limits.pullback.snd f g)) :
    ∃ w : yoneda.obj (Limits.pullback α β) ⟶ Limits.pullback (a ≫ f) (b ≫ g),
      IsPullback (yoneda.map (Limits.pullback.snd α β ≫ β)) w t
        (fibreProductAtlasMap f g a b) ∧
      w ≫ Limits.pullback.fst (a ≫ f) (b ≫ g) = yoneda.map (Limits.pullback.fst α β) ≫ qA ∧
      w ≫ Limits.pullback.snd (a ≫ f) (b ≫ g) = yoneda.map (Limits.pullback.snd α β) ≫ qB := by
  let l := yoneda.map (Limits.pullback.fst α β)
  let r := yoneda.map (Limits.pullback.snd α β)
  have hp := (IsPullback.of_hasPullback α β).map yoneda
  have hr : l ≫ yoneda.map α = r ≫ yoneda.map β := hp.w
  let w : yoneda.obj (Limits.pullback α β) ⟶ Limits.pullback (a ≫ f) (b ≫ g) :=
    Limits.pullback.lift (l ≫ qA) (r ≫ qB) (by
      calc
        (l ≫ qA) ≫ a ≫ f = l ≫ yoneda.map α ≫ t ≫ Limits.pullback.fst f g ≫ f := by
          simp only [Category.assoc, reassoc_of% hA.w]
        _ = r ≫ yoneda.map β ≫ t ≫ Limits.pullback.snd f g ≫ g := by
          rw [← Category.assoc l, hr]
          simp only [Category.assoc, Limits.pullback.condition]
        _ = (r ≫ qB) ≫ b ≫ g := by simp only [Category.assoc, reassoc_of% hB.w])
  have comm : yoneda.map (Limits.pullback.snd α β ≫ β) ≫ t =
      w ≫ fibreProductAtlasMap f g a b := by
    apply Limits.pullback.hom_ext
    · simp only [Category.assoc, fibreProductAtlasMap, Limits.pullback.map,
        Limits.pullback.lift_fst, Limits.pullback.lift_fst_assoc, w, yoneda.map_comp]
      calc
        _ = l ≫ yoneda.map α ≫ t ≫ Limits.pullback.fst f g := by
          simpa only [Category.assoc] using hr.symm =≫ (t ≫ Limits.pullback.fst f g)
        _ = l ≫ qA ≫ a := by
          simpa only [Category.assoc] using (l ≫= hA.w).symm
    · simp only [Category.assoc, fibreProductAtlasMap, Limits.pullback.map,
        Limits.pullback.lift_snd, Limits.pullback.lift_snd_assoc, w, yoneda.map_comp]
      simpa only [Category.assoc] using (r ≫= hB.w).symm
  refine ⟨w, ?_, Limits.pullback.lift_fst _ _ _, Limits.pullback.lift_snd _ _ _⟩
  apply IsPullback.of_isLimit (PullbackCone.IsLimit.mk comm
    (fun s ↦ hp.lift
      (hA.lift (s.snd ≫ Limits.pullback.fst (a ≫ f) (b ≫ g)) s.fst (by
        have h := s.condition =≫ Limits.pullback.fst f g
        simpa [Category.assoc, fibreProductAtlasMap] using h.symm))
      (hB.lift (s.snd ≫ Limits.pullback.snd (a ≫ f) (b ≫ g)) s.fst (by
        have h := s.condition =≫ Limits.pullback.snd f g
        simpa [Category.assoc, fibreProductAtlasMap] using h.symm))
      (by simp)) ?_ ?_ ?_)
  · intro s
    simp [yoneda.map_comp]
  · intro s
    apply Limits.pullback.hom_ext <;> simp [w, l, r, Category.assoc]
  · intro s m hm₁ hm₂
    apply hp.hom_ext
    · apply hA.hom_ext
      · have h := hm₂ =≫ Limits.pullback.fst (a ≫ f) (b ≫ g)
        simpa [w, l, r, Category.assoc] using h
      · have hm : m ≫ yoneda.map (Limits.pullback.snd α β) ≫ yoneda.map β = s.fst := by
          simpa only [yoneda.map_comp, Category.assoc] using hm₁
        rw [← hr] at hm
        simpa only [Category.assoc, IsPullback.lift_fst, IsPullback.lift_snd] using hm
    · apply hB.hom_ext
      · have h := hm₂ =≫ Limits.pullback.snd (a ≫ f) (b ≫ g)
        simpa [w, l, r, Category.assoc] using h
      · simpa [← Category.assoc, yoneda.map_comp] using hm₁

/-- The diagonal test represents the atlas scheme, and its map to the sheaf
Limits.pullback is representable, surjective and étale. Every scheme test is canonically
represented by the fibre product of the two atlas tests. The three projection
equations characterize the comparison on sections and its map to `T`.

Source: Stacks Project, Spaces, Tag 04T9, last paragraph
(blueprint: lem-trf-fibre-product-atlas-tests).

Proof: (1) Matching pairs glue in `F` and `G`; their images agree in `H` by
separation, so the pointwise Limits.pullback is a sheaf. The atlas map is natural because
`a` and `b` are. (2) Test the representable diagonal of `H` on `U ×_S V`.
The resulting scheme `D` represents triples `(u,v,z)` with
`z = f(a(u)) = g(b(v))`. Forgetting the forced `z` gives the natural isomorphism
with `U ×_H V`, compatibly with the projections to `U` and `V`.
(3) For `t : h_T → F ×_H G`, the scheme tests of `a` and `b` give `A`, `B`
and surjective étale maps `α : A → T`, `β : B → T`. Yoneda full faithfulness
identifies these maps and their chosen representing Limits.pullback squares.
(4) A section of the atlas test is a triple `(τ,u,v)` lifting the two components
of `t`. Compatibility in `H` is automatic. It corresponds bijectively to an
`A`-section and a `B`-section with common image `τ`, hence to an `A ×_T B`-section.
The inverse reads off the two lifts. These assignments commute with restriction
and give the three projection equations below.
(5) Apply the singleton case of [lem-weil-pbc-etale-covering-base-change] to
`α` along `β`: the second projection `A ×_T B → B` is surjective étale.
(6) The singleton case of [lem-weil-pbc-etale-covering-composition] gives the
surjective étale composite to `T`. Since `t` is arbitrary this proves the three
scheme-test properties of the atlas map [def-trf-algebraic-space]. -/
theorem fibreProduct_atlas_tests {S : Scheme.{u}}
    (F G H : Sheaf (Scheme.fppfTopology.over S) (Type u))
    (f : F.obj ⟶ H.obj) (g : G.obj ⟶ H.obj)
    (hH : IsRepresentable (prod.lift (𝟙 H.obj) (𝟙 H.obj)))
    (U V : Over S) (a : yoneda.obj U ⟶ F.obj) (b : yoneda.obj V ⟶ G.obj)
    (hae : IsEtale a) (has : IsSurjective a)
    (hbe : IsEtale b) (hbs : IsSurjective b) :
    (∃ (D : Over S) (e : yoneda.obj D ≅ Limits.pullback (a ≫ f) (b ≫ g))
      (p : D ⟶ prod U V),
      e.hom ≫ Limits.pullback.fst (a ≫ f) (b ≫ g) = yoneda.map (p ≫ prod.fst) ∧
      e.hom ≫ Limits.pullback.snd (a ≫ f) (b ≫ g) = yoneda.map (p ≫ prod.snd) ∧
      IsPullback (e.hom ≫ Limits.pullback.fst (a ≫ f) (b ≫ g) ≫ a ≫ f)
        (yoneda.map p) (prod.lift (𝟙 H.obj) (𝟙 H.obj))
        (prod.lift (yoneda.map (prod.fst : prod U V ⟶ U) ≫ a ≫ f)
          (yoneda.map (prod.snd : prod U V ⟶ V) ≫ b ≫ g))) ∧
    IsRepresentable (fibreProductAtlasMap f g a b) ∧
    IsEtale (fibreProductAtlasMap f g a b) ∧
    IsSurjective (fibreProductAtlasMap f g a b) ∧
    ∀ (T : Over S) (t : yoneda.obj T ⟶ Limits.pullback f g)
      (A B : Over S) (α : A ⟶ T) (β : B ⟶ T)
      (qA : yoneda.obj A ⟶ yoneda.obj U) (qB : yoneda.obj B ⟶ yoneda.obj V),
      IsPullback qA (yoneda.map α) a (t ≫ Limits.pullback.fst f g) →
      IsPullback qB (yoneda.map β) b (t ≫ Limits.pullback.snd f g) →
      ∃ e : yoneda.obj (Limits.pullback α β) ≅ Limits.pullback t (fibreProductAtlasMap f g a b),
        e.hom ≫ Limits.pullback.fst t (fibreProductAtlasMap f g a b) =
          yoneda.map (Limits.pullback.snd α β ≫ β) ∧
        e.hom ≫ Limits.pullback.snd t (fibreProductAtlasMap f g a b) ≫
            Limits.pullback.fst (a ≫ f) (b ≫ g) = yoneda.map (Limits.pullback.fst α β) ≫ qA ∧
        e.hom ≫ Limits.pullback.snd t (fibreProductAtlasMap f g a b) ≫
            Limits.pullback.snd (a ≫ f) (b ≫ g) = yoneda.map (Limits.pullback.snd α β) ≫ qB ∧
        Etale (Limits.pullback.snd α β).left ∧ Surjective (Limits.pullback.snd α β).left ∧
        Etale β.left ∧ Surjective β.left := by
  let hz := isLimitOfHasBinaryProductOfPreservesLimit yoneda U V
  let k := hz.lift (BinaryFan.mk (Limits.pullback.fst (a ≫ f) (b ≫ g))
    (Limits.pullback.snd (a ≫ f) (b ≫ g)))
  have hk₁ : k ≫ yoneda.map prod.fst = Limits.pullback.fst (a ≫ f) (b ≫ g) :=
    hz.fac _ ⟨WalkingPair.left⟩
  have hk₂ : k ≫ yoneda.map prod.snd = Limits.pullback.snd (a ≫ f) (b ≫ g) :=
    hz.fac _ ⟨WalkingPair.right⟩
  obtain ⟨D, p, q, hd, _⟩ := hH (prod U V)
    (prod.lift (yoneda.map prod.fst ≫ a ≫ f) (yoneda.map prod.snd ≫ b ≫ g))
  have hw := diagonal_square hz (a ≫ f) (b ≫ g)
  let e := hd.isoIsPullback _ _ hw
  have he₁ : e.hom ≫ Limits.pullback.fst (a ≫ f) (b ≫ g) ≫ a ≫ f = q := by
    exact hd.isoIsPullback_hom_fst _ _ hw
  have he₂ : e.hom ≫ k = yoneda.map p := hd.isoIsPullback_hom_snd _ _ hw
  have hd' : IsPullback
      (e.hom ≫ Limits.pullback.fst (a ≫ f) (b ≫ g) ≫ a ≫ f)
      (yoneda.map p) (prod.lift (𝟙 H.obj) (𝟙 H.obj))
      (prod.lift (yoneda.map prod.fst ≫ a ≫ f) (yoneda.map prod.snd ≫ b ≫ g)) := by
    rw [he₁]
    exact hd
  have tests : ∀ (T : Over S) (t : yoneda.obj T ⟶ Limits.pullback f g)
      (A B : Over S) (α : A ⟶ T) (β : B ⟶ T)
      (qA : yoneda.obj A ⟶ yoneda.obj U) (qB : yoneda.obj B ⟶ yoneda.obj V),
      IsPullback qA (yoneda.map α) a (t ≫ Limits.pullback.fst f g) →
      IsPullback qB (yoneda.map β) b (t ≫ Limits.pullback.snd f g) →
      ∃ e : yoneda.obj (Limits.pullback α β) ≅
          Limits.pullback t (fibreProductAtlasMap f g a b),
        e.hom ≫ Limits.pullback.fst t (fibreProductAtlasMap f g a b) =
          yoneda.map (Limits.pullback.snd α β ≫ β) ∧
        e.hom ≫ Limits.pullback.snd t (fibreProductAtlasMap f g a b) ≫
            Limits.pullback.fst (a ≫ f) (b ≫ g) = yoneda.map (Limits.pullback.fst α β) ≫ qA ∧
        e.hom ≫ Limits.pullback.snd t (fibreProductAtlasMap f g a b) ≫
            Limits.pullback.snd (a ≫ f) (b ≫ g) = yoneda.map (Limits.pullback.snd α β) ≫ qB ∧
        Etale (Limits.pullback.snd α β).left ∧ Surjective (Limits.pullback.snd α β).left ∧
        Etale β.left ∧ Surjective β.left := by
    intro T t A B α β qA qB hA hB
    have hαe := property_of_test _ hae hA
    have hαs := property_of_test _ has hA
    have hβe := property_of_test _ hbe hB
    have hβs := property_of_test _ hbs hB
    have hp := (IsPullback.of_hasPullback α β).map (Over.forget S)
    have hpe : Etale (Limits.pullback.snd α β).left :=
      MorphismProperty.of_isPullback hp hαe
    have hps : Surjective (Limits.pullback.snd α β).left :=
      MorphismProperty.of_isPullback hp hαs
    obtain ⟨w, h, hw₁, hw₂⟩ := test_square f g a b t α β qA qB hA hB
    refine ⟨h.isoPullback, h.isoPullback_hom_fst, ?_, ?_, hpe, hps, hβe, hβs⟩
    · simpa only [← Category.assoc, h.isoPullback_hom_snd] using hw₁
    · simpa only [← Category.assoc, h.isoPullback_hom_snd] using hw₂
  have alltests : IsRepresentableWith
      (fun _ _ p ↦ Etale p.left ∧ Surjective p.left) (fibreProductAtlasMap f g a b) := by
    intro T t
    obtain ⟨A, α, qA, hA, hα⟩ := hae T (t ≫ Limits.pullback.fst f g)
    obtain ⟨B, β, qB, hB, hβ⟩ := hbe T (t ≫ Limits.pullback.snd f g)
    obtain ⟨e, he, _, _, hpe, hps, hβe, hβs⟩ := tests T t A B α β qA qB hA hB
    have := hpe
    have := hps
    have := hβe
    have := hβs
    refine ⟨Limits.pullback α β, Limits.pullback.snd α β ≫ β,
      e.hom ≫ Limits.pullback.snd _ _, ?_, ?_⟩
    · exact (IsPullback.of_hasPullback t (fibreProductAtlasMap f g a b)).flip.of_iso
        e.symm (Iso.refl _) (Iso.refl _) (Iso.refl _)
        (by simp) (by
          change Limits.pullback.fst _ _ = e.inv ≫ yoneda.map _
          rw [← he]
          simp)
        (by simp) (by simp)
    · change Etale ((Limits.pullback.snd α β).left ≫ β.left) ∧
        Surjective ((Limits.pullback.snd α β).left ≫ β.left)
      exact ⟨inferInstance, inferInstance⟩
  refine ⟨⟨D, e, p, ?_, ?_, hd'⟩, ?_, ?_, ?_, tests⟩
  · rw [← hk₁, ← Category.assoc, he₂, ← yoneda.map_comp]
  · rw [← hk₂, ← Category.assoc, he₂, ← yoneda.map_comp]
  · intro T t
    obtain ⟨A, p, q, h, hp⟩ := alltests T t
    exact ⟨A, p, q, h, trivial⟩
  · intro T t
    obtain ⟨A, p, q, h, hp⟩ := alltests T t
    exact ⟨A, p, q, h, hp.1⟩
  · intro T t
    obtain ⟨A, p, q, h, hp⟩ := alltests T t
    exact ⟨A, p, q, h, hp.2⟩

end AlgebraicGeometry.AlgebraicSpace
