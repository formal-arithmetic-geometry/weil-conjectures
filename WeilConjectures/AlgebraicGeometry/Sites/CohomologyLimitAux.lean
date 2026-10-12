/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.HypercoverDescent
public import WeilConjectures.CategoryTheory.Sites.SemiSimplicialHypercover.CohomologyTruncated

/-!
# Auxiliary results for the continuity of étale cohomology

Tools for `WeilConjectures.AlgebraicGeometry.Sites.CohomologyLimit`:

- `AlgebraicGeometry.Etale.ModuleSheaf.restrictAlong_comp_fst`: the restriction of sections of
  inverse images along a morphism into a base change is the pullback of sections followed by the
  composition isomorphism of inverse images;
- `AlgebraicGeometry.Etale.ModuleSheaf.cochainDifferential_restrictAlong`: restriction of
  sections along morphisms commuting with the face maps commutes with the differentials of the
  cochain complexes;
- `AlgebraicGeometry.exists_hom_descent_stage_of_le`,
  `AlgebraicGeometry.exists_eq_descent_stage_of_le`: descent of morphisms of schemes to an étale
  scheme over an earlier stage, and of equalities of such morphisms;
- `AlgebraicGeometry.TruncatedDescent.toCoskLeft`,
  `AlgebraicGeometry.TruncatedDescent.coskTransition`: the projections from a semi-simplicial
  object over the limit to the coskeletal extension of a descended truncation, and the transition
  maps between the coskeletal extensions at two stages.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

namespace Etale.ModuleSheaf

variable {Λ : Type (u + 1)} [CommRing Λ] {R T T' : Scheme.{u}} (t : T ⟶ R)
  (G : Sheaf R.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (f : T' ⟶ T) (t' : T' ⟶ R)
  (ht' : t' = f ≫ t)

/-- The transition map on sections over `V` is the pullback of sections followed by the
composition isomorphism of inverse images. -/
lemma transition_hom_app_apply (V : T.Etale)
    (s : ((t)^*[(ModuleCat.{u + 1} Λ)].obj G).obj.obj (op V)) :
    (transition t G f t' ht').hom.app (op V) s =
      ((upperStarComp (ModuleCat.{u + 1} Λ) f t t' ht').inv.app G).hom.app _
        (Etale.pullbackSection Λ f _ V s) :=
  rfl

/-- Restriction of sections along a morphism `a : V' ⟶ V ×_T T'` (more precisely along its first
component `V' ⟶ V`) is restriction along `a` of the transition map. -/
lemma restrictAlong_comp_fst {V : T.Etale} {V' : T'.Etale}
    (a : V' ⟶ (MorphismProperty.Over.pullback @Etale ⊤ f).obj V)
    (s : ((t)^*[(ModuleCat.{u + 1} Λ)].obj G).obj.obj (op V)) :
    restrictAlong t G f t' ht' (a.left ≫ pullback.fst V.hom f)
        (by rw [Category.assoc, pullback.condition, ← Category.assoc]
            exact congrArg (· ≫ f) (MorphismProperty.Over.w a)) s =
      ((t')^*[(ModuleCat.{u + 1} Λ)].obj G).obj.map a.op
        ((transition t G f t' ht').hom.app (op V) s) := by
  rw [restrictAlong, ConcreteCategory.comp_apply, ← eq_homToPullback]
  rfl

/-- **Restriction of sections commutes with the differentials of cochain complexes**: for maps
`μ₀ : A_q ⟶ B_q` and `μ₁ : A_{q + 1} ⟶ B_{q + 1}` over `f : T' ⟶ T` commuting with the face maps,
the differential of the restriction along `μ₀` is the restriction along `μ₁` of the differential.
-/
lemma cochainDifferential_restrictAlong {A : SemiSimplicialObject T'.Etale}
    {B : SemiSimplicialObject T.Etale} (q : ℕ) (μ₀ : (A.obj q).left ⟶ (B.obj q).left)
    (hμ₀ : μ₀ ≫ (B.obj q).hom = (A.obj q).hom ≫ f)
    (μ₁ : (A.obj (q + 1)).left ⟶ (B.obj (q + 1)).left)
    (hμ₁ : μ₁ ≫ (B.obj (q + 1)).hom = (A.obj (q + 1)).hom ≫ f)
    (hδ : ∀ i, (A.δ q i).left ≫ μ₀ = μ₁ ≫ (B.δ q i).left)
    (s : ((t)^*[(ModuleCat.{u + 1} Λ)].obj G).obj.obj (op (B.obj q))) :
    (A.cochainDifferential ((t')^*[(ModuleCat.{u + 1} Λ)].obj G).obj q).hom
        (restrictAlong t G f t' ht' μ₀ hμ₀ s) =
      restrictAlong t G f t' ht' μ₁ hμ₁
        ((B.cochainDifferential ((t)^*[(ModuleCat.{u + 1} Λ)].obj G).obj q).hom s) := by
  simp only [SemiSimplicialObject.cochainDifferential, ModuleCat.hom_sum, ModuleCat.hom_zsmul,
    LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_zsmul]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  congr 1
  exact (map_restrictAlong t G f t' ht' (A.δ q i) μ₀ hμ₀ s).trans
    ((ConcreteCategory.congr_hom (restrictAlong_congr t G f t' ht' _ (hδ i)) s).trans
      (restrictAlong_map t G f t' ht' (B.δ q i) μ₁ hμ₁ s).symm)

end Etale.ModuleSheaf

section Stage

variable {I : Type u} [SmallCategory I] {D : I ⥤ Scheme.{u}} {c : Cone D} (hc : IsLimit c)

include hc in
/-- **Morphisms to an étale scheme over an earlier stage descend**: a morphism over `X ⟶ Dᵢ`
from the base change `V` of a quasi-compact quasi-separated étale `Dₖ`-scheme `A` to an étale
`Dᵢ`-scheme `B` (where `e : k ⟶ i`) comes from a morphism `A ×_{Dₖ} Dₖ' ⟶ B` at some stage. -/
lemma exists_hom_descent_stage_of_le [IsCofiltered I]
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)] {k i : I} (e : k ⟶ i)
    {A : (D.obj k).Etale} [CompactSpace A.left] [QuasiSeparatedSpace A.left]
    {B : (D.obj i).Etale} {V : c.pt.Etale} {mA : V.left ⟶ A.left}
    (hA : IsPullback mA V.hom A.hom (c.π.app k)) (φ : V.left ⟶ B.left)
    (hφ : φ ≫ B.hom = V.hom ≫ c.π.app i) :
    ∃ (k' : I) (g : k' ⟶ k) (ψ : pullback A.hom (D.map g) ⟶ B.left),
      ψ ≫ B.hom = pullback.snd A.hom (D.map g) ≫ D.map (g ≫ e) ∧
        pullback.lift mA (V.hom ≫ c.π.app k') (by rw [hA.w, Category.assoc, c.w]) ≫ ψ = φ := by
  obtain ⟨k', g, H⟩ := exists_hom_descent_stage hc hA
    (B := (MorphismProperty.Over.pullback @Etale ⊤ (D.map e)).obj B)
    (pullback.lift φ (V.hom ≫ c.π.app k) (by rw [hφ, Category.assoc, c.w e]))
    (pullback.lift_snd _ _ _)
  obtain ⟨ψ, hψ⟩ := H k' (𝟙 _) g (Category.id_comp _)
  have hw : ψ.left ≫ pullback.snd _ _ = pullback.snd _ _ := MorphismProperty.Over.w ψ
  refine ⟨k', g, ψ.left ≫ pullback.fst _ _ ≫ pullback.fst _ _, ?_, ?_⟩
  · have h2 : pullback.fst ((MorphismProperty.Over.pullback @Etale ⊤ (D.map e)).obj B).hom
        (D.map g) ≫ pullback.snd B.hom (D.map e) =
        pullback.snd ((MorphismProperty.Over.pullback @Etale ⊤ (D.map e)).obj B).hom (D.map g) ≫
          D.map g := pullback.condition
    rw [Category.assoc, Category.assoc, pullback.condition, reassoc_of% h2, reassoc_of% hw,
      Functor.map_comp]
  · rw [← Category.assoc, ← Category.assoc, Category.assoc _ ψ.left, hψ, pullback.lift_fst]

include hc in
/-- **Equalities of morphisms to an étale scheme over an earlier stage descend**: two morphisms
`a b : A ⟶ B` over `Dₖ ⟶ Dᵢ` which agree on the base change of `A` to the limit agree after
restriction along every morphism `Y ⟶ A` over a late enough stage `Dₖ'' ⟶ Dₖ`. -/
lemma exists_eq_descent_stage_of_le [IsCofiltered I]
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)] {k i : I} (e : k ⟶ i) {A : (D.obj k).Etale}
    [CompactSpace A.left] {V : c.pt.Etale} {mA : V.left ⟶ A.left}
    (hA : IsPullback mA V.hom A.hom (c.π.app k)) {B : (D.obj i).Etale} (a b : A.left ⟶ B.left)
    (ha : a ≫ B.hom = A.hom ≫ D.map e) (hb : b ≫ B.hom = A.hom ≫ D.map e)
    (h : mA ≫ a = mA ≫ b) :
    ∃ (k' : I) (g : k' ⟶ k), ∀ (k'' : I) (g' : k'' ⟶ k') {Y : Scheme.{u}} (t : Y ⟶ A.left)
      (y : Y ⟶ D.obj k''), t ≫ A.hom = y ≫ D.map (g' ≫ g) → t ≫ a = t ≫ b := by
  obtain ⟨k', g, H⟩ := exists_eq_descent_stage hc hA (Etale.homToPullback (D.map e) a ha)
    (Etale.homToPullback (D.map e) b hb) (by
      apply pullback.hom_ext
      · simpa using h
      · simp)
  refine ⟨k', g, fun k'' g' Y t y ht ↦ ?_⟩
  have H' := congrArg (fun φ ↦ φ.left ≫ pullback.fst _ _ ≫ pullback.fst _ _) (H k'' g')
  simp only [Etale.overPullback_map_left, pullback.lift_fst_assoc, Category.assoc,
    Etale.homToPullback_left_fst] at H'
  rw [← pullback.lift_fst t y ht, Category.assoc, Category.assoc, H']

end Stage

namespace TruncatedDescent

open SemiSimplicialObject

variable {I : Type u} [SmallCategory I] {D : I ⥤ Scheme.{u}} {c : Cone D}
  {U : SemiSimplicialObject c.pt.Etale} {N : ℕ} {k : I} (d : TruncatedDescent c U N k)

/-- The projection from the term `U_n` of the semi-simplicial object over the limit to the term
of degree `n ≤ N` of the coskeletal extension of the descended truncation. -/
noncomputable def toCoskLeft (n : ℕ) (h : n ≤ N) : (U.obj n).left ⟶ (d.T.cosk.obj n).left :=
  d.m n h ≫ (d.T.coskIso n h).inv.left

lemma toCoskLeft_hom (n : ℕ) (h : n ≤ N) :
    d.toCoskLeft n h ≫ (d.T.cosk.obj n).hom = (U.obj n).hom ≫ c.π.app k := by
  rw [toCoskLeft, Category.assoc, MorphismProperty.Over.w, (d.isPullback n h).w]

lemma isPullback_toCoskLeft (n : ℕ) (h : n ≤ N) :
    IsPullback (d.toCoskLeft n h) (U.obj n).hom (d.T.cosk.obj n).hom (c.π.app k) := by
  refine IsPullback.of_iso (d.isPullback n h) (Iso.refl _)
    (Scheme.Etale.leftIso (d.T.coskIso n h).symm) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_ <;>
    simp [toCoskLeft]

lemma toCoskLeft_δ (n : ℕ) (h : n < N) (i : Fin (n + 2)) :
    (U.δ n i).left ≫ d.toCoskLeft n h.le = d.toCoskLeft (n + 1) h ≫ (d.T.cosk.δ n i).left := by
  simp [toCoskLeft, Truncated.cosk_δ _ n h, reassoc_of% (d.m_δ n h i)]

lemma qcqs_cosk (n : ℕ) (h : n ≤ N) : Scheme.Etale.qcqs _ (d.T.cosk.obj n) :=
  (Scheme.Etale.qcqs _).prop_of_iso (d.T.coskIso n h).symm (d.qcqs n h)

variable [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]

/-- The transition map between the coskeletal extensions of the base changes of a descended
truncation to two stages `h' = g ≫ h`, in degrees `≤ N`. -/
noncomputable def coskTransition {k₁ k₂ : I} (h : k₁ ⟶ k) (g : k₂ ⟶ k₁) (h' : k₂ ⟶ k)
    (hg : g ≫ h = h') (n : ℕ) (hn : n ≤ N) :
    ((d.baseChange h').T.cosk.obj n).left ⟶ ((d.baseChange h).T.cosk.obj n).left :=
  ((d.baseChange h').T.coskIso n hn).hom.left ≫
    pullback.map (d.T.obj n hn).hom (D.map h') (d.T.obj n hn).hom (D.map h) (𝟙 _) (D.map g)
      (𝟙 _) (by simp) (by simp [← hg]) ≫ ((d.baseChange h).T.coskIso n hn).inv.left

variable {k₁ k₂ : I} (h : k₁ ⟶ k) (g : k₂ ⟶ k₁) (h' : k₂ ⟶ k) (hg : g ≫ h = h')

lemma coskTransition_hom (n : ℕ) (hn : n ≤ N) :
    d.coskTransition h g h' hg n hn ≫ ((d.baseChange h).T.cosk.obj n).hom =
      ((d.baseChange h').T.cosk.obj n).hom ≫ D.map g := by
  have e₁ := MorphismProperty.Over.w ((d.baseChange h).T.coskIso n hn).inv
  have e₂ := MorphismProperty.Over.w ((d.baseChange h').T.coskIso n hn).hom
  simp only [Functor.const_obj_obj] at e₁ e₂
  rw [coskTransition, Category.assoc, Category.assoc, e₁, ← e₂, Category.assoc]
  exact congrArg (_ ≫ ·) (pullback.lift_snd _ _ _)

lemma coskTransition_δ (n : ℕ) (hn : n < N) (i : Fin (n + 2)) :
    ((d.baseChange h').T.cosk.δ n i).left ≫ d.coskTransition h g h' hg n hn.le =
      d.coskTransition h g h' hg (n + 1) hn ≫ ((d.baseChange h).T.cosk.δ n i).left := by
  have key : ((d.baseChange h').T.δ n hn i).left ≫
      pullback.map (d.T.obj n hn.le).hom (D.map h') (d.T.obj n hn.le).hom (D.map h) (𝟙 _)
        (D.map g) (𝟙 _) (by simp) (by simp [← hg]) =
      pullback.map (d.T.obj (n + 1) hn).hom (D.map h') (d.T.obj (n + 1) hn).hom (D.map h)
        (𝟙 _) (D.map g) (𝟙 _) (by simp) (by simp [← hg]) ≫
          ((d.baseChange h).T.δ n hn i).left := by
    apply pullback.hom_ext <;> simp [baseChange]
  rw [Truncated.cosk_δ _ n hn, Truncated.cosk_δ _ n hn]
  simp only [coskTransition, Etale.etale_comp_left, Category.assoc,
    Scheme.Etale.inv_hom_id_left_assoc]
  exact congrArg (_ ≫ ·) ((reassoc_of% key) _)

lemma toCoskLeft_coskTransition (n : ℕ) (hn : n ≤ N) :
    (d.baseChange h').toCoskLeft n hn ≫ d.coskTransition h g h' hg n hn =
      (d.baseChange h).toCoskLeft n hn := by
  simp only [toCoskLeft, coskTransition, Category.assoc, Scheme.Etale.inv_hom_id_left_assoc]
  rw [← Category.assoc]
  congr 1
  apply pullback.hom_ext <;> simp [baseChange]

end TruncatedDescent

end AlgebraicGeometry
