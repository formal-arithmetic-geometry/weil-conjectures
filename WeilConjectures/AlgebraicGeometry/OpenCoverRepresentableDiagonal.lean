/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AlgebraicSpace
public import Mathlib.CategoryTheory.Subfunctor.Image
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Representability
import Mathlib.CategoryTheory.Sites.SubcanonicalOver
import Mathlib.CategoryTheory.Sites.Limits

/-!
# Representable diagonals descend along an open cover

Source: Stacks Project, Spaces, Tag 02WR, first two paragraphs of the proof
(blueprint: lem-trf-open-cover-representable-diagonal).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

private theorem preimage_square {C : Type*} [Category C] {P Q : C ⥤ Type u}
    (H : Subfunctor Q) (a : P ⟶ Q) :
    IsPullback (H.fromPreimage a) (H.preimage a).ι H.ι a := by
  apply IsPullback.of_forall_isPullback_app
  intro W
  rw [Types.isPullback_iff]
  refine ⟨by rfl, ?_, ?_⟩
  · intro x y h
    exact Subtype.ext h.2
  · intro x y h
    exact ⟨⟨y, by change a.app W y ∈ H.obj W; rw [← h]; exact x.2⟩,
      Subtype.ext h.symm, rfl⟩

private theorem opens_of_open {S : Scheme.{u}} {P : (Over S)ᵒᵖ ⥤ Type u}
    (H : Subfunctor P)
    (hH : IsRepresentableWith (fun _ _ p ↦ IsOpenImmersion p.left) H.ι)
    (T : Over S) (x : P.obj (op T)) :
    ∃ U : T.left.Opens, ∀ (W : Over S) (a : W ⟶ T),
      P.map a.op x ∈ H.obj (op W) ↔ Set.range a.left ⊆ U := by
  obtain ⟨U, p, q, hp, hopen⟩ := hH T (yonedaEquiv.symm x)
  have : IsOpenImmersion p.left := hopen
  refine ⟨p.left.opensRange, fun W a ↦ ?_⟩
  rw [Scheme.Hom.coe_opensRange]
  constructor
  · intro h
    obtain ⟨d, -, hd⟩ := Types.exists_of_isPullback (hp.app (op W)) ⟨_, h⟩ a rfl
    change d ≫ p = a at hd
    rw [← hd, Over.comp_left, Scheme.Hom.comp_base, TopCat.coe_comp]
    exact Set.range_comp_subset_range _ _
  · intro h
    let d : W ⟶ U := Over.homMk (IsOpenImmersion.lift p.left a.left h) (by
      rw [← Over.w p, IsOpenImmersion.lift_fac_assoc, Over.w a])
    have hd : d ≫ p = a := by ext; exact IsOpenImmersion.lift_fac _ _ _
    have he := congr_arg (fun φ ↦ φ.app (op W) d) hp.w
    have hx : P.map a.op x = (q.app (op W) d).1 := by
      rw [← hd]
      exact he.symm
    rw [hx]
    exact (q.app (op W) d).2

private theorem open_preimage {S : Scheme.{u}} {P Q : (Over S)ᵒᵖ ⥤ Type u}
    (H : Subfunctor Q) (a : P ⟶ Q)
    (hH : IsRepresentableWith (fun _ _ p ↦ IsOpenImmersion p.left) H.ι) :
    IsRepresentableWith (fun _ _ p ↦ IsOpenImmersion p.left) (H.preimage a).ι := by
  intro T b
  obtain ⟨U, p, q, hp, hopen⟩ := hH T (b ≫ a)
  let r := (preimage_square H a).lift q (yoneda.map p ≫ b) (by simpa using hp.w)
  refine ⟨U, p, r, ?_, hopen⟩
  exact IsPullback.of_right' hp (preimage_square H a)

private theorem relative_open {S : Scheme.{u}} {P Q : (Over S)ᵒᵖ ⥤ Type u}
    (a : P ⟶ Q)
    (ha : IsRepresentableWith (fun _ _ p ↦ IsOpenImmersion p.left) a) :
    (IsOpenImmersion.inverseImage (Over.forget S)).relative uliftYoneda.{0} a := by
  apply MorphismProperty.relative.of_exists
  intro T b
  let e := uliftYonedaIsoYoneda.{0, u, u + 1} (C := Over S)
  obtain ⟨U, p, q, hp, hopen⟩ := ha T ((e.app T).inv ≫ b)
  refine ⟨U, (e.app U).hom ≫ q, p, ?_, hopen⟩
  exact hp.of_iso' (e.app U) (Iso.refl _) (e.app T) (Iso.refl _)
    (by simp) (by ext; rfl) (by simp) (by simp)

private theorem piece_representable {S : Scheme.{u}} {F : (Over S)ᵒᵖ ⥤ Type u}
    (H : Subfunctor F)
    (hopen : IsRepresentableWith (fun _ _ p ↦ IsOpenImmersion p.left) H.ι)
    (hdiag : ∀ (T T' : Over S) (a : yoneda.obj T ⟶ H.toFunctor)
      (b : yoneda.obj T' ⟶ H.toFunctor), (Limits.pullback a b).IsRepresentable)
    (T T' : Over S) (a : yoneda.obj T ⟶ F) (b : yoneda.obj T' ⟶ F) :
    (H.preimage (pullback.fst a b ≫ a)).toFunctor.IsRepresentable := by
  obtain ⟨U, p, q, hp, -⟩ := hopen T a
  obtain ⟨V, p', q', hp', -⟩ := hopen T' b
  let R := Limits.pullback q q'
  let r : R ⟶ H.toFunctor := pullback.fst q q' ≫ q
  let g : R ⟶ Limits.pullback a b := pullback.lift
    (pullback.fst q q' ≫ yoneda.map p) (pullback.snd q q' ≫ yoneda.map p') (by
      rw [Category.assoc, ← hp.w, ← Category.assoc, pullback.condition,
        Category.assoc, hp'.w, Category.assoc])
  have hrg : IsPullback r g H.ι (pullback.fst a b ≫ a) := by
    apply IsPullback.of_isLimit' ⟨by simp [r, g, hp.w]⟩
    refine PullbackCone.IsLimit.mk _ (fun s ↦ ?_) ?_ ?_ ?_
    · exact pullback.lift
        (hp.lift s.fst (s.snd ≫ pullback.fst a b) (by simpa using s.condition))
        (hp'.lift s.fst (s.snd ≫ pullback.snd a b) (by
          simpa [Category.assoc, pullback.condition] using s.condition)) (by simp)
    · intro s
      simp [r]
    · intro s
      apply pullback.hom_ext <;> simp [g]
    · intro s m hm hn
      apply pullback.hom_ext
      · apply hp.hom_ext
        · simpa [r] using hm
        · simpa [g] using hn =≫ pullback.fst a b
      · apply hp'.hom_ext
        · simpa [r, pullback.condition] using hm
        · simpa [g] using hn =≫ pullback.snd a b
  have : R.IsRepresentable := hdiag U V q q'
  exact isRepresentable_of_natIso R
    (hrg.isoIsPullback _ _ (preimage_square H (pullback.fst a b ≫ a)))

private theorem diagonal_of_pairs {S : Scheme.{u}} {F : (Over S)ᵒᵖ ⥤ Type u}
    (hF : ∀ (T T' : Over S) (a : yoneda.obj T ⟶ F) (b : yoneda.obj T' ⟶ F),
      (Limits.pullback a b).IsRepresentable) :
    IsRepresentable (prod.lift (𝟙 F) (𝟙 F)) := by
  have h : yoneda.relativelyRepresentable (Limits.diag F) := by
    apply Functor.relativelyRepresentable.diag_of_map_from_obj
    intro T a T' b
    have := hF T T' a b
    let e := (Limits.pullback a b).reprW
    refine ⟨_, yoneda.preimage (e.hom ≫ pullback.snd a b),
      e.hom ≫ pullback.fst a b, ?_⟩
    rw [yoneda.map_preimage]
    exact (IsPullback.of_hasPullback a b).of_iso' e (Iso.refl _) (Iso.refl _)
      (Iso.refl _) (by simp) (by simp) (by simp) (by simp)
  intro T a
  obtain ⟨U, p, q, hp⟩ := h a
  exact ⟨U, p, q, hp, trivial⟩

/-- Open subsheaves with representable diagonals that cover fppf locally give a
representable diagonal. The conclusions include the covering of each scheme test,
the representable open pieces of each pairwise fibre product, their covering on
all scheme tests, and representability of the entire fibre product.

Source: Stacks Project, Spaces, Tag 02WR, first two proof paragraphs, and the
pairwise test for the diagonal in lemma-representable-diagonal
(blueprint: lem-trf-open-cover-representable-diagonal).

Proof:
1. For a section of F on T, an fppf local lift into H i factors through its
   representing open V i, by def-pc-open-subfunctor. Joint surjectivity of the
   fppf covering (def-pc-fppf-site) therefore gives the asserted union of opens.
2. For a pair a, b, the inverse image of H i in G = h_T times_F h_T' is
   h_(V i) times_(H i) h_(V' i). Both maps factor uniquely through the opens,
   and their H i sections agree because the inclusion H i into F is injective
   (def-pc-subfunctor). The diagonal hypothesis represents this fibre product.
3. On a scheme test of G, the inverse image of the ith piece is the same open
   as the inverse image of H i under the common F section. Step 1 proves that
   these opens cover every test (def-pc-open-subfunctor).
4. Compatible local pairs in G glue coordinatewise by
   lem-weil-pbc-scheme-morphism-gluing. Zariski covers are fppf covers by
   lem-pc-zariski-coverings-are-fppf, so separation of the sheaf F makes the
   two glued F sections equal (def-weil-pbc-sites-and-cohomology).
5. Apply lem-pc-schemes-criterion to this Zariski sheaf G and its small family
   of representable open subfunctors from steps 2 and 3. This represents G.
6. For a test h_W into F times F, represent h_W times_F h_W by R as in step 5.
   Pull R back along W into W times_S W. Scheme fibre products
   (def-pc-fibre-product) identify its points with a single map to W on which
   the two F sections agree. It represents the diagonal test, as required by
   def-trf-algebraic-space. -/
theorem open_cover_representable_diagonal {S : Scheme.{u}}
    (F : Sheaf (Scheme.fppfTopology.over S) (Type u))
    (I : Type u) (H : I → Subfunctor F.obj)
    (hH : ∀ i : I, Presheaf.IsSheaf (Scheme.fppfTopology.over S) (H i).toFunctor)
    (hopen : ∀ i : I,
      IsRepresentableWith (fun _ _ p ↦ IsOpenImmersion p.left) (H i).ι)
    (hdiag : ∀ (i : I) (T T' : Over S)
      (a : yoneda.obj T ⟶ (H i).toFunctor) (b : yoneda.obj T' ⟶ (H i).toFunctor),
      (Limits.pullback a b).IsRepresentable)
    (hlocal : ∀ (T : Over S) (a : F.obj.obj (op T)),
      ∃ (𝒰 : Scheme.Cover.{u} Scheme.fppfPrecoverage T.left) (k : 𝒰.I₀ → I),
        ∀ j : 𝒰.I₀,
          F.obj.map (Over.homMk (𝒰.f j) rfl : Over.mk (𝒰.f j ≫ T.hom) ⟶ T).op a ∈
            (H (k j)).obj (op (Over.mk (𝒰.f j ≫ T.hom)))) :
    (∀ (T : Over S) (a : F.obj.obj (op T)) (V : I → T.left.Opens),
      (∀ (i : I) (W : Over S) (f : W ⟶ T),
        F.obj.map f.op a ∈ (H i).obj (op W) ↔ Set.range f.left ⊆ V i) →
      (⨆ i : I, V i) = ⊤) ∧
    (∀ (T T' : Over S) (a : yoneda.obj T ⟶ F.obj) (b : yoneda.obj T' ⟶ F.obj),
      (∀ i : I, ((H i).preimage (Limits.pullback.fst a b ≫ a)).toFunctor.IsRepresentable) ∧
      (∀ i : I, IsRepresentableWith (fun _ _ p ↦ IsOpenImmersion p.left)
        ((H i).preimage (Limits.pullback.fst a b ≫ a)).ι) ∧
      (∀ (W : Over S) (c : (Limits.pullback a b).obj (op W)) (V : I → W.left.Opens),
        (∀ (i : I) (Z : Over S) (f : Z ⟶ W),
          (Limits.pullback a b).map f.op c ∈
            ((H i).preimage (Limits.pullback.fst a b ≫ a)).obj (op Z) ↔
              Set.range f.left ⊆ V i) →
        (⨆ i : I, V i) = ⊤) ∧
      (Limits.pullback a b).IsRepresentable) ∧
    IsRepresentable (prod.lift (𝟙 F.obj) (𝟙 F.obj)) := by
  have _ := hH
  have hcover (T : Over S) (a : F.obj.obj (op T)) (V : I → T.left.Opens)
      (hV : ∀ (i : I) (W : Over S) (f : W ⟶ T),
        F.obj.map f.op a ∈ (H i).obj (op W) ↔ Set.range f.left ⊆ V i) :
      (⨆ i, V i) = ⊤ := by
    obtain ⟨𝒰, k, hk⟩ := hlocal T a
    apply top_unique
    intro t ht
    apply TopologicalSpace.Opens.mem_iSup.mpr
    have hcov := (Scheme.ofArrows_mem_precoverage_iff _).mp 𝒰.mem₀
    obtain ⟨j, y, hy⟩ := hcov.1 t
    exact ⟨k j, (hV _ _ _).mp (hk j) ⟨y, hy⟩⟩
  have hpieces (T T' : Over S) (a : yoneda.obj T ⟶ F.obj)
      (b : yoneda.obj T' ⟶ F.obj) := fun i ↦
    piece_representable (H i) (hopen i) (hdiag i) T T' a b
  have hopen' (T T' : Over S) (a : yoneda.obj T ⟶ F.obj)
      (b : yoneda.obj T' ⟶ F.obj) := fun i ↦
    open_preimage (H i) (pullback.fst a b ≫ a) (hopen i)
  have hcover' (T T' : Over S) (a : yoneda.obj T ⟶ F.obj)
      (b : yoneda.obj T' ⟶ F.obj) (W : Over S)
      (c : (Limits.pullback a b).obj (op W)) (V : I → W.left.Opens)
      (hV : ∀ (i : I) (Z : Over S) (f : Z ⟶ W),
        (Limits.pullback a b).map f.op c ∈
          ((H i).preimage (pullback.fst a b ≫ a)).obj (op Z) ↔
            Set.range f.left ⊆ V i) : (⨆ i, V i) = ⊤ := by
    apply hcover W ((pullback.fst a b ≫ a).app (op W) c) V
    intro i Z f
    rw [← NatTrans.naturality_apply]
    exact hV i Z f
  have hrep (T T' : Over S) (a : yoneda.obj T ⟶ F.obj)
      (b : yoneda.obj T' ⟶ F.obj) : (Limits.pullback a b).IsRepresentable := by
    let G := Limits.pullback a b
    let K : I → Subfunctor G := fun i ↦ (H i).preimage (pullback.fst a b ≫ a)
    have hle : Scheme.zariskiTopology.over S ≤ Scheme.fppfTopology.over S := by
      intro W R hR
      exact Precoverage.toGrothendieck_mono
        Scheme.zariskiPrecoverage_le_fppfPrecoverage _ hR
    have hF : Presheaf.IsSheaf (Scheme.zariskiTopology.over S) F.obj :=
      (isSheaf_iff_isSheaf_of_type _ _).mpr (Presieve.isSheaf_of_le _ hle
        ((isSheaf_iff_isSheaf_of_type _ _).mp F.property))
    have hy (W : Over S) :
        Presheaf.IsSheaf (Scheme.zariskiTopology.over S) (yoneda.obj W) :=
      (isSheaf_iff_isSheaf_of_type _ _).mpr
        (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _)
    have hG : Presheaf.IsSheaf (Scheme.zariskiTopology.over S) G := by
      apply ObjectProperty.prop_of_isLimit
        (P := Presheaf.IsSheaf (Scheme.zariskiTopology.over S) (A := Type u))
        (pullback.isLimit a b)
      intro j
      rcases j with _ | (_ | _)
      · exact hF
      · exact hy T
      · exact hy T'
    apply isRepresentable_of_isSheaf_of_zariskiCovers hG K (hpieces T T' a b)
      (fun i ↦ relative_open _ (hopen' T T' a b i))
    intro W c t
    choose V hV using fun i ↦ opens_of_open (K i) (hopen' T T' a b i) W c
    have ht : t ∈ ⨆ i, V i := by rw [hcover' T T' a b W c V hV]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp ht
    refine ⟨i, V i, hi, (hV i _ _).mpr ?_⟩
    change Set.range (V i).ι ⊆ V i
    rw [Scheme.Opens.range_ι]
  exact ⟨hcover, fun T T' a b ↦
    ⟨hpieces T T' a b, hopen' T T' a b, hcover' T T' a b, hrep T T' a b⟩,
    diagonal_of_pairs hrep⟩

end AlgebraicGeometry.AlgebraicSpace
