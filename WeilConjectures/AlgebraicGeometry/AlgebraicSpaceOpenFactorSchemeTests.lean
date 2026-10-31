/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AlgebraicSpaceOpenSubspace
public import WeilConjectures.AlgebraicGeometry.AlgebraicSpacePointTopology
public import WeilConjectures.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
import WeilConjectures.AlgebraicGeometry.AlgebraicSpacePointOpenCalculus
import Mathlib.CategoryTheory.Sites.SubcanonicalOver
import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.CategoryTheory.Limits.Types.Pullbacks

/-!
# Open-subspace factorization and scheme tests

Source: Stacks Project, Properties of Spaces, Tags 03IE, 06NF and 03H4
(blueprint: lem-a1-space-open-factor-scheme-tests).

The pullback open subspace is the literal subfunctor preimage. Comparisons of scheme
base changes are specified by both projections, hence are the canonical comparisons.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

private theorem pullback_cancel_mono {C : Type*} [Category C]
    {P G H F E : C} {q : P ⟶ G} {p : P ⟶ H} {f : G ⟶ E} {a : H ⟶ E}
    (j : E ⟶ F) [Mono j] (h : IsPullback q p (f ≫ j) (a ≫ j)) :
    IsPullback q p f a := by
  exact IsPullback.of_isLimit
    (PullbackCone.isLimitOfFactors _ _ j f a rfl rfl h.cone h.isLimit)

private theorem pullback_comp_mono {C : Type*} [Category C]
    {P G H F E : C} {q : P ⟶ G} {p : P ⟶ H} {f : G ⟶ E} {a : H ⟶ E}
    (j : E ⟶ F) [Mono j] (h : IsPullback q p f a) :
    IsPullback q p (f ≫ j) (a ≫ j) := by
  exact IsPullback.of_isLimit
    (PullbackCone.isLimitOfCompMono f a j h.cone h.isLimit)

private theorem representable_comp {S : Scheme.{u}}
    {E F G : (Over S)ᵒᵖ ⥤ Type u} {f : E ⟶ F} {g : F ⟶ G}
    (hf : IsRepresentable f) (hg : IsRepresentable g) : IsRepresentable (f ≫ g) := by
  intro T a
  obtain ⟨V, p, q, hq, _⟩ := hg T a
  obtain ⟨W, r, s, hs, _⟩ := hf V q
  refine ⟨W, r ≫ p, s, ?_, trivial⟩
  simpa only [yoneda.map_comp] using hs.paste_vert hq

private theorem representable_cancel_mono {S : Scheme.{u}}
    (P : MorphismProperty (Over S)) {E F G : (Over S)ᵒᵖ ⥤ Type u}
    {f : E ⟶ F} (g : F ⟶ G) [Mono g]
    (hf : IsRepresentableWith P (f ≫ g)) : IsRepresentableWith P f := by
  intro T a
  obtain ⟨V, p, q, hq, hp⟩ := hf T (a ≫ g)
  exact ⟨V, p, q, pullback_cancel_mono g hq, hp⟩

private theorem representable_baseChange {S : Scheme.{u}}
    (P : MorphismProperty (Over S)) {E F G H : (Over S)ᵒᵖ ⥤ Type u}
    {q : H ⟶ E} {p : H ⟶ G} {f : E ⟶ F} {a : G ⟶ F}
    (h : IsPullback q p f a) (hf : IsRepresentableWith P f) :
    IsRepresentableWith P p := by
  intro T b
  obtain ⟨V, r, s, hs, hr⟩ := hf T (b ≫ a)
  let t := h.lift s (yoneda.map r ≫ b) (by simpa using hs.w)
  refine ⟨V, r, t, ?_, hr⟩
  apply IsPullback.of_right (by simpa [t] using hs) (h.lift_snd _ _ _) h

-- Glue in the target sheaf, then glue maps to its representing scheme pullback.
private theorem representable_isSheaf {S : Scheme.{u}}
    {F : Sheaf (Scheme.fppfTopology.over S) (Type u)}
    {G : (Over S)ᵒᵖ ⥤ Type u} (f : G ⟶ F.obj) (hf : IsRepresentable f) :
    Presheaf.IsSheaf (Scheme.fppfTopology.over S) G := by
  rw [isSheaf_iff_isSheaf_of_type]
  apply Presieve.isSheaf_of_yoneda
  intro T R hR α
  have hF := (isSheaf_iff_isSheaf_of_type _ _).mp F.property
  obtain ⟨a, ha, huniq⟩ :=
    (Presieve.isSheafFor_iff_yonedaSheafCondition.mp (hF R hR)) (α ≫ f)
  obtain ⟨V, p, q, hq, _⟩ := hf T a
  let β := hq.lift α R.functorInclusion ha.symm
  have hV := GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable
    (J := Scheme.fppfTopology.over S) (yoneda.obj V)
  obtain ⟨b, hb, hbuniq⟩ :=
    (Presieve.isSheafFor_iff_yonedaSheafCondition.mp (hV R hR)) β
  refine ⟨b ≫ q, ?_, ?_⟩
  · change R.functorInclusion ≫ (b ≫ q) = α
    rw [← Category.assoc, hb]
    exact hq.lift_fst _ _ _
  · intro c hc
    have hcf : c ≫ f = a := by
      apply huniq
      rw [← Category.assoc, hc]
    let d := hq.lift c (𝟙 _) (by simpa using hcf)
    have hd : R.functorInclusion ≫ d = β := by
      apply hq.hom_ext
      · simp [d, β, hc]
      · simp [d, β]
    have he : d = b := hbuniq _ hd
    calc
      c = d ≫ q := (hq.lift_fst _ _ _).symm
      _ = b ≫ q := by rw [he]

-- The diagonal and an atlas are obtained by cancellation and pullback, respectively.
private theorem openSubspace_isAlgebraicSpace {S : Scheme.{u}}
    (X : AlgebraicSpace S) (A : OpenSubspace X)
    (hA : Presheaf.IsSheaf (Scheme.fppfTopology.over S) A.val.toFunctor) :
    IsAlgebraicSpace ⟨A.val.toFunctor, hA⟩ := by
  have hj : IsRepresentable A.val.ι := by
    intro T a
    obtain ⟨V, p, q, hq, _⟩ := A.property T a
    exact ⟨V, p, q, hq, trivial⟩
  constructor
  · apply representable_cancel_mono ⊤ (prod.map A.val.ι A.val.ι)
    have h := representable_comp hj X.property.1
    dsimp only [IsRepresentable] at h
    simpa only [prod.lift_map, Category.id_comp, prod.comp_lift,
      Category.comp_id] using h
  · obtain ⟨U, w, hw, hs⟩ := X.property.2
    obtain ⟨V, p, q, hq, _⟩ := A.property U w
    exact ⟨V, q,
      representable_baseChange _ hq.flip hw,
      representable_baseChange _ hq.flip hs⟩

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

private theorem open_preimage {S : Scheme.{u}} {P Q : (Over S)ᵒᵖ ⥤ Type u}
    (H : Subfunctor Q) (a : P ⟶ Q)
    (hH : IsRepresentableWith (fun _ _ p ↦ IsOpenImmersion p.left) H.ι) :
    IsRepresentableWith (fun _ _ p ↦ IsOpenImmersion p.left) (H.preimage a).ι := by
  intro T b
  obtain ⟨U, p, q, hp, hopen⟩ := hH T (b ≫ a)
  let r := (preimage_square H a).lift q (yoneda.map p ≫ b) (by simpa using hp.w)
  refine ⟨U, p, r, ?_, hopen⟩
  exact IsPullback.of_right' hp (preimage_square H a)

private theorem openSubspace_isSheaf {S : Scheme.{u}} (X : AlgebraicSpace S)
    (A : OpenSubspace X) :
    Presheaf.IsSheaf (Scheme.fppfTopology.over S) A.val.toFunctor := by
  apply representable_isSheaf A.val.ι
  intro T a
  obtain ⟨U, p, q, hq, _⟩ := A.property T a
  exact ⟨U, p, q, hq, trivial⟩

private theorem mapPoint_comp {S : Scheme.{u}}
    {F G H : (Over S)ᵒᵖ ⥤ Type u} (f : F ⟶ G) (g : G ⟶ H) (x : Point F) :
    mapPoint (f ≫ g) x = mapPoint g (mapPoint f x) := by
  induction x using Quot.inductionOn with
  | h x => rfl

private theorem pointImage_eq_range {S : Scheme.{u}}
    {F G : (Over S)ᵒᵖ ⥤ Type u} (f : F ⟶ G) :
    pointImage f = Set.range (mapPoint f) := by
  ext x
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨Quot.mk _ a, rfl⟩
  · rintro ⟨a, rfl⟩
    induction a using Quot.inductionOn with
    | h a => exact ⟨a, rfl⟩

private theorem pointImage_iso_comp {S : Scheme.{u}}
    {F G H : (Over S)ᵒᵖ ⥤ Type u} (e : F ≅ G) (f : G ⟶ H) :
    pointImage (e.hom ≫ f) = pointImage f := by
  simp only [pointImage_eq_range]
  ext x
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨mapPoint e.hom a, (mapPoint_comp _ _ _).symm⟩
  · rintro ⟨a, rfl⟩
    refine ⟨mapPoint e.inv a, ?_⟩
    rw [mapPoint_comp e.hom f, ← mapPoint_comp e.inv e.hom, e.inv_hom_id]
    apply congrArg (mapPoint f)
    induction a using Quot.inductionOn with
    | h a => rfl

private theorem preimage_pointImage {S : Scheme.{u}} (X G : AlgebraicSpace S)
    (J : OpenSubspace X) (g : G ⟶ X) :
    pointImage (J.val.preimage g.hom.hom).ι =
      mapPoint g.hom.hom ⁻¹' pointImage J.val.ι := by
  let hJ := openSubspace_isSheaf X J
  let A : AlgebraicSpace S :=
    ⟨⟨J.val.toFunctor, hJ⟩, openSubspace_isAlgebraicSpace X J hJ⟩
  let j : A ⟶ X := ObjectProperty.homMk ⟨J.val.ι⟩
  let hp := (IsPullback.of_hasPullback j.hom g.hom).map
    (sheafToPresheaf (Scheme.fppfTopology.over S) (Type u))
  let e := (preimage_square J.val g.hom.hom).isoIsPullback _ _ hp
  have he : e.hom ≫ (Limits.pullback.snd j.hom g.hom).hom =
      (J.val.preimage g.hom.hom).ι :=
    (preimage_square J.val g.hom.hom).isoIsPullback_hom_snd _ _ hp
  rw [← he, pointImage_iso_comp]
  exact (point_open_calculus.1 A X G j g).2

/-- Pulling back an open subspace along any map gives the inverse image on point classes.
The subfunctor preimage is the fibre product with the subfunctor inclusion.
Source: Stacks, Tags 03IE and 03H4 (blueprint: lem-a1-space-open-factor-scheme-tests).
Proof (step 1): on each test scheme, the subfunctor preimage consists of exactly the
sections whose images belong to the open subfunctor. Its scheme test is therefore the
open subscheme supplied by `OpenSubspace`. The common-field calculation of
lem-a1-space-point-open-calculus identifies its point image with the inverse image.
This applies both to the map being factored and to every arbitrary base-change map;
lem-trf-space-fibre-products-etale-covers supplies the sheaf fibre products. -/
theorem openSubspace_preimage_schemeTests {S : Scheme.{u}} (X G : AlgebraicSpace S)
    (J : OpenSubspace X) (g : G ⟶ X) :
    IsRepresentableWith (fun _ _ p ↦ IsOpenImmersion p.left)
      (J.val.preimage g.hom.hom).ι ∧
    ∀ a : PointRepresentative G.obj.obj,
      Quot.mk _ a ∈ pointImage (J.val.preimage g.hom.hom).ι ↔
        Quot.mk _ (a.map g.hom.hom) ∈ pointImage J.val.ι := by
  refine ⟨open_preimage J.val g.hom.hom J.property, ?_⟩
  intro a
  rw [preimage_pointImage]
  rfl

/-- Image containment gives the unique open factor, an invertible pullback projection,
and identical scheme tests; representable étaleness and full-image surjectivity descend.
Source: Stacks, Tags 03IE and 06NF (blueprint: lem-a1-space-open-factor-scheme-tests).
Proof (steps 2--4): the preceding inverse-image formula gives full point image to the
open pullback. By lem-a1-space-point-open-calculus it equals the ambient space, so its
inclusion is invertible. Compose the inverse with `Subfunctor.fromPreimage` to obtain
the factor. The inclusion of a subfunctor is sectionwise injective, proving uniqueness.
For every scheme test, compatible pairs over the open and over the ambient space are
identical: equality after the subfunctor inclusion implies equality before it. This gives
the comparison isomorphism commuting with both projections. Apply the scheme-test
criterion of def-trf-algebraic-space to inherit representable étaleness. If the point image
is the entire open, injectivity on point classes makes the factor point-surjective;
the representable-surjectivity criterion of lem-a1-space-point-open-calculus makes every
scheme base change surjective. Fibre products exist by
lem-trf-space-fibre-products-etale-covers. -/
theorem openSubspace_factor_schemeTests {S : Scheme.{u}} (X Y : AlgebraicSpace S)
    (J : OpenSubspace X) (f : Y ⟶ X)
    (hf : pointImage f.hom.hom ⊆ pointImage J.val.ι) :
    IsIso (J.val.preimage f.hom.hom).ι ∧
    ∃ fJ : Y.obj.obj ⟶ J.val.toFunctor,
      fJ ≫ J.val.ι = f.hom.hom ∧
      (∀ k : Y.obj.obj ⟶ J.val.toFunctor, k ≫ J.val.ι = f.hom.hom → k = fJ) ∧
      (∀ (T : Over S) (t : yoneda.obj T ⟶ J.val.toFunctor),
        ∃ e : Limits.pullback fJ t ≅ Limits.pullback f.hom.hom (t ≫ J.val.ι),
          e.hom ≫ Limits.pullback.fst f.hom.hom (t ≫ J.val.ι) =
            Limits.pullback.fst fJ t ∧
          e.hom ≫ Limits.pullback.snd f.hom.hom (t ≫ J.val.ι) =
            Limits.pullback.snd fJ t) ∧
      (IsEtale f.hom.hom → IsEtale fJ ∧
        (pointImage f.hom.hom = pointImage J.val.ι → IsSurjective fJ)) := by
  let K : OpenSubspace Y := ⟨J.val.preimage f.hom.hom,
    open_preimage J.val f.hom.hom J.property⟩
  have hK : K.val = ⊤ := by
    apply point_open_calculus.2.2.2.2.2.2 Y K
    rw [preimage_pointImage]
    apply Set.eq_univ_of_forall
    intro a
    induction a using Quot.inductionOn with
    | h a => exact hf ⟨a, rfl⟩
  have hKi : IsIso (J.val.preimage f.hom.hom).ι :=
    (Subfunctor.eq_top_iff_isIso K.val).mp hK
  have := hKi
  let fJ := inv (J.val.preimage f.hom.hom).ι ≫ J.val.fromPreimage f.hom.hom
  have hfac : fJ ≫ J.val.ι = f.hom.hom := by
    simp [fJ, Subfunctor.fromPreimage_ι]
  refine ⟨hKi, fJ, hfac, ?_, ?_, ?_⟩
  · intro k hk
    apply (cancel_mono J.val.ι).mp
    exact hk.trans hfac.symm
  · intro T t
    have hp : IsPullback (Limits.pullback.fst fJ t) (Limits.pullback.snd fJ t)
        f.hom.hom (t ≫ J.val.ι) := by
      have hp' := pullback_comp_mono J.val.ι (IsPullback.of_hasPullback fJ t)
      simpa only [hfac] using hp'
    exact ⟨hp.isoPullback, hp.isoPullback_hom_fst, hp.isoPullback_hom_snd⟩
  · intro he
    have heJ : IsEtale fJ := by
      apply representable_cancel_mono _ J.val.ι
      rwa [hfac]
    refine ⟨heJ, ?_⟩
    intro himage
    let hJ := openSubspace_isSheaf X J
    let A : AlgebraicSpace S :=
      ⟨⟨J.val.toFunctor, hJ⟩, openSubspace_isAlgebraicSpace X J hJ⟩
    let a : Y ⟶ A := ObjectProperty.homMk ⟨fJ⟩
    apply (point_open_calculus.2.1 Y A a ?_).mpr
    · intro z
      have hz : mapPoint J.val.ι z ∈ pointImage J.val.ι := by
        rw [pointImage_eq_range]
        exact ⟨z, rfl⟩
      rw [← himage] at hz
      obtain ⟨y, hy⟩ := hz
      refine ⟨Quot.mk _ y, ?_⟩
      apply (point_open_calculus.2.2.2.2.1 X J).1.injective
      change mapPoint J.val.ι (mapPoint fJ (Quot.mk _ y)) = mapPoint J.val.ι z
      rw [← mapPoint_comp, hfac]
      exact hy
    · intro T t
      obtain ⟨U, p, q, hq, _⟩ := heJ T t
      exact ⟨U, p, q, hq, trivial⟩

/-- A full open point image remains that same open image after arbitrary base change.
Source: Stacks, Tag 03H4 (blueprint: lem-a1-space-open-factor-scheme-tests).
Proof (step 5): lem-a1-space-point-open-calculus identifies the image of the sheaf
pullback projection with the inverse image of the image of `f`. Replace this image by
that of `J`, and apply `openSubspace_preimage_schemeTests` to `g`. This is precisely the
point image of the pullback open subspace. No extra condition on `g` occurs. The
pullback is an algebraic space by lem-trf-space-fibre-products-etale-covers. -/
theorem openSubspace_pullback_image {S : Scheme.{u}} (X Y G : AlgebraicSpace S)
    (J : OpenSubspace X) (f : Y ⟶ X) (g : G ⟶ X)
    (hf : pointImage f.hom.hom = pointImage J.val.ι) :
    pointImage (Limits.pullback.snd f.hom g.hom).hom =
      pointImage (J.val.preimage g.hom.hom).ι := by
  rw [(point_open_calculus.1 Y X G f g).2, hf, preimage_pointImage]

end AlgebraicGeometry.AlgebraicSpace
