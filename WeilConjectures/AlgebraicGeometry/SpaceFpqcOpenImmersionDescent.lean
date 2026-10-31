/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AlgebraicSpace
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import WeilConjectures.AlgebraicGeometry.AlgebraicSpaceFpqcSheaf
import WeilConjectures.AlgebraicGeometry.FpqcOpenSubschemeDescent

/-!
# Fpqc descent of an open immersion from an algebraic space to a scheme

Source: Stacks Project, Descent of Spaces, Tag 041X,
`lemma-descending-property-open-immersion`
(blueprint: lem-sfb-space-fpqc-open-immersion-descent).

The conclusion gives a representing scheme and an open immersion into the target,
compatible with the original morphism. Schematicity of the source is a conclusion.
-/

@[expose] public section

universe u v

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

/-- Cartesian local presentations give containment of the inverse-image opens.
Source: Stacks Project, Tag 041X, equality of the two inverse-image opens. -/
private theorem local_image_le
    {S : Scheme.{u}} {F : (Over S)ᵒᵖ ⥤ Type u}
    {P A B X Y T : Over S} (a : F ⟶ yoneda.obj P)
    (p : A ⟶ P) (r : B ⟶ P) (q : X ⟶ A) (t : Y ⟶ B)
    [IsOpenImmersion q.left] [IsOpenImmersion t.left]
    (k : yoneda.obj X ⟶ F) (l : yoneda.obj Y ⟶ F)
    (hk : IsPullback k (yoneda.map q) a (yoneda.map p))
    (hl : IsPullback l (yoneda.map t) a (yoneda.map r))
    (b : T ⟶ A) (c : T ⟶ B) (hbc : b ≫ p = c ≫ r) :
    b.left ⁻¹ᵁ q.left.opensRange ≤ c.left ⁻¹ᵁ t.left.opensRange := by
  let V : Over S := Over.mk (pullback.fst q.left b.left ≫ X.hom)
  let v : V ⟶ X := Over.homMk (pullback.fst q.left b.left) rfl
  let w : V ⟶ T := Over.homMk (pullback.snd q.left b.left) (by
    dsimp [V]
    rw [← Over.w b, ← Category.assoc, ← pullback.condition, Category.assoc, Over.w q])
  have hvw : v ≫ q = w ≫ b := by
    ext
    exact pullback.condition
  let d : yoneda.obj V ⟶ yoneda.obj Y :=
    hl.lift (yoneda.map v ≫ k) (yoneda.map (w ≫ c)) (by
      rw [Category.assoc, hk.w, ← Functor.map_comp_assoc, hvw,
        ← Functor.map_comp, Category.assoc, hbc, ← Category.assoc, Functor.map_comp])
  let e : V ⟶ Y := yoneda.preimage d
  have he : e ≫ t = w ≫ c := by
    apply yoneda.map_injective
    rw [Functor.map_comp, Functor.map_preimage]
    exact hl.lift_snd _ _ _
  intro x hx
  obtain ⟨z, hz⟩ := hx
  obtain ⟨y, _, hy⟩ := Scheme.Pullback.exists_preimage_pullback z x hz
  refine ⟨e.left y, ?_⟩
  rw [← Scheme.Hom.comp_apply, ← Over.comp_left, he, Over.comp_left,
    Scheme.Hom.comp_apply]
  change c.left (pullback.snd q.left b.left y) = c.left x
  rw [hy]

/-- Local open immersions and fpqc sheaf uniqueness give injectivity on sections.
Source: Stacks Project, Tag 041X, final bijectivity argument. -/
private theorem sections_injective
    {S : Scheme.{u}} (P : Over S) (Z : AlgebraicSpace S)
    (a : Z.obj.obj ⟶ yoneda.obj P) {I : Type v}
    (A X : I → Over S) (p : ∀ i, A i ⟶ P) (q : ∀ i, X i ⟶ A i)
    (hq : ∀ i, IsOpenImmersion (q i).left)
    (k : ∀ i, yoneda.obj (X i) ⟶ Z.obj.obj)
    (hk : ∀ i, IsPullback (k i) (yoneda.map (q i)) a (yoneda.map (p i)))
    (hcover : Presieve.ofArrows (fun i ↦ (A i).left) (fun i ↦ (p i).left) ∈
      Scheme.fpqcPrecoverage P.left) (T : Over S) :
    Function.Injective (a.app (op T)) := by
  intro z z' hzz
  let f : T ⟶ P := a.app (op T) z
  let V (i : I) : Over S := Over.mk (pullback.fst f.left (p i).left ≫ T.hom)
  let w (i : I) : V i ⟶ T := Over.homMk (pullback.fst f.left (p i).left) rfl
  let t (i : I) : V i ⟶ A i := Over.homMk (pullback.snd f.left (p i).left) (by
    dsimp [V]
    rw [← Over.w (p i), ← Category.assoc, ← pullback.condition,
      Category.assoc, Over.w f])
  have hwt (i : I) : w i ≫ f = t i ≫ p i := by
    ext
    exact pullback.condition
  have hcov : Presieve.ofArrows (fun i ↦ (V i).left) (fun i ↦ (w i).left) ∈
      Scheme.fpqcPrecoverage T.left :=
    Precoverage.mem_coverings_of_isPullback (fun i ↦ (p i).left) hcover f.left
      (fun i ↦ (w i).left) (fun i ↦ (t i).left)
      (fun i ↦ IsPullback.of_hasPullback f.left (p i).left)
  apply (existsUnique_section_and_eq_of_fpqc_cover Z T
    (fun i ↦ (V i).left) (fun i ↦ (w i).left) hcov).2 z z'
  intro i
  change Z.obj.obj.map (w i).op z = Z.obj.obj.map (w i).op z'
  have : IsOpenImmersion (q i).left := hq i
  have : Mono (q i) := Over.mono_of_mono_left _
  have h₁ : yoneda.map (w i) ≫ yonedaEquiv.symm z ≫ a =
      yoneda.map (t i) ≫ yoneda.map (p i) := by
    rw [yonedaEquiv_symm_naturality_right]
    change yoneda.map (w i) ≫ yoneda.map f = _
    rw [← Functor.map_comp, hwt, Functor.map_comp]
  have h₂ : yoneda.map (w i) ≫ yonedaEquiv.symm z' ≫ a =
      yoneda.map (t i) ≫ yoneda.map (p i) := by
    simpa only [Category.assoc, yonedaEquiv_symm_naturality_right, hzz] using h₁
  have hd : (hk i).lift (yoneda.map (w i) ≫ yonedaEquiv.symm z)
      (yoneda.map (t i)) h₁ =
      (hk i).lift (yoneda.map (w i) ≫ yonedaEquiv.symm z')
        (yoneda.map (t i)) h₂ := by
    apply (cancel_mono (yoneda.map (q i))).mp
    simp only [IsPullback.lift_snd]
  have hh := congrArg (fun d ↦ d ≫ k i) hd
  simp only [IsPullback.lift_fst] at hh
  simpa only [← yonedaEquiv_naturality, Equiv.apply_symm_apply] using
    congrArg yonedaEquiv hh

/-- Every section maps into the descended open, by joint surjectivity of the cover.
Source: Stacks Project, Tag 041X, final test-scheme factorization argument. -/
private theorem section_range
    {S : Scheme.{u}} (P : Over S) (Z : AlgebraicSpace S)
    (a : Z.obj.obj ⟶ yoneda.obj P) {I : Type v}
    (A X : I → Over S) (p : ∀ i, A i ⟶ P) (q : ∀ i, X i ⟶ A i)
    (hq : ∀ i, IsOpenImmersion (q i).left)
    (k : ∀ i, yoneda.obj (X i) ⟶ Z.obj.obj)
    (hk : ∀ i, IsPullback (k i) (yoneda.map (q i)) a (yoneda.map (p i)))
    (hcover : Presieve.ofArrows (fun i ↦ (A i).left) (fun i ↦ (p i).left) ∈
      Scheme.fpqcPrecoverage P.left)
    (U : P.left.Opens) (hU : ∀ i, (p i).left ⁻¹ᵁ U = (q i).left.opensRange)
    (T : Over S) (z : Z.obj.obj.obj (op T)) :
    Set.range (a.app (op T) z).left ⊆ U := by
  let f : T ⟶ P := a.app (op T) z
  rintro _ ⟨x, rfl⟩
  obtain ⟨B, g, hg, y, hy⟩ := Scheme.JointlySurjective.exists_eq
    (K := Scheme.precoverage @Flat)
    (Presieve.ofArrows (fun i ↦ (A i).left) (fun i ↦ (p i).left)) hcover.2 (f.left x)
  obtain ⟨i⟩ := hg
  obtain ⟨v, hv₁, hv₂⟩ := Scheme.Pullback.exists_preimage_pullback x y hy.symm
  let V : Over S := Over.mk (pullback.fst f.left (p i).left ≫ T.hom)
  let w : V ⟶ T := Over.homMk (pullback.fst f.left (p i).left) rfl
  let t : V ⟶ A i := Over.homMk (pullback.snd f.left (p i).left) (by
    dsimp [V]
    rw [← Over.w (p i), ← Category.assoc, ← pullback.condition,
      Category.assoc, Over.w f])
  have hwt : w ≫ f = t ≫ p i := by ext; exact pullback.condition
  let d : yoneda.obj V ⟶ yoneda.obj (X i) :=
    (hk i).lift (yoneda.map w ≫ yonedaEquiv.symm z) (yoneda.map t) (by
      rw [Category.assoc, yonedaEquiv_symm_naturality_right]
      change yoneda.map w ≫ yoneda.map f = _
      rw [← Functor.map_comp, hwt, Functor.map_comp])
  let e : V ⟶ X i := yoneda.preimage d
  have he : e ≫ q i = t := by
    apply yoneda.map_injective
    rw [Functor.map_comp, Functor.map_preimage]
    exact (hk i).lift_snd _ _ _
  have hi : y ∈ (q i).left.opensRange := by
    have : IsOpenImmersion (q i).left := hq i
    refine ⟨e.left v, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← Over.comp_left, he]
    exact hv₂
  rw [← hU i] at hi
  change (p i).left y ∈ U at hi
  rwa [hy] at hi

/-- A map into the descended open lifts to a section by fpqc gluing.
Source: Stacks Project, Tag 041X, gluing the local maps into the algebraic space. -/
private theorem section_exists
    {S : Scheme.{u}} (P : Over S) (Z : AlgebraicSpace S)
    (a : Z.obj.obj ⟶ yoneda.obj P) {I : Type v}
    (A X : I → Over S) (p : ∀ i, A i ⟶ P) (q : ∀ i, X i ⟶ A i)
    (hq : ∀ i, IsOpenImmersion (q i).left)
    (k : ∀ i, yoneda.obj (X i) ⟶ Z.obj.obj)
    (hk : ∀ i, IsPullback (k i) (yoneda.map (q i)) a (yoneda.map (p i)))
    (hcover : Presieve.ofArrows (fun i ↦ (A i).left) (fun i ↦ (p i).left) ∈
      Scheme.fpqcPrecoverage P.left)
    (U : P.left.Opens) (hU : ∀ i, (p i).left ⁻¹ᵁ U = (q i).left.opensRange)
    (T : Over S) (f : T ⟶ P) (hf : Set.range f.left ⊆ U) :
    ∃ z : Z.obj.obj.obj (op T), a.app (op T) z = f := by
  let V (i : I) : Over S := Over.mk (pullback.fst f.left (p i).left ≫ T.hom)
  let w (i : I) : V i ⟶ T := Over.homMk (pullback.fst f.left (p i).left) rfl
  let t (i : I) : V i ⟶ A i := Over.homMk (pullback.snd f.left (p i).left) (by
    dsimp [V]
    rw [← Over.w (p i), ← Category.assoc, ← pullback.condition,
      Category.assoc, Over.w f])
  have hwt (i : I) : w i ≫ f = t i ≫ p i := by ext; exact pullback.condition
  have hcov : Presieve.ofArrows (fun i ↦ (V i).left) (fun i ↦ (w i).left) ∈
      Scheme.fpqcPrecoverage T.left :=
    Precoverage.mem_coverings_of_isPullback (fun i ↦ (p i).left) hcover f.left
      (fun i ↦ (w i).left) (fun i ↦ (t i).left)
      (fun i ↦ IsPullback.of_hasPullback f.left (p i).left)
  have ht (i : I) : Set.range (t i).left ⊆ Set.range (q i).left := by
    have : IsOpenImmersion (q i).left := hq i
    rintro _ ⟨y, rfl⟩
    change (t i).left y ∈ (q i).left.opensRange
    rw [← hU i]
    change ((t i) ≫ p i).left y ∈ U
    rw [← hwt, Over.comp_left, Scheme.Hom.comp_apply]
    exact hf ⟨_, rfl⟩
  let d (i : I) : V i ⟶ X i := Over.homMk
    (@IsOpenImmersion.lift _ _ _ (q i).left (t i).left (hq i) (ht i)) (by
      rw [← Over.w (q i), IsOpenImmersion.lift_fac_assoc, Over.w (t i)])
  have hd (i : I) : d i ≫ q i = t i := by
    ext
    exact IsOpenImmersion.lift_fac _ _ _
  let z (i : I) : Z.obj.obj.obj (op (V i)) :=
    yonedaEquiv (yoneda.map (d i) ≫ k i)
  have hz (i : I) : a.app (op (V i)) (z i) = w i ≫ f := by
    rw [← yonedaEquiv_comp, Category.assoc, (hk i).w, ← Functor.map_comp_assoc,
      hd, ← Functor.map_comp, ← hwt, yonedaEquiv_yoneda_map]
  obtain ⟨b, hb, _⟩ :=
    (existsUnique_section_and_eq_of_fpqc_cover Z T
      (fun i ↦ (V i).left) (fun i ↦ (w i).left) hcov).1 z (by
        intro i j
        apply sections_injective P Z a A X p q hq k hk hcover
        let B : Over S := Over.mk
          (pullback.fst (w i).left (w j).left ≫ (w i).left ≫ T.hom)
        let r : B ⟶ V i := Over.homMk (pullback.fst (w i).left (w j).left) rfl
        let s : B ⟶ V j := Over.homMk (pullback.snd (w i).left (w j).left)
          (pullback.condition_assoc (f := (w i).left) (g := (w j).left) T.hom).symm
        change a.app (op B) (Z.obj.obj.map r.op (z i)) =
          a.app (op B) (Z.obj.obj.map s.op (z j))
        rw [a.naturality_apply, a.naturality_apply, hz, hz]
        change _ ≫ (w i ≫ f) = _ ≫ (w j ≫ f)
        apply Over.OverMorphism.ext
        change (pullback.fst (w i).left (w j).left ≫ (w i).left) ≫ f.left =
          (pullback.snd (w i).left (w j).left ≫ (w j).left) ≫ f.left
        rw [pullback.condition])
  refine ⟨b, ?_⟩
  have hb' (i : I) : Z.obj.obj.map (w i).op b = z i := by
    exact hb i
  have hs := (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable
    (J := Scheme.fpqcTopology) (yoneda.obj P.left)).isSheafFor
      (Presieve.ofArrows (fun i ↦ (V i).left) (fun i ↦ (w i).left))
      (Precoverage.generate_mem_toGrothendieck hcov)
  apply Over.OverMorphism.ext
  apply hs.isSeparatedFor.ext
  intro B g hg
  obtain ⟨i⟩ := hg
  have hi := congrArg Over.Hom.left ((a.naturality_apply (w i).op b).symm)
  change (w i).left ≫ (a.app (op T) b).left = (a.app (op (V i))
    (Z.obj.obj.map (w i).op b)).left at hi
  rw [hb' i, hz i] at hi
  exact hi

/-- A morphism from an algebraic space to a scheme identifies its source with an open
subscheme if its pullbacks along an fpqc covering are schemes mapping by open immersions.
Source: Stacks Project, Descent of Spaces, Tag 041X,
`lemma-descending-property-open-immersion`
(blueprint: lem-sfb-space-fpqc-open-immersion-descent).

Proof:
1. Identify the scheme pullbacks with their open images in the covering schemes. On
   every double overlap their pullbacks represent the same fibre-product functor, so
   the open images agree. Pulling back one local open immersion supplies a test
   scheme and a section, which lifts through the other cartesian presentation. The
   equation of its projection gives containment of the open images in each direction.
2. Descend these compatible opens to an open subscheme of the target using
   lem-weil-pbc-open-subscheme-fpqc-descent, in its full covering-family form.
3. For a test scheme and a section of the space, pull back the fpqc cover
   (lem-galois-fpqc-covering-base-change). The image of its map to the target lies in
   the descended open, since this holds on the jointly surjective cover. Unique open
   factorization (lem-weil-pbc-morphism-factors-through-open-subscheme) defines a
   natural map from the space to the represented open subscheme.
4. Conversely, a map from a test scheme to that open has unique lifts on the cover.
   They agree on overlaps by monicity of open immersions. Glue them uniquely using
   lem-a1-algebraic-space-fpqc-sheaf. Scheme fpqc descent uniqueness
   (lem-weil-pbc-fpqc-representable-descent) checks that the composite is the prescribed
   map to the target. The same uniqueness shows that the natural map is bijective.
5. The inverses of these bijections commute with restriction by uniqueness. They give
   the representing isomorphism, and its composite with the open immersion is `a`.
   No representability or quasi-compactness of `a` is assumed. -/
theorem exists_scheme_openImmersion_of_fpqc_cover
    {S : Scheme.{u}} (P : Over S) (Z : AlgebraicSpace S)
    (a : Z.obj.obj ⟶ yoneda.obj P) {I : Type v}
    (Pᵢ : I → Over S) (p : ∀ i : I, Pᵢ i ⟶ P)
    (hcover : Presieve.ofArrows (fun i ↦ (Pᵢ i).left) (fun i ↦ (p i).left) ∈
      Scheme.fpqcPrecoverage P.left)
    (hlocal : ∀ i : I, ∃ (Zᵢ : Over S) (q : Zᵢ ⟶ Pᵢ i)
      (e : Limits.pullback a (yoneda.map (p i)) ≅ yoneda.obj Zᵢ),
      IsOpenImmersion q.left ∧
        Limits.pullback.snd a (yoneda.map (p i)) = e.hom ≫ yoneda.map q) :
    ∃ (U : Over S) (j : U ⟶ P), IsOpenImmersion j.left ∧
      ∃ e : Z.obj.obj ≅ yoneda.obj U, a = e.hom ≫ yoneda.map j := by
  classical
  choose X q e hq he using hlocal
  let k (i : I) : yoneda.obj (X i) ⟶ Z.obj.obj :=
    (e i).inv ≫ pullback.fst a (yoneda.map (p i))
  have hk (i : I) : IsPullback (k i) (yoneda.map (q i)) a (yoneda.map (p i)) := by
    apply (IsPullback.of_hasPullback a (yoneda.map (p i))).of_iso'
      (e i).symm (Iso.refl _) (Iso.refl _) (Iso.refl _)
    · simp [k]
    · simpa using (Iso.inv_comp_eq (e i)).mpr (he i)
    · simp
    · simp
  have hW (i j : I) :
      pullback.fst (p i).left (p j).left ⁻¹ᵁ (q i).left.opensRange =
        pullback.snd (p i).left (p j).left ⁻¹ᵁ (q j).left.opensRange := by
    let T : Over S := Over.mk
      (pullback.fst (p i).left (p j).left ≫ (Pᵢ i).hom)
    let b : T ⟶ Pᵢ i := Over.homMk (pullback.fst (p i).left (p j).left) rfl
    let c : T ⟶ Pᵢ j := Over.homMk (pullback.snd (p i).left (p j).left) (by
      dsimp [T]
      rw [← Over.w (p j), ← Category.assoc, ← pullback.condition,
        Category.assoc, Over.w (p i)])
    have hbc : b ≫ p i = c ≫ p j := by
      ext
      exact pullback.condition
    exact le_antisymm
      (local_image_le a (p i) (p j) (q i) (q j) (k i) (k j) (hk i) (hk j) b c hbc)
      (local_image_le a (p j) (p i) (q j) (q i) (k j) (k i) (hk j) (hk i) c b hbc.symm)
  obtain ⟨U, hU, _⟩ := openSubscheme_existsUnique_of_fpqc
    (fun i ↦ (p i).left) hcover (fun i ↦ (q i).left.opensRange) hW
  let V : Over S := Over.mk (U.ι ≫ P.hom)
  let j : V ⟶ P := Over.homMk U.ι rfl
  have hj : IsOpenImmersion j.left := by
    change IsOpenImmersion U.ι
    infer_instance
  have : Mono j := Over.mono_of_mono_left _
  have hr (T : Over S) (z : Z.obj.obj.obj (op T)) :
      Set.range (a.app (op T) z).left ⊆ Set.range U.ι := by
    rw [Scheme.Opens.range_ι]
    exact section_range P Z a Pᵢ X p q hq k hk hcover U hU T z
  let b : Z.obj.obj ⟶ yoneda.obj V :=
    { app := fun T ↦ ↾fun z ↦ Over.homMk
        (IsOpenImmersion.lift U.ι (a.app T z).left (hr T.unop z)) (by
          change IsOpenImmersion.lift U.ι (a.app T z).left _ ≫
            (U.ι ≫ P.hom) = T.unop.hom
          rw [IsOpenImmersion.lift_fac_assoc, Over.w])
      naturality := by
        intro T T' f
        ext z
        apply (cancel_mono j).mp
        apply Over.OverMorphism.ext
        change IsOpenImmersion.lift U.ι (a.app T' (Z.obj.obj.map f z)).left _ ≫ U.ι =
          (f.unop.left ≫ IsOpenImmersion.lift U.ι (a.app T z).left _) ≫ U.ι
        rw [Category.assoc, IsOpenImmersion.lift_fac, IsOpenImmersion.lift_fac]
        exact congrArg Over.Hom.left (a.naturality_apply f z) }
  have hb (T : Over S) (z : Z.obj.obj.obj (op T)) :
      b.app (op T) z ≫ j = a.app (op T) z := by
    ext
    exact IsOpenImmersion.lift_fac _ _ _
  have : IsIso b := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro T
    rw [isIso_iff_bijective]
    constructor
    · intro z z' h
      apply sections_injective P Z a Pᵢ X p q hq k hk hcover T.unop
      rw [← hb, ← hb, h]
    · intro t
      obtain ⟨z, hz⟩ := section_exists P Z a Pᵢ X p q hq k hk hcover U hU
        T.unop (t ≫ j) (by
          rintro _ ⟨x, rfl⟩
          exact (t.left x).property)
      refine ⟨z, ?_⟩
      apply (cancel_mono j).mp
      rw [hb, hz]
  refine ⟨V, j, hj, asIso b, ?_⟩
  ext T z
  exact (hb T.unop z).symm

end AlgebraicGeometry.AlgebraicSpace
