/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q62
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Limits.Types.Colimits
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.Sheafification
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Sheaf.AlgebraicGeometry.EtaleRelationKernelPair
import Mathlib.CategoryTheory.Sites.LocallySurjective
import Mathlib.CategoryTheory.Limits.Types.Pullbacks
import Mathlib.CategoryTheory.Sites.SubcanonicalOver

/-!
# Incidence open models for a restricted fppf-relation quotient

Source: Stacks Project, Spaces, Tag 02WU (lemma-finding-opens), the incidence open
image and the two directions of its representing property after a lift to the atlas
(blueprint: lem-trf-relation-incidence-open-model).

The coequalizers of the Yoneda maps are the pointwise quotient presheaves. The pairs
`F, η` and `F', η'` specify their sheafifications by the sheafification universal
property. This uses no assumption of sheafification for every small-valued presheaf
on the big site. The compatibility `hα` specifies the canonical map on quotients.

For each `v : V ⟶ U`, the asserted pullback square gives the natural isomorphism
from the representable of the open preimage to `h_V ×_F F'`, over `h_V`. The last
clause gives its compatibility with every map over `U`: `kW` is the unique map
between the open preimages over `k`. Such a map exists by restriction to opens.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

-- The image-subsheaf argument works for any specified small-valued sheafification,
-- even when the big site does not admit sheafification in that value universe.
private theorem locallySurjective_of_universal
    {C : Type*} [Category* C] (J : GrothendieckTopology C)
    {P : Cᵒᵖ ⥤ Type u} (F : Sheaf J (Type u)) (η : P ⟶ F.obj)
    (hη : ∀ G : Sheaf J (Type u),
      Function.Bijective (fun f : F.obj ⟶ G.obj ↦ η ≫ f)) :
    Presheaf.IsLocallySurjective J η := by
  let R := (Subfunctor.range η).sheafify J
  have hR : Presheaf.IsSheaf J R.toFunctor :=
    (isSheaf_iff_isSheaf_of_type J _).mpr
      ((Subfunctor.range η).sheafify_isSheaf
        ((isSheaf_iff_isSheaf_of_type J _).mp F.property))
  obtain ⟨l, hl⟩ := (hη ⟨R.toFunctor, hR⟩).surjective (Subfunctor.toRangeSheafify J η)
  have he : l ≫ R.ι = 𝟙 F.obj := by
    apply (hη F).injective
    change η ≫ l ≫ R.ι = η ≫ 𝟙 F.obj
    dsimp only at hl
    rw [← Category.assoc, hl]
    simp [Subfunctor.toRangeSheafify, R]
  rw [Presheaf.isLocallySurjective_iff_range_sheafify_eq_top']
  apply le_antisymm le_top
  intro T z _
  have hz : (l.app T z).val = z := by
    simpa using ConcreteCategory.congr_hom (NatTrans.congr_app he T) z
  exact hz ▸ (l.app T z).property

-- A monomorphic map of sheaves has a range already closed under local membership.
private theorem range_closed
    {C : Type*} [Category* C] (J : GrothendieckTopology C)
    {F G : Sheaf J (Type u)} (α : F.obj ⟶ G.obj) [Mono α]
    {T : C} (z : G.obj.obj (op T))
    (hz : Presheaf.imageSieve α z ∈ J T) : ∃ x, α.app (op T) x = z := by
  have hR : Presieve.IsSheaf J (Subfunctor.range α).toFunctor :=
    Presieve.isSheaf_iso J (asIso (Subfunctor.toRange α))
      ((isSheaf_iff_isSheaf_of_type J _).mp F.property)
  have he := (Subfunctor.range α).eq_sheafify
    ((isSheaf_iff_isSheaf_of_type J _).mp G.property) hR
  have hm : z ∈ ((Subfunctor.range α).sheafify J).obj (op T) := hz
  rw [← he] at hm
  exact hm

private theorem yoneda_locallySurjective_of_cover
    {C : Type*} [Category.{u} C] (J : GrothendieckTopology C)
    {X Y : C} (f : X ⟶ Y) (hf : Sieve.generate (Presieve.singleton f) ∈ J Y) :
    Presheaf.IsLocallySurjective J (yoneda.map f) := by
  constructor
  intro T a
  apply J.superset_covering ?_ (J.pullback_stable a hf)
  rintro Z b ⟨V, c, _, ⟨⟩, hc⟩
  exact ⟨c, hc⟩

private theorem over_cover
    {S : Scheme.{u}} {X Y : Over S} (f : X ⟶ Y)
    [Surjective f.left] [Flat f.left] [LocallyOfFinitePresentation f.left] :
    Sieve.generate (Presieve.singleton f) ∈ (Scheme.fppfTopology.over S) Y := by
  rw [GrothendieckTopology.mem_over_iff]
  change (Sieve.generate (Presieve.singleton f)).functorPushforward (Over.forget S) ∈ _
  rw [← Sieve.generate_map_eq_functorPushforward, Presieve.map_singleton]
  exact Precoverage.generate_mem_toGrothendieck f.left.singleton_mem_fppfPrecoverage

/-- The incidence image of a restricted fppf relation is open and represents every
pullback of the restricted quotient along a map to its atlas, compatibly with further
pullback. The image is an actual open subscheme and its incidence map is fppf.

Source: Stacks Project, Spaces, Tag 02WU (lemma-finding-opens)
(blueprint: lem-trf-relation-incidence-open-model).

Proof:
1. The projection `U' ×_U R → R` is a base change of `g`; it is flat and locally of
   finite presentation. Composing with `t` gives these properties for the incidence
   map `p`. No surjectivity of `g`, quasi-compactness or quasi-separatedness is used.
   Use lem-weil-pbc-flat-morphism-base-change, lem-weil-pbc-qcqs-morphism-permanence(3),
   lem-pc-flat-compose and lem-sbc-locally-finite-presentation-composition.
2. A flat locally finitely presented morphism is open, so its image `W` is open.
   Factor `p` uniquely through `W`. The factorization square along the open immersion
   `W → U` is Cartesian, so the factor is flat and locally of finite presentation.
   It is surjective by the definition of the image; its singleton family is fppf.
   Use lem-weil-pbc-flat-lfp-open, lem-weil-pbc-morphism-factors-through-open-subscheme,
   the base-change lemmas of Step 1 and def-pc-fppf-site.
3. A monomorphic map of sheaves has a range closed under local membership: its
   range presheaf is isomorphic to its source, hence is already a sheaf. The fppf
   covering `E → W` makes `h_E → h_W` locally surjective. The incidence identity
   `α q'(b) = q(p)` therefore gives a section of `F'(W)` mapping to `q(W → U)`.
   Yoneda gives the comparison `βW : h_W → F'`.
4. The specified universal property of `η'` implies its local surjectivity without
   any large-site sheafification instance: sheafify its image inside `F'`, factor
   `η'` into this subsheaf, and apply the universal property to obtain a retraction
   of the inclusion. Hence the locally generated image is all of `F'`. The
   coequalizer projection is sectionwise surjective, so `q'` is locally surjective.
5. Given `a : T → U` and `z ∈ F'(T)` with `q(a) = α(z)`, locally lift `z` to maps
   `c : Z → U'`. The kernel-pair theorem gives `d : Z → R` with `s d = g c` and
   `t d = a|Z`. These define maps to `E`, and hence local factorizations of `a`
   through `W`. The range of `h_W → h_U` is a sheaf by Step 3, so the local
   factorizations give a global factorization. This uses
   lem-trf-etale-relation-kernel-pair, def-pc-fibre-product and the sheaf axiom.
6. The factorization just obtained and injectivity of `α` prove sectionwise that
   `(h_W → h_U, βW)` is a pullback. For every `v : V → U`, the restriction square
   for `v⁻¹(W)` is Cartesian. Apply Yoneda and paste with this first pullback.
7. For a map `k` over `U`, the two induced maps from the restricted open to `W`
   agree after composition with the monomorphism `W → U`, so they agree. Applying
   Yoneda and composing with `βW` proves the final compatibility. -/
theorem relation_incidence_open_model
    {S : Scheme.{u}} {R U U' : Over S} (s t : R ⟶ U)
    [Mono (prod.lift s t)]
    (hrel : ∀ T : Over S, Equivalence (fun a b : T ⟶ U ↦
      ∃ r : T ⟶ R, r ≫ s = a ∧ r ≫ t = b))
    [Surjective s.left] [Flat s.left] [LocallyOfFinitePresentation s.left]
    [Surjective t.left] [Flat t.left] [LocallyOfFinitePresentation t.left]
    (g : U' ⟶ U) [Flat g.left] [LocallyOfFinitePresentation g.left]
    (F : Sheaf (Scheme.fppfTopology.over S) (Type u))
    (η : coequalizer (yoneda.map s) (yoneda.map t) ⟶ F.obj)
    (hη : ∀ G : Sheaf (Scheme.fppfTopology.over S) (Type u),
      Function.Bijective (fun f : F.obj ⟶ G.obj ↦ η ≫ f))
    (F' : Sheaf (Scheme.fppfTopology.over S) (Type u))
    (η' : coequalizer
      (yoneda.map (pullback.fst (pullback.snd g s ≫ t) g ≫ pullback.fst g s))
      (yoneda.map (pullback.snd (pullback.snd g s ≫ t) g)) ⟶ F'.obj)
    (hη' : ∀ G : Sheaf (Scheme.fppfTopology.over S) (Type u),
      Function.Bijective (fun f : F'.obj ⟶ G.obj ↦ η' ≫ f))
    (α : F'.obj ⟶ F.obj)
    (hα : (coequalizer.π
        (yoneda.map (pullback.fst (pullback.snd g s ≫ t) g ≫ pullback.fst g s))
        (yoneda.map (pullback.snd (pullback.snd g s ≫ t) g)) ≫ η') ≫ α =
      yoneda.map g ≫ (coequalizer.π (yoneda.map s) (yoneda.map t) ≫ η))
    (hα_injective : ∀ T : Over S, Function.Injective (α.app (op T))) :
    Flat (pullback.snd g s ≫ t).left ∧
    LocallyOfFinitePresentation (pullback.snd g s ≫ t).left ∧
    ∃ W : U.left.Opens,
      (W : Set U.left) = Set.range (pullback.snd g s ≫ t).left ∧
      (∃ pW : (pullback g s).left ⟶ W.toScheme,
        pW ≫ W.ι = (pullback.snd g s ≫ t).left ∧
        Surjective pW ∧ Flat pW ∧ LocallyOfFinitePresentation pW) ∧
      ∃ β : ∀ (V : Over S) (v : V ⟶ U),
          yoneda.obj (Over.mk ((v.left ⁻¹ᵁ W).ι ≫ V.hom)) ⟶ F'.obj,
        (∀ (V : Over S) (v : V ⟶ U),
          IsPullback (yoneda.map (Over.homMk (v.left ⁻¹ᵁ W).ι rfl)) (β V v)
            (yoneda.map v ≫ (coequalizer.π (yoneda.map s) (yoneda.map t) ≫ η)) α) ∧
        ∀ (V₁ V : Over S) (v : V ⟶ U) (k : V₁ ⟶ V)
          (kW : Over.mk (((k ≫ v).left ⁻¹ᵁ W).ι ≫ V₁.hom) ⟶
            Over.mk ((v.left ⁻¹ᵁ W).ι ≫ V.hom)),
          kW ≫ Over.homMk (v.left ⁻¹ᵁ W).ι rfl =
              Over.homMk ((k ≫ v).left ⁻¹ᵁ W).ι rfl ≫ k →
            yoneda.map kW ≫ β V v = β V₁ (k ≫ v) := by
  classical
  let E := pullback g s
  let p : E ⟶ U := pullback.snd g s ≫ t
  let b : E ⟶ U' := pullback.fst g s
  let r : E ⟶ R := pullback.snd g s
  have hgs := (IsPullback.of_hasPullback g s).map (Over.forget S)
  have : Flat r.left := MorphismProperty.of_isPullback hgs ‹Flat g.left›
  have : LocallyOfFinitePresentation r.left :=
    MorphismProperty.of_isPullback hgs ‹LocallyOfFinitePresentation g.left›
  have : Flat p.left := Flat.comp r.left t.left
  have : LocallyOfFinitePresentation p.left :=
    locallyOfFinitePresentation_comp r.left t.left
  refine ⟨‹Flat p.left›, ‹LocallyOfFinitePresentation p.left›, ?_⟩
  let W : U.left.Opens := ⟨Set.range p.left, p.left.isOpenMap.isOpen_range⟩
  let pW : E.left ⟶ W.toScheme := IsOpenImmersion.lift W.ι p.left (by simp [W])
  have hpW : pW ≫ W.ι = p.left := IsOpenImmersion.lift_fac _ _ _
  have hWpb := (IsOpenImmersion.isPullback_lift_id p.left W.ι (by simp [W])).flip
  have : Flat pW := MorphismProperty.of_isPullback hWpb ‹Flat p.left›
  have : LocallyOfFinitePresentation pW :=
    MorphismProperty.of_isPullback hWpb ‹LocallyOfFinitePresentation p.left›
  have : Surjective pW := by
    constructor
    intro x
    obtain ⟨y, hy⟩ := x.property
    refine ⟨y, W.ι.isOpenEmbedding.injective ?_⟩
    change (pW ≫ W.ι) y = W.ι x
    rw [hpW]
    exact hy
  refine ⟨W, rfl, ⟨pW, hpW, inferInstance, inferInstance, inferInstance⟩, ?_⟩
  let J := Scheme.fppfTopology.over S
  let q := coequalizer.π (yoneda.map s) (yoneda.map t) ≫ η
  let q' := coequalizer.π
    (yoneda.map (pullback.fst (pullback.snd g s ≫ t) g ≫ pullback.fst g s))
    (yoneda.map (pullback.snd (pullback.snd g s ≫ t) g)) ≫ η'
  let WO : Over S := Over.mk (W.ι ≫ U.hom)
  let i : WO ⟶ U := Over.homMk W.ι rfl
  let e : E ⟶ WO := Over.homMk pW (by
    change pW ≫ W.ι ≫ U.hom = E.hom
    rw [← Category.assoc, hpW]
    exact Over.w p)
  have hei : e ≫ i = p := by ext; exact hpW
  have hα' : q' ≫ α = yoneda.map g ≫ q := hα
  have hqrel : yoneda.map s ≫ q = yoneda.map t ≫ q := by
    dsimp [q]
    rw [coequalizer.condition_assoc]
  have hqp : yoneda.map b ≫ q' ≫ α = yoneda.map p ≫ q := by
    rw [hα', ← Category.assoc, ← Functor.map_comp]
    change yoneda.map (pullback.fst g s ≫ g) ≫ q = _
    rw [pullback.condition, Functor.map_comp, Category.assoc, hqrel]
    rfl
  have : Mono α := (NatTrans.mono_iff_mono_app α).mpr fun T ↦
    (mono_iff_injective _).mpr (hα_injective T.unop)
  have : Surjective e.left := ‹Surjective pW›
  have : Flat e.left := ‹Flat pW›
  have : LocallyOfFinitePresentation e.left := ‹LocallyOfFinitePresentation pW›
  have : Presheaf.IsLocallySurjective J (yoneda.map e) :=
    yoneda_locallySurjective_of_cover J e (over_cover e)
  obtain ⟨zW, hzW⟩ : ∃ z, α.app (op WO) z = q.app (op WO) i := by
    apply range_closed J α
    apply J.superset_covering ?_
      (Presheaf.imageSieve_mem J (yoneda.map e) (𝟙 WO))
    intro T f hf
    obtain ⟨c, hc⟩ := hf
    change c ≫ e = f ≫ 𝟙 WO at hc
    have hc' : c ≫ e = f := hc.trans (Category.comp_id f)
    refine ⟨q'.app (op T) (c ≫ b), ?_⟩
    have heq := ConcreteCategory.congr_hom (NatTrans.congr_app hqp (op T)) c
    change α.app (op T) (q'.app (op T) (c ≫ b)) = q.app (op T) (c ≫ p) at heq
    rw [← hei, ← Category.assoc, hc'] at heq
    rw [heq]
    exact q.naturality_apply f.op i
  let βW : yoneda.obj WO ⟶ F'.obj := yonedaEquiv.symm zW
  have hβW : yoneda.map i ≫ q = βW ≫ α := by
    apply yonedaEquiv.injective
    rw [yonedaEquiv_comp, yonedaEquiv_comp, yonedaEquiv_yoneda_map]
    simpa [βW] using hzW.symm
  have : Presheaf.IsLocallySurjective J η' := locallySurjective_of_universal J F' η' hη'
  have : Presheaf.IsLocallySurjective J
      (coequalizer.π
        (yoneda.map (pullback.fst (pullback.snd g s ≫ t) g ≫ pullback.fst g s))
        (yoneda.map (pullback.snd (pullback.snd g s ≫ t) g))) :=
    Presheaf.isLocallySurjective_of_surjective J _ fun T ↦ by
      apply (epi_iff_surjective _).mp
      infer_instance
  have : Presheaf.IsLocallySurjective J q' := inferInstance
  have hkernel := etale_relation_kernel_pair s t hrel F η hη
  have hiSheaf : Presheaf.IsSheaf J (yoneda.obj WO) :=
    (isSheaf_iff_isSheaf_of_type J _).mpr
      (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _)
  have huSheaf : Presheaf.IsSheaf J (yoneda.obj U) :=
    (isSheaf_iff_isSheaf_of_type J _).mpr
      (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _)
  have hfactor : ∀ (T : Over S) (a : T ⟶ U) (z : F'.obj.obj (op T)),
      q.app (op T) a = α.app (op T) z → ∃ l : T ⟶ WO, l ≫ i = a := by
    intro T a z haz
    apply range_closed J (F := ⟨yoneda.obj WO, hiSheaf⟩)
      (G := ⟨yoneda.obj U, huSheaf⟩) (yoneda.map i) a
    apply J.superset_covering ?_ (Presheaf.imageSieve_mem J q' z)
    intro Z f hf
    obtain ⟨c, hc⟩ := hf
    have hca : q.app (op Z) (c ≫ g) = q.app (op Z) (f ≫ a) := by
      have hcompat := ConcreteCategory.congr_hom (NatTrans.congr_app hα' (op Z)) c
      change α.app (op Z) (q'.app (op Z) c) = q.app (op Z) (c ≫ g) at hcompat
      rw [← hcompat, hc, α.naturality_apply, ← haz]
      exact (q.naturality_apply f.op a).symm
    obtain ⟨d, hd₁, hd₂⟩ := Types.exists_of_isPullback (hkernel.app (op Z))
      (c ≫ g) (f ≫ a) hca
    change d ≫ s = c ≫ g at hd₁
    change d ≫ t = f ≫ a at hd₂
    let ce : Z ⟶ E := pullback.lift c d hd₁.symm
    refine ⟨ce ≫ e, ?_⟩
    change (ce ≫ e) ≫ i = f ≫ a
    rw [Category.assoc, hei]
    dsimp [ce, p]
    rw [pullback.lift_snd_assoc, hd₂]
  have hpbW : IsPullback (yoneda.map i) βW q α := by
    apply IsPullback.of_forall_isPullback_app
    intro T
    apply (Types.isPullback_iff _ _ _ _).mpr
    refine ⟨NatTrans.congr_app hβW T, ?_, ?_⟩
    · intro x y h
      exact (mono_iff_injective ((yoneda.map i).app T)).mp inferInstance h.1
    · intro a z haz
      obtain ⟨l, hl⟩ := hfactor T.unop a z haz
      refine ⟨l, hl, ?_⟩
      apply hα_injective T.unop
      have heq := ConcreteCategory.congr_hom (NatTrans.congr_app hβW T) l
      change q.app T (l ≫ i) = α.app T (βW.app T l) at heq
      rw [← heq, hl]
      exact haz
  let WV (V : Over S) (v : V ⟶ U) : Over S :=
    Over.mk ((v.left ⁻¹ᵁ W).ι ≫ V.hom)
  let j (V : Over S) (v : V ⟶ U) : WV V v ⟶ V :=
    Over.homMk (v.left ⁻¹ᵁ W).ι rfl
  let l (V : Over S) (v : V ⟶ U) : WV V v ⟶ WO :=
    Over.homMk (v.left ∣_ W) (by
      change (v.left ∣_ W) ≫ (W.ι ≫ U.hom) = (v.left ⁻¹ᵁ W).ι ≫ V.hom
      rw [← Category.assoc, morphismRestrict_ι, Category.assoc, Over.w v])
  have hl (V : Over S) (v : V ⟶ U) : j V v ≫ v = l V v ≫ i := by
    ext
    exact (morphismRestrict_ι v.left W).symm
  have hpb (V : Over S) (v : V ⟶ U) :
      IsPullback (yoneda.map (j V v)) (yoneda.map (l V v)) (yoneda.map v) (yoneda.map i) := by
    apply IsPullback.map
    apply IsPullback.of_map_of_faithful (Over.forget S)
    exact (isPullback_morphismRestrict v.left W).flip
  refine ⟨fun V v ↦ yoneda.map (l V v) ≫ βW, ?_, ?_⟩
  · intro V v
    exact (hpb V v).paste_vert hpbW
  · intro V₁ V v k kW hk
    have he : kW ≫ l V v = l V₁ (k ≫ v) := by
      apply (cancel_mono i).mp
      rw [Category.assoc, ← hl, ← Category.assoc, hk, Category.assoc, hl]
    simpa only [← Category.assoc, ← Functor.map_comp] using
      congrArg (fun f ↦ yoneda.map f ≫ βW) he

end AlgebraicGeometry.Scheme
