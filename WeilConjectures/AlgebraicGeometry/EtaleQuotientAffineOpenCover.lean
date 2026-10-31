/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Limits
public import WeilConjectures.AlgebraicGeometry.AlgebraicSpace
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.Sheafification
import WeilConjectures.AlgebraicGeometry.EtaleRelationRestrictionQuotient
import WeilConjectures.AlgebraicGeometry.EtaleRelationFindingOpens
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import Mathlib.Topology.Clopen
import Mathlib.CategoryTheory.Sites.Subsheaf

/-!
# Affine chart quotients cover an étale relation quotient

Source: Stacks Project, Spaces, Tag 02WW, affine-coproduct replacement and restricted
quotient open-cover paragraphs, with Tags 02WT, 02WU, Groupoids Tag 045Z and Sites
Tag 00WK (blueprint: lem-trf-etale-quotient-affine-open-cover).

The quotient presheaves are coequalizers of Yoneda maps. Each specified sheafification
unit has the universal property for all fppf sheaves, as in the restriction interface.
The constructions below are the actual coproduct and iterated pullbacks in `Over S`.
-/

@[expose] public section

universe u

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

namespace AffineQuotientCover

/-- The chosen chart with its structural map to the base.
Source: Stacks, Spaces, Tag 02WW (blueprint: lem-trf-etale-quotient-affine-open-cover). -/
def chart {S : Scheme.{u}} (V : Over S) (𝒰 : Scheme.OpenCover.{u} V.left)
    (i : 𝒰.I₀) : Over S :=
  Over.mk (𝒰.f i ≫ V.hom)

/-- The scheme coproduct of the chosen charts, with its structural map to the base.
Source: Stacks, Spaces, Tag 02WW (blueprint: lem-trf-etale-quotient-affine-open-cover). -/
noncomputable def coproduct {S : Scheme.{u}} (V : Over S)
    (𝒰 : Scheme.OpenCover.{u} V.left) : Over S :=
  ∐ (chart V 𝒰)

/-- The canonical coproduct inclusion of a chart.
Source: Stacks, Spaces, Tag 02WW (blueprint: lem-trf-etale-quotient-affine-open-cover). -/
noncomputable def inclusion {S : Scheme.{u}} (V : Over S)
    (𝒰 : Scheme.OpenCover.{u} V.left) (i : 𝒰.I₀) : chart V 𝒰 i ⟶ coproduct V 𝒰 :=
  Sigma.ι (chart V 𝒰) i

/-- The map from the chart coproduct induced by the given open immersions.
Source: Stacks, Spaces, Tag 02WW (blueprint: lem-trf-etale-quotient-affine-open-cover). -/
noncomputable def map {S : Scheme.{u}} (V : Over S)
    (𝒰 : Scheme.OpenCover.{u} V.left) : coproduct V 𝒰 ⟶ V :=
  Sigma.desc (fun i ↦ Over.homMk (𝒰.f i))

/-- The source projection of the restriction to the chart coproduct.
Source: Stacks, Spaces, Tag 02WT (blueprint: lem-trf-etale-quotient-affine-open-cover). -/
noncomputable def source {S : Scheme.{u}} {R V : Over S} (s t : R ⟶ V)
    (𝒰 : Scheme.OpenCover.{u} V.left) :
    Limits.pullback (pullback.snd (map V 𝒰) s ≫ t) (map V 𝒰) ⟶ coproduct V 𝒰 :=
  pullback.fst (pullback.snd (map V 𝒰) s ≫ t) (map V 𝒰) ≫
    pullback.fst (map V 𝒰) s

/-- The target projection of the restriction to the chart coproduct.
Source: Stacks, Spaces, Tag 02WT (blueprint: lem-trf-etale-quotient-affine-open-cover). -/
noncomputable def target {S : Scheme.{u}} {R V : Over S} (s t : R ⟶ V)
    (𝒰 : Scheme.OpenCover.{u} V.left) :
    Limits.pullback (pullback.snd (map V 𝒰) s ≫ t) (map V 𝒰) ⟶ coproduct V 𝒰 :=
  pullback.snd (pullback.snd (map V 𝒰) s ≫ t) (map V 𝒰)

/-- The source of the relation obtained by restricting again to one summand.
Source: Stacks, Spaces, Tags 02WT/02WW
(blueprint: lem-trf-etale-quotient-affine-open-cover). -/
noncomputable def chartSource {S : Scheme.{u}} {R V : Over S} (s t : R ⟶ V)
    (𝒰 : Scheme.OpenCover.{u} V.left) (i : 𝒰.I₀) :
    Limits.pullback
      (pullback.snd (inclusion V 𝒰 i) (source s t 𝒰) ≫ target s t 𝒰) (inclusion V 𝒰 i) ⟶
      chart V 𝒰 i :=
  pullback.fst (pullback.snd (inclusion V 𝒰 i) (source s t 𝒰) ≫ target s t 𝒰)
      (inclusion V 𝒰 i) ≫ pullback.fst (inclusion V 𝒰 i) (source s t 𝒰)

/-- The target of the relation obtained by restricting again to one summand.
Source: Stacks, Spaces, Tags 02WT/02WW
(blueprint: lem-trf-etale-quotient-affine-open-cover). -/
noncomputable def chartTarget {S : Scheme.{u}} {R V : Over S} (s t : R ⟶ V)
    (𝒰 : Scheme.OpenCover.{u} V.left) (i : 𝒰.I₀) :
    Limits.pullback
      (pullback.snd (inclusion V 𝒰 i) (source s t 𝒰) ≫ target s t 𝒰) (inclusion V 𝒰 i) ⟶
      chart V 𝒰 i :=
  pullback.snd (pullback.snd (inclusion V 𝒰 i) (source s t 𝒰) ≫ target s t 𝒰)
    (inclusion V 𝒰 i)

end AffineQuotientCover

open AffineQuotientCover

-- Restriction geometry is needed before any quotient sheaf is supplied.
-- Prove it directly using the two pullback universal properties (Stacks 02WT).
private theorem restricted_geometry {S : Scheme.{u}} {R V W : Over S}
    (s t : R ⟶ V) [Mono (prod.lift s t)]
    (hrel : ∀ T : Over S, Equivalence (fun a b : T ⟶ V ↦
      ∃ r : T ⟶ R, r ≫ s = a ∧ r ≫ t = b))
    (g : W ⟶ V) [Etale s.left] [Etale t.left] [Etale g.left] :
    Mono (prod.lift (restrictedEtaleRelationSource s t g)
      (restrictedEtaleRelationTarget s t g)) ∧
    (∀ T : Over S, Equivalence (fun a b : T ⟶ W ↦
      ∃ r : T ⟶ restrictedEtaleRelation s t g,
        r ≫ restrictedEtaleRelationSource s t g = a ∧
        r ≫ restrictedEtaleRelationTarget s t g = b)) ∧
    Etale (restrictedEtaleRelationSource s t g).left ∧
    Etale (restrictedEtaleRelationTarget s t g).left := by
  let p := pullback.fst (pullback.snd g s ≫ t) g
  let q := pullback.snd (pullback.snd g s ≫ t) g
  let a := pullback.fst g s
  let b := pullback.snd g s
  have hp : IsPullback p.left q.left (b ≫ t).left g.left :=
    (IsPullback.of_hasPullback (b ≫ t) g).map (Over.forget S)
  have ha : IsPullback a.left b.left g.left s.left :=
    (IsPullback.of_hasPullback g s).map (Over.forget S)
  have hep : Etale p.left := MorphismProperty.of_isPullback hp.flip inferInstance
  have hea : Etale a.left := MorphismProperty.of_isPullback ha.flip inferInstance
  have heb : Etale b.left := MorphismProperty.of_isPullback ha inferInstance
  have het : Etale (b ≫ t).left := by
    change Etale (b.left ≫ t.left)
    infer_instance
  have heq : Etale q.left := MorphismProperty.of_isPullback hp het
  have hr (T : Over S) (x y : T ⟶ W) :
      (∃ r : T ⟶ restrictedEtaleRelation s t g,
        r ≫ restrictedEtaleRelationSource s t g = x ∧
        r ≫ restrictedEtaleRelationTarget s t g = y) ↔
      ∃ r : T ⟶ R, r ≫ s = x ≫ g ∧ r ≫ t = y ≫ g := by
    constructor
    · rintro ⟨r, rfl, rfl⟩
      refine ⟨r ≫ p ≫ b, ?_, ?_⟩
      · simp only [restrictedEtaleRelationSource, Category.assoc]
        rw [← pullback.condition]
      · simpa [p, q, b, restrictedEtaleRelationTarget, Category.assoc] using
          congrArg (fun k ↦ r ≫ k) (pullback.condition (f := b ≫ t) (g := g))
    · rintro ⟨r, hs, ht⟩
      let l := pullback.lift x r hs.symm
      refine ⟨pullback.lift l y (by simp [l, ht]), ?_, ?_⟩
      · simp [restrictedEtaleRelationSource, l]
      · simp [restrictedEtaleRelationTarget]
  refine ⟨?_, fun T ↦ ?_, ?_, heq⟩
  · constructor
    intro T x y h
    have hx : x ≫ restrictedEtaleRelationSource s t g =
        y ≫ restrictedEtaleRelationSource s t g := by
      simpa using congrArg (fun k ↦ k ≫ prod.fst) h
    have hy : x ≫ restrictedEtaleRelationTarget s t g =
        y ≫ restrictedEtaleRelationTarget s t g := by
      simpa using congrArg (fun k ↦ k ≫ prod.snd) h
    apply pullback.hom_ext
    · apply pullback.hom_ext
      · exact hx
      · apply (cancel_mono (prod.lift s t)).mp
        apply prod.hom_ext
        · simp only [Category.assoc, prod.lift_fst]
          simpa only [restrictedEtaleRelationSource, Category.assoc,
            pullback.condition] using congrArg (fun k ↦ k ≫ g) hx
        · simp only [Category.assoc, prod.lift_snd]
          simpa [restrictedEtaleRelationTarget, Category.assoc,
            pullback.condition] using congrArg (fun k ↦ k ≫ g) hy
    · exact hy
  · refine ⟨fun x ↦ (hr T x x).mpr ((hrel T).refl _), ?_, ?_⟩
    · intro x y h
      exact (hr T y x).mpr ((hrel T).symm ((hr T x y).mp h))
    · intro x y z hxy hyz
      exact (hr T x z).mpr ((hrel T).trans ((hr T x y).mp hxy) ((hr T y z).mp hyz))
  · change Etale (p.left ≫ a.left)
    infer_instance

private theorem chart_geometry {S : Scheme.{u}} (V : Over S)
    (𝒰 : Scheme.OpenCover.{u} V.left) :
    (∀ i : 𝒰.I₀, IsOpenImmersion (inclusion V 𝒰 i).left ∧
      IsClopen (Set.range (inclusion V 𝒰 i).left)) ∧
    Surjective (map V 𝒰).left ∧ Etale (map V 𝒰).left := by
  classical
  let e : (∐ 𝒰.X) ≅ (coproduct V 𝒰).left :=
    asIso (sigmaComparison (Over.forget S) (chart V 𝒰))
  have hi (i : 𝒰.I₀) :
      Sigma.ι 𝒰.X i ≫ e.hom = (inclusion V 𝒰 i).left := by
    exact ι_comp_sigmaComparison (Over.forget S) (chart V 𝒰) i
  have hm : e.hom ≫ (map V 𝒰).left = Sigma.desc 𝒰.f := by
    apply Sigma.hom_ext
    intro i
    rw [← Category.assoc, hi]
    change ((inclusion V 𝒰 i) ≫ map V 𝒰).left = _
    simp [inclusion, map, chart]
  have hopen (i : 𝒰.I₀) : IsOpenImmersion (inclusion V 𝒰 i).left := by
    rw [← hi]
    infer_instance
  refine ⟨fun i ↦ ⟨hopen i, ?_⟩, ?_, ?_⟩
  · have hc : IsClopen (Set.range (Sigma.ι 𝒰.X i)) := by
      have := (show IsClopen ((sigmaMk 𝒰.X) '' Set.range (Sigma.mk i)) from
        ⟨(sigmaMk 𝒰.X).isClosedMap _ isClopen_range_sigmaMk.1,
          (sigmaMk 𝒰.X).isOpenMap _ isClopen_range_sigmaMk.2⟩)
      simpa only [← Set.range_comp, Function.comp_def, sigmaMk_mk] using this
    have := (show IsClopen ((Scheme.homeoOfIso e) '' Set.range (Sigma.ι 𝒰.X i)) from
      ⟨(Scheme.homeoOfIso e).isClosedMap _ hc.1,
        (Scheme.homeoOfIso e).isOpenMap _ hc.2⟩)
    have hfun : (Scheme.homeoOfIso e) ∘ (Sigma.ι 𝒰.X i) =
        (inclusion V 𝒰 i).left := by
      funext x
      exact congrArg (fun k : 𝒰.X i ⟶ (coproduct V 𝒰).left ↦ k x) (hi i)
    rw [← Set.range_comp, hfun] at this
    exact this
  · constructor
    intro x
    obtain ⟨i, y, rfl⟩ := 𝒰.exists_eq x
    refine ⟨(inclusion V 𝒰 i).left y, ?_⟩
    have h := congrArg (fun f : 𝒰.X i ⟶ V.left ↦ f y)
      (show (inclusion V 𝒰 i).left ≫ (map V 𝒰).left = 𝒰.f i by
        change ((inclusion V 𝒰 i) ≫ map V 𝒰).left = _
        simp [inclusion, map, chart])
    exact h
  · have he : Etale (e.hom ≫ (map V 𝒰).left) := by
      rw [hm]
      exact IsZariskiLocalAtSource.sigmaDesc (fun i ↦ inferInstance)
    exact (MorphismProperty.cancel_left_of_respectsIso (P := @Etale) e.hom _).mp he

private theorem chart_sections_cover {S : Scheme.{u}} {V : Over S}
    (𝒰 : Scheme.OpenCover.{u} V.left) {F : (Over S)ᵒᵖ ⥤ Type u}
    (q : yoneda.obj V ⟶ F) (D : Subfunctor F)
    (hq : ∀ i : 𝒰.I₀, ∀ (T : Over S) (v : T ⟶ chart V 𝒰 i),
      D.obj (op T) (q.app (op T) (v ≫ Over.homMk (𝒰.f i)))) :
    ∀ (T : Over S) (v : T ⟶ V), (D.sheafify (Scheme.fppfTopology.over S)).obj (op T)
      (q.app (op T) v) := by
  intro T v
  let U (i : 𝒰.I₀) : Over S :=
    Over.mk (pullback.fst v.left (𝒰.f i) ≫ T.hom)
  let p (i : 𝒰.I₀) : U i ⟶ T := Over.homMk (pullback.fst v.left (𝒰.f i))
  let a (i : 𝒰.I₀) : U i ⟶ chart V 𝒰 i :=
    Over.homMk (pullback.snd v.left (𝒰.f i)) (by
      simp only [chart, Over.mk_left, Over.mk_hom, U]
      rw [← pullback.condition_assoc, Over.w])
  have ha (i : 𝒰.I₀) : p i ≫ v = a i ≫ Over.homMk (𝒰.f i) := by
    ext
    exact pullback.condition
  have hc : (Presieve.ofArrows U p).map (Over.forget S) ∈
      Scheme.fppfPrecoverage T.left := by
    apply Scheme.zariskiPrecoverage_le_fppfPrecoverage
    rw [Presieve.map_ofArrows]
    change Presieve.ofArrows (fun i ↦ Limits.pullback v.left (𝒰.f i))
      (fun i ↦ pullback.fst v.left (𝒰.f i)) ∈ Scheme.zariskiPrecoverage T.left
    exact (𝒰.pullback₁ v.left).mem₀
  change D.sieveOfSection (q.app (op T) v) ∈ (Scheme.fppfTopology.over S) T
  apply (Scheme.fppfTopology.over S).superset_covering _
    (show Sieve.generate (Presieve.ofArrows U p) ∈ (Scheme.fppfTopology.over S) T from ?_)
  · rw [Sieve.generate_le_iff]
    intro W f hf
    cases hf with
    | mk i =>
      change D.obj (op (U i)) (F.map (p i).op (q.app (op T) v))
      rw [← NatTrans.naturality_apply]
      change D.obj (op (U i)) (q.app (op (U i)) (p i ≫ v))
      rw [ha]
      exact hq i _ (a i)
  · rw [GrothendieckTopology.mem_over_iff]
    change (Sieve.generate (Presieve.ofArrows U p)).functorPushforward
      (Over.forget S) ∈ Scheme.fppfTopology T.left
    rw [← Sieve.generate_map_eq_functorPushforward]
    exact Precoverage.generate_mem_toGrothendieck hc

-- Use the locally generated image, rather than a global sheafification functor:
-- the specified universal property forces this image to be all of F (Sites 00WK).
private theorem quotient_local_chart_lifts {S : Scheme.{u}} {R V : Over S}
    (s t : R ⟶ V) (𝒰 : Scheme.OpenCover.{u} V.left)
    (F : Sheaf (Scheme.fppfTopology.over S) (Type u))
    (η : coequalizer (yoneda.map s) (yoneda.map t) ⟶ F.obj)
    (hη : ∀ G : Sheaf (Scheme.fppfTopology.over S) (Type u),
      Function.Bijective (fun k : F.obj ⟶ G.obj ↦ η ≫ k))
    (Fi : 𝒰.I₀ → Sheaf (Scheme.fppfTopology.over S) (Type u))
    (qi : ∀ i : 𝒰.I₀, yoneda.obj (chart V 𝒰 i) ⟶ (Fi i).obj)
    (γ : ∀ i : 𝒰.I₀, (Fi i).obj ⟶ F.obj)
    (hγ : ∀ i : 𝒰.I₀, qi i ≫ γ i = yoneda.map (Over.homMk (𝒰.f i)) ≫
      (coequalizer.π (yoneda.map s) (yoneda.map t) ≫ η)) :
    ∀ (T : Over S) (x : F.obj.obj (op T)),
      ∃ C : Presieve T, C.map (Over.forget S) ∈ Scheme.fppfPrecoverage T.left ∧
        ∀ (W : Over S) (f : W ⟶ T), C f →
          ∃ (i : 𝒰.I₀) (y : (Fi i).obj.obj (op W)),
            (γ i).app (op W) y = F.obj.map f.op x := by
  let J := Scheme.fppfTopology.over S
  let q := coequalizer.π (yoneda.map s) (yoneda.map t) ≫ η
  let D : Subfunctor F.obj :=
    { obj := fun T ↦ {x | ∃ (i : 𝒰.I₀) (y : (Fi i).obj.obj T), (γ i).app T y = x}
      map := by
        intro T W f x hx
        obtain ⟨i, y, rfl⟩ := hx
        exact ⟨i, (Fi i).obj.map f y, (γ i).naturality_apply f y⟩ }
  let E := D.sheafify J
  have hE : Presheaf.IsSheaf J E.toFunctor :=
    (isSheaf_iff_isSheaf_of_type J E.toFunctor).mpr
      (D.sheafify_isSheaf ((isSheaf_iff_isSheaf_of_type J F.obj).mp F.property))
  have hq : ∀ (T : Over S) (v : T ⟶ V), E.obj (op T) (q.app (op T) v) := by
    apply chart_sections_cover 𝒰 q D
    intro i T v
    refine ⟨i, (qi i).app (op T) v, ?_⟩
    exact congrArg (fun k ↦ k.app (op T) v) (hγ i)
  let qE : yoneda.obj V ⟶ E.toFunctor :=
    { app := fun T ↦ ↾fun v ↦ ⟨q.app T v, hq T.unop v⟩
      naturality := by
        intro T W f
        ext v
        apply Subtype.ext
        exact q.naturality_apply f v }
  have hqE : qE ≫ E.ι = q := rfl
  let ηE : coequalizer (yoneda.map s) (yoneda.map t) ⟶ E.toFunctor :=
    coequalizer.desc qE (by
      apply (cancel_mono E.ι).mp
      simp only [Category.assoc, hqE, q]
      exact coequalizer.condition_assoc _ _ η)
  obtain ⟨l, hl⟩ := (hη ⟨E.toFunctor, hE⟩).surjective ηE
  have hlE : l ≫ E.ι = 𝟙 F.obj := by
    apply (hη F).injective
    apply (cancel_epi (coequalizer.π (yoneda.map s) (yoneda.map t))).mp
    simp only [← Category.assoc, hl, ηE, coequalizer.π_desc, hqE, q, Category.comp_id]
  intro T x
  have hx : E.obj (op T) x := by
    have he : (l.app (op T) x).val = x :=
      congrArg (fun k ↦ k.app (op T) x) hlE
    exact he ▸ (l.app (op T) x).property
  change D.sieveOfSection x ∈ J T at hx
  have : Scheme.fppfPrecoverage.HasIsos := by
    constructor
    intro X Y f hf
    have := hf
    exact f.singleton_mem_fppfPrecoverage
  let K := Scheme.fppfPrecoverage.comap (Over.forget S)
  have hJK : J = K.toGrothendieck :=
    over_toGrothendieck_eq_toGrothendieck_comap_forget _ _
  rw [hJK] at hx
  obtain ⟨C, hC, hle⟩ := K.mem_toGrothendieck_iff_of_isStableUnderComposition.mp hx
  exact ⟨C, hC, fun W f hf ↦ hle W f hf⟩

/-- The coproduct of an affine open covering gives the same fppf quotient, and its
restricted chart quotients form a representable open covering of that quotient.
No quotient is assumed to be an algebraic space. The compatibility equations specify
precisely the canonical maps on sheafified quotients.

Source: Stacks Project, Spaces, Tag 02WW, affine-coproduct and restricted-quotient paragraphs
(blueprint: lem-trf-etale-quotient-affine-open-cover).

Proof:
1. Apply lem-weil-pbc-scheme-coproduct-family to the chart family. Its coproduct exists,
   the summand images are disjoint and open, and their complements are unions of the
   other summand images, hence open. The universal property constructs `map V 𝒰`;
   since the chosen charts cover `V`, this map is surjective on points.
2. Each chart inclusion into `V` is étale by lem-weil-pbc-open-immersion-etale. On the
   summand open cover these are the restrictions of `map V 𝒰`, so
   lem-weil-pbc-etale-local-on-source makes that map étale. It is thus flat and locally
   finitely presented (def-weil-etale-morphism); with surjectivity it is an fppf cover
   (def-pc-fppf-site), even for an infinite or empty chart index set.
3. Apply lem-trf-etale-relation-restriction-quotient to this surjective étale map. It
   gives the étale equivalence relation on the coproduct and the canonical isomorphism
   `β : Q → F`, characterized by its equation on quotient projections.
4. Apply the same restriction lemma along each summand inclusion. It gives the étale
   equivalence relations on the charts and the canonical maps `α i : Fᵢ → Q`. On test
   points, the iterated pullback consists of `(a,r,b)` with `s r = g ιᵢ a` and
   `t r = g ιᵢ b`; by def-pc-fibre-product this is the direct restriction to the chart.
   The composite sends `[a]` to `[g ιᵢ a]`; def-weil-pbc-sheafification extends this
   equation uniquely to the indicated canonical maps on sheafifications.
5. Reflexivity gives a common section of the two coproduct-relation projections by
   applying the equivalence relation to the identity coproduct-valued point. Both
   projections are therefore surjective. Their étaleness supplies flatness and local
   finite presentation; the summand inclusion has these too. These are exactly the
   hypotheses required by the finding-opens lemma.
6. Apply lem-trf-etale-relation-finding-opens to each summand. Each `α i` is representable
   by open immersions. For a test map to `F`, compose with `β⁻¹` and use the resulting
   open subscheme representing the pullback. Since `β` is an isomorphism, it also
   represents the pullback of `α i ≫ β`, proving the asserted open immersion.
7. Given `x ∈ F(T)`, lem-weil-pbc-site-sheafification-sections-local supplies an fppf
   cover with representatives `vₐ : Tₐ → V`. Pull back the chosen open cover along
   every `vₐ` and compose coverings (def-weil-pbc-sites-and-cohomology). On
   `Tₐ ×_V Vᵢ`, the projection to `Vᵢ` gives a section of `Fᵢ`, whose image is the
   restriction of `x` by the compatibility equations. This proves the displayed local
   lifting statement. Empty index sets and empty test schemes are covered by the
   same covering axioms; no nonemptiness hypothesis is used. -/
theorem etale_quotient_affine_open_cover {S : Scheme.{u}} {R V : Over S}
    (s t : R ⟶ V) [Mono (prod.lift s t)]
    (hrel : ∀ T : Over S, Equivalence (fun a b : T ⟶ V ↦
      ∃ r : T ⟶ R, r ≫ s = a ∧ r ≫ t = b))
    [Etale s.left] [Etale t.left]
    (𝒰 : Scheme.OpenCover.{u} V.left) [∀ i : 𝒰.I₀, IsAffine (𝒰.X i)]
    (F : Sheaf (Scheme.fppfTopology.over S) (Type u))
    (η : coequalizer (yoneda.map s) (yoneda.map t) ⟶ F.obj)
    (hη : ∀ G : Sheaf (Scheme.fppfTopology.over S) (Type u),
      Function.Bijective (fun k : F.obj ⟶ G.obj ↦ η ≫ k)) :
    (∀ i : 𝒰.I₀, IsOpenImmersion (inclusion V 𝒰 i).left ∧
      IsClopen (Set.range (inclusion V 𝒰 i).left)) ∧
    Surjective (map V 𝒰).left ∧ Etale (map V 𝒰).left ∧
    Mono (prod.lift (source s t 𝒰) (target s t 𝒰)) ∧
    (∀ T : Over S, Equivalence (fun a b : T ⟶ coproduct V 𝒰 ↦
      ∃ r : T ⟶ Limits.pullback (pullback.snd (map V 𝒰) s ≫ t) (map V 𝒰),
        r ≫ source s t 𝒰 = a ∧ r ≫ target s t 𝒰 = b)) ∧
    Etale (source s t 𝒰).left ∧ Etale (target s t 𝒰).left ∧
    (∀ i : 𝒰.I₀,
      Mono (prod.lift (chartSource s t 𝒰 i) (chartTarget s t 𝒰 i)) ∧
      (∀ T : Over S, Equivalence (fun a b : T ⟶ chart V 𝒰 i ↦
        ∃ r : T ⟶ Limits.pullback
          (pullback.snd (inclusion V 𝒰 i) (source s t 𝒰) ≫ target s t 𝒰) (inclusion V 𝒰 i),
          r ≫ chartSource s t 𝒰 i = a ∧ r ≫ chartTarget s t 𝒰 i = b)) ∧
      Etale (chartSource s t 𝒰 i).left ∧ Etale (chartTarget s t 𝒰 i).left) ∧
    ∀ (Q : Sheaf (Scheme.fppfTopology.over S) (Type u))
      (ηQ : coequalizer (yoneda.map (source s t 𝒰))
        (yoneda.map (target s t 𝒰)) ⟶ Q.obj)
      (_hηQ : ∀ G : Sheaf (Scheme.fppfTopology.over S) (Type u),
        Function.Bijective (fun k : Q.obj ⟶ G.obj ↦ ηQ ≫ k))
      (Fi : 𝒰.I₀ → Sheaf (Scheme.fppfTopology.over S) (Type u))
      (ηi : ∀ i : 𝒰.I₀, coequalizer (yoneda.map (chartSource s t 𝒰 i))
        (yoneda.map (chartTarget s t 𝒰 i)) ⟶ (Fi i).obj)
      (_hηi : ∀ (i : 𝒰.I₀) (G : Sheaf (Scheme.fppfTopology.over S) (Type u)),
        Function.Bijective (fun k : (Fi i).obj ⟶ G.obj ↦ ηi i ≫ k)),
      ∃ (β : Q.obj ⟶ F.obj) (α : ∀ i : 𝒰.I₀, (Fi i).obj ⟶ Q.obj),
        IsIso β ∧
        (coequalizer.π (yoneda.map (source s t 𝒰)) (yoneda.map (target s t 𝒰)) ≫ ηQ) ≫ β =
          yoneda.map (map V 𝒰) ≫ (coequalizer.π (yoneda.map s) (yoneda.map t) ≫ η) ∧
        (∀ i : 𝒰.I₀,
          (coequalizer.π (yoneda.map (chartSource s t 𝒰 i))
            (yoneda.map (chartTarget s t 𝒰 i)) ≫ ηi i) ≫ α i =
              yoneda.map (inclusion V 𝒰 i) ≫
                (coequalizer.π (yoneda.map (source s t 𝒰)) (yoneda.map (target s t 𝒰)) ≫ ηQ) ∧
          IsRepresentableWith (fun _ _ p ↦ IsOpenImmersion p.left) (α i ≫ β)) ∧
        ∀ (T : Over S) (x : F.obj.obj (op T)),
          ∃ C : Presieve T, C.map (Over.forget S) ∈ Scheme.fppfPrecoverage T.left ∧
            ∀ (W : Over S) (f : W ⟶ T), C f →
              ∃ (i : 𝒰.I₀) (y : (Fi i).obj.obj (op W)),
                (α i ≫ β).app (op W) y = F.obj.map f.op x := by
  classical
  obtain ⟨hinc, hg, hge⟩ := chart_geometry V 𝒰
  have := hg
  have := hge
  obtain ⟨hm, hr, hs, ht⟩ := restricted_geometry s t hrel (map V 𝒰)
  change Mono (prod.lift (source s t 𝒰) (target s t 𝒰)) at hm
  change ∀ T : Over S, Equivalence (fun a b : T ⟶ coproduct V 𝒰 ↦
    ∃ r, r ≫ source s t 𝒰 = a ∧ r ≫ target s t 𝒰 = b) at hr
  change Etale (source s t 𝒰).left at hs
  change Etale (target s t 𝒰).left at ht
  have := hm
  have := hs
  have := ht
  have hic (i : 𝒰.I₀) : IsOpenImmersion (inclusion V 𝒰 i).left := (hinc i).1
  have hri (i : 𝒰.I₀) :=
    restricted_geometry (source s t 𝒰) (target s t 𝒰) hr (inclusion V 𝒰 i)
  refine ⟨hinc, hg, hge, hm, hr, hs, ht, ?_, ?_⟩
  · intro i
    exact hri i
  · intro Q ηQ hηQ Fi ηi hηi
    obtain ⟨_, _, _, _, β, hβ, _, hβiso⟩ :=
      etale_relation_restriction_quotient s t hrel (map V 𝒰) F η hη Q ηQ hηQ
    have := hβiso hg
    obtain ⟨e, he₁, he₂⟩ := (hr (coproduct V 𝒰)).refl (𝟙 _)
    have hss : Surjective (source s t 𝒰).left := by
      constructor
      intro x
      refine ⟨e.left x, ?_⟩
      exact congrArg (fun k : coproduct V 𝒰 ⟶ coproduct V 𝒰 ↦ k.left x) he₁
    have hts : Surjective (target s t 𝒰).left := by
      constructor
      intro x
      refine ⟨e.left x, ?_⟩
      exact congrArg (fun k : coproduct V 𝒰 ⟶ coproduct V 𝒰 ↦ k.left x) he₂
    have halpha (i : 𝒰.I₀) := etale_relation_finding_opens
      (source s t 𝒰) (target s t 𝒰) hr (inclusion V 𝒰 i) Q ηQ hηQ
      (Fi i) (ηi i) (hηi i)
    choose α hα hαopen using halpha
    change ∀ i, (coequalizer.π (yoneda.map (chartSource s t 𝒰 i))
      (yoneda.map (chartTarget s t 𝒰 i)) ≫ ηi i) ≫ α i =
        yoneda.map (inclusion V 𝒰 i) ≫
          (coequalizer.π (yoneda.map (source s t 𝒰))
            (yoneda.map (target s t 𝒰)) ≫ ηQ) at hα
    change (coequalizer.π (yoneda.map (source s t 𝒰))
      (yoneda.map (target s t 𝒰)) ≫ ηQ) ≫ β =
        yoneda.map (map V 𝒰) ≫ (coequalizer.π (yoneda.map s) (yoneda.map t) ≫ η) at hβ
    refine ⟨β, α, inferInstance, hβ, ?_, ?_⟩
    · intro i
      refine ⟨hα i, ?_⟩
      intro T a
      obtain ⟨U, p, q, hp, ho⟩ := hαopen i T (a ≫ inv β)
      refine ⟨U, p, q, ?_, ho⟩
      have hi : IsPullback (a ≫ inv β) (𝟙 _) β a :=
        IsPullback.of_vert_isIso ⟨by simp⟩
      simpa using hp.paste_vert hi
    · apply quotient_local_chart_lifts s t 𝒰 F η hη Fi
        (fun i ↦ coequalizer.π (yoneda.map (chartSource s t 𝒰 i))
          (yoneda.map (chartTarget s t 𝒰 i)) ≫ ηi i) (fun i ↦ α i ≫ β)
      intro i
      rw [← Category.assoc, hα, Category.assoc, hβ, ← Category.assoc, ← yoneda.map_comp]
      congr 2
      simp [inclusion, map, chart]

end AlgebraicGeometry.AlgebraicSpace
