/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AlgebraicSpace
public import WeilConjectures.AlgebraicGeometry.AlgebraicSpacePointTopology
public import WeilConjectures.AlgebraicGeometry.AlgebraicSpaceOpenSubspace
public import WeilConjectures.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Limits.Types.Colimits
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
import WeilConjectures.AlgebraicGeometry.ProperCurveModuli
import Mathlib.CategoryTheory.Sites.Subsheaf
import Mathlib.CategoryTheory.Limits.Types.Pullbacks
import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
import WeilConjectures.AlgebraicGeometry.EtalePullbackRelationPresheaf
import WeilConjectures.AlgebraicGeometry.EtaleAtlasPresentation
import WeilConjectures.AlgebraicGeometry.EtaleRelationRestrictionQuotient
import WeilConjectures.AlgebraicGeometry.EtaleRelationQuotient
import WeilConjectures.AlgebraicGeometry.EtaleRelationFindingOpens
import Mathlib.AlgebraicGeometry.Restrict
import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-!
# The invariant-open quotient of an étale atlas

Source: Stacks Project, Properties of Spaces, Tag 03BZ (lemma-open-subspaces),
inverse construction; Spaces, Tags 0262, 02WT, 02WW and 02WU
(blueprint: lem-a1-space-invariant-open-quotient).

Schemes representing fibre products are specified by their pullback squares. The two
squares with the same `r : RV ⟶ R` express equality as open subschemes of `R`, including
their scheme structures. They also identify `RV` with the double restriction of the
relation to `V`. The quotient sheaf and its sheafification unit are existentially supplied,
with the universal property at this particular presheaf quotient, in the original
value universe. No sheafification instance for every presheaf on the big site is assumed.
-/

@[expose] public section

universe u

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

/-- Sheafify a subpresheaf inside an existing sheaf, in its original universe. -/
private theorem reflection_of_mono {C : Type*} [Category C]
    (J : GrothendieckTopology C) {P : Cᵒᵖ ⥤ Type u} (F : Sheaf J (Type u))
    (f : P ⟶ F.obj) [Mono f] :
    ∃ (H : Sheaf J (Type u)) (η : P ⟶ H.obj),
      ∀ G : Sheaf J (Type u), Function.Bijective (fun g : H.obj ⟶ G.obj ↦ η ≫ g) := by
  let K := Subfunctor.range f
  let H : Sheaf J (Type u) := ⟨(K.sheafify J).toFunctor,
    (isSheaf_iff_isSheaf_of_type _ _).2
      (K.sheafify_isSheaf ((isSheaf_iff_isSheaf_of_type _ _).1 F.property))⟩
  refine ⟨H, Subfunctor.toRangeSheafify J f, fun G ↦ ⟨?_, ?_⟩⟩
  · intro g h e
    apply K.to_sheafify_lift_unique ((isSheaf_iff_isSheaf_of_type _ _).1 G.property)
    apply (cancel_epi (Subfunctor.toRange f)).1
    exact e
  · intro g
    refine ⟨K.sheafifyLift (inv (Subfunctor.toRange f) ≫ g)
      ((isSheaf_iff_isSheaf_of_type _ _).1 G.property), ?_⟩
    dsimp [Subfunctor.toRangeSheafify]
    rw [Category.assoc, Subfunctor.to_sheafifyLift, IsIso.hom_inv_id_assoc]

/-- A represented kernel pair embeds its presheaf quotient into the target. -/
private theorem quotient_desc_mono {C : Type*} [Category.{u} C]
    {R U : C} {F : Cᵒᵖ ⥤ Type u} (s t : R ⟶ U) (p : yoneda.obj U ⟶ F)
    (h : IsPullback (yoneda.map s) (yoneda.map t) p p) :
    Mono (coequalizer.desc p h.w) := by
  apply (NatTrans.mono_iff_mono_app _).2
  intro T
  apply (CategoryTheory.mono_iff_injective _).2
  intro x y e
  obtain ⟨a, rfl⟩ := (CategoryTheory.epi_iff_surjective
    ((coequalizer.π (yoneda.map s) (yoneda.map t)).app T)).1 inferInstance x
  obtain ⟨b, rfl⟩ := (CategoryTheory.epi_iff_surjective
    ((coequalizer.π (yoneda.map s) (yoneda.map t)).app T)).1 inferInstance y
  have he := ConcreteCategory.congr_hom
    (congr_app (coequalizer.π_desc p h.w) T)
  have e' : p.app T a = p.app T b := (he a).symm.trans (e.trans (he b))
  obtain ⟨r, hr, ht⟩ := Types.exists_of_isPullback (h.app T) a b e'
  have hc := ConcreteCategory.congr_hom
    (congr_app (coequalizer.condition (yoneda.map s) (yoneda.map t)) T) r
  change r ≫ s = a at hr
  change r ≫ t = b at ht
  change (coequalizer.π (yoneda.map s) (yoneda.map t)).app T (r ≫ s) =
    (coequalizer.π (yoneda.map s) (yoneda.map t)).app T (r ≫ t) at hc
  simpa only [hr, ht] using hc

/-- A field-valued section has the class of the residue field at its image point. -/
private theorem representative_eq_schemePoint {S : Scheme.{u}}
    {F : (Over S)ᵒᵖ ⥤ Type u} {U : Over S} (p : yoneda.obj U ⟶ F)
    {K : Type u} [Field K] {b : Spec (.of K) ⟶ S} (a : Over.mk b ⟶ U) :
    Quot.mk _ (PointRepresentative.map p ⟨K, b, a⟩) =
      schemePointMap p (a.left (IsLocalRing.closedPoint K)) := by
  let x := a.left (IsLocalRing.closedPoint K)
  let e := Scheme.descResidueField (Scheme.stalkClosedPointTo a.left)
  have he : Spec.map e ≫ U.left.fromSpecResidueField x = a.left :=
    Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField K U.left a.left
  let c : Over.mk b ⟶ Over.mk (U.left.fromSpecResidueField x ≫ U.hom) :=
    Over.homMk (Spec.map e) (by
      change Spec.map e ≫ (U.left.fromSpecResidueField x ≫ U.hom) = b
      rw [← Category.assoc, he, Over.w a]
      rfl)
  apply Quot.sound
  refine ⟨K, inferInstance, b, 𝟙 _, c, ?_⟩
  change F.map (𝟙 _).op (p.app _ a) =
    F.map c.op (p.app _ (Over.homMk (U.left.fromSpecResidueField x) rfl))
  rw [op_id, F.map_id_apply]
  rw [← NatTrans.naturality_apply]
  apply congrArg (p.app _)
  apply Over.OverMorphism.ext
  exact he.symm

/-- Naturality of the scheme point map under a scheme morphism. -/
private theorem schemePoint_comp {S : Scheme.{u}} {F : (Over S)ᵒᵖ ⥤ Type u}
    {V U : Over S} (i : V ⟶ U) (p : yoneda.obj U ⟶ F) (x : V.left) :
    schemePointMap (yoneda.map i ≫ p) x = schemePointMap p (i.left x) := by
  let a : Over.mk (V.left.fromSpecResidueField x ≫ V.hom) ⟶ V :=
    Over.homMk (V.left.fromSpecResidueField x) rfl
  have h := representative_eq_schemePoint p (a ≫ i)
  change schemePointMap (yoneda.map i ≫ p) x =
    schemePointMap p (i.left ((V.left.fromSpecResidueField x)
      (IsLocalRing.closedPoint (V.left.residueField x)))) at h
  exact h.trans (congrArg (fun y ↦ schemePointMap p (i.left y))
    (V.left.fromSpecResidueField_apply x _))

/-- Invariance makes the double restriction a pullback along either projection. -/
private theorem invariant_restriction_squares {S : Scheme.{u}} {R U V : Over S}
    (s t : R ⟶ U) (i : V ⟶ U) [IsOpenImmersion i.left]
    (hinv : s.left ⁻¹' Set.range i.left = t.left ⁻¹' Set.range i.left) :
    let r := pullback.fst (pullback.snd i s ≫ t) i ≫ pullback.snd i s
    IsPullback r (restrictedEtaleRelationSource s t i) s i ∧
      IsPullback r (restrictedEtaleRelationTarget s t i) t i := by
  let P := Limits.pullback i s
  let k : P ⟶ U := pullback.snd i s ≫ t
  let a := pullback.fst k i
  let r := a ≫ pullback.snd i s
  have hi : Mono i := Over.mono_of_mono_left i
  have hP := (IsPullback.of_hasPullback i s).flip
  have hPsch : IsPullback (pullback.snd i s).left (pullback.fst i s).left
      s.left i.left := by
    simpa only [Over.forget_map] using hP.map (Over.forget S)
  have hsrange : Set.range k.left ⊆ Set.range i.left := by
    rintro _ ⟨y, rfl⟩
    change t.left ((pullback.snd i s).left y) ∈ Set.range i.left
    rw [← Set.mem_preimage, ← hinv]
    refine ⟨(pullback.fst i s).left y, ?_⟩
    exact (congrArg (fun f : P ⟶ U ↦ f.left y) (pullback.condition (f := i) (g := s)))
  let c : P ⟶ V := Over.homMk (IsOpenImmersion.lift i.left k.left hsrange) (by
    rw [← Over.w i, ← Category.assoc, IsOpenImmersion.lift_fac, Over.w k])
  have hc : c ≫ i = k := by
    apply Over.OverMorphism.ext
    exact IsOpenImmersion.lift_fac _ _ _
  have hac : a ≫ c = pullback.snd k i := by
    apply (cancel_mono i).1
    rw [Category.assoc, hc]
    exact pullback.condition
  have ha : IsIso a := by
    let b := pullback.lift (𝟙 P) c (by simpa only [Category.id_comp] using hc.symm)
    refine ⟨⟨b, ?_, ?_⟩⟩
    · apply pullback.hom_ext
      · simp [b, a]
      · change a ≫ b ≫ pullback.snd k i = pullback.snd k i
        rw [pullback.lift_snd]
        exact hac
    · simp [b, a]
  have hfirst : IsPullback r (restrictedEtaleRelationSource s t i) s i := by
    apply hP.of_iso (asIso a).symm (Iso.refl _) (Iso.refl _) (Iso.refl _)
    all_goals simp [r, restrictedEtaleRelationSource, a, k]
  have haLeft : IsIso a.left := (Over.forget S).map_isIso a
  have hsOpen : IsOpenImmersion (pullback.snd i s).left :=
    MorphismProperty.of_isPullback hPsch.flip inferInstance
  have hrOpen : IsOpenImmersion r.left := by
    change IsOpenImmersion (a.left ≫ (pullback.snd i s).left)
    infer_instance
  have hrange : r.left.opensRange = s.left ⁻¹ᵁ i.left.opensRange := by
    have hpb : IsPullback (restrictedEtaleRelationSource s t i).left r.left
        i.left s.left := by
      simpa only [Over.forget_map] using hfirst.flip.map (Over.forget S)
    have h := IsOpenImmersion.image_preimage_eq_preimage_image_of_isPullback
      hpb (⊤ : V.left.Opens)
    simpa only [Scheme.Hom.preimage_top, Scheme.Hom.image_top_eq_opensRange] using h
  have ht : r ≫ t = restrictedEtaleRelationTarget s t i ≫ i := by
    simpa only [r, a, k, restrictedEtaleRelationTarget, Category.assoc] using
      (pullback.condition (f := k) (g := i))
  refine ⟨hfirst, ?_⟩
  have hsecond : IsPullback r.left (restrictedEtaleRelationTarget s t i).left
      t.left i.left := by
    apply IsPullback.flip
    apply IsOpenImmersion.isPullback
    · exact congrArg (fun f ↦ f.left) ht
    · rw [hrange]
      apply TopologicalSpace.Opens.ext
      simpa only [Scheme.Hom.coe_preimage, Scheme.Hom.coe_opensRange] using hinv.symm
  apply IsPullback.of_map_of_faithful (Over.forget S)
  simpa only [Over.forget_map] using hsecond

/-- A representably surjective scheme map is surjective on point classes. -/
private theorem schemePoint_surjective {S : Scheme.{u}}
    {F : (Over S)ᵒᵖ ⥤ Type u} {U : Over S} (p : yoneda.obj U ⟶ F)
    (hp : IsSurjective p) : Function.Surjective (schemePointMap p) := by
  intro x
  induction x using Quot.ind with
  | mk x =>
    let T := Over.mk x.base
    let e : yoneda.obj T ⟶ F := yonedaEquiv.symm x.value
    obtain ⟨P, r, q, hpb, hr⟩ := hp T e
    obtain ⟨y, hy⟩ := hr.surj (IsLocalRing.closedPoint x.K)
    let v : P ⟶ U := yoneda.preimage q
    have hv : yoneda.map v ≫ p = yoneda.map r ≫ e := by
      rw [Functor.map_preimage]
      exact hpb.w
    refine ⟨v.left y, ?_⟩
    calc
      schemePointMap p (v.left y) = schemePointMap (yoneda.map v ≫ p) y :=
        (schemePoint_comp v p y).symm
      _ = schemePointMap e (IsLocalRing.closedPoint x.K) := by
        rw [hv, schemePoint_comp, hy]
      _ = Quot.mk _ x := by
        have he := representative_eq_schemePoint e (𝟙 T)
        simpa [e, T, PointRepresentative.map] using he.symm

/-- A surjective quotient atlas computes the point image of every map from its quotient. -/
private theorem image_from_atlas {S : Scheme.{u}}
    {F G : (Over S)ᵒᵖ ⥤ Type u} {V : Over S}
    (q : yoneda.obj V ⟶ F) (hq : IsSurjective q) (j : F ⟶ G) :
    pointImage j = Set.range (schemePointMap (q ≫ j)) := by
  ext x
  constructor
  · rintro ⟨a, rfl⟩
    obtain ⟨v, hv⟩ := schemePoint_surjective q hq (Quot.mk _ a)
    exact ⟨v, congrArg (mapPoint j) hv⟩
  · rintro ⟨v, rfl⟩
    exact ⟨⟨V.left.residueField v, V.left.fromSpecResidueField v ≫ V.hom,
      q.app _ (Over.homMk (V.left.fromSpecResidueField v) rfl)⟩, rfl⟩

/-- Scheme-test representability is invariant under postcomposition with an isomorphism. -/
private theorem representable_comp_iso {S : Scheme.{u}}
    {F G H : (Over S)ᵒᵖ ⥤ Type u} (P : MorphismProperty (Over S))
    (f : F ⟶ G) (e : G ≅ H) (hf : IsRepresentableWith P f) :
    IsRepresentableWith P (f ≫ e.hom) := by
  intro T a
  obtain ⟨V, r, q, hpb, hr⟩ := hf T (a ≫ e.inv)
  refine ⟨V, r, q, ?_, hr⟩
  apply hpb.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) e
  all_goals simp

/-- The inverse image of an open point subset in an atlas is an invariant open subscheme;
its restricted equivalence relation has an algebraic-space quotient giving that open
subspace. `hR` specifies the scheme representing `U ×_X U`. The existential open immersion
`i` represents the unique open subscheme with the specified underlying subset. The two
pullback squares specify `s⁻¹(V) = t⁻¹(V) = RV` as open subschemes, and hence specify the
iterated pullback relation. `η` exhibits `J` as its fppf sheaf quotient. The quotient atlas
is the coequalizer projection followed by `η`. Its compatibility characterizes `j`.
Finally, `Subfunctor.toRange j` identifies the quotient with the open image subfunctor.
Source: Stacks, Properties of Spaces, Tag 03BZ; Spaces, Tags 0262, 02WT, 02WW and 02WU
(blueprint: lem-a1-space-invariant-open-quotient).

Proof:
1. Apply lem-a1-etale-atlas-presentation to the atlas and its representing square `hR`.
   It identifies the relation with equality of images in `X`, gives surjective étale
   projections, and identifies its sheaf quotient with `X`. By
   def-a1-space-point-topology, the inverse image of `O` is open. Give it the open
   subscheme structure of def-weil-open-immersion, obtaining `V` and `i`.
2. The equality of the composites with `p` makes the inverse images of `V` under `s`
   and `t` equal. By lem-weil-pbc-open-preimage-fibre-product these are the scheme
   pullbacks. Equal opens have the same restricted structure sheaf, so their common
   open subscheme `RV` has both displayed pullback squares and is the double restriction.
3. The map `i` is étale by lem-weil-pbc-open-immersion-etale. Apply
   lem-trf-etale-relation-restriction-quotient: the restricted projections form a monic
   étale equivalence relation, and its quotient maps injectively to the original one.
4. Form the fppf sheaf quotient of this restricted relation, with its unit `η` and
   sheafification universal property (def-weil-pbc-sheafification). Theorem
   lem-trf-etale-relation-quotient gives algebraicity and the representable surjective
   étale quotient atlas. Compose the restricted quotient map with the original
   presentation isomorphism to obtain `j` with the stated atlas compatibility.
5. Étale maps are flat and locally finitely presented by def-weil-etale-morphism.
   Thus lem-trf-etale-relation-finding-opens applies to the surjective étale original
   projections and to `i`; it makes `j` representable by open immersions.
6. The surjectivity clause of lem-a1-space-point-open-calculus makes the point maps
   of both atlases surjective. Compatibility therefore gives
   `im |j| = |p|(|V|) = |p|(|p|⁻¹(O)) = O`. The sectionwise injection identifies `J`
   with `Subfunctor.range j`. Its inclusion is representable by open immersions,
   so it is an OpenSubspace by def-a1-space-open-subspace. -/
theorem space_invariant_open_quotient {S : Scheme.{u}} (X : AlgebraicSpace S)
    (U : Over S) (p : yoneda.obj U ⟶ X.obj.obj)
    (hp : IsEtale p) (hsur : IsSurjective p)
    (O : Set (Point X.obj.obj)) (hO : IsOpen O)
    (R : Over S) (s t : R ⟶ U)
    (hR : IsPullback (yoneda.map s) (yoneda.map t) p p) :
    ∃ (V : Over S) (i : V ⟶ U),
      IsOpenImmersion i.left ∧
      Set.range i.left.base = schemePointMap p ⁻¹' O ∧
      ∃ (RV : Over S) (r : RV ⟶ R) (sV tV : RV ⟶ V),
        IsPullback r sV s i ∧ IsPullback r tV t i ∧
        Mono (prod.lift sV tV) ∧
        (∀ T : Over S, Equivalence (fun a b : T ⟶ V ↦
          ∃ v : T ⟶ RV, v ≫ sV = a ∧ v ≫ tV = b)) ∧
        Etale sV.left ∧ Etale tV.left ∧
        ∃ (J : Sheaf (Scheme.fppfTopology.over S) (Type u))
          (η : coequalizer (yoneda.map sV) (yoneda.map tV) ⟶ J.obj),
          (∀ G : Sheaf (Scheme.fppfTopology.over S) (Type u),
            Function.Bijective (fun a : J.obj ⟶ G.obj ↦ η ≫ a)) ∧
          IsAlgebraicSpace J ∧
          IsEtale (coequalizer.π (yoneda.map sV) (yoneda.map tV) ≫ η) ∧
          IsSurjective (coequalizer.π (yoneda.map sV) (yoneda.map tV) ≫ η) ∧
          ∃ j : J.obj ⟶ X.obj.obj,
            (coequalizer.π (yoneda.map sV) (yoneda.map tV) ≫ η) ≫ j = yoneda.map i ≫ p ∧
            IsRepresentableWith (fun _ _ f ↦ IsOpenImmersion f.left) j ∧
            pointImage j = O ∧ IsIso (Subfunctor.toRange j) ∧
            ∃ A : OpenSubspace X, A.val = Subfunctor.range j := by
  classical
  let f := coequalizer.desc p hR.w
  have hf : Mono f := quotient_desc_mono s t p hR
  obtain ⟨Q, ηQ, hηQ⟩ := reflection_of_mono _ X.obj f
  obtain ⟨hm, hrel, hs, hss, ht, hts, he, hQp⟩ :=
    etale_atlas_presentation X U p hp hsur R s t hR Q ηQ hηQ
  let e := etaleAtlasPresentationMap p s t hR Q ηQ hηQ
  have he' : IsIso e.hom := (sheafToPresheaf _ _).map_isIso e
  have hpre : IsOpen (schemePointMap p ⁻¹' O) := by
    exact isOpen_coinduced.mp
      (isOpen_iSup_iff.mp (isOpen_iSup_iff.mp (isOpen_iSup_iff.mp hO U) p) hp)
  let W : U.left.Opens := ⟨schemePointMap p ⁻¹' O, hpre⟩
  let V : Over S := Over.mk (W.ι ≫ U.hom)
  let i : V ⟶ U := Over.homMk W.ι
  have hi : IsOpenImmersion i.left := inferInstanceAs (IsOpenImmersion W.ι)
  have hiRange : Set.range i.left = schemePointMap p ⁻¹' O :=
    Scheme.Opens.range_ι W
  have hinv : s.left ⁻¹' Set.range i.left = t.left ⁻¹' Set.range i.left := by
    rw [hiRange]
    ext x
    change schemePointMap p (s.left x) ∈ O ↔ schemePointMap p (t.left x) ∈ O
    rw [← schemePoint_comp s p, ← schemePoint_comp t p, hR.w]
  obtain ⟨hfirst, hsecond⟩ := invariant_restriction_squares s t i hinv
  have hrel' := fun T ↦ (hrel T).1
  obtain ⟨s', t', r', hs', ht', hr', _, _, hm', _, hrelV, hsV, htV,
      _, _, _, _, v, _, hv, _⟩ := etale_pullback_relation_presheaf s t hrel' i
  subst s'
  subst t'
  subst r'
  have hvMono : Mono v := (NatTrans.mono_iff_mono_app _).2 (fun T ↦
    (CategoryTheory.mono_iff_injective _).2 (hv T.unop))
  obtain ⟨J, η, hη⟩ := reflection_of_mono _ X.obj (v ≫ f)
  obtain ⟨_, _, _, _, β, hβ, hβmono, _⟩ :=
    etale_relation_restriction_quotient s t hrel' i Q ηQ hηQ J η hη
  obtain ⟨α, hα, hαopen⟩ := etale_relation_finding_opens s t hrel' i Q ηQ hηQ J η hη
  dsimp only [restrictedEtaleRelationSource, restrictedEtaleRelationTarget] at hβ
  have hαβ : α = β := by
    apply (hη Q).injective
    apply (cancel_epi (coequalizer.π
      (yoneda.map (restrictedEtaleRelationSource s t i))
      (yoneda.map (restrictedEtaleRelationTarget s t i)))).1
    simpa only [Category.assoc, restrictedEtaleRelationSource,
      restrictedEtaleRelationTarget] using hα.trans hβ.symm
  have hαmono : Mono α := hαβ.symm ▸ hβmono
  obtain ⟨hJ, hqEt, hqSur, _⟩ := etale_relation_quotient
    (restrictedEtaleRelationSource s t i) (restrictedEtaleRelationTarget s t i)
    hrelV J η hη
  let q := coequalizer.π (yoneda.map (restrictedEtaleRelationSource s t i))
    (yoneda.map (restrictedEtaleRelationTarget s t i)) ≫ η
  let j : J.obj ⟶ X.obj.obj := α ≫ e.hom
  have hcompat : q ≫ j = yoneda.map i ≫ p := by
    dsimp only [j, q, restrictedEtaleRelationSource, restrictedEtaleRelationTarget]
    rw [← Category.assoc, hα, Category.assoc, hQp]
  have hjOpen : IsRepresentableWith (fun _ _ f ↦ IsOpenImmersion f.left) j :=
    representable_comp_iso _ α (asIso e.hom) hαopen
  have hjMono : Mono j := inferInstance
  have himage : pointImage j = O := by
    calc
      pointImage j = Set.range (schemePointMap (q ≫ j)) := image_from_atlas q hqSur j
      _ = Set.range (schemePointMap p ∘ i.left) := by
        rw [hcompat]
        congr 1
        funext x
        exact schemePoint_comp i p x
      _ = schemePointMap p '' Set.range i.left := Set.range_comp _ _
      _ = O := by rw [hiRange, Set.image_preimage_eq O (schemePoint_surjective p hsur)]
  have hto : IsIso (Subfunctor.toRange j) := inferInstance
  have hrangeOpen : IsRepresentableWith (fun _ _ f ↦ IsOpenImmersion f.left)
      (Subfunctor.range j).ι := by
    intro T a
    obtain ⟨P, r, b, hb, hr⟩ := hjOpen T a
    refine ⟨P, r, b ≫ Subfunctor.toRange j, ?_, hr⟩
    apply hb.of_iso (Iso.refl _) (asIso (Subfunctor.toRange j))
      (Iso.refl _) (Iso.refl _)
    all_goals simp
  exact ⟨V, i, hi, hiRange, restrictedEtaleRelation s t i,
    pullback.fst (pullback.snd i s ≫ t) i ≫ pullback.snd i s,
    restrictedEtaleRelationSource s t i, restrictedEtaleRelationTarget s t i,
    hfirst, hsecond, hm', hrelV, hsV, htV, J, η, hη, hJ, hqEt, hqSur,
    j, hcompat, hjOpen, himage, hto, ⟨Subfunctor.range j, hrangeOpen⟩, rfl⟩

end AlgebraicGeometry.AlgebraicSpace
