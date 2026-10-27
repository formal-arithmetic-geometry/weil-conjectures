/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D8
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.CategoryTheory.Limits.Types.Pullbacks

/-!
# The represented kernel relation of a surjective étale map to an fppf sheaf

Source: Stacks Project, Spaces, Tag 0262 (lemma-space-presentation), first proof
paragraph; Sites, Tag 00W2 (lemma-limit-sheaf)
(blueprint: lem-a1-representable-etale-kernel-relation).

Only the given scheme map to the sheaf is assumed representable. No hypothesis
on the diagonal of the sheaf is used.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

-- A scheme-test property transfers to every representing pullback, by Yoneda uniqueness.
private theorem property_of_representing_pullback {S : Scheme.{u}}
    (P : MorphismProperty Scheme.{u}) [P.RespectsIso]
    {G H : (Over S)ᵒᵖ ⥤ Type u} {f : G ⟶ H}
    (hf : IsRepresentableWith (P.inverseImage (Over.forget S)) f)
    {T V : Over S} {a : yoneda.obj T ⟶ H} {v : V ⟶ T}
    {q : yoneda.obj V ⟶ G} (h : IsPullback q (yoneda.map v) f a) : P v.left := by
  obtain ⟨W, w, b, hb, hw⟩ := hf T a
  let e : V ≅ W := yoneda.preimageIso (h.isoIsPullback _ _ hb)
  have he : e.hom ≫ w = v := by
    apply yoneda.map_injective
    simpa only [Functor.map_comp, e, Functor.preimageIso_hom, Functor.map_preimage] using
      h.isoIsPullback_hom_snd _ _ hb
  have hP : P (e.hom.left ≫ w.left) :=
    MorphismProperty.RespectsIso.precomp P e.hom.left w.left hw
  simpa only [← Over.comp_left, he] using hP

/-- A represented kernel pair has the natural sectionwise equality relation,
surjective étale projections, a diagonal, and an involution switching factors.
Source: Stacks Project, Spaces, Tag 0262, first proof paragraph, generalized to a
sheaf with a representable surjective étale scheme map; Sites, Tag 00W2
(blueprint: lem-a1-representable-etale-kernel-relation).

Proof:
1. Evaluate the representing pullback square at every test scheme T, using
   lem-weil-pbc-site-sheaf-sets-limits-sectionwise, clause (2). The resulting
   pullback of sets gives β_T(r) = (r ≫ s, r ≫ t). Associativity gives its
   compatibility with precomposition; naturality of p preserves equal images.
2. By def-pc-fibre-product the two projections define the map into U ×_S U.
   Equality after this map gives equality of both components of β_T and hence
   equality of sections. Thus the map is mono. Its image is exactly equality
   of p-values, which is reflexive, symmetric and transitive.
3. Test p against itself in def-trf-algebraic-space. Representability with the
   étale and surjective properties gives these properties for one projection;
   interchange of the identical factors gives them for the other. If a different
   representing scheme is chosen by the definition, lem-pc-representable-unique
   identifies it with R compatibly with the projections. Scheme isomorphisms
   preserve both properties. No representability of the diagonal of F is needed.
4. The unique inverse image of (𝟙 U, 𝟙 U) under β_U defines d. Its composites
   with s and t are identities, and naturality identifies it with the diagonal.
5. The inverse image of (t,s) under β_R defines i. Its composites with s,t are
   t,s. Applying β_R twice shows i ≫ i = 𝟙 R by injectivity. Precomposition
   shows that i acts by factor interchange on every set of test sections. -/
theorem representable_etale_kernel_relation {S : Scheme.{u}}
    (F : Sheaf (Scheme.fppfTopology.over S) (Type u))
    (U : Over S) (p : yoneda.obj U ⟶ F.obj)
    (hrep : IsRepresentable p) (hsur : IsSurjective p) (het : IsEtale p)
    (R : Over S) (s t : R ⟶ U)
    (hR : IsPullback (yoneda.map s) (yoneda.map t) p p) :
    (∃ β : ∀ T : Over S,
        (T ⟶ R) ≃ {ab : (T ⟶ U) × (T ⟶ U) |
          p.app (op T) ab.1 = p.app (op T) ab.2},
      (∀ (T : Over S) (r : T ⟶ R), (β T r).val = (r ≫ s, r ≫ t)) ∧
      ∀ (T T' : Over S) (g : T' ⟶ T) (r : T ⟶ R),
        (β T' (g ≫ r)).val = (g ≫ (β T r).val.1, g ≫ (β T r).val.2)) ∧
    Mono (pullback.lift s.left t.left (s.w.trans t.w.symm)) ∧
    (∀ T : Over S, Equivalence (fun a b : T ⟶ U ↦
      ∃ r : T ⟶ R, r ≫ s = a ∧ r ≫ t = b)) ∧
    Surjective s.left ∧ Etale s.left ∧ Surjective t.left ∧ Etale t.left ∧
    (∃ d : U ⟶ R, d ≫ s = 𝟙 U ∧ d ≫ t = 𝟙 U) ∧
    ∃ i : R ⟶ R, i ≫ s = t ∧ i ≫ t = s ∧ i ≫ i = 𝟙 R := by
  classical
  have _representable := hrep
  let β : ∀ T : Over S,
      (T ⟶ R) ≃ {ab : (T ⟶ U) × (T ⟶ U) |
        p.app (op T) ab.1 = p.app (op T) ab.2} := fun T ↦
    PullbackCone.IsLimit.equivPullbackObj
      ((hR.map ((evaluation (Over S)ᵒᵖ (Type u)).obj (op T))).isLimit)
  have hβ (T : Over S) (r : T ⟶ R) : (β T r).val = (r ≫ s, r ≫ t) := by
    exact Prod.ext (PullbackCone.IsLimit.equivPullbackObj_apply_fst _ _)
      (PullbackCone.IsLimit.equivPullbackObj_apply_snd _ _)
  have relation (T : Over S) (a b : T ⟶ U) :
      (∃ r : T ⟶ R, r ≫ s = a ∧ r ≫ t = b) ↔
        p.app (op T) a = p.app (op T) b := by
    constructor
    · rintro ⟨r, rfl, rfl⟩
      have hr := (β T r).property
      change p.app (op T) (β T r).val.1 = p.app (op T) (β T r).val.2 at hr
      simpa only [hβ] using hr
    · intro hab
      obtain ⟨r, hr⟩ := (β T).surjective ⟨(a, b), hab⟩
      have he := congrArg Subtype.val hr
      rw [hβ] at he
      exact ⟨r, congrArg Prod.fst he, congrArg Prod.snd he⟩
  have hmono : Mono (pullback.lift s.left t.left (s.w.trans t.w.symm)) := by
    let V : Over S := Over.mk (pullback.fst U.hom U.hom ≫ U.hom)
    let j : R ⟶ V := Over.homMk
      (pullback.lift s.left t.left (s.w.trans t.w.symm)) (by
        dsimp [V]
        rw [pullback.lift_fst_assoc]
        exact s.w)
    have hjfst : j.left ≫ pullback.fst U.hom U.hom = s.left :=
      pullback.lift_fst _ _ _
    have hjsnd : j.left ≫ pullback.snd U.hom U.hom = t.left :=
      pullback.lift_snd _ _ _
    have hj : Mono j := by
      constructor
      intro T a b hab
      apply (β T).injective
      apply Subtype.ext
      rw [hβ, hβ]
      apply Prod.ext
      · apply Over.OverMorphism.ext
        have he := congrArg (fun f ↦ f.left ≫ pullback.fst U.hom U.hom) hab
        simpa only [Over.comp_left, Category.assoc, hjfst] using he
      · apply Over.OverMorphism.ext
        have he := congrArg (fun f ↦ f.left ≫ pullback.snd U.hom U.hom) hab
        simpa only [Over.comp_left, Category.assoc, hjsnd] using he
    exact @Over.mono_left_of_mono _ _ _ _ _ j hj
  have heq (T : Over S) : Equivalence (fun a b : T ⟶ U ↦
      ∃ r : T ⟶ R, r ≫ s = a ∧ r ≫ t = b) := by
    refine ⟨fun a ↦ (relation T a a).mpr rfl, ?_, ?_⟩
    · intro a b hab
      exact (relation T b a).mpr ((relation T a b).mp hab).symm
    · intro a b c hab hbc
      exact (relation T a c).mpr (((relation T a b).mp hab).trans
        ((relation T b c).mp hbc))
  have hs : Surjective s.left :=
    property_of_representing_pullback @Surjective hsur hR.flip
  have hse : Etale s.left :=
    property_of_representing_pullback @Etale het hR.flip
  have ht : Surjective t.left :=
    property_of_representing_pullback @Surjective hsur hR
  have hte : Etale t.left :=
    property_of_representing_pullback @Etale het hR
  obtain ⟨d, hds, hdt⟩ := (relation U (𝟙 U) (𝟙 U)).mpr rfl
  have hst := (relation R s t).mp ⟨𝟙 R, by simp, by simp⟩
  obtain ⟨i, his, hit⟩ := (relation R t s).mpr hst.symm
  have hii : i ≫ i = 𝟙 R := by
    apply (β R).injective
    apply Subtype.ext
    rw [hβ, hβ]
    simp only [Category.assoc, his, hit, Category.id_comp]
  refine ⟨⟨β, hβ, ?_⟩, hmono, heq, hs, hse, ht, hte, ⟨d, hds, hdt⟩,
    ⟨i, his, hit, hii⟩⟩
  intro T T' g r
  rw [hβ, hβ]
  simp only [Category.assoc]

end AlgebraicGeometry.AlgebraicSpace
