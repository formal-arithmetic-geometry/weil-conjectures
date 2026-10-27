/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NO
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Sites.Over
import Sheaf.AlgebraicGeometry.RepresentableEtaleFppfLocalLifting
import Sheaf.AlgebraicGeometry.RepresentableEtaleKernelRelation
import Sheaf.AlgebraicGeometry.EtaleRelationQuotient
import Mathlib.CategoryTheory.MorphismProperty.Representable
import Mathlib.CategoryTheory.Limits.Types.Pullbacks
import Mathlib.CategoryTheory.Sites.Subsheaf

/-! # Recognizing a presheaf over an algebraic space

Source: Stacks Project, bootstrap.tex, Tag 02YS,
lemma-representable-by-spaces-over-space
(blueprint: lem-sfb-presheaf-space-target-bootstrap).

The input is an arbitrary presheaf. The conclusion equips that same presheaf with
fppf descent and the algebraic-space property, using only scheme tests over the target.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

/-- Sheaf descent can be tested in every representable fibre over a sheaf. -/
private theorem isSheaf_of_fibres {S : Scheme.{u}}
    (P Z : (Over S)ᵒᵖ ⥤ Type u) (a : P ⟶ Z)
    (hZ : Presheaf.IsSheaf (Scheme.fppfTopology.over S) Z)
    (h : ∀ (T : Over S) (t : yoneda.obj T ⟶ Z),
      Presheaf.IsSheaf (Scheme.fppfTopology.over S) (Limits.pullback t a)) :
    Presheaf.IsSheaf (Scheme.fppfTopology.over S) P := by
  apply (isSheaf_iff_isSheaf_of_type _ _).2
  apply Presieve.isSheaf_of_yoneda
  intro T R hR f
  let hZR := hZ.isSheafFor R hR
  let t := hZR.extend (f ≫ a)
  have ht : R.functorInclusion ≫ t = f ≫ a :=
    hZR.functorInclusion_comp_extend (f ≫ a)
  let l := Limits.pullback.lift R.functorInclusion f ht
  let hB := (h T t).isSheafFor R hR
  let v := hB.extend l
  have hv : R.functorInclusion ≫ v = l := hB.functorInclusion_comp_extend l
  refine ⟨v ≫ Limits.pullback.snd t a, ?_, ?_⟩
  · change R.functorInclusion ≫ (v ≫ Limits.pullback.snd t a) = f
    rw [← Category.assoc, hv, Limits.pullback.lift_snd]
  · intro g hg
    have hga : g ≫ a = t := hZR.unique_extend _ (by
      rw [← Category.assoc, hg])
    have hgB : Limits.pullback.lift (𝟙 _) g (by simpa using hga.symm) = v := by
      apply hB.unique_extend
      apply Limits.pullback.hom_ext <;> simp [l, hg]
    simpa using congrArg (fun k ↦ k ≫ Limits.pullback.snd t a) hgB

/-- The scheme-test definition agrees with Mathlib's relative morphism property. -/
private theorem representableWith_iff {S : Scheme.{u}}
    (Q : MorphismProperty (Over S)) [Q.RespectsIso]
    {G F : (Over S)ᵒᵖ ⥤ Type u} (f : G ⟶ F) :
    IsRepresentableWith Q f ↔ Q.relative yoneda f := by
  constructor
  · intro h
    apply MorphismProperty.relative.of_exists
    intro T a
    obtain ⟨U, p, q, h, hp⟩ := h T a
    exact ⟨U, q, p, h, hp⟩
  · intro h T a
    exact ⟨h.rep.pullback a, h.rep.snd a, h.rep.fst a,
      h.rep.isPullback a, h.property_snd a⟩

/-- A locally bijective map to a sheaf has the sheafification universal property.
The subsheaf closure of its range avoids any size assumption on global sheafification. -/
private theorem reflection_of_locally_bijective {S : Scheme.{u}}
    {P : (Over S)ᵒᵖ ⥤ Type u}
    (F : Sheaf (Scheme.fppfTopology.over S) (Type u)) (η : P ⟶ F.obj)
    [Mono η] [Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) η] :
    ∀ G : Sheaf (Scheme.fppfTopology.over S) (Type u),
      Function.Bijective (fun g : F.obj ⟶ G.obj ↦ η ≫ g) := by
  intro G
  let J := Scheme.fppfTopology.over S
  let K := Subfunctor.range η
  have hG := (isSheaf_iff_isSheaf_of_type _ _).1 G.property
  have : IsIso (K.sheafify J).ι := (Subfunctor.eq_top_iff_isIso _).mp
    ((Presheaf.isLocallySurjective_iff_range_sheafify_eq_top' J η).mp inferInstance)
  have fac : Subfunctor.toRangeSheafify J η ≫ (K.sheafify J).ι = η := by
    simp [Subfunctor.toRangeSheafify, K]
  constructor
  · intro g h e
    apply (cancel_epi (K.sheafify J).ι).1
    apply K.to_sheafify_lift_unique hG
    apply (cancel_epi (Subfunctor.toRange η)).1
    rw [← fac] at e
    simpa only [Subfunctor.toRangeSheafify, Category.assoc] using e
  · intro g
    refine ⟨inv (K.sheafify J).ι ≫
      K.sheafifyLift (inv (Subfunctor.toRange η) ≫ g) hG, ?_⟩
    have fac' : η ≫ inv (K.sheafify J).ι = Subfunctor.toRangeSheafify J η := by
      calc
        η ≫ inv (K.sheafify J).ι =
            (Subfunctor.toRangeSheafify J η ≫ (K.sheafify J).ι) ≫
              inv (K.sheafify J).ι := congrArg (fun k ↦ k ≫ inv (K.sheafify J).ι) fac.symm
        _ = _ := by simp
    change η ≫ (inv (K.sheafify J).ι ≫ _) = g
    rw [← Category.assoc, fac']
    change (Subfunctor.toRange η ≫ Subfunctor.homOfLe (K.le_sheafify J)) ≫
      K.sheafifyLift (inv (Subfunctor.toRange η) ≫ g) hG = g
    rw [Category.assoc, K.to_sheafifyLift, IsIso.hom_inv_id_assoc]

/-- A represented kernel pair makes the map from its presheaf quotient monic. -/
private theorem quotient_unit_mono {S : Scheme.{u}} {R W : Over S} (s t : R ⟶ W)
    {F : (Over S)ᵒᵖ ⥤ Type u}
    (η : coequalizer (yoneda.map s) (yoneda.map t) ⟶ F)
    (h : IsPullback (yoneda.map s) (yoneda.map t)
      (coequalizer.π (yoneda.map s) (yoneda.map t) ≫ η)
      (coequalizer.π (yoneda.map s) (yoneda.map t) ≫ η)) : Mono η := by
  apply (NatTrans.mono_iff_mono_app _).2
  intro T
  apply (CategoryTheory.mono_iff_injective _).2
  intro x y e
  obtain ⟨a, rfl⟩ := (CategoryTheory.epi_iff_surjective
    ((coequalizer.π (yoneda.map s) (yoneda.map t)).app T)).1 inferInstance x
  obtain ⟨b, rfl⟩ := (CategoryTheory.epi_iff_surjective
    ((coequalizer.π (yoneda.map s) (yoneda.map t)).app T)).1 inferInstance y
  obtain ⟨r, hr, ht⟩ := Types.exists_of_isPullback (h.app T) a b e
  have he := ConcreteCategory.congr_hom
    (congr_app (coequalizer.condition (yoneda.map s) (yoneda.map t)) T) r
  change (coequalizer.π (yoneda.map s) (yoneda.map t)).app T (r ≫ s) =
    (coequalizer.π (yoneda.map s) (yoneda.map t)).app T (r ≫ t) at he
  change r ≫ s = a at hr
  change r ≫ t = b at ht
  simpa only [hr, ht] using he

/-- A presheaf mapping to an algebraic space is algebraic if every scheme base change
is isomorphic to an algebraic-space presheaf. The pullback is in presheaves, so its
sections are pairs `(v, p)` satisfying `t(v) = a(p)`, with componentwise restriction.
No sheaf condition on `P` is assumed.

Source: Stacks Project, bootstrap.tex, Tag 02YS,
lemma-representable-by-spaces-over-space
(blueprint: lem-sfb-presheaf-space-target-bootstrap).

Proof:
1. Express descent as unique extension of maps from a covering sieve. Extend the
   image of such a map in Z to a map t from the representable. The map to P and
   the sieve inclusion give a map to h_T ×_Z P, which is a sheaf by hypothesis.
   Extend this map and compose with the second projection to obtain the gluing
   in P. Any other gluing gives a map to the pullback and therefore agrees by
   uniqueness of extension there. This includes empty coverings.
2. Choose a representable surjective etale scheme atlas h_U → Z. The hypothesis
   gives an algebraic space B isomorphic to h_U ×_Z P. Choose an atlas h_W → B.
3. Compose h_W → B with the isomorphism and the second pullback projection.
   Mathlib's relative morphism properties identify the scheme-test definitions
   and supply base change and composition on arbitrary presheaves. Applied to
   etaleness and surjectivity separately, they show p : h_W → P is representable
   surjective etale. This is the pasted scheme-test argument of Stacks 02YS.
4. Test p against itself to obtain R and its two maps s,t to W. The existing
   representable-etale kernel-relation theorem supplies the equivalence relation
   and etaleness of s,t. The representing square and faithfulness of Yoneda show
   that (s,t) is monic in Over S.
5. The representable-etale local-lifting theorem makes p locally surjective.
6. Define η from the presheaf coequalizer of h_s,h_t to P. Its kernel-pair
   square shows η is monic: equal images of two representatives give a section
   of R, and related representatives have the same coequalizer class. Local
   surjectivity of p implies local surjectivity of η. The closure of the image
   of η inside P is consequently all of P. Since η identifies its source with
   its image, the subsheaf-closure universal property proves that η is a
   sheafification. No global sheafification functor on this big site is needed.
7. Apply the existing etale-relation quotient theorem with this specified η
   and the sheaf structure on P proved in step 1. -/
theorem presheaf_space_target_bootstrap {S : Scheme.{u}}
    (P : (Over S)ᵒᵖ ⥤ Type u) (Z : AlgebraicSpace S) (a : P ⟶ Z.obj.obj)
    (h : ∀ (T : Over S) (t : yoneda.obj T ⟶ Z.obj.obj),
      ∃ B : AlgebraicSpace S, Nonempty (Limits.pullback t a ≅ B.obj.obj)) :
    ∃ hP : Presheaf.IsSheaf (Scheme.fppfTopology.over S) P,
      IsAlgebraicSpace ⟨P, hP⟩ := by
  classical
  have hP : Presheaf.IsSheaf (Scheme.fppfTopology.over S) P := by
    apply isSheaf_of_fibres P Z.obj.obj a Z.obj.property
    intro T t
    obtain ⟨B, ⟨e⟩⟩ := h T t
    exact (Presheaf.isSheaf_of_iso_iff e).2 B.obj.property
  let F : Sheaf (Scheme.fppfTopology.over S) (Type u) := ⟨P, hP⟩
  obtain ⟨U, u, huE, huS⟩ := Z.property.2
  obtain ⟨B, ⟨e⟩⟩ := h U u
  obtain ⟨W, b, hbE, hbS⟩ := B.property.2
  let p : yoneda.obj W ⟶ P := b ≫ e.inv ≫ Limits.pullback.snd u a
  have hp (Q : MorphismProperty (Over S)) [Q.RespectsIso] [Q.IsMultiplicative]
      (hu : IsRepresentableWith Q u) (hb : IsRepresentableWith Q b) :
      IsRepresentableWith Q p := by
    have := MorphismProperty.relative_isStableUnderBaseChange Q (F := yoneda)
    apply (representableWith_iff Q p).2
    exact (Q.relative yoneda).comp_mem _ _ ((representableWith_iff Q b).1 hb)
      ((Q.relative yoneda).comp_mem _ _ ((Q.relative yoneda).of_isIso e.inv)
        ((Q.relative yoneda).of_isPullback (IsPullback.of_hasPullback u a)
          ((representableWith_iff Q u).1 hu)))
  have hpE : IsEtale p := hp
    (MorphismProperty.inverseImage @Etale (Over.forget S)) huE hbE
  have hpS : IsSurjective p := hp
    (MorphismProperty.inverseImage @Surjective (Over.forget S)) huS hbS
  have hpR : IsRepresentable p := by
    intro T x
    obtain ⟨D, d, c, hc, _⟩ := hpE T x
    exact ⟨D, d, c, hc, trivial⟩
  obtain ⟨R, t, s', hR, _⟩ := hpE W p
  let s : R ⟶ W := yoneda.preimage s'
  have hs : yoneda.map s = s' := yoneda.map_preimage s'
  have hR' : IsPullback (yoneda.map s) (yoneda.map t) p p := by
    rw [hs]
    exact hR
  obtain ⟨_, _, hrel, _, hsE, _, htE, _⟩ :=
    representable_etale_kernel_relation F W p hpR hpS hpE R s t hR'
  have : Etale s.left := hsE
  have : Etale t.left := htE
  have : Mono (prod.lift s t) := by
    constructor
    intro T f g hfg
    apply yoneda.map_injective
    apply hR'.hom_ext
    · rw [← Functor.map_comp, ← Functor.map_comp]
      exact congrArg yoneda.map (by
        simpa using congrArg (fun k ↦ k ≫ prod.fst) hfg)
    · rw [← Functor.map_comp, ← Functor.map_comp]
      exact congrArg yoneda.map (by
        simpa using congrArg (fun k ↦ k ≫ prod.snd) hfg)
  let η : coequalizer (yoneda.map s) (yoneda.map t) ⟶ P :=
    coequalizer.desc p hR'.w
  have hπη : coequalizer.π (yoneda.map s) (yoneda.map t) ≫ η = p := by
    simp [η]
  have : Mono η := quotient_unit_mono s t η (by simpa only [hπη] using hR')
  let pF : (Scheme.fppfTopology.over S).yoneda.obj W ⟶ F := ⟨p⟩
  have hpLoc := (representable_etale_fppf_local_lifting F W pF hpE hpS).2.1
  have : Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) p := hpLoc
  have : Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) η :=
    Presheaf.isLocallySurjective_of_isLocallySurjective_fac
      (Scheme.fppfTopology.over S) hπη
  exact ⟨hP, (etale_relation_quotient s t hrel F η
    (reflection_of_locally_bijective F η)).1⟩

end AlgebraicGeometry.AlgebraicSpace
