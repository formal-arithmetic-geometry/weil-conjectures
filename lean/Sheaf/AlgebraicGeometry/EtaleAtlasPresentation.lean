/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NY
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Limits.Types.Colimits
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
import Sheaf.AlgebraicGeometry.RepresentableEtaleKernelRelation
import Sheaf.AlgebraicGeometry.RepresentableEtaleFppfLocalLifting
import Mathlib.CategoryTheory.Sites.LocallySurjective

/-!
# Presentation of an algebraic space by an étale atlas

Source: Stacks Project, Spaces, Tag 0262 (lemma-space-presentation), clauses (1)-(3);
Sites, Tags 00WH and 086K (blueprint: lem-a1-etale-atlas-presentation).

The presheaf coequalizer is the sectionwise relation quotient. Its sheafification
is specified by the universal property at this presheaf, as in the definition of
sheafification, without assuming sheafification for all small-valued presheaves
on the big site. The comparison map is constructed using that universal property.

## Main definitions and statements

* `etaleAtlasPresentationMap`: the canonical comparison induced by the atlas.
* `etale_atlas_presentation`: the relation, its projections, and its quotient.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

/-- The comparison from the sheafified relation quotient to the given algebraic space.
First descend `p` to the presheaf coequalizer, then use the inverse of the
sheafification hom-set bijection. This is a uniquely specified map, with no choice
of an atlas or a representing scheme in its construction.
Source: Stacks, Spaces, Tag 0262; Sites, Tag 00WH
(blueprint: lem-a1-etale-atlas-presentation). -/
noncomputable def etaleAtlasPresentationMap {S : Scheme.{u}} {X : AlgebraicSpace S}
    {U R : Over S} (p : yoneda.obj U ⟶ X.obj.obj) (s t : R ⟶ U)
    (hR : IsPullback (yoneda.map s) (yoneda.map t) p p)
    (Q : Sheaf (Scheme.fppfTopology.over S) (Type u))
    (η : coequalizer (yoneda.map s) (yoneda.map t) ⟶ Q.obj)
    (hη : ∀ G : Sheaf (Scheme.fppfTopology.over S) (Type u),
      Function.Bijective (fun a : Q.obj ⟶ G.obj ↦ η ≫ a)) : Q ⟶ X.obj :=
  ⟨(Equiv.ofBijective (fun a : Q.obj ⟶ X.obj.obj ↦ η ≫ a) (hη X.obj)).symm
    (coequalizer.desc p hR.w)⟩

/-- Descent along a locally surjective map, using the sheaf image to glue the
fiberwise constant map. This is the descent argument of Stacks, Sites, Tag 086K;
it works for small-valued sheaves on a large site without global sheafification. -/
private theorem exists_descent {C : Type*} [Category C] {J : GrothendieckTopology C}
    {A F H : Sheaf J (Type u)} (p : A ⟶ F) (q : A ⟶ H)
    [Sheaf.IsLocallySurjective p]
    (hq : ∀ (T : Cᵒᵖ) (a b : A.obj.obj T),
      p.hom.app T a = p.hom.app T b → q.hom.app T a = q.hom.app T b) :
    ∃ b : F ⟶ H, p ≫ b = q := by
  classical
  let d : (Subfunctor.range p.hom).toFunctor ⟶ H.obj :=
    { app := fun T ↦ ↾fun x ↦ q.hom.app T x.property.choose
      naturality := by
        intro T T' f
        ext x
        change q.hom.app T'
          (((Subfunctor.range p.hom).toFunctor.map f x).property.choose) =
            H.obj.map f (q.hom.app T x.property.choose)
        rw [← q.hom.naturality_apply]
        apply hq
        exact (((Subfunctor.range p.hom).toFunctor.map f x).property.choose_spec).trans
          ((congrArg (F.obj.map f) x.property.choose_spec.symm).trans
            (p.hom.naturality_apply f x.property.choose).symm) }
  have hd : Subfunctor.toRange p.hom ≫ d = q.hom := by
    ext T a
    apply hq
    exact (Subfunctor.toRange p.hom |>.app T a).property.choose_spec
  let e : Sheaf.image p ⟶ H :=
    ⟨(Subfunctor.range p.hom).sheafifyLift d
      ((isSheaf_iff_isSheaf_of_type J H.obj).mp H.property)⟩
  have he : Sheaf.toImage p ≫ e = q := by
    apply Sheaf.hom_ext
    change (Subfunctor.toRange p.hom ≫
      Subfunctor.homOfLe ((Subfunctor.range p.hom).le_sheafify J)) ≫ e.hom = q.hom
    rw [Category.assoc, Subfunctor.to_sheafifyLift]
    exact hd
  have : IsIso (Sheaf.imageι p) := (Sheaf.isLocallySurjective_iff_isIso p).mp
    inferInstance
  refine ⟨inv (Sheaf.imageι p) ≫ e, ?_⟩
  rw (occs := .pos [1]) [← Sheaf.toImage_ι p]
  rw [Category.assoc, IsIso.hom_inv_id_assoc, he]

/-- Every representable surjective étale scheme atlas presents its algebraic space
as the sheafification of its sectionwise relation quotient. The representing
pullback square is `hR`; `η` and `hη` specify the sheafification of its presheaf
quotient. The monomorphism into the product and the sectionwise clauses say that
the relation is precisely equality of images under `p`.
Source: Stacks, Spaces, Tag 0262, clauses (1)-(3); Sites, Tags 00WH and 086K
(blueprint: lem-a1-etale-atlas-presentation).

Proof:
1. By lem-weil-pbc-site-sheaf-sets-limits-sectionwise, evaluate the representing
   pullback square on each S-scheme T. Its sections are exactly pairs (a,b) with
   p(a)=p(b), with a unique section of R for each pair. The scheme product of
   def-pc-fibre-product represents pairs of S-morphisms. Thus (s,t) is mono and
   its image is an equivalence relation, since equality is reflexive, symmetric
   and transitive. The representing scheme is the one in
   lem-trf-space-fibre-products-etale-covers.
2. Test the representable étale and surjective map p against itself using
   def-trf-algebraic-space. Its base change is one projection R to U. Swapping
   the factors gives the other projection. Both are surjective and étale.
3. For any section x of X on T, the scheme V=T times_X U is surjective étale
   over T. Étale maps are flat and locally of finite presentation by
   def-weil-etale-morphism, so this singleton is an fppf cover by def-pc-fppf-site.
   The second projection gives a lift of x. Hence p is locally surjective and
   is an epimorphism by lem-weil-pbc-site-sheaf-sets-epi-locally-surjective.
4. The represented relation is its sheaf kernel pair. Apply
   lem-weil-pbc-site-sheaf-sets-epi-kernel-pair-coequalizer to conclude that X
   is its coequalizer among fppf sheaves.
5. The presheaf coequalizer is T mapped to U(T)/R(T), by the sectionwise
   description in step 1. Its universal property followed by the bijections hη
   gives the same coequalizer property for Q (def-weil-pbc-sheafification).
   Descending p gives the displayed comparison. The two coequalizer properties
   supply its inverse; uniqueness makes both composites identities. The
   defining factorization identifies the quotient map with p.
-/
theorem etale_atlas_presentation {S : Scheme.{u}} (X : AlgebraicSpace S)
    (U : Over S) (p : yoneda.obj U ⟶ X.obj.obj)
    (hp : IsEtale p) (hsur : IsSurjective p)
    (R : Over S) (s t : R ⟶ U)
    (hR : IsPullback (yoneda.map s) (yoneda.map t) p p)
    (Q : Sheaf (Scheme.fppfTopology.over S) (Type u))
    (η : coequalizer (yoneda.map s) (yoneda.map t) ⟶ Q.obj)
    (hη : ∀ G : Sheaf (Scheme.fppfTopology.over S) (Type u),
      Function.Bijective (fun a : Q.obj ⟶ G.obj ↦ η ≫ a)) :
    Mono (prod.lift s t) ∧
    (∀ T : Over S,
      Equivalence (fun a b : T ⟶ U ↦ ∃ r : T ⟶ R, r ≫ s = a ∧ r ≫ t = b) ∧
      ∀ a b : T ⟶ U,
        (∃ r : T ⟶ R, r ≫ s = a ∧ r ≫ t = b) ↔ p.app (op T) a = p.app (op T) b) ∧
    Etale s.left ∧ Surjective s.left ∧ Etale t.left ∧ Surjective t.left ∧
    IsIso (etaleAtlasPresentationMap p s t hR Q η hη) ∧
    (coequalizer.π (yoneda.map s) (yoneda.map t) ≫ η) ≫
      (etaleAtlasPresentationMap p s t hR Q η hη).hom = p := by
  have hrep : IsRepresentable p := by
    intro T a
    obtain ⟨V, v, q, hv, _⟩ := hp T a
    exact ⟨V, v, q, hv, trivial⟩
  obtain ⟨⟨β, hβ, _⟩, _, hrel, hssur, hset, htsur, htet, _⟩ :=
    representable_etale_kernel_relation X.obj U p hrep hsur hp R s t hR
  have hmono : Mono (prod.lift s t) := by
    constructor
    intro T a b hab
    apply (β T).injective
    apply Subtype.ext
    rw [hβ, hβ]
    apply Prod.ext
    · simpa only [Category.assoc, prod.lift_fst] using
        congrArg (fun f ↦ f ≫ prod.fst) hab
    · simpa only [Category.assoc, prod.lift_snd] using
        congrArg (fun f ↦ f ≫ prod.snd) hab
  have hiff (T : Over S) (a b : T ⟶ U) :
      (∃ r : T ⟶ R, r ≫ s = a ∧ r ≫ t = b) ↔
        p.app (op T) a = p.app (op T) b := by
    constructor
    · rintro ⟨r, rfl, rfl⟩
      have hh := (β T r).property
      rw [hβ] at hh
      exact hh
    · intro hab
      let r := (β T).symm ⟨(a, b), hab⟩
      have hh := congrArg Subtype.val ((β T).apply_symm_apply ⟨(a, b), hab⟩)
      rw [hβ] at hh
      exact ⟨r, congrArg Prod.fst hh, congrArg Prod.snd hh⟩
  let A : Sheaf (Scheme.fppfTopology.over S) (Type u) :=
    (Scheme.fppfTopology.over S).yoneda.obj U
  let p' : A ⟶ X.obj := ⟨p⟩
  have hlift := representable_etale_fppf_local_lifting X.obj U p' hp hsur
  have : Sheaf.IsLocallySurjective p' := hlift.2.1
  have : Epi p' := hlift.2.2
  let q : A ⟶ Q := ⟨coequalizer.π (yoneda.map s) (yoneda.map t) ≫ η⟩
  have hq : ∀ (T : (Over S)ᵒᵖ) (a b : A.obj.obj T),
      p'.hom.app T a = p'.hom.app T b → q.hom.app T a = q.hom.app T b := by
    intro T a b hab
    obtain ⟨r, rfl, rfl⟩ := (hiff T.unop a b).mpr hab
    exact ConcreteCategory.congr_hom
      (congr_app (coequalizer.condition_assoc (yoneda.map s) (yoneda.map t) η) T) r
  obtain ⟨b, hb⟩ := exists_descent p' q hq
  let α := etaleAtlasPresentationMap p s t hR Q η hη
  have hα : η ≫ α.hom = coequalizer.desc p hR.w := by
    exact Equiv.ofBijective_apply_symm_apply _ (hη X.obj) _
  have hfactor : q ≫ α = p' := by
    apply Sheaf.hom_ext
    change (coequalizer.π (yoneda.map s) (yoneda.map t) ≫ η) ≫ α.hom = p
    rw [Category.assoc, hα, coequalizer.π_desc]
  have hbα : b ≫ α = 𝟙 X.obj := by
    apply (cancel_epi p').mp
    rw [← Category.assoc, hb, hfactor, Category.comp_id]
  have hαb : α ≫ b = 𝟙 Q := by
    apply Sheaf.hom_ext
    apply (hη Q).injective
    apply coequalizer.hom_ext
    change q.hom ≫ α.hom ≫ b.hom = q.hom ≫ 𝟙 Q.obj
    have hh := congrArg (fun f : A ⟶ Q ↦ f.hom)
      ((Category.assoc q α b).symm.trans
        ((congrArg (fun f ↦ f ≫ b) hfactor).trans hb))
    simpa only [ObjectProperty.FullSubcategory.comp_hom, Category.comp_id,
      Category.assoc] using hh
  have hiso : IsIso α := ⟨⟨b, hαb, hbα⟩⟩
  refine ⟨hmono, fun T ↦ ⟨hrel T, hiff T⟩, hset, hssur, htet, htsur, hiso, ?_⟩
  exact congrArg (fun f : A ⟶ X.obj ↦ f.hom) hfactor

end AlgebraicGeometry.AlgebraicSpace
