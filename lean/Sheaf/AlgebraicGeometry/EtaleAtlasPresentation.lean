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
import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.CategoryTheory.Sites.LocallySurjective
import Mathlib.CategoryTheory.Sites.RegularEpi
import Mathlib.CategoryTheory.Limits.Shapes.KernelPair

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
  sorry

end AlgebraicGeometry.AlgebraicSpace
