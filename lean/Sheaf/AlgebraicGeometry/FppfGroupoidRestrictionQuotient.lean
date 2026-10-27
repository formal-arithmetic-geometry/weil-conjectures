/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q59
-/
module

public import Sheaf.AlgebraicGeometry.GroupoidScheme
public import Sheaf.AlgebraicGeometry.EtaleRelationRestrictionQuotient
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Limits.Types.Colimits
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic

import Mathlib.CategoryTheory.Sites.LocallyBijective

/-!
# Fppf restriction of a scheme groupoid

Source: Stacks Project, Groupoids Tags 02VB and 02VH; Descent Tag 02YK
(blueprint: lem-sfb-fppf-groupoid-restriction-quotient).

The existing `restrictedEtaleRelation` definitions impose no etaleness hypotheses:
they give the iterated pullback and its two endpoint maps for any pair of arrows.
Coequalizers of the lifted Yoneda maps are the presheaves of connected components
when the arrows form a groupoid. Values lie in `Type (u + 1)`, containing the
objects and arrows of the big site of `u`-small schemes, so sheafification exists.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- The middle projection from the restricted groupoid to its original arrows.
Source: Stacks Project, Tag 02VB
(blueprint: lem-sfb-fppf-groupoid-restriction-quotient). -/
noncomputable def restrictedGroupoidMiddle {S : Scheme.{u}} {R U U' : Over S}
    (s t : R ⟶ U) (q : U' ⟶ U) : restrictedEtaleRelation s t q ⟶ R :=
  pullback.fst (pullback.snd q s ≫ t) q ≫ pullback.snd q s

/-- The canonical map on composable pairs, induced by the middle projection.
Source: Stacks Project, Tag 02VB
(blueprint: lem-sfb-fppf-groupoid-restriction-quotient). -/
noncomputable def restrictedGroupoidComposableMap {S : Scheme.{u}} {R U U' : Over S}
    (s t : R ⟶ U) (q : U' ⟶ U) :
    pullback (restrictedEtaleRelationSource s t q).left
      (restrictedEtaleRelationTarget s t q).left ⟶ pullback s.left t.left :=
  pullback.map _ _ _ _ (restrictedGroupoidMiddle s t q).left
    (restrictedGroupoidMiddle s t q).left q.left
    (by
      change ((restrictedEtaleRelationSource s t q) ≫ q).left =
        ((restrictedGroupoidMiddle s t q) ≫ s).left
      congr 1
      simp only [restrictedEtaleRelationSource, restrictedGroupoidMiddle, Category.assoc,
        pullback.condition])
    (by
      change ((restrictedEtaleRelationTarget s t q) ≫ q).left =
        ((restrictedGroupoidMiddle s t q) ≫ t).left
      congr 1
      exact (pullback.condition (f := pullback.snd q s ≫ t) (g := q)).symm)

/-- The canonical map of orbit presheaves: on representatives it sends `[x]` to `[x q]`.
It is constructed by the coequalizer universal property, without any groupoid or cover
hypothesis. Source: Stacks Project, Tag 02VH
(blueprint: lem-sfb-fppf-groupoid-restriction-quotient). -/
noncomputable def restrictedGroupoidQuotientMap {S : Scheme.{u}} {R U U' : Over S}
    (s t : R ⟶ U) (q : U' ⟶ U) :
    coequalizer (uliftYoneda.{u + 1}.map (restrictedEtaleRelationSource s t q))
      (uliftYoneda.{u + 1}.map (restrictedEtaleRelationTarget s t q)) ⟶
        coequalizer (uliftYoneda.{u + 1}.map s) (uliftYoneda.{u + 1}.map t) :=
  coequalizer.desc
    (uliftYoneda.{u + 1}.map q ≫
      coequalizer.π (uliftYoneda.{u + 1}.map s) (uliftYoneda.{u + 1}.map t))
    (by
      have hs : restrictedEtaleRelationSource s t q ≫ q =
          restrictedGroupoidMiddle s t q ≫ s := by
        simp only [restrictedEtaleRelationSource, restrictedGroupoidMiddle, Category.assoc,
          pullback.condition]
      have ht : restrictedEtaleRelationTarget s t q ≫ q =
          restrictedGroupoidMiddle s t q ≫ t :=
        (pullback.condition (f := pullback.snd q s ≫ t) (g := q)).symm
      rw [← Functor.map_comp_assoc, hs, Functor.map_comp_assoc, coequalizer.condition,
        ← Functor.map_comp_assoc, ← ht, Functor.map_comp_assoc])

/-- Restriction along an fppf covering preserves the quotient sheaf and reflects
monicity of the arrow relation. The restricted identity, inverse and composition
are specified by their middle projections; together with the groupoid laws these
equations determine exactly the usual restricted operations on triples.

Source: Stacks Project, Groupoids Tags 02VB and 02VH; Descent Tag 02YK
(blueprint: lem-sfb-fppf-groupoid-restriction-quotient).

Proof:
1. The two pullback universal properties identify the restricted arrows on every
   test scheme with triples (x,r,y) with qx = sr and tr = qy. Define identity,
   inverse and composition as (x,e(qx),x), (y,i(r),x), and (x,c(r,h),z).
   The original groupoid laws give all laws in the middle coordinate and the
   endpoint coordinates agree identically. These formulas commute with base change.
2. If the restricted relation is monic, pull back q successively along the common
   source and target of two original arrows. Upstairs those arrows give triples
   with equal endpoints, hence equal middle coordinates. Both covers are fppf,
   hence fpqc. Uniqueness in representable fpqc descent, applied twice, gives
   equality downstairs. Identity, inverse and composition give equivalence of
   arrow existence; monicity makes each witnessing arrow unique in both groupoids.
3. Without monicity, arrow existence is still an equivalence relation by the
   groupoid laws, so its set quotient is the sectionwise coequalizer of the two
   Yoneda maps. The pullback description shows that [x] maps to [qx] injectively:
   an arrow between qx and qy gives the restricted triple (x,r,y).
4. Every original class has a representative u. Pulling back q along u gives an
   fppf cover on which u lifts, so the presheaf map is locally surjective. Its
   sectionwise injectivity gives local injectivity as well.
5. The set-presheaf local-bijection criterion makes its sheafification an
   isomorphism. Naturality of the sheafification unit identifies this map with
   the canonical quotient-sheaf map induced by q. No separatedness, affineness,
   quasi-compactness or additional finiteness property is used. -/
theorem fppf_groupoid_restriction_quotient {S : Scheme.{u}} {R U U' : Over S}
    (s t : R ⟶ U) (e : U ⟶ R) (i : R ⟶ R)
    (c : pullback s.left t.left ⟶ R.left)
    (hG : IsGroupoidScheme s.left t.left e.left i.left c)
    (q : U' ⟶ U) [Surjective q.left] [Flat q.left] [LocallyOfFinitePresentation q.left] :
    (∃ (e' : U' ⟶ restrictedEtaleRelation s t q)
      (i' : restrictedEtaleRelation s t q ⟶ restrictedEtaleRelation s t q)
      (c' : pullback (restrictedEtaleRelationSource s t q).left
        (restrictedEtaleRelationTarget s t q).left ⟶ (restrictedEtaleRelation s t q).left),
      IsGroupoidScheme (restrictedEtaleRelationSource s t q).left
        (restrictedEtaleRelationTarget s t q).left e'.left i'.left c' ∧
      e' ≫ restrictedGroupoidMiddle s t q = q ≫ e ∧
      i' ≫ restrictedGroupoidMiddle s t q = restrictedGroupoidMiddle s t q ≫ i ∧
      c' ≫ (restrictedGroupoidMiddle s t q).left =
        restrictedGroupoidComposableMap s t q ≫ c) ∧
    (Mono (prod.lift (restrictedEtaleRelationSource s t q)
        (restrictedEtaleRelationTarget s t q)) →
      Mono (prod.lift s t) ∧
      (∀ T : Over S, Equivalence (fun a b : T ⟶ U ↦
        ∃ r : T ⟶ R, r ≫ s = a ∧ r ≫ t = b)) ∧
      (∀ T : Over S, Equivalence (fun a b : T ⟶ U' ↦
        ∃ r : T ⟶ restrictedEtaleRelation s t q,
          r ≫ restrictedEtaleRelationSource s t q = a ∧
          r ≫ restrictedEtaleRelationTarget s t q = b))) ∧
    IsIso ((presheafToSheaf (Scheme.fppfTopology.over S) (Type (u + 1))).map
      (restrictedGroupoidQuotientMap s t q)) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
