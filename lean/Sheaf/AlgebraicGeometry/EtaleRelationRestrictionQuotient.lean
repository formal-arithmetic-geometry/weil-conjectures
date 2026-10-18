/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N0
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.Sheafification
import Sheaf.CategoryTheory.SiteCoveringAxioms
import WeilConjectures.AlgebraicGeometry.SiteSheafificationSectionsLocal

/-!
# Restriction of an étale equivalence relation

Source: Stacks Project, Groupoids Tag 045Z and Spaces Tag 02WT
(blueprint: lem-trf-etale-relation-restriction-quotient).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

/-- The iterated pullback relation obtained by restricting an étale relation along `g`.
Source: Stacks, Spaces, Tag 02WT (blueprint: lem-trf-etale-relation-restriction-quotient). -/
noncomputable def restrictedEtaleRelation {S : Scheme.{u}} {R U U' : Over S}
    (s t : R ⟶ U) (g : U' ⟶ U) : Over S :=
  pullback (pullback.snd g s ≫ t) g

/-- The first projection of the restricted relation.
Source: Stacks, Spaces, Tag 02WT (blueprint: lem-trf-etale-relation-restriction-quotient). -/
noncomputable def restrictedEtaleRelationSource {S : Scheme.{u}} {R U U' : Over S}
    (s t : R ⟶ U) (g : U' ⟶ U) : restrictedEtaleRelation s t g ⟶ U' :=
  pullback.fst (pullback.snd g s ≫ t) g ≫ pullback.fst g s

/-- The second projection of the restricted relation.
Source: Stacks, Spaces, Tag 02WT (blueprint: lem-trf-etale-relation-restriction-quotient). -/
noncomputable def restrictedEtaleRelationTarget {S : Scheme.{u}} {R U U' : Over S}
    (s t : R ⟶ U) (g : U' ⟶ U) : restrictedEtaleRelation s t g ⟶ U' :=
  pullback.snd (pullback.snd g s ≫ t) g

/-- Restricting an étale equivalence relation along an étale morphism preserves the
relation and its quotient sheaf. If the morphism is surjective, the quotient map is an
isomorphism.

Source: Stacks Project, Groupoids Tag 045Z and Spaces Tag 02WT
(blueprint: lem-trf-etale-relation-restriction-quotient).

Proof:
1. A map from a test scheme `T` to the iterated pullback is a triple `(a, r, b)`
   with `r ≫ s = a ≫ g` and `r ≫ t = b ≫ g` (def-pc-fibre-product).
   The induced relation is therefore the inverse image under `g` of the original
   equivalence relation. Reflexivity, symmetry and transitivity follow. Monicity of
   the original relation makes `r` unique for its endpoints, proving monicity of the
   restricted relation.
2. The first restricted projection is the composite of a base change of `g` and a
   base change of `s`. Reassociate the pullbacks for the second projection to express
   it as the composite of a base change of `g` and a base change of `t`. The lemmas
   lem-weil-pbc-etale-scheme-base-change and lem-weil-pbc-etale-composition-cancellation
   make both projections étale.
3. The map `[a] ↦ [a ≫ g]` on presheaf quotients is well defined by step 1. If two
   images agree, an arrow `r` in the original relation joins their endpoints. Then
   `(a, r, b)` joins the original representatives in the restricted relation, proving
   injectivity on every test scheme. The sheafification universal property
   (def-weil-pbc-sheafification) gives the canonical map `α`, with the displayed
   compatibility with the quotient projections. That compatibility determines it
   uniquely, since the presheaf coequalizer projection is epi and `hη'` is injective.
4. For sections with equal images under `α`, take local representatives in the
   restricted quotient using lem-weil-pbc-site-sheafification-sections-local.
   Refine to a common covering using def-weil-pbc-sites-and-cohomology. Local equality
   in the original sheafification gives a further covering where the quotient
   classes agree. Step 3 makes the restricted classes equal there. Sheaf separation
   then proves injectivity of `α` on every test scheme.
5. If `g` is surjective, its flatness and local finite presentation
   (def-weil-etale-morphism) make its singleton family an fppf cover
   (def-pc-fppf-site). Represent any section of `F` locally by a map to `U`, and pull
   back `g` along that map. The lemma lem-weil-pbc-etale-covering-base-change makes
   this another étale surjective cover, on which the representative lifts to `U'`.
   Composing coverings gives local lifts through `α`.
6. On overlaps these lifts have equal images, so step 4 makes them agree. The sheaf
   gluing axiom (def-weil-pbc-sites-and-cohomology) gives a unique global lift.
   Uniqueness makes the inverse natural in the test scheme, proving `IsIso α`.
-/
theorem etale_relation_restriction_quotient {S : Scheme.{u}} {R U U' : Over S}
    (s t : R ⟶ U) [Mono (prod.lift s t)]
    (hrel : ∀ T : Over S, Equivalence (fun a b : T ⟶ U ↦
      ∃ r : T ⟶ R, r ≫ s = a ∧ r ≫ t = b))
    (g : U' ⟶ U) [Etale s.left] [Etale t.left] [Etale g.left]
    (F : Sheaf (Scheme.fppfTopology.over S) (Type u))
    (η : coequalizer (yoneda.map s) (yoneda.map t) ⟶ F.obj)
    (hη : ∀ G : Sheaf (Scheme.fppfTopology.over S) (Type u),
      Function.Bijective (fun k : F.obj ⟶ G.obj ↦ η ≫ k))
    (F' : Sheaf (Scheme.fppfTopology.over S) (Type u))
    (η' : coequalizer (yoneda.map (restrictedEtaleRelationSource s t g))
      (yoneda.map (restrictedEtaleRelationTarget s t g)) ⟶ F'.obj)
    (hη' : ∀ G : Sheaf (Scheme.fppfTopology.over S) (Type u),
      Function.Bijective (fun k : F'.obj ⟶ G.obj ↦ η' ≫ k)) :
    Mono (prod.lift (restrictedEtaleRelationSource s t g)
      (restrictedEtaleRelationTarget s t g)) ∧
    (∀ T : Over S, Equivalence (fun a b : T ⟶ U' ↦
      ∃ r : T ⟶ restrictedEtaleRelation s t g,
        r ≫ restrictedEtaleRelationSource s t g = a ∧
        r ≫ restrictedEtaleRelationTarget s t g = b)) ∧
    Etale (restrictedEtaleRelationSource s t g).left ∧
    Etale (restrictedEtaleRelationTarget s t g).left ∧
    ∃ α : F'.obj ⟶ F.obj,
      (coequalizer.π (yoneda.map (restrictedEtaleRelationSource s t g))
          (yoneda.map (restrictedEtaleRelationTarget s t g)) ≫ η') ≫ α =
        yoneda.map g ≫ (coequalizer.π (yoneda.map s) (yoneda.map t) ≫ η) ∧
      Mono α ∧ (Surjective g.left → IsIso α) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
