/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q84
-/
module

public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Sheaf.CategoryTheory.Sites.CoherentTopos
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.ObjectProperty.LimitsClosure
public import Mathlib.CategoryTheory.Category.Cat
import Mathlib.CategoryTheory.Sites.Limits

/-!
# Finite-limit closure through quasi-compact subobjects of generators

Source: Stacks Project, `sites.tex`, Tags 00W2, 0D07, 0GMP, 0GMQ; the agent
finite-limit closure argument in the node, with ILO, Exposé XI, proof of Lemma 2.5,
printed p. 179 as context (blueprint: lem-trf-coherent-generator-subobject-closure).
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- A quasi-compact generating family whose arbitrary overlaps over its members are
quasi-compact consists of coherent objects. With terminal and binary-product closure,
its quasi-compact subobjects are coherent and closed under finite limits; there is a
small full coherent generating subcategory containing the family and closed under
finite limits up to isomorphism. Its entire finite-limit closure is coherent.

Source: the agent closure argument recorded in the node; Stacks Project, `sites.tex`,
Tags 00W2, 0D07, 0GMP and 0GMQ, with ILO XI, proof of Lemma 2.5, printed p. 179 as context
(blueprint: lem-trf-coherent-generator-subobject-closure).

Proof:
1. By `lem-weil-pbc-site-sheaf-sets-limits-sectionwise`, limits of set sheaves exist
   and are computed sectionwise. Quasi-compactness and quasi-separatedness are invariant
   under isomorphism: cancel the isomorphism in epimorphic covers and identify pullbacks
   by their universal properties (`def-trf-coherent-topos`).
2. Generation supplies a small epimorphic coproduct onto every quasi-compact object.
   Its quasi-compactness selects a finite generator cover, possibly empty.
3. For quasi-compact B,C over a generator, take finite generator covers of B and C.
   Clause (1) of `lem-trf-topos-finite-cover-calculus` makes their pairwise pullbacks
   cover B ×_G C. Each source is quasi-compact by the overlap hypothesis; clause (3)
   makes B ×_G C quasi-compact. Thus each generator is quasi-separated and coherent.
4. A monomorphism T → G identifies B ×_T C with B ×_G C by cancellation against that
   monomorphism. A quasi-compact T embedded in G is therefore quasi-separated, hence
   coherent (`def-trf-coherent-topos`).
5. Under the additional assumptions, the terminal object is coherent, and its
   quasi-separatedness makes every product of quasi-compact objects quasi-compact.
   The product of embeddings T → G_i and S → G_j is monic into G_i × G_j, which is
   isomorphic to a generator. Thus the class D contains the terminal object and is
   closed under binary products, hence finite products, including the empty product.
6. For arbitrary f,g : T → S in D, their graphs T → T × S have quasi-compact pullback
   since T × S is quasi-separated. The two pullback projections agree by their first
   components. Their common map to T is the equalizer of f,g by the pullback universal
   property, and is monic. Composing it with T → G_i puts the equalizer in D.
7. A finite diagram has limit the equalizer of the two maps from the product over its
   objects to the product over its arrows, expressing compatibility with each arrow.
   Steps 5 and 6 put this object in D. This includes the empty diagram and arbitrary
   sheaf morphisms, and step 1 handles any isomorphic choice of limit.
8. Starting with the given family and a terminal object, repeatedly adjoin chosen
   binary products and equalizers of all parallel arrow pairs. Each stage is small:
   morphisms between fixed sheaves form a set of natural transformations bounded by
   the product of sectionwise function sets. The countable union is small and all its
   objects are in D by steps 5 and 6. Its full subcategory has chosen finite limits up
   to isomorphism by step 7. It generates since it contains the original generators.
   Finally D contains the family and is closed under isomorphisms and finite limits,
   so every object of its finite-limit closure is coherent.
-/
theorem coherent_generator_subobject_closure
    {C : Type u} [Category.{v} C]
    (J : Precoverage C) (_hJ : J.IsSiteForCoverings)
    {I : Type (max u v w)} (G : I → Sheaf J.toGrothendieck (Type (max u v w)))
    (hqc : ∀ i, IsQuasiCompactObject.{max u v w} (G i))
    (hgen : ∀ X : Sheaf J.toGrothendieck (Type (max u v w)),
      ∃ (A : Type (max u v w)) (ι : A → I) (f : ∀ a, G (ι a) ⟶ X),
        Epi (Sigma.desc f))
    (hoverlap : ∀ (i j k : I) (f : G j ⟶ G i) (g : G k ⟶ G i),
      IsQuasiCompactObject.{max u v w} (pullback f g)) :
    (∀ i, IsCoherentObject.{max u v w} (G i)) ∧
    ((∃ i, Nonempty ((⊤_ (Sheaf J.toGrothendieck (Type (max u v w)))) ≅ G i)) →
      (∀ i j, ∃ k, Nonempty ((G i ⨯ G j) ≅ G k)) →
      (∀ T : Sheaf J.toGrothendieck (Type (max u v w)),
        IsQuasiCompactObject.{max u v w} T →
          (∃ (i : I) (m : T ⟶ G i), Mono m) → IsCoherentObject.{max u v w} T) ∧
      (∀ (K : Type) [SmallCategory K] [FinCategory K],
        ObjectProperty.IsClosedUnderLimitsOfShape
          ((fun T : Sheaf J.toGrothendieck (Type (max u v w)) ↦
            IsQuasiCompactObject.{max u v w} T ∧
              ∃ (i : I) (m : T ⟶ G i), Mono m) : ObjectProperty _) K) ∧
      (∃ S : ObjectProperty (Sheaf J.toGrothendieck (Type (max u v w))),
        ObjectProperty.Small.{max u v w} S ∧
        (∀ i, S (G i)) ∧
        (∀ T, S T → IsCoherentObject.{max u v w} T) ∧
        (∀ (K : Type) [SmallCategory K] [FinCategory K],
          S.isoClosure.IsClosedUnderLimitsOfShape K) ∧
        (∀ X : Sheaf J.toGrothendieck (Type (max u v w)),
          ∃ (A : Type (max u v w)) (B : A → Sheaf J.toGrothendieck (Type (max u v w)))
            (f : ∀ a, B a ⟶ X), (∀ a, S (B a)) ∧ Epi (Sigma.desc f))) ∧
      (∀ T : Sheaf J.toGrothendieck (Type (max u v w)),
        (ObjectProperty.ofObj G).limitsClosure
          (fun K : (Σ K : Cat.{0, 0}, FinCategory K) ↦ K.1) T →
            IsCoherentObject.{max u v w} T)) := by
  sorry

end CategoryTheory
