/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.CategoryTheory.Sites.CoherentTopos
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.Limits.HasLimits

import Mathlib.CategoryTheory.Sites.Sheafification
import Mathlib.CategoryTheory.Sites.LocallySurjective
import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.CategoryTheory.Sites.LeftExact
import WeilConjectures.AlgebraicGeometry.SiteSheafificationSectionsLocal
import Sheaf.CategoryTheory.SiteCoveringAxioms
import Sheaf.CategoryTheory.Sites.CoherentToposRepair

/-!
# Coherent objects: finite images and filtered approximation

Source: Orgogozo, author draft, §8.1, printed pp. 17--18, and Lemma 8.3.3,
printed p. 19 (blueprint: lem-trf-coherent-object-approximation).
-/

@[expose] public section

universe w u v

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- In a coherent Grothendieck topos, coherent objects are stable under finite coproducts,
finite limits and images, and every quasi-separated object is a directed union of coherent
subobjects. Source: Orgogozo, §8.1 and the final paragraph of Lemma 8.3.3. The proof below
is the node's general coherent-topos argument, using the cited set-sheaf calculus.

1. Present the topos by a small site (`def-trf-coherent-topos`). Sheafification of the
sectionwise coproduct is the coproduct by its adjunction (`def-weil-pbc-sheafification`).
Sections locally lie in summands (`lem-weil-pbc-site-sheafification-sections-local`), so
joint epimorphy is local lifting (`lem-weil-pbc-site-sheaf-sets-epi-locally-surjective`).
Sectionwise pullbacks (`lem-weil-pbc-site-sheaf-sets-limits-sectionwise`) show these covers
are stable under pullback; refining local lifts proves stability under composition.

2. Sheafify the sectionwise image of `f : A ⟶ B`. Exact sheafification
(`lem-weil-pbc-sheafification-sets-exact`) preserves its monomorphism into `B`, since
its diagonal is an isomorphism. Local representatives lift to `A`, making `A ⟶ im f`
epic by the local epi criterion. Every subobject through which `f` factors contains its
sectionwise image, so the adjunction makes the sheafified image the least such subobject.

3. A finite jointly epic family of quasi-compact objects has quasi-compact target:
pull a cover back to each source, choose finite subcovers, and take their finite union.
Hence epimorphic images and finite coproducts of quasi-compact objects are quasi-compact.
The initial object is strict (`lem-trf-set-sheaf-finite-extensivity`), so the empty family
also gives quasi-compactness of the empty coproduct.

4. Every quasi-compact object has a finite cover by the given coherent generators:
choose a finite subcover of its generating cover (`def-trf-coherent-topos`). Subobjects
of quasi-separated objects are quasi-separated, since monicity identifies the fibre
product over the subobject with that over the ambient object. Thus a quasi-compact
subobject of a quasi-separated object is coherent.

5. The terminal generator is coherent, so products of quasi-compact objects are
quasi-compact. To test quasi-separatedness of a product of coherent `A` and `B`, cover
the quasi-compact test objects by finite families of generators `U` and `V`. For each
pair, `T = U × V` is a coherent generator. The subobjects `U ×_A V` and `U ×_B V` of
`T` are quasi-compact. Their intersection is quasi-compact by quasi-separatedness of
`T`; sectionwise limits identify it with `U ×_(A × B) V`. These finitely many
intersections cover the desired test fibre product, so Step 3 proves it quasi-compact.

6. The equalizer of two maps `A ⇉ B` between coherent objects is `A ×_(B × B) B`.
It is quasi-compact by quasi-separatedness of `B × B`, and quasi-separated as a
subobject of `A`. Finite products and these equalizers yield all finite limits through
the product-equalizer formula, checked sectionwise by the cited sheaf-limit lemma.

7. Finite coproducts are quasi-compact by Step 3. Finite extensivity decomposes test
objects over a coproduct into their pullbacks to its summands. Each such piece of a
quasi-compact test object is quasi-compact: add the complementary summand to its cover,
choose a finite subcover of the whole object, and pull back, eliminating the complement
by disjointness. Fibre products of these pieces are quasi-compact by quasi-separatedness
of the coherent summands. Extensivity and Step 3 prove quasi-separatedness of the
coproduct. Strictness of the initial object also treats the empty coproduct.

8. The image of a map from a quasi-compact object to a quasi-separated object is
quasi-compact by Steps 2--3 and quasi-separated by Step 4. This proves image coherence,
in particular for maps between coherent objects.

9. Cover a quasi-separated `G` by a small family of coherent generators. Index by the
finite subsets of this family, ordered by inclusion, and take the images of the finite
subcoproducts in `G`. Steps 3 and 8 make these images coherent. The least-image property
gives unique inclusion transitions over `G`; uniqueness gives their functor laws.
The index is small, contains the empty subset, and is directed by finite union.

10. A section of `G` locally lifts to a generator and hence to one of the images.
A compatible family of maps from the images to any sheaf defines a map locally on these
representatives. Two representatives agree in the image indexed by the union of their
indices because its map to `G` is monic. Their images therefore agree; the sheaf axiom
glues them uniquely. Restricting representatives proves naturality, compatibility and
uniqueness. This is the colimit universal property (`def-weil-pbc-category-colimit`).

11. A subobject of coherent `F` is quasi-separated by Step 4, so Steps 9--10 apply,
without assuming that subobject quasi-compact or coherent.
(blueprint: lem-trf-coherent-object-approximation). -/
theorem coherentObjectApproximation
    (E : Type u) [Category.{v} E] [HasCoproducts.{w} E] [HasFiniteLimits E]
    (hE : IsCoherentTopos.{w} E) :
    (∀ (n : ℕ) (X : Fin n → E),
      (∀ i, IsCoherentObject (X i)) →
      IsCoherentObject (∐ (fun i : ULift.{w} (Fin n) => X i.down))) ∧
    (∀ (J : Type) [SmallCategory J] [FinCategory J],
      ObjectProperty.IsClosedUnderLimitsOfShape
        (fun X : E => IsCoherentObject X) J) ∧
    (∀ (A B : E) (f : A ⟶ B),
      IsCoherentObject A → IsCoherentObject B →
      ∃ (I : E) (e : A ⟶ I) (m : I ⟶ B),
        Epi e ∧ Mono m ∧ e ≫ m = f ∧ IsCoherentObject I ∧
        ∀ (D : E) (d : D ⟶ B), Mono d →
          (∃ q : A ⟶ D, q ≫ d = f) →
          ∃ q' : I ⟶ D, q' ≫ d = m) ∧
    (∀ (G : E), IsQuasiSeparatedObject G →
      ∃ (I : Type w) (_ : PartialOrder I),
        Nonempty I ∧ IsDirected I (· ≤ ·) ∧
        ∃ (F : I ⥤ E),
          (∀ i, IsCoherentObject (F.obj i)) ∧
          (∀ (i j : I) (h : i ≤ j), Mono (F.map (homOfLE h))) ∧
          ∃ (c : Cocone F),
            c.pt = G ∧ (∀ i, Mono (c.ι.app i)) ∧ Nonempty (IsColimit c)) ∧
    (∀ (G F : E) (m : G ⟶ F), Mono m → IsCoherentObject F →
      ∃ (I : Type w) (_ : PartialOrder I),
        Nonempty I ∧ IsDirected I (· ≤ ·) ∧
        ∃ (D : I ⥤ E),
          (∀ i, IsCoherentObject (D.obj i)) ∧
          (∀ (i j : I) (h : i ≤ j), Mono (D.map (homOfLE h))) ∧
          ∃ (c : Cocone D),
            c.pt = G ∧ (∀ i, Mono (c.ι.app i)) ∧ Nonempty (IsColimit c)) := by
  sorry

end CategoryTheory
