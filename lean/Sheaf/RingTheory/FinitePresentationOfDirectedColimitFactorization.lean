module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.RingTheory.FinitePresentation
import WeilConjectures.RingTheory.ColimitFinitelyPresentedAlgebras
import WeilConjectures.CategoryTheory.ExistsDirectedReindexing
import Mathlib.RingTheory.FiniteStability

/-!
# Finite presentation from factorization through directed colimit stages

Source: Stacks Project, Algebra, Tag 00QO, Lemma `lemma-characterize-finite-presentation`,
implication (3) implies (1).
(blueprint: lem-sfb-algebra-directed-hom-finite-presentation)
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits

namespace CommAlgCat

/-- An algebra is finitely presented if every map from it into a directed colimit of
algebras factors through a stage. The colimit is expressed by its cocone `c` and its
universal property, so the hypothesis applies to every colimit representative.
All test algebras and indices lie in the same universe as `C`, containing the base ring.

Source: Stacks Project, Algebra, Tag 00QO, Lemma `lemma-characterize-finite-presentation`,
implication (3) implies (1).
(blueprint: lem-sfb-algebra-directed-hom-finite-presentation)

Proof plan:
1. Take the set of quotients of finite polynomial rings over `R` by finitely generated
ideals. By the definition of finite presentation it represents every finitely presented
`R`-algebra. Apply `lem-weil-pbc-algebra-colimit-fp-algebras-over-it` to `C`: the category
of such algebras equipped with a map to `C` is small and filtered, and its canonical
cocone with vertex `C` is a colimit. These quotient models and their maps form sets in
`Type (max u v)`.
2. Apply clause (1) of `lem-weil-pbc-filtered-category-directed-cofinal` to reindex this
colimit by a nonempty directed preorder in that same universe. Write its finitely
presented algebras as `B_i` and its cocone maps as `v_i : B_i ⟶ C`.
3. Apply `hfactor` to this cocone and the identity of `C`. Obtain a stage `B` and an
`R`-algebra map `s : C ⟶ B` with `s ≫ v = 𝟙 C`, where `v` is its cocone map.
4. Finite polynomial generators of `B` over `R` also generate it over `C` via `s`, since
`s` respects the `R`-algebra structures. Thus `B` is of finite type over `C`
(`def-weil-pbc-finite-type-algebra`). The composite `C → B → C` is the identity and is
of finite presentation, with zero generators and zero relations
(`def-weil-pbc-finitely-presented-algebra`).
5. Apply `lem-weil-pbc-finite-presentation-over-finite-type-algebra` with base `C`,
intermediate algebra `B`, final algebra `C`, and map `v`. The identity above is exactly
the required scalar compatibility; hence `v` is of finite presentation. Compose with
the finitely presented structure map `R → B` by clause (2) of
`lem-weil-pbc-finite-presentation-base-change-composition`. The composite is the original
structure map of `C` because `v` is an `R`-algebra map. -/
theorem finitePresentation_of_directed_colimit_factorization
    (R : Type u) [CommRing R] (C : CommAlgCat.{max u v} R)
    (hfactor : ∀ (I : Type (max u v)) [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
      (F : I ⥤ CommAlgCat.{max u v} R) (c : Cocone F), IsColimit c →
        ∀ h : C ⟶ c.pt, ∃ (i : I) (h_i : C ⟶ F.obj i), h_i ≫ c.ι.app i = h) :
    Algebra.FinitePresentation R C := by
  sorry

end CommAlgCat
