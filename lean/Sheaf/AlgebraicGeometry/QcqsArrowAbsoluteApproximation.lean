module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
import WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit
import Mathlib.CategoryTheory.Presentable.Directed
import Mathlib.CategoryTheory.Limits.Final
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.AffineTransitionLimit

/-!+# Simultaneous absolute approximation of a qcqs scheme morphism

Source: Stacks Project, Limits of Schemes, Tag 0GS1, `lemma-approximate-morphism`
(blueprint: lem-trf-qcqs-arrow-absolute-approximation).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- Every morphism between qcqs schemes is a directed inverse limit of morphisms
between schemes of finite type over the integers, with affine transitions on both sides.
The diagrams encode the transition identity and composition laws; naturality of `F`
encodes all transition squares. The cones have the specified vertices `X` and `S`.

Source: Stacks Project, Limits of Schemes, Tag 0GS1, `lemma-approximate-morphism`
(blueprint: lem-trf-qcqs-arrow-absolute-approximation).

Proof plan, following the node's eight steps:
1. Apply `prop-nagata-noetherian-inverse-system` separately to `X` and `S`, and
   `lem-weil-pbc-cofiltered-limit-directed-reindex` to both diagrams. This gives nonempty
   directed preorders `A₀`, `B₀` and finite-type integer stages with affine transitions.
   Replace `A₀` by `A₀ × ℕ`, ordered by equality or by the original order in the first
   coordinate and strict inequality in the second. This is a partial order: strict cycles
   would imply a strict cycle in `ℕ`; directedness follows by taking a common upper bound
   in `A₀` and a strictly larger integer. The projection to `A₀` is cofinal: every index
   has a lift, and any two lifts above an index have a common upper bound above it.
   Apply `lem-weil-pbc-initial-functor-limit` to the opposite projection to retain the
   limiting cone. Do the same for `B₀`, obtaining directed partial orders `A` and `B`.
2. By `lem-weil-pbc-finite-type-over-noetherian`, all stages are Noetherian.
   `lem-weil-pbc-locally-noetherian-quasi-separated` makes them quasi-separated, and
   `pqf-lem-lft-fp-locnoeth` makes each target stage locally of finite presentation
   over `Spec ℤ`. Thus the source stages are qcqs and the target stages have the
   presentation hypothesis needed for factorization.
3. For each `b : B`, factor the composite `X → S → S_b` through some `X_a` using
   `lem-weil-pbc-finite-presentation-map-limit-factorization` over `Spec ℤ`. Precompose
   with a transition map to arrange that `a` lies above any prescribed source bound.
4. Let `I` consist of triples `(a,b,v)` with `v : X_a → S_b` and
   `p_a ≫ v = f ≫ q_b`. This is a small, nonempty set. Order triples by domination
   of both indices and commutativity of the transition square. Transition identities
   and composition give reflexivity and transitivity. Domination in both directions
   identifies the indices by antisymmetry of `A` and `B`, then identifies the maps.
5. Given two triples, choose a target index `d` above both target indices. Step 3
   factors `X → S_d` through some `X_e`. Choose a source index above both original
   source indices and `e`. The two comparisons to each original target agree on `X`.
   Apply `lem-weil-pbc-locally-finite-type-limit-map-equality` successively to these
   two comparisons, increasing the source index each time. The first equality persists
   after precomposition. The resulting triple dominates both given triples, proving
   directedness. Choosing an upper target bound repairs the direction in the printed
   proof; no finite-type property of `f` is used.
6. Both projections from `I` to `A` and `B` are cofinal. For a source bound use step 3
   above that bound; for a target bound use step 3 at that target. Two triples above
   either bound have a common upper bound by step 5, still above the chosen bound.
   On opposite categories these give nonempty, connected comma categories, with the
   length-two zigzag through a common upper bound and commuting triangles in the posets.
7. Apply `lem-weil-pbc-initial-functor-limit` to these two opposite projections.
   The restricted cones retain vertices `X` and `S` and their limit universal properties.
8. At `(a,b,v)` take the stages `X_a`, `S_b`, the stage morphism `v`, and projections
   `p_a`, `q_b`. The order defines the natural transformation of stage diagrams;
   membership gives the square with `f`. Transitions, finite type, qcqs and the two
   limiting properties are exactly those established above. -/
theorem Scheme.Hom.exists_qcqs_arrow_absoluteApproximation
    {X S : Scheme.{u}} (f : X ⟶ S)
    [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace S] [QuasiSeparatedSpace S] :
    ∃ (I : Type u) (_ : PartialOrder I) (_ : Nonempty I) (_ : IsDirected I (· ≤ ·))
      (D E : Iᵒᵖ ⥤ Scheme.{u}) (F : D ⟶ E)
      (p : (Functor.const Iᵒᵖ).obj X ⟶ D) (q : (Functor.const Iᵒᵖ).obj S ⟶ E),
      (∀ i : Iᵒᵖ,
        LocallyOfFiniteType (specULiftZIsTerminal.from (D.obj i)) ∧
        QuasiCompact (specULiftZIsTerminal.from (D.obj i)) ∧
        CompactSpace (D.obj i) ∧ QuasiSeparatedSpace (D.obj i) ∧
        LocallyOfFiniteType (specULiftZIsTerminal.from (E.obj i)) ∧
        QuasiCompact (specULiftZIsTerminal.from (E.obj i)) ∧
        CompactSpace (E.obj i) ∧ QuasiSeparatedSpace (E.obj i)) ∧
      (∀ (i j : Iᵒᵖ) (a : i ⟶ j), IsAffineHom (D.map a) ∧ IsAffineHom (E.map a)) ∧
      (∀ i : Iᵒᵖ, p.app i ≫ F.app i = f ≫ q.app i) ∧
      Nonempty (IsLimit (Cone.mk X p)) ∧ Nonempty (IsLimit (Cone.mk S q)) := by
  sorry

end AlgebraicGeometry
