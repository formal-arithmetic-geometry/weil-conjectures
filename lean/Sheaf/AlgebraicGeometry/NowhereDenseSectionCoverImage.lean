module

public import WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.Topology.GDelta.Basic

/-!
# Nowhere dense images through a finite closed section cover

Source: Stacks Project, Morphisms, Tag 03HX, proof of
`lemma-image-nowhere-dense-finite`, final finite closed section-cover paragraph
(blueprint: lem-sfb-nowhere-dense-section-cover-image).
-/

@[expose] public section

universe u v

open CategoryTheory

namespace AlgebraicGeometry

/-- A finite locally free morphism covered by finitely many closed subschemes, each mapping
isomorphically to the target, sends closed nowhere dense sets to closed nowhere dense sets.

Source: Stacks Project, Morphisms, Tag 03HX, proof of
`lemma-image-nowhere-dense-finite`, final finite closed section-cover paragraph
(blueprint: lem-sfb-nowhere-dense-section-cover-image).

Proof:
1. Put `C j = Set.range (i j)`. Closed immersions make these closed and identify `Wj j`
   homeomorphically with `C j` (def-weil-closed-immersion). Since `i j ≫ q` is an
   isomorphism, the restriction `h j : C j → X` is a homeomorphism. Thus
   `E j = h j (A ∩ C j)` is closed. The cover gives `q(A) = ⋃ j, E j`, which is closed
   by finiteness. If the index is empty, the cover forces `W` and `A` to be empty.
2. Suppose `A ∩ C j₀` contains a nonempty relatively open set `V` of `C j₀`. Process
   the other finitely many `C j`, keeping `V` nonempty, relatively open and inside `A`.
   If `V ∩ C j` is proper in `V`, replace `V` by its nonempty open complement;
   otherwise keep `V`. Closedness of `C j` makes each replacement relatively open.
   Earlier decisions persist, so finally each `C j` either contains `V` or misses it.
3. Set `U = h j₀ (V)`, a nonempty open subset of `X`. For an index whose `C j` contains
   `V`, injectivity of `h j` gives `C j ∩ q⁻¹(U) = V`. The cover therefore gives
   `V = q⁻¹(U) ∖ ⋃ {j | C j ∩ V = ∅}, C j`. This is open in `W`, since `q` is
   continuous and the removed union is finite and closed. This contradicts the empty
   interior of the closed nowhere dense set `A`. Thus each `A ∩ C j` has empty
   relative interior, and each closed `E j` has empty interior by its homeomorphism.
4. A finite union of closed sets of empty interior has empty interior: if an open `O`
   lies in `D ∪ F`, then the open `O ∖ F` lies in `D`, hence is empty; then `O` lies
   in `F`, hence is empty. Induct on the finite index set, starting with the empty
   union. Applying this to the `E j` proves that the already closed `q(A)` is nowhere
   dense. These are exactly the four proof steps of the DAG node. -/
theorem Scheme.Hom.isClosed_and_isNowhereDense_image_of_finite_closed_section_cover
    {W X : Scheme.{u}} (q : W ⟶ X) [q.IsFiniteLocallyFree]
    {J : Type v} [Finite J] (Wj : J → Scheme.{u}) (i : ∀ j : J, Wj j ⟶ W)
    [∀ j : J, IsClosedImmersion (i j)]
    (hcover : ∀ w : W, ∃ j : J, w ∈ Set.range (i j))
    [∀ j : J, IsIso (i j ≫ q)]
    (A : Set W) (hA : IsClosed A) (hnd : IsNowhereDense A) :
    IsClosed (q '' A) ∧ IsNowhereDense (q '' A) := by
  sorry

end AlgebraicGeometry
