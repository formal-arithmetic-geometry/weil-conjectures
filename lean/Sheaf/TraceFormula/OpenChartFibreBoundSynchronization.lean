module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.Topology.KrullDimension
import Mathlib.AlgebraicGeometry.Properties
import Sheaf.AlgebraicGeometry.FibreDimensionAfterBaseChange
import WeilConjectures.Mathlib.Topology.KrullDimension
import WeilConjectures.Topology.DimensionSupremumLocalDimensions

/-!
# Open-chart fibre bounds and directed synchronization

Source: Stacks Project, Morphisms, Tag 02FY (1), Topology, Tags 0055 and 0B7I,
and Morphisms, Tag 01QR. Auxiliary finite-chart propagation and globalization lemma
(blueprint: lem-trf-open-chart-fibre-bound-synchronization).

The open subschemes are represented by open immersions `ιW` and `ιV`. Their naturality
expresses compatibility with transitions. The equality `hrestrict` makes `g` exactly the
restriction of `f`. The closed comparison is the canonical `pullback.lift` of its two maps.
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- Fibre bounds are local on compatible open charts and synchronize along closed comparisons.

Source: Stacks Project, Morphisms, Tag 02FY (1), Topology, Tags 0055 and 0B7I,
and Morphisms, Tag 01QR
(blueprint: lem-trf-open-chart-fibre-bound-synchronization).

Proof:
1. Fix `i` and a point `s` of `S_i`. For `s` in the image of `V_{i,a}`, the fibre of
   `g_{i,a}` is the open subspace `W_{i,a} ∩ f_i⁻¹(s)` of the scheme-theoretic fibre.
   An open immersion preserves residue fields. Outside that image the intersection is
   empty, since `g_{i,a}` is the restriction of `f_i`. These intersections cover the fibre,
   and the identifications preserve strict chains of irreducible closed subsets.
2. Open-subspace dimension monotonicity (`lem-weil-pbc-open-subspace-dimension-monotone`)
   gives the forward direction of (1). Conversely schemes are sober
   (`lem-weil-pbc-scheme-sober`), so the open-cover bound
   (`lem-weil-pbc-dimension-bound-open-cover`) bounds the entire fibre. Empty intersections
   have dimension bottom. No finite-type hypothesis is needed here.
3. For `i ≤ j` and `a`, base change `g_{i,a}` along `V_{j,a} → V_{i,a}`. At every point
   of a new fibre, `lem-sc-fibre-dimension-after-base-change` identifies its local dimension
   with that of a point of the old fibre. The latter is bounded by the whole old fibre,
   by `def-kun-topological-dimension-at-point`. Take the supremum over all new points using
   `lem-weil-pbc-dimension-supremum-local-dimensions`. An empty supremum is bottom.
4. Base change the assumed closed comparison to each fibre, using
   `lem-weil-pbc-closed-immersion-base-change`. Pullback pasting identifies its source with
   the corresponding fibre of `g_{j,a}`: both universal properties specify a map to
   `W_{j,a}` and a compatible map to the spectrum of the residue field of the base point.
5. A closed immersion identifies the source with a closed subspace. Strict chains of
   nonempty irreducible closed subsets remain strict such chains in the ambient space.
   Its dimension is therefore bounded by that of the base-changed fibre from step 3.
   This proves persistence, including empty source fibres.
6. Choose one bounding index for each `a`. Finite induction and directedness give a common
   upper bound `j`; for an empty chart index type use nonemptiness of `I`. At every `k ≥ j`,
   persistence bounds every chart fibre and (1) bounds every fibre of `f_k`. If there are no
   charts, the covering condition forces every `X_k` empty, so the same conclusion holds.
-/
theorem openChart_fibreBound_synchronization
    {I : Type u} [PartialOrder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (X S : Iᵒᵖ ⥤ Scheme.{u}) (f : X ⟶ S)
    {A : Type v} [Finite A] (W V : A → Iᵒᵖ ⥤ Scheme.{u})
    (ιW : ∀ a : A, W a ⟶ X) (ιV : ∀ a : A, V a ⟶ S)
    (hW : ∀ (a : A) (i : I), IsOpenImmersion ((ιW a).app (op i)))
    (hV : ∀ (a : A) (i : I), IsOpenImmersion ((ιV a).app (op i)))
    (hcover : ∀ (i : I) (x : X.obj (op i)),
      ∃ a : A, x ∈ Set.range ((ιW a).app (op i)))
    (g : ∀ a : A, W a ⟶ V a)
    (hrestrict : ∀ a : A, g a ≫ ιV a = ιW a ≫ f) (d : ℕ) :
    (∀ i : I,
      (∀ s : S.obj (op i), topologicalKrullDim ((f.app (op i)).fiber s) ≤
        (d : WithBot ℕ∞)) ↔
      ∀ (a : A) (t : (V a).obj (op i)),
        topologicalKrullDim (((g a).app (op i)).fiber t) ≤ (d : WithBot ℕ∞)) ∧
    ((∀ (a : A) (i : I), LocallyOfFiniteType ((g a).app (op i))) →
      (∀ (a : A) (i j : I) (h : i ≤ j),
        IsClosedImmersion (pullback.lift ((W a).map (homOfLE h).op)
          ((g a).app (op j)) ((g a).naturality (homOfLE h).op))) →
      (∀ (a : A) (i j : I), i ≤ j →
        (∀ t : (V a).obj (op i),
          topologicalKrullDim (((g a).app (op i)).fiber t) ≤ (d : WithBot ℕ∞)) →
        ∀ t : (V a).obj (op j),
          topologicalKrullDim (((g a).app (op j)).fiber t) ≤ (d : WithBot ℕ∞)) ∧
      ((∀ a : A, ∃ i : I, ∀ t : (V a).obj (op i),
          topologicalKrullDim (((g a).app (op i)).fiber t) ≤ (d : WithBot ℕ∞)) →
        ∃ j : I, ∀ k : I, j ≤ k → ∀ s : S.obj (op k),
          topologicalKrullDim ((f.app (op k)).fiber s) ≤ (d : WithBot ℕ∞))) := by
  sorry

end AlgebraicGeometry
