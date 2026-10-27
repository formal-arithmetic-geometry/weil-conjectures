module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.Topology.Irreducible
public import Mathlib.Topology.Sober

import WeilConjectures.AlgebraicGeometry.GenericClosedSubsetFibreNonempty
import WeilConjectures.AlgebraicGeometry.GenericFibreClosedCoverSpread
import WeilConjectures.AlgebraicGeometry.GenericOpenFibreDensity

/-! # Simultaneous spreading of closed generic pieces

Source: Stacks Project, `more-morphisms.tex`, Tag 0554
(`lemma-irreducible-components-in-neighbourhood`), successive shrinkings in the proof
(blueprint: lem-trf-generic-closed-pieces-simultaneous-spread).
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory Topology

namespace AlgebraicGeometry

/-- A finite closed generic cover by incomparable irreducible pieces spreads to nonempty
closed covering pieces with dense pairwise relative complements in every nearby ordinary fibre.

Source: Stacks Project, Tag 0554, proof from the pairwise intersections through the
successive shrinkings and the open neighbourhood contained in every component image.

Proof:
1. Put D_i = range j_i. The closed immersion j_i identifies Z_i with the closed subset
   D_i. The ordinary-fibre homeomorphisms identify the fibre of j_i ≫ f at t with
   (f.fiberι t)^{-1}(D_i). These subsets are closed by continuity of the projection.
2. For i ≠ k, the open W_ik = Z_i \ j_i^{-1}(D_k) has dense generic fibre: under the
   preceding homeomorphism it is C_i \ C_k, a nonempty open subset of the irreducible
   C_i. Nonemptiness follows from incomparability; density follows since otherwise
   its proper closed closure and the proper closed C_i ∩ C_k would cover C_i.
3. Apply lem-sbc-generic-open-fibre-density to j_i ≫ f and W_ik. It gives a generic
   neighbourhood U_ik where this open has dense ordinary fibres. Transporting density
   by the fibre homeomorphism gives density in the subtype D_{i,t}, not in all of X_t.
4. The finite union C of the D_i is closed. The generic cover and the fibre
   homeomorphism give f^{-1}({η}) ⊆ C. Apply lem-sbc-generic-fibre-closed-cover-spread
   to C and the empty closed subset. Since closure {η} is all of Y, the resulting
   generic neighbourhood U_cov has all its ordinary fibres covered by the D_{i,t}.
   This works also for an empty family, when those fibres must be empty.
5. Nonemptiness of C_i gives a point in D_i ∩ f^{-1}({η}). Apply
   lem-sbc-generic-closed-subset-fibre-nonempty to each closed D_i and f, giving U_i.
   The fibre homeomorphism turns nonempty intersections into nonempty D_{i,t}.
6. Intersect U_cov, every U_i, and every U_ik for i ≠ k. Finiteness gives an open
   containing η. The preceding steps give closedness, nonemptiness, covering and
   pairwise relative density on it. Empty intersections contribute the whole base;
   no pairwise condition is imposed for a singleton family. No specialized piece is
   asserted to be irreducible.

(blueprint: lem-trf-generic-closed-pieces-simultaneous-spread) -/
theorem exists_open_fibre_closed_pieces_dense_complements
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f] [QuasiCompact f]
    (hY : IsIrreducible (Set.univ : Set Y))
    (η : Y) (hη : IsGenericPoint η (Set.univ : Set Y))
    (I : Type v) [Finite I] (Z : I → Scheme.{u}) (j : ∀ i : I, Z i ⟶ X)
    [∀ i : I, IsClosedImmersion (j i)]
    [∀ i : I, LocallyOfFiniteType (j i ≫ f)] [∀ i : I, QuasiCompact (j i ≫ f)]
    (hpieces : ∀ i : I, IsIrreducible ((f.fiberι η) ⁻¹' Set.range (j i)))
    (hcover : (⋃ i : I, (f.fiberι η) ⁻¹' Set.range (j i)) = Set.univ)
    (hincomparable : ∀ i k : I, i ≠ k →
      ¬ (f.fiberι η) ⁻¹' Set.range (j i) ⊆ (f.fiberι η) ⁻¹' Set.range (j k)) :
    ∃ V : Y.Opens, η ∈ V ∧ ∀ t : Y, t ∈ V →
      (∀ i : I, IsClosed ((f.fiberι t) ⁻¹' Set.range (j i)) ∧
        ((f.fiberι t) ⁻¹' Set.range (j i)).Nonempty) ∧
      (⋃ i : I, (f.fiberι t) ⁻¹' Set.range (j i)) = Set.univ ∧
      ∀ i k : I, i ≠ k →
        Dense {x : (f.fiberι t) ⁻¹' Set.range (j i) |
          (x : f.fiber t) ∉ (f.fiberι t) ⁻¹' Set.range (j k)} := by
  sorry

end AlgebraicGeometry
