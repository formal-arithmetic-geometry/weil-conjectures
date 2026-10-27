module

public import Mathlib.AlgebraicGeometry.Scheme
public import WeilConjectures.AlgebraicGeometry.QuasiFiniteMorphism
public import Mathlib.Topology.GDelta.Basic
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Fiber
import Mathlib.AlgebraicGeometry.OpenImmersion
import WeilConjectures.AlgebraicGeometry.QuasiFiniteAffineOpenInFinite

/-! # Quasi-finite images of closed nowhere dense subsets

Source: Stacks Project, Morphisms of Schemes, Tag 03J2,
`lemma-image-nowhere-dense-quasi-finite`.
(blueprint: lem-sfb-quasifinite-closed-nowhere-dense-image)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A quasi-finite morphism sends a closed nowhere dense subset to a nowhere dense subset.
The image need not be closed. Source: Stacks Project, Morphisms of Schemes, Tag 03J2,
`lemma-image-nowhere-dense-quasi-finite`.
(blueprint: lem-sfb-quasifinite-closed-nowhere-dense-image)

Proof (the node's six steps):
1. Work over an affine open V of X. Quasi-finiteness includes finite type
   (`pqf-def-quasifinite`, `def-weil-finite-type-morphism`), so its preimage has a finite
   affine open cover U_i. Each T_i = T ∩ U_i is closed and nowhere dense in U_i:
   an open subset of U_i contained in T_i is open in Y and contained in T, hence empty.
2. Each restriction g_i : U_i → V is quasi-finite. The affine-pairs criterion
   (`lem-weil-pbc-lft-affine-pairs`) gives local finite type. A map between affine schemes
   is affine (`lem-weil-pbc-morphism-affine-schemes-affine`), hence quasi-compact
   (`lem-weil-pbc-affine-morphism-permanence`), so finite type. Isolation in the fibres
   passes to the open restriction, using the fibre homeomorphism (`def-pc-scheme-fibre`).
3. By `lem-weil-pbc-quasi-finite-affine-open-in-finite`, factor g_i as an open immersion
   j_i : U_i → Z_i followed by a finite map π_i : Z_i → V, with Z_i affine.
4. Let C_i be the closure of j_i(T_i) in Z_i. By `def-weil-open-immersion`, j_i identifies
   U_i with an open O_i. Closedness of T_i gives C_i ∩ O_i = j_i(T_i). Any Z_i-open H
   contained in C_i misses O_i by nowhere denseness there. A point of H would
   then have a neighbourhood disjoint from j_i(T_i), contradicting membership in C_i.
   Thus C_i is closed and nowhere dense (Topology, Tag 03J0).
5. By `lem-sfb-finite-image-nowhere-dense`, π_i(C_i) is closed and nowhere dense.
   Since g_i(T_i) ⊆ π_i(C_i), its closure is contained there, so it is nowhere dense.
6. The image over V is the finite union of the g_i(T_i), hence nowhere dense
   (Topology, Tag 03HO). For two nowhere dense sets, an open inside the union of their
   closures has empty difference with the first closure, then must itself be empty.
   Induct from the empty union. Closure commutes with restriction to an open V, so an
   open inside the global image closure meets each affine V trivially, hence is empty
   (Topology, Tag 03HP). Empty schemes, empty T and empty finite covers are included. -/
theorem Scheme.Hom.isNowhereDense_image_of_isQuasiFinite
    {X Y : Scheme.{u}} (f : Y ⟶ X) (hf : f.IsQuasiFinite)
    (T : Set Y) (hT : IsClosed T) (hTd : IsNowhereDense T) :
    IsNowhereDense (f '' T) := by
  sorry

end AlgebraicGeometry
