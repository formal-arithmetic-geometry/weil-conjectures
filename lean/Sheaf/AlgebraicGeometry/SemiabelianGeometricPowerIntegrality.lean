module

public import Sheaf.AlgebraicGeometry.ToriMultiplicativeType
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import Mathlib.CategoryTheory.Limits.Shapes.Products

import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Fiber
import Mathlib.CategoryTheory.Yoneda
import Mathlib.Topology.Connected.Clopen
import Sheaf.AlgebraicGeometry.GeometricallyConnectedAlgebraicClosure

/-! # Integral finite powers of a geometric semiabelian group

Source: Stacks Project, groupoids.tex, Tags 0499, 049B and 0B7Q;
topology.tex, Tag 0377; varieties.tex, Tag 056T.
(blueprint: lem-sfb-semiabelian-geometric-power-integrality)

The kernel square and fppf local surjectivity express the exact sequence with its
specified split torus and quotient. Finite powers are products in schemes over F;
the empty product is the terminal F-scheme, hence Spec F.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

namespace AlgebraicGeometry

/-- Every finite power of a smooth separated finite-type extension of a proper smooth
geometrically connected commutative group by a split torus is integral.

Source: Stacks Project, groupoids.tex, Tags 0499, 049B and 0B7Q;
topology.tex, Tag 0377; varieties.tex, Tag 056T.
(blueprint: lem-sfb-semiabelian-geometric-power-integrality)

Proof plan, following the seven steps of the DAG node:
1. Apply lem-sfb-diagonalizable-group-geometric-criteria to Z^r. The split torus is
   smooth, geometrically connected and affine, including r = 0. Over an affine
   chart of B it has the finite presentation F[x_i,y_i]/(x_i*y_i-1), with the
   chart's ring replacing F. The definition def-sbc-locally-finite-presentation,
   lem-weil-pbc-affine-morphism-permanence and lem-pc-proper-base-change give finite
   presentation and smoothness after base change to B.
2. The kernel square gives a unique torus element expressing the difference of
   two lifts of the same section of B. The fppf local lifts trivialize G over B
   by t mapped to i(t)*s. Apply lem-sfb-smooth-affine-group-torsor-representability
   and lem-galois-yoneda-fully-faithful to conclude that q is affine, smooth,
   surjective and universally open, with its translation torsor isomorphism.
3. Each fibre is nonempty by lem-weil-pbc-surjective-base-change. Apply
   lem-sfb-scheme-large-algclosed-jacobson to find an algebraically closed extension
   over which it has a rational closed point. Translation by this point identifies
   the extended fibre with the split torus. The criterion
   lem-weil-geometrically-connected-algebraic-closure makes the fibre geometrically
   connected; no point over the original residue field is assumed.
4. By def-pc-scheme-fibre the scheme fibre is homeomorphic to the topological
   fibre. The open surjective q is a quotient map. Apply
   lem-weil-pbc-connected-fibres-quotient-preimage-connected to the nonempty connected
   B. Thus G is connected, and lem-weil-geometrically-connected-algebraic-closure
   over the algebraically closed F makes it geometrically connected.
5. Induct on n for smoothness of the power. At n = 0 the structure map is the
   identity of Spec F, smooth by def-sbc-smooth-morphisms. The successor projection
   is a smooth base change by lem-pc-proper-base-change; composition is smooth by
   lem-trf-smooth-composition.
6. After every field extension K/F, induct on n for nonempty connectedness of the
   power. The base is Spec K. For the successor, apply
   lem-weil-pbc-geometrically-connected-product-components to G_K and the preceding
   power. Associativity of fibre products identifies this product with the next
   power. Hence every power is geometrically connected, including the empty one.
7. Apply lem-trf-smooth-connected-fibre-normal-integrality over Spec F using steps
   5 and 6. The unique fibre is the power itself, so it is integral. By
   def-pc-integral-scheme this includes nonemptiness, reducedness and irreducibility.
   For n = 0 the coordinate ring is the field F itself.
-/
theorem semiabelian_geometric_power_integrality
    {F : Type u} [Field F] [IsAlgClosed F]
    (G : Grp (Over (Spec (.of F))))
    [IsCommMonObj G.X] [Smooth G.X.hom] [IsSeparated G.X.hom]
    [LocallyOfFiniteType G.X.hom] [QuasiCompact G.X.hom]
    (r : ℕ) (B : Grp (Over (Spec (.of F))))
    [IsCommMonObj B.X] [IsProper B.X.hom] [Smooth B.X.hom]
    [GeometricallyConnected B.X.hom]
    (i : MultiplicativeType.splitTorus F r ⟶ G) (q : G ⟶ B)
    (hker : IsPullback i.hom.hom (toUnit (MultiplicativeType.splitTorus F r).X)
      q.hom.hom η[B.X])
    (hepi : Presheaf.IsLocallySurjective (Scheme.fppfTopology.over (Spec (.of F)))
      (yoneda.map q.hom.hom)) :
    ∀ n : ℕ, IsIntegral (∏ᶜ fun _ : Fin n ↦ G.X).left := by
  sorry

end AlgebraicGeometry
