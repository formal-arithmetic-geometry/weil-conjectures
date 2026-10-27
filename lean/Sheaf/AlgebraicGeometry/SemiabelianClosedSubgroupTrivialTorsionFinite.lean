module

public import Sheaf.AlgebraicGeometry.SemiabelianGeometricFibres
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.Finite

import Sheaf.AlgebraicGeometry.ZeroDimensionalClosedSubschemeFinite
import WeilConjectures.AlgebraicGeometry.AbelianVariety.Isogeny
import Sheaf.AlgebraicGeometry.GroupNeutralComponentTranslates
import Sheaf.AlgebraicGeometry.LocallyAlgebraicGroupIdentityComponent
import Sheaf.AlgebraicGeometry.ClosedImmersionProducts
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme

/-! # Closed semiabelian subgroups with trivial prime torsion

Source: Brian Conrad, Semistable reduction for abelian varieties, Corollary 3.3, p. 8.
(blueprint: lem-sfb-semiabelian-closed-subgroup-trivial-torsion-finite)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory MonObj

namespace AlgebraicGeometry

/-- A closed subgroup of a semiabelian group with trivial invertible-prime torsion is finite.

Source: Brian Conrad, Semistable reduction for abelian varieties, Corollary 3.3, p. 8.
(blueprint: lem-sfb-semiabelian-closed-subgroup-trivial-torsion-finite)

Here `𝟙 H ^ ℓ` is multiplication by `ℓ`, using the group law on morphisms to `H`.
`GrpObj.ker` is its pullback along the identity section. The hypothesis on the structure
map of this pullback says exactly that its identity section is an isomorphism: the section
and the structure map are inverse whenever either is an isomorphism. No reducedness or
connectedness of `H` is assumed, and the semiabelian predicate permits rank zero.

Proof:
1. Closedness and finite type of `G` give finite type of `H`. Apply
   lem-sfb-locally-algebraic-group-identity-component to obtain the clopen identity component
   and its smooth connected reduction `B`. Reduction and the two subgroup inclusions are
   closed immersions, whose composition is closed by lem-weil-pbc-closed-immersion-products.
2. On every test algebra, injectivity of `B → H` makes the triviality of `H[ℓ]` imply that
   of `B[ℓ]`.
3. By lem-sfb-smooth-connected-semiabelian-subgroup, `B` is an extension of an abelian variety
   by a split torus of rank `r`.
4. If `r > 0`, a root of `1 + X + ⋯ + X^(ℓ-1)` in `k` is nonzero and different from one
   because `ℓ` is nonzero in `k`. It gives a nonidentity `ℓ`-torsion point of the torus,
   contradicting step 2. Thus `r = 0`.
5. The quotient with trivial torus is an isomorphism: unique fppf-local lifts glue. Thus `B`
   is an abelian variety. By lem-sc-mult-n-finite-flat its `ℓ`-torsion has order `ℓ^(2 dim B)`;
   triviality and primality of `ℓ` force dimension zero.
6. Reduction preserves the underlying space. By lem-sfb-group-neutral-component-translates,
   `H` has finitely many clopen components, all translates of its identity component, so it
   has dimension zero. Apply lem-pc-zero-dimensional-closed-subscheme-finite to `H → G`.
-/
theorem isFinite_closedSubgroup_of_semiabelian_trivial_prime_torsion
    (k : Type u) [Field k] [IsAlgClosed k]
    (G : Grp (Over (Spec (.of k)))) [IsCommMonObj G.X]
    [Smooth G.X.hom] [IsSeparated G.X.hom]
    [LocallyOfFiniteType G.X.hom] [QuasiCompact G.X.hom]
    (hG : HasSemiabelianGeometricFibres G)
    (H : Over (Spec (.of k))) [GrpObj H]
    (i : H ⟶ G.X) [IsClosedSubgroupScheme i]
    (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓk : (ℓ : k) ≠ 0)
    (hH : IsIso (GrpObj.ker (𝟙 H ^ ℓ)).hom) :
    IsFinite H.hom := by
  sorry

end AlgebraicGeometry
