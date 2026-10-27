module

public import Sheaf.AlgebraicGeometry.LinearlyReductiveGroupScheme
public import Sheaf.AlgebraicGeometry.SemisimpleGroupSchemePoint
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Sheaf.AlgebraicGeometry.GroupoidScheme
import Sheaf.AlgebraicGeometry.PerfectFieldGroupoidImageClosure
import Sheaf.AlgebraicGeometry.GeometricReducedFiniteTypePerfectField
import Mathlib.AlgebraicGeometry.Group.Smooth
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
import WeilConjectures.Mathlib.RingTheory.Nullstellensatz

/-! # The cyclic closure of a semisimple point is linearly reductive

Source: Milne, Algebraic Groups (2017), Corollary 13.8, printed p.257;
Lemma 1.40, Theorem 1.45, Definition 1.48, Proposition 1.26 and Section 9.19
(blueprint: lem-sfb-semisimple-cyclic-closure-linearly-reductive).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory
open scoped MonObj

namespace AlgebraicGeometry

/-- The reduced closed subscheme supported on the closure of the integer powers of
s inherits the ambient group operations, is smooth and linearly reductive, and contains
a Zariski-dense cyclic subgroup. The hypotheses on G and j specify precisely that reduced
induced closed subscheme; they do not assume any group structure on G. A closed immersion
and its reduced source are determined, up to unique isomorphism over H, by their support.
Source: Milne, Algebraic Groups (2017), Corollary 13.8, printed p.257 and Section 9.19,
printed p.171 (blueprint: lem-sfb-semisimple-cyclic-closure-linearly-reductive).

Proof plan, following the six steps of the node:
1. Construct the constant integer group scheme as the coproduct of copies of Spec k;
   multiplication adds the indices. Map its nth component to H by s^n. This is a
   homomorphism, hence a map of absolute groupoids (def-a1-groupoid-scheme).
2. An algebraically closed field is perfect. Apply
   lem-sfb-perfect-field-groupoid-image-closure to obtain the restricted group laws
   on the reduced image closure, and identify it with G by its reduced closed support.
   The quotient of the finitely generated coordinate algebra of H shows G is finite type.
   Each s^n factors through G, and the resulting points are dense by its support.
3. By lem-kun-geometric-reduced-perfect, G is geometrically reduced. Then
   lem-sfb-geometrically-reduced-group-smooth gives smoothness, without connectedness.
4. Use lem-sc-kernel-subgroup for the identity of H and
   lem-sfb-normal-subgroup-representation-kernel to obtain a faithful representation.
   Restrict it to G. The hypothesis diagonalizes s in this representation, and
   lem-sfb-rational-representation-semisimple-point diagonalizes its image in every
   representation of G. Handle the zero-dimensional representation by the empty sum.
5. In an eigenbasis for s, every off-diagonal coefficient vanishes at each s^n. Density
   and lem-wf-affine-nullstellensatz-vanishing on the reduced finite-type coordinate
   algebra make these coefficients zero. Evaluation on any algebra, including a
   nonreduced algebra, therefore gives diagonal matrices with invertible entries.
6. The eigenlines are invariant simple subspaces over every algebra and their internal
   direct sum is the entire representation. This is linear reductivity as stated. -/
theorem semisimple_cyclic_closure_linearlyReductive
    {k : Type u} [Field k] [IsAlgClosed k]
    (H : Over (Spec (.of k))) [GrpObj H] [IsAffine H.left]
    [LocallyOfFiniteType H.hom] [QuasiCompact H.hom]
    (s : StandardGroupSchemes.affine k k ⟶ H) (hs : IsSemisimpleGroupSchemePoint H s)
    (G : Over (Spec (.of k))) (j : G ⟶ H)
    [IsClosedImmersion j.left] [IsReduced G.left]
    (hG : Set.range j.left =
      closure (Set.range (fun n : ℤ ↦ (s ^ n).left (IsLocalRing.closedPoint k)))) :
    ∃ (_ : GrpObj G), IsClosedSubgroupScheme j ∧ Smooth G.hom ∧
      IsLinearlyReductiveGroupScheme G ∧
      ∃ t : StandardGroupSchemes.affine k k ⟶ G, t ≫ j = s ∧
        DenseRange (fun n : ℤ ↦ (t ^ n).left (IsLocalRing.closedPoint k)) := by
  sorry

end AlgebraicGeometry
