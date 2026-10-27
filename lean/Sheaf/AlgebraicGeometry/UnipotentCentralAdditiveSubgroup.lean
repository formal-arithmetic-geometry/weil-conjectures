module

public import Sheaf.AlgebraicGeometry.SolvableGroupStructure
import Sheaf.AlgebraicGeometry.NilpotentConnectedCentralSeries
import Sheaf.AlgebraicGeometry.CharZeroCommutativeUnipotentVectorGroup
import Sheaf.AlgebraicGeometry.BoundedExponentReducedPKernel

/-! # A central additive subgroup of a nontrivial unipotent group

Source: Milne, Algebraic Groups (2017), Corollary 14.55 and its proof, printed p.297;
Proposition 14.32, first paragraph of the proof, printed p.289
(blueprint: lem-sfb-unipotent-central-additive-subgroup).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory
open scoped MonObj

namespace AlgebraicGeometry

/-- A nontrivial smooth connected affine unipotent group over a perfect field contains
 a smooth connected closed central subgroup isomorphic to the additive group.
Source: Milne, Algebraic Groups (2017), Corollary 14.55, printed p.297, and
Proposition 14.32 proof, printed p.289
(blueprint: lem-sfb-unipotent-central-additive-subgroup).

Proof:
1. Apply lem-sfb-geometric-unipotence-unitriangular-embedding to embed V in U_n.
Intersect V with the coordinate filtration of lem-sfb-unitriangular-coordinate-filtration.
Conjugation fixes the next coordinate quotient, so every commutator of V with a
filtration term belongs to the next term. This is a finite central series ending at 1.
2. Apply lem-sfb-nilpotent-connected-central-series. The last nontrivial term C of
its smooth connected series is central over every k-algebra, hence commutative.
Restrict the unitriangular embedding to C.
3. In characteristic zero, lem-sfb-char-zero-commutative-unipotent-vector-group gives
an isomorphism Ga^d -> C, with d positive since C is nontrivial.
4. In characteristic p, choose e >= 1 with p^e >= n. Every unitriangular matrix is
I+T with T^n = 0. Over every k-algebra, the binomial identity gives
(I+T)^(p^e) = I+T^(p^e) = I. Thus C is killed by p^e.
5. Apply lem-sfb-bounded-exponent-reduced-p-kernel to obtain a nontrivial smooth
connected commutative closed K in C killed by p. By
lem-sfb-perfect-exponent-p-vector-group, K is Ga^d with d positive.
6. In either characteristic, take the image of the first coordinate factor under
the vector-group isomorphism. The equations x_2 = ... = x_d = 0 show it is a closed
subgroup N, and the first coordinate map gives Ga -> N as a group-scheme isomorphism.
The affine line is smooth because its polynomial coordinate lifts freely, and connected
because its coordinate ring is a domain. These properties transport to N. Since N lies
in C, its points commute with all points of V over every commutative k-algebra. -/
theorem exists_central_additive_subgroup_of_unipotent
    {k : Type u} [Field k] [PerfectField k]
    (V : Grp (Over (Spec (.of k))))
    [IsAffine V.X.left] [LocallyOfFiniteType V.X.hom] [QuasiCompact V.X.hom]
    [Smooth V.X.hom] [ConnectedSpace V.X.left]
    (hunipotent : SolvableGroupStructure.IsUnipotent V)
    (hnontrivial : ¬ Nonempty (V ≅ Grp.trivial _)) :
    ∃ (N : Grp (Over (Spec (.of k)))) (i : N ⟶ V),
      IsClosedSubgroupScheme i.hom.hom ∧
      Smooth N.X.hom ∧ ConnectedSpace N.X.left ∧
      Nonempty (Grp.mk (StandardGroupSchemes.additive k) ≅ N) ∧
      ∀ (R : Type u) [CommRing R] [Algebra k R]
        (n : (Spec (.of R)).asOver (Spec (.of k)) ⟶ N.X)
        (v : (Spec (.of R)).asOver (Spec (.of k)) ⟶ V.X),
        (n ≫ i.hom.hom) * v = v * (n ≫ i.hom.hom) := by
  sorry

end AlgebraicGeometry
