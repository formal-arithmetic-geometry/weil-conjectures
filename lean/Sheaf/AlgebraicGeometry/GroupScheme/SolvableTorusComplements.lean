module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.Defs
public import Sheaf.AlgebraicGeometry.GroupScheme.Semisimple
public import Sheaf.AlgebraicGeometry.SolvableGroupStructure
public import Sheaf.AlgebraicGeometry.ToriMultiplicativeType
public import Sheaf.AlgebraicGeometry.ReductiveTorusCentralizerTerminology
public import Sheaf.AlgebraicGeometry.GroupScheme.AffineNormalQuotientGeometry
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.Topology.Connected.Basic

import Sheaf.AlgebraicGeometry.GroupScheme.HomomorphismFactorization

/-!
# Maximal tori complement the unipotent kernel of a solvable group

Source: Milne, Algebraic Groups (2017), Theorems 16.26(a), 16.27(b), pp.332--333,
and Theorem 16.33(d), pp.335--336 (blueprint: lem-sfb-solvable-torus-complements).

The conclusion concerns the given quotient homomorphism restricted to the given
maximal torus, as an isomorphism of group schemes over the ground field.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- Every maximal torus of a smooth connected solvable affine algebraic group maps
isomorphically to its torus quotient by a smooth connected normal unipotent subgroup.

Source: Milne, Algebraic Groups (2017), Theorems 16.26(a), 16.27(b), pp.332--333,
and Theorem 16.33(d), pp.335--336 (blueprint: lem-sfb-solvable-torus-complements).

Proof plan, following the five steps of the DAG node:
1. Apply lem-sfb-lie-kolchin-triangular-embedding to H. For its triangular image put
   V = H intersect U_n. By lem-sfb-triangular-diagonal-kernel the diagonal quotient
   D_0 = H/V embeds in a split torus and has a group-scheme section s_0.
2. By lem-sfb-unipotent-to-multiplicative-trivial the restrictions U to D_0 and V
   to D are trivial. The scheme-theoretic kernel clause of
   lem-sfb-affine-normal-quotient-geometry gives U = V on all algebras. The sheaf
   quotient universal property identifies D_0 with D and transports s_0 to a
   section s of q.
3. The intersection K = T intersect U is unipotent and a subgroup of a torus, so
   lem-sfb-unipotent-to-multiplicative-trivial makes K trivial as a group scheme.
   By lem-sfb-algebraic-group-homomorphism-factorization the map T to D therefore
   identifies T with a closed torus S in D: the quotient T/1 is T itself.
4. Form P = H times_D S. By lem-sfb-affine-normal-quotient-geometry its quotient
   by U is S, and P is smooth and connected because U and S are. The inclusion
   of T and the restriction of s give two sections of P to S. Apply
   lem-sfb-triangular-quotient-section-conjugacy to obtain u in U(F) with
   T = Int(u)s(S), hence T is contained in Int(u)s(D).
5. The homomorphism b = Int(u) composed with s satisfies q b = id_D, since q(u)=1.
   Its kernel is trivial. By lem-sfb-algebraic-group-homomorphism-factorization
   its image T' is a closed torus isomorphic to D. It contains T, so maximality
   gives T = T'. The identities q b = id_D and b q = id_T' show that the actual
   restriction of q to T is an isomorphism. -/
theorem solvable_torus_complements {F : Type u} [Field F] [IsAlgClosed F]
    (H U D : Grp (Over (Spec (.of F))))
    (hH : SolvableGroupStructure.IsAlgebraic H)
    (hU : SolvableGroupStructure.IsAlgebraic U)
    (hD : SolvableGroupStructure.IsAlgebraic D)
    [Smooth H.X.hom] [ConnectedSpace H.X.left]
    (hsolv : IsSolvableGroupScheme H.X)
    (iU : U ⟶ H) [IsClosedSubgroupScheme iU.hom.hom]
    [IsNormalSubgroupScheme iU.hom.hom] [ConnectedSpace U.X.left]
    (hunip : SolvableGroupStructure.IsUnipotent U)
    (q : H ⟶ D) (hquot : IsFppfGroupQuotient iU q)
    (htorus : MultiplicativeType.IsTorus D)
    (T : Grp (Over (Spec (.of F))))
    (hT : SolvableGroupStructure.IsAlgebraic T)
    (iT : T ⟶ H) (hmax : ReductiveTorusCentralizer.IsMaximalTorus iT) :
    IsIso (iT ≫ q) := by
  sorry

end AlgebraicGeometry
