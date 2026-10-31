/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ToriMultiplicativeType
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent
import WeilConjectures.AlgebraicGeometry.GeometricallyConnectedAlgebraicClosure
import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Connected
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.LinearAlgebra.FreeModule.PID

/-!
# Largest subtori of groups of multiplicative type

Source: Milne, Algebraic Groups (2017), Theorem 12.9(c), Definitions 12.14 and 12.17,
Theorem 12.23, Corollary 12.24 and Notation 12.29, printed pp.233--241
(blueprint: lem-sfb-multiplicative-type-largest-subtorus).

Equality of subgroup schemes is expressed independently of a choice of representative:
the pulled-back inclusion is again a largest subtorus. Thus it agrees, as a subobject,
with any largest subtorus chosen after scalar extension.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry
namespace MultiplicativeType

/-- Tori are smooth and connected; multiplicative-type groups have a largest subtorus
compatible with every field extension; closed subgroups remain of multiplicative type;
smooth connected groups of multiplicative type, and smooth connected closed subgroups
of tori, are tori. All the group schemes quantified here are affine and of finite type.
Source: Milne, Theorem 12.9(c), Definitions 12.14 and 12.17, Theorem 12.23,
Corollary 12.24 and Notation 12.29, pp.233--241
(blueprint: lem-sfb-multiplicative-type-largest-subtorus).

Proof:
1. After algebraic closure, compose the two closed immersions into a split torus;
coordinate-ring surjections compose and remain surjective after scalar extension.
This proves stability under closed subgroups.
2. A torus splits geometrically. The diagonalizable geometric criteria show that a
split torus is smooth and connected, including rank zero. Smoothness descends fpqc;
the algebraic-closure test gives geometric connectedness and hence connectedness.
Its character group is a finite-rank free abelian group, hence torsion-free.
3. A smooth connected multiplicative-type group has a rational identity, so the
rational-point criterion makes it geometrically connected. Smoothness survives base
change. For its geometric character group, connectedness permits only p-primary
torsion in characteristic p, while smoothness excludes that torsion; in characteristic
zero connectedness excludes all torsion. Finite generation and the finite-basis lemma
identify the character group with Z^d, so the group is a torus. Step 1 gives the special
case of closed subgroups of a torus.
4. For M = X*(D), its torsion subgroup A is Galois stable. The quotient M/A is finitely
generated and torsion-free: if n(m+A)=0, then nm is torsion, hence m is torsion. The
character antiequivalence turns M → M/A into a closed immersion of a torus into D.
The scalar-extension character identification and the equivalence over the algebraic
closure identify its geometric fibre with the split torus of the rank of M/A.
5. Any character map M → X*(S) for a subtorus S kills A, because X*(S) is torsion-free.
It factors through M/A; full faithfulness gives the factorization S → D^t → D.
6. For any extension K/k, an algebraic closure containing the original algebraic
closure shows D_K remains of multiplicative type. The character identification preserves
orders, A, and M/A. The base-changed inclusion has the same quotient character map.
Full faithfulness therefore identifies it with the largest subtorus of D_K, with
commuting inclusions. This covers inseparable and transcendental extensions too. -/
theorem multiplicativeType_largestSubtorus (k : Type u) [Field k] :
    (∀ (T : Grp (Over (Spec (.of k)))) [IsAffine T.X.left]
      [LocallyOfFiniteType T.X.hom] [QuasiCompact T.X.hom],
      IsTorus T → Smooth T.X.hom ∧ ConnectedSpace T.X.left) ∧
    (∀ (D : Grp (Over (Spec (.of k)))) [IsAffine D.X.left]
      [LocallyOfFiniteType D.X.hom] [QuasiCompact D.X.hom],
      IsMultiplicativeType D →
        ∃ (T : Grp (Over (Spec (.of k)))) (i : T ⟶ D),
          IsAffine T.X.left ∧ LocallyOfFiniteType T.X.hom ∧ QuasiCompact T.X.hom ∧
          IsLargestSubtorus i ∧
          ∀ (K : Type u) [Field K] [Algebra k K],
            IsLargestSubtorus ((baseChange (k := k) (K := K)).map i)) ∧
    (∀ (D H : Grp (Over (Spec (.of k)))) [IsAffine D.X.left] [IsAffine H.X.left]
      [LocallyOfFiniteType D.X.hom] [QuasiCompact D.X.hom]
      [LocallyOfFiniteType H.X.hom] [QuasiCompact H.X.hom] (j : H ⟶ D),
      IsClosedSubgroupScheme j.hom.hom → IsMultiplicativeType D →
        IsMultiplicativeType H) ∧
    (∀ (H : Grp (Over (Spec (.of k)))) [IsAffine H.X.left]
      [LocallyOfFiniteType H.X.hom] [QuasiCompact H.X.hom],
      IsMultiplicativeType H → Smooth H.X.hom → ConnectedSpace H.X.left → IsTorus H) ∧
    (∀ (T H : Grp (Over (Spec (.of k)))) [IsAffine T.X.left] [IsAffine H.X.left]
      [LocallyOfFiniteType T.X.hom] [QuasiCompact T.X.hom]
      [LocallyOfFiniteType H.X.hom] [QuasiCompact H.X.hom] (j : H ⟶ T),
      IsTorus T → IsClosedSubgroupScheme j.hom.hom → Smooth H.X.hom →
        ConnectedSpace H.X.left → IsTorus H) := by
  sorry

end MultiplicativeType
end AlgebraicGeometry
