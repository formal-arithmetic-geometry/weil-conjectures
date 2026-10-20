# AlgebraicGeometry.GeneralLinearGroup.mixedCommutator_tangent

## Reason

The assigned module is marked `retire` in coord/queue.tsv. Its only importer is the
unclaimed Sheaf.AlgebraicGeometry.MatrixSubgroupLieBracket, which has no importers in either
library root. Both Sheaf modules are redundant with completed adopted source modules.
The earlier retirement audit kept them because a consumer was in a pending landing;
the current import graph has no consumers of the parent. Withdraw both Sheaf files together,
so nothing imports the withdrawn item. No declaration, signature, attribute, import, or body
under lean/WeilConjectures is changed.

The source counterpart of mixedCommutator_tangent provides the base changes, mixed matrix
identity, and descended tangent point, omitting the Sheaf version's separate four-factor and
injectivity conjuncts. The source counterpart of
exists_tangentMatrixSubmodule_differential proves the consumer's conclusion over every field,
without its IsAlgClosed and CharZero assumptions. The withdrawn Sheaf consumer contains no
proof using the additional conjuncts. It is not needed by any further module.

## Old

Sheaf.AlgebraicGeometry.MixedCommutatorTangent:

```lean
theorem mixedCommutator_tangent
    {k n : Type u} {V : Type v} [Field k] [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] [Fintype n] [DecidableEq n] (b : Module.Basis n k V)
    (G : Over (Spec (.of k))) [GrpObj G]
    (i : G ⟶ AlgebraicGeometry.GeneralLinearGroup n k) [IsClosedSubgroupScheme i]
    (X Y : Module.End k V) (x y : AlgebraicGeometry.points G (DualNumber k))
    (hx : homMulEquiv n k (DualNumber k) (x ≫ i) = dualUnit (LinearMap.toMatrix b b X))
    (hy : homMulEquiv n k (DualNumber k) (y ≫ i) = dualUnit (LinearMap.toMatrix b b Y)) :
    ∃ p q : AlgebraicGeometry.points G (DualNumber (DualNumber k)),
      homMulEquiv n k (DualNumber (DualNumber k)) (p ≫ i) =
        Matrix.GeneralLinearGroup.map (inlHom (DualNumber k) (DualNumber k))
          (dualUnit (LinearMap.toMatrix b b X)) ∧
      homMulEquiv n k (DualNumber (DualNumber k)) (q ≫ i) =
        Matrix.GeneralLinearGroup.map
          (DualNumber.mapRingHom (inlHom k k)) (dualUnit (LinearMap.toMatrix b b Y)) ∧
      (homMulEquiv n k (DualNumber (DualNumber k)) ((p * q * p⁻¹ * q⁻¹) ≫ i) :
        Matrix n n (DualNumber (DualNumber k))) =
        (1 + (LinearMap.toMatrix b b X).map (fun a ↦ inl (inr a))) *
        (1 + (LinearMap.toMatrix b b Y).map (fun a ↦ inr (inl a))) *
        (1 - (LinearMap.toMatrix b b X).map (fun a ↦ inl (inr a))) *
        (1 - (LinearMap.toMatrix b b Y).map (fun a ↦ inr (inl a))) ∧
      (homMulEquiv n k (DualNumber (DualNumber k)) ((p * q * p⁻¹ * q⁻¹) ≫ i) :
        Matrix n n (DualNumber (DualNumber k))) =
        1 + (LinearMap.toMatrix b b (X * Y - Y * X)).map (fun a ↦ inr (inr a)) ∧
      Function.Injective (DualNumber.mulRingHom (R := k)) ∧
      ∃ z : AlgebraicGeometry.points G (DualNumber k),
        homMulEquiv n k (DualNumber k) (z ≫ i) =
          dualUnit (LinearMap.toMatrix b b (X * Y - Y * X))
```

Sheaf.AlgebraicGeometry.MatrixSubgroupLieBracket:

```lean
theorem exists_tangentMatrixSubmodule_differential
    {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]
    {n m : Type u} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
    (I : Ideal (Matrix.GeneralLinearGroup.CoordinateRing n k)) [I.IsHopfIdeal k] :
    ∃ S : Submodule k (Matrix n n k),
      (∀ X : Matrix n n k, X ∈ S ↔
        dualUnit X ∈ Matrix.GeneralLinearGroup.zeroLocus I (DualNumber k)) ∧
      (∀ X ∈ S, ∀ Y ∈ S, X * Y - Y * X ∈ S) ∧
      (∀ (r : RationalHom (subgroupScheme I) m) [IsMonHom r],
        ∃ d : S →ₗ[k] Matrix m m k,
          (∀ (X : S) (g : AlgebraicGeometry.points (subgroupScheme I) (DualNumber k)),
            homMulEquiv n k (DualNumber k) (g ≫ subgroupSchemeι I) = dualUnit X.val →
              r.points (DualNumber k) g = dualUnit (d X)) ∧
          (∀ X Y Z : S, Z.val = X.val * Y.val - Y.val * X.val →
            d Z = d X * d Y - d Y * d X))
```

Both declarations had one sorry. Their adopted source counterparts remain verbatim.

## New

Withdraw lean/Sheaf/AlgebraicGeometry/MixedCommutatorTangent.lean and
lean/Sheaf/AlgebraicGeometry/MatrixSubgroupLieBracket.lean using deleted.txt.
The delivery process leaves empty modules in their place. Repoint the two DAG lean attachments
to the upstream twins; retain both DAG nodes, their mathematical statements and their original
proof plans. This claims no equivalence between the stronger old mixed-commutator
conjunction and the smaller source theorem signature.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.MixedCommutatorTangent | G6 | Assigned module withdrawn. |
| Sheaf.AlgebraicGeometry.MatrixSubgroupLieBracket | unclaimed | Sole importer withdrawn together; has no importers itself. |

`tools/downstream.py --uses` lists no users of either declaration. Direct import search
finds only the second row importing the first. No target statement or definition changes.

## Status

landed 20261020T154615-L-3136321 2026-10-20 (merge of deliver/G6/Sheaf.AlgebraicGeometry.MixedCommutatorTangent)
