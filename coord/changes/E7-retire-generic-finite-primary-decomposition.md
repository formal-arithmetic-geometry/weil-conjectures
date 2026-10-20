# AlgebraicGeometry.Scheme.exists_finite_primary_sheaf_decomposition

## Reason

Retire the duplicate explicitly listed in `coord/retire-items.tsv` under the
2026-10-20 retirement decision. The item has zero sorry holes. The adopted
upstream module already proves the same finite-primary decomposition, with
identical universes, stalk, finite and primary conditions, and sum identity.
Its signature omits the torsion hypothesis that the old proof ignored.
Both consumers keep their complete original signatures and proof arguments;
only the proof import and application of the existing upstream theorem change.
An anonymous `have _ := hM` retains the now-unused hypothesis without a lint warning.
No source-library file is modified and no target's meaning changes.

## Old

The withdrawn Sheaf module supplied this signature:

```lean
theorem exists_finite_primary_sheaf_decomposition
    (K : Type u) [Field K]
    (M : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u + 1})
    (hM : M.IsTorsion)
    (hfinite : Finite (((pointSmallEtale
      (Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K))))).sheafFiber
        (A := AddCommGrpCat.{u + 1})).obj M)) :
    ∃ (r : ℕ) (p : Fin r → ℕ)
      (N : Fin r → Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u + 1}),
      (∀ i, (p i).Prime) ∧
      (∀ i, Finite (((pointSmallEtale
        (Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K))))).sheafFiber
          (A := AddCommGrpCat.{u + 1})).obj (N i))) ∧
      (∀ i, IsPGroup (p i) (Multiplicative (((pointSmallEtale
        (Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K))))).sheafFiber
          (A := AddCommGrpCat.{u + 1})).obj (N i)))) ∧
      ∃ (a : ∀ i, M ⟶ N i) (b : ∀ i, N i ⟶ M),
        ∑ i, a i ≫ b i = 𝟙 M
```

The two direct callers imported the Sheaf module and supplied `hM` between
`M` and `hfinite` in the theorem application.

## New

Withdraw `lean/Sheaf/AlgebraicGeometry/Curve/GenericFinitePrimaryDecomposition.lean`
using `deleted.txt`. Retain the existing upstream theorem verbatim:

```lean
theorem exists_finite_primary_sheaf_decomposition
    (K : Type u) [Field K]
    (M : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u + 1})
    (hfinite : Finite (((pointSmallEtale
      (Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K))))).sheafFiber
        (A := AddCommGrpCat.{u + 1})).obj M)) :
    ∃ (r : ℕ) (p : Fin r → ℕ)
      (N : Fin r → Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u + 1}),
      (∀ i, (p i).Prime) ∧
      (∀ i, Finite (((pointSmallEtale
        (Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K))))).sheafFiber
          (A := AddCommGrpCat.{u + 1})).obj (N i))) ∧
      (∀ i, IsPGroup (p i) (Multiplicative (((pointSmallEtale
        (Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K))))).sheafFiber
          (A := AddCommGrpCat.{u + 1})).obj (N i)))) ∧
      ∃ (a : ∀ i, M ⟶ N i) (b : ∀ i, N i ⟶ M),
        ∑ i, a i ≫ b i = 𝟙 M
```

The two direct consumers instead import
`WeilConjectures.AlgebraicGeometry.Curve.GenericFinitePrimaryDecomposition`
and apply its theorem to `K`, `M`, and `hfinite`. The DAG attachment points to
that existing declaration and records its actual signature. The mathematical
node statement, dependencies and unit route are retained: the upstream proof
uses the same stalk/representation equivalence, finite representation primary
decomposition, and transport through the additive equivalence. The upstream
construction uses `SeparableClosure K` and the canonical equivalence instead
of choosing the equivalence from the Sheaf classification theorem.

## Users

`tools/downstream.py` reports these 13 downstream modules and exactly two
external declaration users. Both direct users are unclaimed. Remaining rows
are indirect importers, with their current holder recorded when present.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteCoarseTraceFiltrationData | unclaimed | Migrate proof import, omit the redundant torsion argument, retain hM and all signatures. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecond | unclaimed | No source edit; existing signatures and mathematical dependencies unchanged. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecondReduction | unclaimed | No source edit; existing signatures and mathematical dependencies unchanged. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteTraceFiltrationData | unclaimed | No source edit; existing signatures and mathematical dependencies unchanged. |
| Sheaf.AlgebraicGeometry.EtaleModuleAffineBound | unclaimed | No source edit; existing signatures and mathematical dependencies unchanged. |
| Sheaf.AlgebraicGeometry.FiniteClassicalUnboundedComparison | unclaimed | No source edit; existing signatures and mathematical dependencies unchanged. |
| Sheaf.AlgebraicGeometry.ProEtaleClassicalBounds | unclaimed | No source edit; existing signatures and mathematical dependencies unchanged. |
| Sheaf.AlgebraicGeometry.Sites.FiniteFieldTorsionCohomologicalDimension | unclaimed | Migrate proof import, omit the redundant torsion argument, retain hM and all signatures. |
| Sheaf.AlgebraicGeometry.UnboundedDirectImageComparison | unclaimed | No source edit; existing signatures and mathematical dependencies unchanged. |
| Sheaf.AlgebraicGeometry.UnboundedDirectImageTruncationStability | unclaimed | No source edit; existing signatures and mathematical dependencies unchanged. |
| Sheaf.AlgebraicGeometry.UnboundedSiteComparison | unclaimed | No source edit; existing signatures and mathematical dependencies unchanged. |
| Sheaf.Paper.FiniteRingCompactSupportProjection | unclaimed | No source edit; existing signatures and mathematical dependencies unchanged. |
| Sheaf.SixFunctors.ClassicalModuleAffineEvaluationBound | unclaimed | No source edit; existing signatures and mathematical dependencies unchanged. |

Both adapted consumers compile remotely, without warnings. A source import-closure
scan checked all 13 downstream modules against the delivery overlay: none imports
the withdrawn module transitively, and none gains a new paired Sheaf/upstream
module in its environment. Both consumer declaration inventories and signatures
are unchanged.

The item itself is the third declaration-name occurrence reported by
`downstream.py --uses`; it is withdrawn. Its only declaration is retained by
the upstream module. Parent DAG references continue to reach the same node,
now attached to that retained upstream declaration. This is a duplicate
retirement, not deletion of the primary decomposition argument.

## Status

landed 20261020T221138-L-4148952 2026-10-20 (merge of deliver/E7/Sheaf.AlgebraicGeometry.Curve.GenericFinitePrimaryDecomposition)
