# AlgebraicGeometry.Scheme.IsCoefficientConstructibleEtaleModule

## Reason

Restore the quarantined module assigned in coord/rework.tsv. Its definition refers to the
retired `LocallyClosedStratification`; the current dependency node
`def-constructible-stratification` records `Scheme.FiniteLocallyClosedStratification`.
Import that existing module publicly and use its recorded declaration. The finite index,
locally closed subsets, covering and disjointness, realizing schemes and immersion maps
are retained; constructibility remains an explicit conjunct. This is the same affine-local
condition of Stacks 03RW(3), not a change in the mathematical statement. The bounded derived
condition and full subcategories continue to use this predicate. No target meaning changes.

## Old

From quarantine/Sheaf/AlgebraicGeometry/CoefficientConstructibleEtaleModules.lean:

```lean
def IsCoefficientConstructibleEtaleModule (X : Scheme.{u})
    (A : Type (max v (u + 1))) [CommRing A] [IsNoetherianRing A]
    (F : CategoryTheory.ConstantCompletion.Mod
      (CategoryTheory.ConstantCompletion.constant (smallModelComparisonEtaleTopology.{u, v} X)
        A)) : Prop :=
  ∀ U : X.Opens, IsAffineOpen U →
    ∃ S : LocallyClosedStratification U.toScheme,
      (∀ i : Fin S.n, Topology.IsConstructible (S.stratum i)) ∧
      ∀ i : Fin S.n, IsCoefficientModelLocallyConstantFinite
        (smallModelComparisonEtaleTopology.{u, v} (S.domain i)) A
        ((coefficientEtaleFixedPullback.{u, v} (S.immersion i ≫ U.ι) A).obj
          ((coefficientModelFixedScalars _ A).obj F))
```

## New

Add `public import Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification` and replace
the definition body by:

```lean
def IsCoefficientConstructibleEtaleModule (X : Scheme.{u})
    (A : Type (max v (u + 1))) [CommRing A] [IsNoetherianRing A]
    (F : CategoryTheory.ConstantCompletion.Mod
      (CategoryTheory.ConstantCompletion.constant (smallModelComparisonEtaleTopology.{u, v} X)
        A)) : Prop :=
  ∀ U : X.Opens, IsAffineOpen U →
    ∃ S : FiniteLocallyClosedStratification U.toScheme,
      (∀ i : Fin S.n, Topology.IsConstructible (S.stratum i)) ∧
      ∀ i : Fin S.n, IsCoefficientModelLocallyConstantFinite
        (smallModelComparisonEtaleTopology.{u, v} (S.domain i)) A
        ((coefficientEtaleFixedPullback.{u, v} (S.immersion i ≫ U.ι) A).obj
          ((coefficientModelFixedScalars _ A).obj F))
```

All other declarations, imports, docstrings and proofs in the archived item are retained.
No declaration is removed. In particular the existing continuity proof remains complete.

## Users

The item is absent from the current library; the source scan finds no live importers or
external references to its declarations. The archived consumers below are preserved in
quarantine and not withdrawn by this delivery. They continue to use the same coefficient
categories, functors and predicates. No live module requires forced adaptation.
The restored module compiles against the published build in 2.5 seconds.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.CoefficientConstructibleEtaleModules | C1 | Restored with the recorded stratification; bounded predicate and both full categories inherit the repaired body. |
| Sheaf.CategoryTheory.CoefficientFiniteLocalSystemsPullback | unclaimed, quarantined | Uses only the unchanged finite-local-system predicate; its unchanged archived source is checked against this restoration. |
| Sheaf.AlgebraicGeometry.CoefficientAffineConstructibleProEtaleModules | unclaimed, quarantined | Imports the unchanged fixed-scalar API. Its own retired LocallyClosedStratification reference and quarantine dependency failures predate this repair. |
| Sheaf.AlgebraicGeometry.ConstructibleProEtaleComparison | unclaimed, quarantined | Uses the same constructible full subcategories and unchanged functors. Its own retired stratification reference and missing dependencies predate this repair. |
| Sheaf.Paper.AdicConstructibleFiniteReductions | unclaimed, quarantined | Uses the unchanged bounded-constructible predicate with the same meaning. Its quarantined dependencies remain separate rework items. |
| Sheaf.AlgebraicGeometry.NoetherianGlobalConstructibility | unclaimed, quarantined | Indirect consumer; its own retired stratification references and missing dependencies predate this repair. Its restoration must use the recorded finite locally closed interface, as this predicate now does. |

The definition node already lists `def-constructible-stratification` in stmt_deps. Its
Lean attachment, declaration list and signature remain unchanged; the note now records
this restoration. There is no change to a unit route or proof dependency.

Edge cases: the structure permits n = 0, hence the empty scheme is not excluded; all
indices remain Fin S.n; infinite finitely generated modules such as Z over Z remain
allowed; the zero ring and zero module remain allowed. Constructibility is still tested
on every affine open rather than on one global stratification. The cohomology condition
still uses one finite interval for all integer degrees and retains all ambient morphisms.

## Status

landed 20261020T221059-L-4141681 2026-10-20 (merge of deliver/C1/Sheaf.AlgebraicGeometry.CoefficientConstructibleEtaleModules)
