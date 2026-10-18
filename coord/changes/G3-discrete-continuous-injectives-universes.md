# Rep.discreteContinuousRep_functorialInjectiveEmbeddings

## Reason

The independent carrier universe `w` in the original signature need not contain the
profinite group. The existing general embedding theorem instead uses `max u v w`.
Compiling the direct specialization at the old signature gives an application type
mismatch between functors on `DiscreteContinuousRep.{u,v,max u v w}` and
`DiscreteContinuousRep.{u,v,w}`. This is a real size issue, not merely elaboration.

To see the obstruction, take A = F_p and G the product of copies of the finite
additive group F_p indexed by a set K too large for the carrier universe. G is
profinite. If an injective object I contained the trivial one-dimensional module,
let x be the nonzero invariant image of 1. For each coordinate character chi_i,
the two-dimensional representation with action
`g(e1) = e1`, `g(e2) = e2 + chi_i(g)e1` has open stabilizers. Extend the map
`e1 ↦ x` from its trivial submodule into I by injectivity. The resulting image y_i
of e2 satisfies `(g - 1)y_i = chi_i(g)x`. Distinct coordinate characters force
distinct y_i. This injects K into I, contrary to its prescribed small carrier.
Thus even enough injectives at the old independent universe can fail.

Use the common carrier universe `max u v w`, just as the already reviewed general
Tag 04JF embedding theorem does. The finite-ring and profinite-group hypotheses,
category definition, morphisms, naturality, monicity, and injectivity clauses stay
unchanged. This repairs the Lean encoding of the source's category in a universe
containing R and G. It does not prove the stronger original small-universe claim.

Source read: literature/stacks-project/injectives.tex, Tag 04JF,
label lemma-G-modules, including the group-ring construction in its proof.
The mathematical DAG statement needs no edit; its Lean attachment records the
corrected carrier universe. No target signature or definition changes.

## Old

```lean
theorem discreteContinuousRep_functorialInjectiveEmbeddings
    (A : Type u) [Ring A] [Finite A] (G : Type v) [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G] :
    (∃ (J : DiscreteContinuousRep.{u, v, w} A G ⥤
          DiscreteContinuousRep.{u, v, w} A G)
       (j : 𝟭 (DiscreteContinuousRep.{u, v, w} A G) ⟶ J),
       ∀ M, Mono (j.app M) ∧ Injective (J.obj M)) ∧
      EnoughInjectives (DiscreteContinuousRep.{u, v, w} A G)
```

## New

```lean
theorem discreteContinuousRep_functorialInjectiveEmbeddings
    (A : Type u) [Ring A] [Finite A] (G : Type v) [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G] :
    (∃ (J : DiscreteContinuousRep.{u, v, max u v w} A G ⥤
          DiscreteContinuousRep.{u, v, max u v w} A G)
       (j : 𝟭 (DiscreteContinuousRep.{u, v, max u v w} A G) ⟶ J),
       ∀ M, Mono (j.app M) ∧ Injective (J.obj M)) ∧
      EnoughInjectives (DiscreteContinuousRep.{u, v, max u v w} A G)
```

## Users

`python3 tools/downstream.py Sheaf.RepresentationTheory.DiscreteContinuousInjectives
--uses discreteContinuousRep_functorialInjectiveEmbeddings` lists the eleven
transitive importers below. Both that use search and a repository-wide `rg` find
no applications of the changed theorem outside the item. Its sole direct importer
is DiscreteModulesAbelian; it compiles unchanged against the repaired module.
All public imports remain identical, so the other importers retain their available
names and instances. No adaptation is necessary and no consumer statement changes.
The local shared claim records show these consumers as unclaimed.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.FieldDiscreteModules | unclaimed | Import dependency only; no application or adaptation. |
| Sheaf.CategoryTheory.DiscreteModulesAbelian | unclaimed | Import dependency only; no application or adaptation. |
| Sheaf.RepresentationTheory.CoinducedContinuousAcyclic | unclaimed | Import dependency only; no application or adaptation. |
| Sheaf.RepresentationTheory.CoinducedDiscreteEmbedding | unclaimed | Import dependency only; no application or adaptation. |
| Sheaf.RepresentationTheory.CoinducedHomotopyContinuous | unclaimed | Import dependency only; no application or adaptation. |
| Sheaf.RepresentationTheory.CoinducedHomotopyIdentity | unclaimed | Import dependency only; no application or adaptation. |
| Sheaf.RepresentationTheory.ContinuousCochainsDeltaFunctor | unclaimed | Import dependency only; no application or adaptation. |
| Sheaf.RepresentationTheory.ContinuousCochainsDerivedInvariants | unclaimed | Import dependency only; no application or adaptation. |
| Sheaf.RepresentationTheory.ContinuousCochainsInvariantsZero | unclaimed | Import dependency only; no application or adaptation. |
| Sheaf.RepresentationTheory.ContinuousCochainsShortExact | unclaimed | Import dependency only; no application or adaptation. |
| Sheaf.RepresentationTheory.DiscreteContinuousCohomology | unclaimed | Import dependency only; no application or adaptation. |

The parent theorem `CategoryTheory.discreteModules_abelian` independently contains
the same small-universe enough-injectives overstatement. Its current proof is still
`by sorry`; it is not an application of this theorem and does not fail compilation
because of this repair. The maintainer should arrange a corresponding size repair
when that parent is proved. No parent declaration is changed in this delivery.

## Status

landed 20261018T062757-L-651262 2026-10-18 (merge of deliver/G3/Sheaf.RepresentationTheory.DiscreteContinuousInjectives)
