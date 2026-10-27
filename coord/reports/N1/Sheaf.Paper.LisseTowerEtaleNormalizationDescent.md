## What changed

Replaced the sole hole in `Sheaf.Paper.LisseTowerEtaleNormalizationDescent` with an
explicit lift of each actual semilinear transition. The proof uses the existing
`ProEtale.bijective_comparisonUpperStar_mapDerivedCategory_map`, the fixed-realization
equivalence, and preservation of cohomological vanishing by exact scalar restriction.
It transports the actual transition through the supplied level comparisons, takes its
etale preimage, proves the descent equation by cancellation, and assembles every field
of the original record. The theorem signature and all existing definitions are unchanged.

Added `EtaleNormalizationCoherence` with a complete proof for arbitrary coefficient
rings and arbitrary arrows. The source library's ordinary coefficient composition law
and exact-localization square pasting prove exactly the coherence required by the
record. This argument requires no scalar-extension functor or universality assumption.

Added `LisseTowerScalarRestriction` and `LisseTowerLocalizedRealization` for two genuine
remaining steps. The first concerns one section-normalized consecutive scalar square,
reflection of the actual normalized transition on etale sources, and universality of
constant algebraic arrows on those sources. The second transports already supplied
arrows and their proved descent equations to local model comparisons. Neither restates
the item: the first constructs no descended arrow or localized model; the second
assumes the arrows and equations and proves no universality. The main module performs
the arrow lift, proves its equation, proves all coherence, and assembles the record.

Every new functor and data definition has a concrete body. In particular,
`lisseTowerLocalRealization` is exact fixed-coefficient inverse image along `f.left`
followed by the existing fixed realization at `W.hom ≫ g`; it is not chosen from an
existence theorem. The scalar square is uniquely determined by its underlying abelian
sheaf normalization. The normalization predicate is factored through a general
categorical definition to avoid expensive reduction of concrete adic ring expressions.

The packet changes only the item module, three new modules, their three new nodes and
the item's proof records. No source-library file, existing shared definition, statement,
instance, attribute, public import, target, or unit realization is changed.

Validation: `lcompile.py --all` compiled all four delivered files in import order with
no errors or warnings. Their times were 9.2, 17.3, 15.9 and 11.9 seconds, respectively.
The original theorem signature is unchanged verbatim. Every node's proof dependencies
match the union of its proof uses.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Scheme.lisse_tower_etale_normalization_descent`
(node `lem-weil-pbc-lisse-tower-etale-normalization-descent`). Its proof is complete
relative to the two remaining statements below. The item itself has zero holes.

Also proved `AlgebraicGeometry.Scheme.etaleNormalization_coherence`
(node `lem-weil-pbc-etale-normalization-coherence`), including the exact inverse
restriction-compositor equation without a universality assumption. Its module has zero
holes. The new ordinary-realization, forgetful and derived-square definitions and
instances in `LisseTowerScalarRestriction` are all constructed and proved.

Added exactly two holes, each the entire body of a named public theorem in its own
new module:

- `AlgebraicGeometry.Scheme.lisseTower_scalar_restriction`
  (`lem-weil-pbc-lisse-tower-scalar-restriction`).
- `AlgebraicGeometry.Scheme.lisseTower_localized_realization`
  (`lem-weil-pbc-lisse-tower-localized-realization`).

Thus this is a decomposition: one original hole closed, two lower holes added, net
minus one closed hole in this packet before closure accounting. It is not reported as
a proof without new obligations. Each remaining theorem has its source, complete proof
in words and a matching DAG node. There are no holes inside definitions or private
helpers. The zero ring, zero complexes and empty bases are covered; no finite
Tor-amplitude or local-constancy hypothesis was added.

## No longer needed

Removed the item's two original direct proof imports:

- `Sheaf.AlgebraicGeometry.CompactSupportComparisonUnit`: the existing source-library
  bounded-below full-faithfulness theorem gives exactly the needed morphism bijection.
- `Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence`: the main proof delegates
  the localized model comparisons to their precise separate statement; it does not
  itself invoke the whole coherence package.

The latter node (`lem-weil-pbc-comparison-pullback`) remains a dependency of the new
localized-comparison node. The constant quotient scalar comparison and constant
restricted tower nodes likewise remain needed through the concrete data and new
coefficient/localization steps. The site-comparison node is still used through the
source-library full-faithfulness API. No whole existing module or node is claimed
unreachable, and no declaration or module is withdrawn. The blueprint unit's own
statement and realized proof steps are retained.

## Where the brief, the DAG or earlier work was wrong

The existing statement survives the edge cases considered. No false statement or
incorrect definition was found. The previous proof plan did not give a Lean-level
coefficient-square interface from which an actual arrow could be lifted. The new
ordinary square, its exact localization and the supplied descent equation make that
step explicit. The independent coherence theorem removes restriction coherence from
the coefficient obligation entirely.

The current source graph forbids importing
`Sheaf.AlgebraicGeometry.DerivedScalarExtensionLocalSystems` here: its dependencies
run through scalar extension and the completed-coefficient finiteness modules back to
this descent item. Published artifacts had permitted a proof using it to compile, but
the delivery's source-cycle check correctly rejected that route. The final packet does
not import or cite that cyclic dependency. Source universality remains in the single
coefficient lemma, whose proof plan uses the direct flat-resolution tensor calculation.
The generic coherence proof uses only the ordinary coefficient comparison and its
exact localization; the current server import graph permits that source module.

The whole original obligation is not moved to another name. The main theorem now
constructs its arrows by full faithfulness and proves their equation, and the coherence
part is proved directly from existing ordinary infrastructure. The remaining two nodes
are strict parts of the coefficient and localization argument. All changes are below
the unit level. No change record or forced adaptation is needed.

## New nodes

`lem-weil-pbc-lisse-tower-scalar-restriction` records the ordinary fixed-realization
scalar square normalized on underlying abelian sheaves, its specified exact derived
square and the two source-universality assertions. Its theorem has one hole.

`lem-weil-pbc-etale-normalization-coherence` records the independent inverse-compositor
coherence equation for arbitrary coefficient arrows. Its theorem is proved from the
existing ordinary and exact-localization coefficient-pasting APIs.

`lem-weil-pbc-lisse-tower-localized-realization` records the explicit local realization
and its model, actual and coefficient comparisons with both normalization equations,
assuming the already descended arrows and their equations. Its theorem has one hole.
All three nodes inherit the item's chapter and unit, identify the amplification
finite-level descent step, record the Mathlib searches, and have matching Lean records.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.EtaleNormalizationCoherence": "be858dcea213625a32cb9a9dc228375a351ac273", "Sheaf.Paper.LisseTowerEtaleNormalizationDescent": "964ee6f37d157bc8c8e4bdec6183b90ea8a2363a", "Sheaf.Paper.LisseTowerLocalizedRealization": "a520a2aa6d8c87c2ed9dea579d9b10701533ef72", "Sheaf.Paper.LisseTowerScalarRestriction": "7e30777a7b9f93c0c1a8798c6ecf274a3bb46eed"}, "results": {"Sheaf.Paper.LisseTowerEtaleDescent": {"hash": "565c65b15f193fb09becdfa4c04724697d548e15", "status": "OK"}}, "seconds": 17, "time": "2026-10-28T04:30:38+0800", "transitive": 0, "version": 1}
```

## Second reading by N1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
