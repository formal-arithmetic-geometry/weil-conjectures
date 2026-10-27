## What changed

The item retains both public theorem signatures. The transpose proof now explicitly
calculates the adjunction units and direct-image exchange, restricts to the graph and
its complement, and applies `Scheme.Etale.graph_hom_ext`.
Private helpers express the graph section, its clopen projection, and the associated
transfer. The complement pullback is empty by its two projection equations and the
disjointness of the graph and its complement.

The six proof-helper propositions are private proved theorems with local
instance attributes. The scope-only change record is
`coord/changes/G5-graph-normalization-proof-scope.md`.

The two existing node records have their proof, proof dependencies and proof origin
updated to describe this calculation. No new nodes or public definitions were added.
The proof adds private imports of
`WeilConjectures.SixFunctors.BaseChange.Etale` and
`WeilConjectures.ConstructibleSheaf.EtaleMorphismDescent` for the restriction exchange
and inverse-image/restriction composition equations. The repaired item passed `lcompile.py` without warnings or errors in 47.7 seconds. The proof handles empty
graphs and zero coefficient rings without extra hypotheses.

## Proved and sorry left

Proved the one original hole,
`AlgebraicGeometry.Etale.compactSupportGraphSheafComparison_normalization_transpose`
(node `lem-asd-compact-support-graph-sheaf-normalization-transpose`).
`AlgebraicGeometry.Etale.compactSupportGraphSheafComparison_normalization` retains
its existing adjunction injectivity proof from the now-proved transpose theorem.

Holes closed: 1 of 1. Holes added: 0. Split off: 0. Holes left in the item: 0.
There are no new modules or remaining `sorry` declarations in this delivery.

## No longer needed

Removed four duplicate private helper declarations reported in the return:
`GraphNormalization.section_fst`, `GraphNormalization.section_snd`,
`GraphNormalization.comparison_app`, and `graph_transfer_composition`.
Mathlib supplies the projection equations directly; the two adjunction calculations
are local to their consuming proofs. No replacement helper declaration was added.

Removed proof imports:

- `WeilConjectures.AlgebraicGeometry.EtaleSheafClopenProduct`: the argument uses the
  already proved `Scheme.Etale.graph_hom_ext` from the existing finite-etale API.
- `WeilConjectures.AlgebraicGeometry.EtaleLowerShriekBaseChangeMap`: already publicly
  available through `EtaleCompactSupportNormalizationData`.
- `WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMap`: already available through
  the normalization data and its public graph-construction import.
- `Sheaf.AlgebraicGeometry.EtaleCompactificationGraphMap`: already publicly imported
  by `EtaleCompactSupportNormalizationData`.

The normalization node no longer separately needs
`lem-weil-pbc-etale-restriction-injectives`, `def-weil-pbc-adjunction-conjugate`,
`def-weil-pbc-etale-shriek-base-change-map`, `lem-weil-pbc-mate-pasting`, or
`lem-weil-pbc-etale-sheaf-clopen-product`: its proof applies the transpose theorem.
The transpose calculation still uses the first three. It proves the needed unit
calculation directly from `leftAdjointUniq` and its unit law, so does not use
`lem-weil-pbc-mate-pasting`. It uses the source graph gluing API rather than
`lem-weil-pbc-etale-sheaf-clopen-product`. These are dependency removals for this
proof only; no source declarations or modules are withdrawn. Other existing
consumers still import the clopen-product module, so no global module pruning is
claimed.

## Where the brief, the DAG or earlier work was wrong

The return at head `322e42761b2` flagged four added declarations duplicating private
helpers in `EtaleCompactSupportGraphGeometricBaseChange`. All four have been removed:
`GraphNormalization.section_fst`, `GraphNormalization.section_snd`,
`GraphNormalization.comparison_app`, and `graph_transfer_composition`.
The projection equations now use Mathlib's `pullback.lift_fst` and `pullback.lift_snd`
directly. The graph-map equation is a definitional calculation inside
`comparison_unit`; the transfer calculation uses Mathlib's
`Adjunction.unit_leftAdjointUniq_hom_app` inside `transfer_formula`.
A compiler probe importing the geometric-base-change module confirmed that its
private helper names are not accessible to importers. No helper is renamed or
redeclared, and no import of that large unrelated derived calculation is needed.
`tools/import_prune_check.py` now accepts the item against the current shared source.


The initial delivery check correctly rejected the preserved attempt because the
original transpose hole remained. The earlier missing-Mathlib compiler failure is
not present in the current compiler probes. The preserved attempt needed the
complement restriction argument and further explicit naturality and pullback
calculations; those are now written. No statement is disputed or weakened. Delivery preflight requested a scope change
record for added helper instances and elaboration commands; the record documents
those proof-only additions and the instances are explicitly local.

## Second reading by G5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
