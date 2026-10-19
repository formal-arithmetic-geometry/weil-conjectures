## What changed

Proved `AlgebraicGeometry.Scheme.affine_strict_local_ring_comparison` from the existing
geometric strict henselian local structure, affine-chart ind-etaleness and maximal-ideal
formula, and unique henselian lifting on etale stages. The chart structural-map and
geometric evaluation identities are proved directly from the defining cocones. Evaluation
lands in the fixed relative separable closure; its surjectivity follows from separability
and the separably closed residue field. The inverse comparison maps preserve the specified
base and residue maps, and their composites are identities by unique lifting.

Added the proved module `Sheaf.RingTheory.StrictHenselizationPresentationProperties`.
Its theorem `Algebra.StrictHenselizationPresentation.local_properties` transports the
specified presentation, including its residue map, to the existing residue-triple colimit.
Private helpers construct the equivalence of the indexing categories and transfer the
colimit. No existing signature, definition, or public import changes. The existing node
records the actual proof route; the new properties theorem has its own node.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.affine_strict_local_ring_comparison`
(`lem-exc-affine-strict-local-ring-comparison`).

Added zero holes. The new theorem
`Algebra.StrictHenselizationPresentation.local_properties`
(`lem-exc-strict-henselization-presentation-properties`) and every private helper are
fully proved. No sorry declarations remain in the two delivered modules. No statement
has been split off with an unproved proof.

## No longer needed

Removed the following direct proof imports from the item:

- `WeilConjectures.AlgebraicGeometry.EtaleLocalRingTriples` (including its duplicate).
- `WeilConjectures.AlgebraicGeometry.EtaleResidueTriples`.
- `Sheaf.RingTheory.StrictHenselizationTriples`.
- `Sheaf.AlgebraicGeometry.StrictHenselization`.
- `Sheaf.RingTheory.StrictHenselizationPresentationIn`.

The geometric diagram/triples comparison is encapsulated by the existing chart
ind-etale and maximal-ideal theorems; the algebraic triples comparison is encapsulated
by the new, proved properties theorem. The parent node therefore no longer directly
uses `lem-weil-pbc-etale-local-ring-triples`,
`def-weil-pbc-etale-residue-triples`,
`lem-weil-pbc-strict-henselization-triples`, or
`lem-weil-pbc-morphism-from-spec-field`. These nodes remain needed transitively.
The redundant direct definition edges `def-weil-open-immersion`,
`def-weil-geometric-point`, `def-weil-pbc-localization-at-prime`, and
`def-weil-pbc-strict-henselization-limit` are removed from proof dependencies; the
statement dependencies retain the definitions. Removed the old tool-use entries for
`lem-weil-pbc-etale-local-ring-triples` and
`lem-weil-pbc-strict-henselization-triples`, whose direct applications were replaced.
No whole module is claimed to leave the targets' import closure.

Removed redundant direct imports of
`WeilConjectures.AlgebraicGeometry.EtaleResidueTriples` and
`Mathlib.CategoryTheory.Filtered.Connected` from the new properties module: its other
imports already publicly supply these declarations.

The earlier pointed-presentation attempt and compiler probes are scratch work only;
they are not included as library files or new holes.

## Where the brief, the DAG or earlier work was wrong

The earlier sandbox attempt relied on an unproved new presentation statement. It has
been replaced by the fully proved properties module. The original DAG's geometric
triples translation is already available through the existing local-structure,
ind-etale and chart maximal-ideal results; directly reconstructing it is unnecessary.
The fixed relative closure in Omega, structural compatibility, specified residue map,
and quotient compatibility clauses are all retained. Both existing signatures were
compared verbatim with current repository sources. The unit route is preserved.
The resumed dry run found two final proof errors: `ext` descended through the subtype
when proving the quotient-map identity, and `simpa only` did not unfold the local chart
and structural-map abbreviations. Using `RingHom.ext` and explicitly listing those
abbreviations fixes both; the complete item compiled cleanly in 9 seconds.


The resumed dry run on 2026-10-19 reached server preflight. Its visibility check
identified two extra module-level universe names introduced only for a private lifting
helper. Replaced those names by implicit universe levels in the private helper, keeping
the module-level commands identical to the original. The required resumed dry run
completed successfully at commit `d235f13f3b`: both delivered modules compile and the
packet passes preflight, classified CODEX for the new proved module and node.
A source check also confirms zero `sorry` occurrences and no lines over 100 characters
in either delivered Lean module.

## New nodes

`lem-exc-strict-henselization-presentation-properties` records the fully proved
local-properties theorem from steps 4 and 5 of the original argument. Its source is
Stacks Project, Algebra, Tags 04GP and 04GW. It proves the properties of the residue map
induced by the given presentation, rather than choosing another map. The construction
works for a field base and the identity presentation, in arbitrary characteristic,
with no Noetherian, reducedness, or extra finiteness hypothesis. Its proof dependencies
include the existing filteredness theorem needed to forget the algebra colimit.
No change record is needed: existing statements and definitions are unchanged.

## Second reading by A6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
