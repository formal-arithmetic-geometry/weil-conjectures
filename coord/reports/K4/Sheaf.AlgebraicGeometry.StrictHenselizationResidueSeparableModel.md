## What changed

Completed the listed retirement repair for
`Sheaf.AlgebraicGeometry.StrictHenselizationResidueSeparableModel`, which already
had zero holes. Its upstream twin proves the same mathematical assertion using
`strictLocalization` and `strictLocalizationToBase` in place of the legacy
`strictHenselizationScheme` and `strictHenselizationStructuralMap`.

Withdrew the item and its five unclaimed legacy consumers as one closed set:

| Withdrawn Sheaf module under AlgebraicGeometry | Existing upstream replacement |
|---|---|
| StrictHenselizationResidueSeparableModel | WeilConjectures.AlgebraicGeometry.StrictHenselizationResidueSeparableModel |
| CompatibleStrictHenselizationResidueSeparability | WeilConjectures.AlgebraicGeometry.CompatibleStrictHenselizationResidueSeparability |
| CompatibleStrictHenselizationResiduePolynomial | WeilConjectures.AlgebraicGeometry.CompatibleStrictHenselizationResiduePolynomial |
| CompatibleStrictHenselizationResidueImage | WeilConjectures.AlgebraicGeometry.CompatibleStrictHenselizationResidueImage |
| ProjectiveLineCompatibleStrictHenselizationResiduesCore | WeilConjectures.AlgebraicGeometry.ProjectiveLineCompatibleStrictHenselizationResiduesCore |
| ProjectiveLineCompatibleStrictHenselizationResidues | WeilConjectures.AlgebraicGeometry.ProjectiveLineCompatibleStrictHenselizationResidues |

The delivery's `deleted.txt` names those six paths. All seven associated DAG
nodes remain present and now select the existing upstream declarations, with
their exact upstream signatures in `lean.statement`. The unit's realized nodes
and all incoming dependencies remain intact. The polynomial node now records
the existing proof through residue separability and the minimal-polynomial core.

Every public signature was compared with its upstream counterpart: after the
two model/map name replacements, all binders, hypotheses and conclusions match.
The canonical colimit comparison identifies the two strict-henselization
constructions. This is a replacement of duplicate presentations, with no change
to a target or to any adopted source-library file.

The complete six-module set has no external Lean importer, including in
`quarantine/`. Its terminal theorem is already used through the upstream module
by `WeilConjectures.AlgebraicGeometry.ProjectiveLineStrictLocalModelComparison`.
The five downstream copies are unclaimed; no module held by another group is
adapted. The change record is
`coord/changes/K4-strict-henselization-residue-model-retirement.md`.

## Proved and sorry left

This is a retirement repair of an already proved module: zero original holes,
zero holes closed, zero holes added, zero split off, and zero holes remaining in
the six withdrawn copies or their seven upstream public replacements. It is not
a new proof or a decomposition. The retained upstream declarations are:

- `AlgebraicGeometry.Scheme.strictHenselization_residue_separable_model`
- `AlgebraicGeometry.Etale.compatibleStrictHenselization_residue_isSeparable`
- `AlgebraicGeometry.Etale.compatibleStrictHenselization_residue_separable_polynomial`
- `AlgebraicGeometry.Etale.compatibleStrictHenselization_residue_image`
- `AlgebraicGeometry.Etale.projectiveLine_compatibleStrictHenselizationResidues_core`
- `AlgebraicGeometry.Etale.compatibleStrictHenselization_residue_square`
- `AlgebraicGeometry.Etale.projectiveLine_compatibleStrictHenselizationResidues`

Copied all six unchanged upstream sources to a separate scratch validation tree
and compiled them in import order using `lcompile.py --all`. They compiled in
3.6, 2.7, 1.8, 2.4, 2.8 and 2.7 seconds, respectively. Appended `#print axioms`
checks show exactly `propext`, `Classical.choice` and `Quot.sound` for every
public theorem listed above. There is no dependency on an unfinished proof.
These validation copies are not delivered.

## No longer needed

The six legacy modules in the table are retired. Their mathematical statements
remain needed and are preserved by the upstream attachments; no DAG node is
deleted. The blueprint unit `sk-thm-p1` retains all its realized statements and
steps. No target-closure hole reduction is claimed for removing these already
unused legacy import copies.

The withdrawn files' imports disappear with them. The complete distinct list is:

- `Sheaf.AlgebraicGeometry.StrictHenselizationStructuralMap`
- `WeilConjectures.Mathlib.RingTheory.Henselian`
- `Sheaf.Paper.StrictHenselizationFunctoriality`
- `Sheaf.AlgebraicGeometry.StrictHenselizationResidueSeparableModel`
- `WeilConjectures.AlgebraicGeometry.EtaleLocalRingTriples`
- `WeilConjectures.AlgebraicGeometry.CompatibleStrictHenselizationResiduePolynomialCore`
- `Sheaf.AlgebraicGeometry.CompatibleStrictHenselizationResidueSeparability`
- `WeilConjectures.RingTheory.StrictHenselizationTriples`
- `Sheaf.AlgebraicGeometry.CompatibleStrictHenselizationResiduePolynomial`
- `WeilConjectures.AlgebraicGeometry.Morphisms.UniversalHomeomorphism`
- `Sheaf.AlgebraicGeometry.CompatibleStrictHenselizationCoreData`
- `Sheaf.AlgebraicGeometry.CompatibleStrictHenselizationResidueImage`
- `Sheaf.AlgebraicGeometry.CompatibleStrictHenselizationResidueLift`
- `Sheaf.AlgebraicGeometry.ProjectiveLineCompatibleStrictHenselizationResiduesCore`

This list describes imports of the withdrawn copies, not a claim that the
upstream replacements avoid those mathematical dependencies. In particular the
geometric functoriality and strict-henselization triple arguments remain used
upstream. The polynomial node no longer directly depends on
`lem-weil-pbc-etale-local-ring-triples`,
`lem-weil-pbc-strict-henselization-triples`, or `def-pc-separably-closed`; its actual
proof uses the separability node and the already proved polynomial-core node.

## Where the brief, the DAG or earlier work was wrong

The generic proof brief describes an open theorem, but the current item is a
listed duplicate-retirement repair with zero holes. The authoritative row is
`retire:Sheaf.AlgebraicGeometry.StrictHenselizationResidueSeparableModel` in
`coord/retire-items.tsv`. The human's retirement instructions are in
`coord/changes/retire-sheaf-twins-20261020.md`.

A simple import rewrite would mix the legacy small-colimit presentation with
the canonical presentation. A scratch compile reproduced a duplicate-name
import error for `smallStrictHenselizationColimitIso`. Both presentations also
retain overlapping structural-map theorem names. Retiring the closed consumer
chain avoids mixing these APIs; no upstream declaration is edited or removed.

The existing polynomial node still described an earlier direct triple-colimit
argument, although both the legacy and upstream Lean proofs use separability and
the minimal polynomial. Its proof and proof dependencies now match that code.

Required searches were run through `msearch.py`: LeanFinder returned residue
separability results for formally unramified finite-type local algebras; Loogle
returned `IsSeparable.of_algHom`; Mathlib grep found no strict-henselization
separability match. Searching both library roots found the complete upstream
chain. No new lemma or node was needed.

## Second reading by K4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
