## What changed

Completed the listed duplicate-retirement repair for
`Sheaf.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison`.
The adopted source theorem
`AlgebraicGeometry.Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf`
has the identical statement, universes and coefficient parameters. Its complete proof
uses the same stratification and applies `finite_locally_constant_module_values_iff`
stratumwise in both directions, including empty schemes and empty strata.

Withdrew the duplicate module through `deleted.txt`. Migrated the private comparison
imports and theorem applications of all 23 live direct consumers to the source spelling.
Reattached `lem-weil-pbc-constructible-etale-module-sheaf-comparison` to the canonical
source declaration. Its statement, mathematical dependencies and all parent dependency
edges remain; the unit route is preserved. No upstream file, public consumer signature,
public definition or target was changed.

Retained the previously reviewed compilation repair: explicit cochain tensor
structure and K-flat equivalence arguments in `FiniteCoefficientFlatModel`.
Reviewer correction: `ProjectiveLineConstructible` and `FiniteConstructibleDirectImage`
were rewritten on `sheaf-dag` after this delivery's base; their delivered copies reverted
those landed changes. They now carry the current live text with only the import swap and
theorem rename, and the former `Nonempty` helper repair is moot. The change record
`coord/changes/D9-constructible-etale-module-comparison-retirement.md` gives the details.

Repair of returned head `dbbc27947d`: compared every retained Lean file with the current
shared source. Apart from the comparison migration and those two documented compilation
repairs, their token streams agree. Refreshed the node copy from the current source,
retaining only the delivery-owned attachment and proof changes. The current downstream
checker skips absent live paths before reading them; the missing quarantined
`FiniteTypeTorsionUniversalStar` reported by the failed landing is not restored, deleted,
or replaced by an empty module in this packet. Its quarantine archive and obligation
remain intact. Delivery is rebuilt on the freshly fetched `sheaf-dag` by `deliver3.py`.

Server validation in this repair: `lcompile.py --all` successfully compiled all 23
adapted production modules, without warnings. A separate server compile of
`CheckComparison.lean` printed the canonical theorem's axioms: exactly `propext`,
`Classical.choice` and `Quot.sound`. No profiling options or increased limits remain.

The change record lists downstream users and the five quarantined direct consumers
with their restoration migration. No quarantined archive is changed. There is no
second-reader claim; the maintainer performs the independent review.

## Proved and sorry left

The item started with zero holes. Closed zero holes, added zero holes, split off zero.
The withdrawn `AlgebraicGeometry.Scheme.isConstructibleEtaleModuleSheaf_iff` was already
proved; this is duplicate retirement, not new proof progress. Its canonical replacement
is fully proved and its axiom check contains no `sorryAx`.

There are no `sorry` occurrences in any of the 23 delivered Lean files. No holes remain
in the delivered item or its adaptations.

## No longer needed

Pruned `Sheaf.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison` and its
short-name theorem. Removed that private import from all 23 live consumers and replaced
it with the canonical source module. The duplicate's private finite-value proof import
and redundant reconstruction of stratification records are no longer needed.

The finite-value comparison, stratification and constructibility definition nodes remain
needed by the canonical source proof. All DAG parents retain the comparison node,
including parents whose proofs are unfinished or whose modules are quarantined.
No mathematical dependency, unit step, source declaration or quarantined obligation
is withdrawn. The five quarantined direct consumers must use the same import and name
migration when restored, as specified in the change record.

## Where the brief, the DAG or earlier work was wrong

This is a zero-hole retirement item in `coord/retire-items.tsv`. Its DIFFERENT label
reflects the longer suffix `_isConstructibleSheaf` on the source theorem; its type is
identical. The node's declaration already used the longer spelling while its module
and saved statement still named the duplicate; those attachment fields are reconciled.

The earlier return on `347e73b1f8` required explicit module rows for the five quarantined
consumers, including `FiniteRingEtaleCompactGenerators`; those rows are retained.
The latest review passed the mathematics but landing failed while reading an absent
quarantined path. The current checker skips absent live paths. This repair preserves
the reviewed packet, reconciles it with current sources and recompiles it on the server;
it does not withdraw or erase that quarantined module.

The retained search log records LeanFinder, Loogle and Mathlib grep searches. Repository
searches found the exact proved source theorem, which is preferable to a new lemma.
No new lemma or node was required.

## Second reading by D9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
