## What changed

Retire Sheaf.AlgebraicGeometry.StrictHenselizationModuleFibreFactorization, as assigned
by coord/retire-items.tsv row 2933 and the human retirement hand-off. The module has
zero holes. List its path in deleted.txt and attach
lem-sbc-strict-henselization-module-fibre-factorization to the already proved theorem
AlgebraicGeometry.Etale.strictHenselizationModuleFibre_factorization in
WeilConjectures.AlgebraicGeometry.StrictHenselizationModuleFibreFactorization.

The DAG statement and statement_change explicitly record the full affine-neighbourhood
strictLocalization presentation and its canonical isomorphism over the base with the
former small representative ring-colimit presentation. The Lean signature is copied
verbatim from the official theorem. Its proof, proof_deps and proof_origin now follow
the official pointed lift, closed-fibre result, qcqs module comparison, private germ
calculation and strictLocal_exchange_compatibility assembly.

Change record: coord/changes/F1-strict-henselization-module-fibre-factorization-retirement.md.
The only listed historical consumer is already retired: its official replacement
WeilConjectures.AlgebraicGeometry.IntegralFibreSectionLocalZero imports and applies the
full-model theorem. No adopted source file, target or consumer is edited. Active
parent dependencies and the unit route remain intact.

## Proved and sorry left

Holes closed: 0 of 0. Holes added: 0. Split off: 0. This is retirement of a proved
duplicate, not a new proof or decomposition. No sorry remains in the item. The removed
public theorem is AlgebraicGeometry.Etale.strictHenselizationModuleFibre_factorization;
its full-model counterpart remains proved in the official module. The removed private
pointedStrictHenselizationLift likewise has a proved counterpart there.

Compiled the unchanged official factorization module (8.6 s) and its unchanged
IntegralFibreSectionLocalZero consumer (4.8 s), separately with lcompile.py. A separate
import probe compiled in 2.4 s; #print axioms for both the official factorization
and integralFibreSection_localZero reports exactly propext, Classical.choice and
Quot.sound. No source-library declaration is removed or given a sorry.

## No longer needed

Pruned module: Sheaf.AlgebraicGeometry.StrictHenselizationModuleFibreFactorization.
The current Lean import scan and tools/downstream.py find zero importers of this copy.
The active parent node lem-sbc-integral-fibre-section-local-zero retains this result
as a dependency and already realizes it via the unchanged official full-model theorem.
Thus retirement preserves the required mathematics, including unfinished-parent needs;
it is not based solely on zero importers.

Removed with the duplicate are its imports of
WeilConjectures.AlgebraicGeometry.GeometricFibreExchangeGerms,
WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMap,
WeilConjectures.SixFunctors.BaseChange.GlobalSections,
WeilConjectures.AlgebraicGeometry.GeometricFibreExchangeRepresentative,
Sheaf.AlgebraicGeometry.StrictHenselizationClosedFiberComparison,
Sheaf.AlgebraicGeometry.EtaleUnitSectionRestriction,
Sheaf.AlgebraicGeometry.SmallStrictLocalSectionMaps, and
WeilConjectures.AlgebraicGeometry.QcqsStrictLocalModuleComparison.
No claim is made that these modules are globally unused.

The official proof no longer directly needs these old proof dependencies:
def-weil-pbc-small-strict-local-section-maps,
lem-weil-pbc-etale-unit-section-restriction-comp,
lem-weil-pbc-strict-henselization-small-closed-fiber-comparison, and
lem-weil-pbc-exchange-pointed-representative. It uses the official full-model
closed-fibre and strict-local exchange compatibility results instead. The general
unit-restriction and small-model comparison nodes may remain needed elsewhere;
no other module or DAG node is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The generic proof brief describes an obligation split four times, but the current
source already has a complete zero-hole proof and the queue explicitly assigns
retirement. The retirement row lists a Sheaf consumer that is now absent; the current
upstream consumer has already migrated its entire argument to strictLocalization.
The row's mention of transportedIso_hom is stale: the current copy has no declaration
by that name. No missing public API needs recreating.

The small and full strict-henselization presentations are canonically isomorphic,
not definitionally equal. This packet explicitly records that change of presentation
rather than silently relabeling the old Lean signature. Both theorem signatures have
the same geometric hypotheses and factorization clauses, including arbitrary local
structure, empty schemes and arbitrary commutative coefficient ring. The unit record
sk-lem-universal-datum has no realized entry for this node, and no unit step is removed.
Searches through msearch.py (LeanFinder, Loogle, grep) are recorded in searches.jsonl.
LeanFinder returned unrelated tilde-module stalk facts; Loogle and Mathlib grep found
no matching theorem. Direct source search found the exact official theorem and its
already migrated consumer, which are retained without editing.

## Second reading by F1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
