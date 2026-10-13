## What changed

Removed AlgebraicGeometry.Scheme.Modules.isZero_of_isZero_stalks from
Sheaf.AlgebraicGeometry.SheafZeroStalks, as required by upstream review #1428.
The declaration-free compatibility module preserves both original public imports.
No library caller uses the removed theorem name, so no caller adaptation is needed.
Updated pqf-lem-sheaf-zero-stalks's lean record to identify the canonical upstream
AlgebraicGeometry.Scheme.Modules.isZero_of_isZero_stalk, and replaced the old local
proof route with this existing-result reference. No mathematical statement changed.

Change record: coord/changes/remove-sheaf-zero-stalks-duplicate.md.

## Proved and sorry left

This is duplicate removal, not a new proof or decomposition: 0 of 0 original
sorries proved, 0 holes added, 0 split off, and no sorry remains in the item.
The deleted theorem was already proved. No new declaration is introduced.

## No longer needed

Removed private imports Mathlib.Topology.Sheaves.Abelian and
Mathlib.Algebra.Category.Grp.Zero from the retired theorem's module.
The local proof no longer needs def-pc-module-stalk-functor or
def-weil-sheaf-of-modules-category as proof dependencies; both are removed from
pqf-lem-sheaf-zero-stalks.proof_deps. Its original statement dependencies stay.
Sheaf.AlgebraicGeometry.SheafZeroStalks now holds no declaration; it remains for
compatibility with the existing import in TorAmplitudeOpenLocal.
No whole module is claimed to leave the targets' import closure.

## Where the brief, the DAG or earlier work was wrong

The earlier attempt removed an unused import from TorAmplitudeOpenLocal and
called that a forced adaptation. The dry run compiled the original caller against
the changed dependency successfully and rejected the adaptation as not forced.
That sandbox edit is removed. The earlier attempt's unchanged DAG record pointed
to the deleted name, and its change record lacked the required sections and users;
both are repaired here.

The canonical upstream FiniteFibre module identified by the supplied review is
absent from this repository and the installed source checkout. We therefore
record the review's canonical module/name with lean.statement null and an explicit
lean.note rather than inventing or claiming to verify its exact signature.
The upstream reference remains to be checked against that source by the reviewer.
No code imports a nonexistent module.

## Second reading by T3

1. **Visible declarations and statements.** Compared the delivered module with the repository version. The only declaration change is the explicitly recorded retirement of `AlgebraicGeometry.Scheme.Modules.isZero_of_isZero_stalks`; the two public imports remain byte-for-byte unchanged, and no other module was adapted.

2. **Compilation and proof safety.** Compiled `Sheaf.AlgebraicGeometry.SheafZeroStalks.lean` with `lcompile.py`; it succeeds with no errors or warnings. The delivered compatibility module contains no declarations, `sorry`, axioms, unsafe or opaque code, and no definition data.

3. **Statement and dependency review.** The retired theorem had no local callers. The DAG node now records the canonical upstream theorem reference and has no proof dependencies; no new split-off statement was introduced. The upstream declaration is not present in this snapshot, so its exact signature remains explicitly marked unverified rather than fabricated.

4. **Pruning and route.** The retired theorem's proof-only imports `Mathlib.Topology.Sheaves.Abelian` and `Mathlib.Algebra.Category.Grp.Zero` are removed. The compatibility module keeps its original public imports, and the unit route is unchanged because this duplicate declaration is not a unit step used by any caller.

5. **DAG and records.** Checked that the node's proof, `proof_deps`, and `proof_origin` describe the delivered retirement, and that the change record names the old declaration, users, and unchanged public interface. The dry run initially found this section missing; adding this second reading is the only subsequent change.

I changed the report by adding this second-reading record. No Lean source, node, or change-record content was changed during the second reading.
