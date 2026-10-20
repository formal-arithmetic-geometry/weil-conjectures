## What changed

Replaced the duplicate implementation in Sheaf.Algebra.Homology.TelescopeColimit
with a public re-export of the already proved
WeilConjectures.Algebra.Homology.TelescopeColimit. Kept telescopeShiftColimit as a
transparent abbreviation of telescopeColimitShift, with exactly the old morphism
type and coproduct formula. The source supplies telescopeToColimit and
quasiIso_telescopeColimit, including both original canonicality conditions.
The private duplicate telescope_cokernel construction is no longer needed here.
No source-library declarations, proofs, attributes, signatures or imports change.

Updated lem-pc-complex-hocolim-colimit's Lean attachment to the source module,
including its actual shift name, and adjusted the corresponding proof-step names.
The proof dependencies and mathematical statement stay unchanged.
Change record: coord/changes/telescope-colimit-source-consolidation.md.

Remote compilation passed for the consolidated module (1.3 seconds), the full
former-interface probe (2.1 seconds), and unchanged copies of both direct importers:
RingedCechKoszulHomLimitComparison (3.4 seconds) and
Sites.ContractibleDerivedSectionsTensor (37.2 seconds). Probe files are not delivered.

## Proved and sorry left

The starting item has zero holes. Holes closed: none (0 of 0).
Holes added: none. Split-off statements: none. Remaining holes in this delivery: none.
This is duplicate-definition consolidation, not a new theorem proof.
The source CochainComplex.quasiIso_telescopeColimit is already proved; an interface
probe applies it directly to the complete former statement and confirms that
#print axioms lists only propext, Classical.choice, and Quot.sound.
The compatibility construction and old colimit-map formula both pass rfl checks.

## No longer needed

Removed this file's direct public imports of:

- Mathlib.Algebra.Homology.HomotopyCategory.ShortExact
- Mathlib.Algebra.Homology.HomotopyCategory.HomComplex
- Mathlib.Algebra.Homology.HomologicalComplexLimits
- Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
- Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
- Mathlib.Algebra.Category.Grp.FilteredColimits
- Mathlib.Algebra.Category.Ring.Limits

These public dependencies are all re-exported by the source module, preserving the
consumer environment. Removed the direct private proof import of
WeilConjectures.Algebra.Homology.TelescopeShiftMono; the source comparison still
uses it, so its module and lem-pc-telescope-shift-mono are not pruned. Likewise,
lem-pc-cone-short-exact-quasi-iso and the two definition nodes remain needed by
the existing source proof. No DAG dependency or library module is claimed pruned.
Only the duplicate local telescopeToColimit, quasiIso_telescopeColimit, and private
telescope_cokernel implementations are retired; their source counterparts remain.
The compatibility abbreviation retains telescopeShiftColimit.

## Where the brief, the DAG or earlier work was wrong

This dispatch names an item with no sorry and no TelescopeColimit-specific return
entry in coord/returns/M4.md or repair entry in coord/repairs.txt. The problem is
the duplicate source implementation, rather than an unfinished telescope proof.
The 2026-10-20 kept-twins inventory labels this module DIFFERENT because the shift
name differs. Reading both complete implementations shows that the constructions
are definitionally identical and the comparison theorem has the identical
canonicality clauses. Retaining an abbreviation resolves that apparent difference.
The DAG still attached the comparison to the duplicate Sheaf implementation;
it now points to the existing source theorem. No mathematical statement was false
or weakened, no new node is needed, and the unit route is unchanged.

The required msearch.py searches were run: Loogle did not know the project-local
theorem name; Lean Finder returned Mathlib's mappingCone.quasiIso_descShortComplex
among eight results; Mathlib grep found no project telescope declaration.
Direct rg in the project located the exact proved source implementation.

## Second reading by M4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
