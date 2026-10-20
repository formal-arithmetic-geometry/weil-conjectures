## What changed

Restored Sheaf.Algebra.Homology.RhomGlobalSectionsOfUniverses verbatim from its
quarantine archive. Repaired its duplicate-declaration import failure by canonicalizing
the two unclaimed hypercohomology companion modules. The legacy
Sheaf.Algebra.Homology.RingedSiteZerothHypercohomology now re-exports the byte-identical
upstream definition, retaining all original public infrastructure imports. The
independent-universe companion imports that upstream module directly; its complete
definition is unchanged. No source-library file, consumer signature, theorem proof,
mathematical route or DAG attachment changes. Change record:
coord/changes/B4-rhom-global-sections-canonical-hypercohomology.md.

Validation: lcompile.py --all compiled all three delivered modules. A separate
consumer sandbox compiled the unchanged DerivedInternalHomSectionsModel,
RhomHypercohomologyBridgeOfUniverses, and LocallyFreeDerivedHom (24.7 s), then the
restored theorem and a probe importing the theorem, LocallyFreeDerivedHom and the
independent-universe companion together. This tests the combined import context
used by quarantined QbarCohomologyFiniteLevelComparison without changing that
consumer. All compiles passed below 60 seconds without warnings. Axiom probe results
are recorded below. The legacy and upstream definition signatures and complete bodies
were also checked byte-identical before replacing the local duplicate by its re-export.
The complete three-module dry run passed compilation and server preflight (CODEX).

## Proved and sorry left

Assigned repair with zero original holes. Restored the complete proof of
CategoryTheory.rhom_global_sectionsOfUniverses (lem-pur-rhom-global-sections).
Closed 0 holes; added 0 holes; split off 0 statements; 0 holes remain in all delivered
modules. This is an import repair, not a new mathematical proof. The theorem's axiom
probe includes sorryAx from existing proof dependencies, including the unchanged
CategoryTheory.DerivedInternalHomSectionsModel.derived_internalHom_sections_model
(lem-sfb-derived-internal-hom-sections-model). This delivery does not claim that its
transitive proof closure is complete; no dependency hole is added or modified.
The two hypercohomology definitions' probes show only propext, Classical.choice and
Quot.sound.

## No longer needed

Removed the companion's public import of the legacy Sheaf module, replacing it with
the canonical source module. The legacy module's duplicate local definition body is
no longer needed: it now exports the same name from the source module, with all
original public infrastructure retained. The legacy module is not withdrawn;
LocallyFreeDerivedHom still imports it. No node or module is pruned from the library.
Every dependency of lem-pur-rhom-global-sections remains needed and unchanged.

## Where the brief, the DAG or earlier work was wrong

The item is absent from lean/ because of quarantine, not withdrawal. Its quarantine
archive is fully proved. The sync introduced the identical equal-universe declaration
upstream while the local legacy module retained the duplicate declaration. The initial
server compile reproduced exactly the rework.tsv error. Canonicalizing both import
paths repairs it without changing any statement or definition. LeanFinder found Ext
comparisons rather than a shorter site-level theorem; Loogle confirmed the K-injective
Qh_map_bijective API already used by the archived proof. The existing proof follows
the recorded DAG and Stacks 08JA; no new nodes are needed.

## Second reading by B4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
