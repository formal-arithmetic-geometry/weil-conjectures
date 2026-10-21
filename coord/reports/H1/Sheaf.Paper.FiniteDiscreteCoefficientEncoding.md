## What changed

Restored lean/Sheaf/Paper/FiniteDiscreteCoefficientEncoding.lean verbatim from its
quarantine archive, as required by coord/rework.tsv. The live module was absent.
The restored finiteDiscreteCoefficientEquivalence constructs the common encoding by
inverting the proved sectionwise sheafEncoding for the fixed G and composing with
inverse restriction of scalars along finiteDiscreteSchemeRingIso. The restored
finiteDiscreteCoefficientEquivalenceForgetIso gives the underlying abelian-sheaf
comparison by whiskering sheafEncodingForgetIso and the encoding counit.

The current dependency declarations and their nodes were read. The scalar-transport
inverse is explicitly comap along the inverse ring isomorphism. The sheaf-encoding
inverse comes from a fully proved equivalence; no arbitrary witness of an unproved
existence theorem is used. Both constructions apply without nonempty-scheme or
nonzero-ring assumptions. The node and its unit route remain unchanged.

Remote single-file compilation passed without diagnostics (4.3 seconds). The restored
file is byte-identical to its archive. All 10 direct and 153 transitive consumers,
including quarantined consumers, were enumerated in the change record; none requires
adaptation because every archived signature, import, attribute and body is preserved.

Change record: coord/changes/H1-finite-discrete-coefficient-encoding-restore.md.

## Proved and sorry left

This is a zero-hole restoration/repair. Original archived holes: 0; holes closed: 0;
holes added: 0; holes left: 0. No split-off theorems.
The restored definitions finiteDiscreteCoefficientEquivalence and
finiteDiscreteCoefficientEquivalenceForgetIso have complete construction bodies.
There is no sorry in either definition or anywhere else in the module.

## No longer needed

None. No imports, modules or nodes are removed. Both declared proof dependencies,
lem-weil-pbc-constant-internal-module-sheaf-equivalence and
lem-weil-pbc-finite-discrete-scheme-ring-constant, remain needed by the construction.
Mathlib search (leanfinder, loogle, grep through msearch.py, plus local rg) found
ordinary ModuleCat scalar restriction equivalences, but no replacement for this
internal-module sheaf encoding. Existing library APIs already implement the short
categorical assembly, so no additional lemmas are introduced.

## Where the brief, the DAG or earlier work was wrong

The item is absent from lean/ because it was quarantined, not because its declaration
or dependencies were withdrawn. The archived item has zero sorries, despite the queue
showing 1. No proof defect was reproduced: the archived implementation compiles on
the current server. The repair restores the actual missing module and its original
Lean attachment, preserving the archive and the existing DAG node unchanged.

## Second reading by H1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
