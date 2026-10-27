## What changed

Repaired compilation of `Sheaf.SixFunctorsBasics.BrownHypotheses` by caching existing
canonical instances in six transparent abbreviations:
`CategoryTheory.brownHypothesesCondensedMonoidal`,
`CategoryTheory.brownHypothesesCondensedBraided`,
`CategoryTheory.brownHypothesesSheafMonoidal`,
`CategoryTheory.brownHypothesesSheafBraided`,
`CategoryTheory.brownHypothesesCoefficientMonObj`, and
`CategoryTheory.brownHypothesesModuleMonoidalClosed`.
The instance attributes are local. The pro-etale caches explicitly use the library's
named canonical structures; the ring-object cache uses `Functor.monObjObj`.
Supplied explicit coefficient arguments in the existing isomorphism-invariance proof.
All existing signatures, definitions, imports, proof dependencies and mathematical
arguments are preserved. No extra transparency or irreducibility options are retained.
The change record is `coord/changes/G2-brown-canonical-instance-cache.md`.
Profiling found repeated site-size inference; the uncached file took 74.7 seconds.
The cached version with the restored original obligation compiled in 45.9 seconds;
the final packet preserves the shared source's parent proof and compiled through
`lcompile.py` in 58.7 seconds, with no errors or warnings reported.

## Proved and sorry left

No theorem is newly proved. Zero holes closed; zero holes added; zero split off.
The one existing hole remains:
`CategoryTheory.brownHypotheses_arbitraryField_compactness_witness`, node
`new-sfb-brown-arbitrary-field-compactness-witness`.
The original `CategoryTheory.brownHypotheses` proof is preserved, including its use of
that witness. This delivery claims a compilation repair, not proof progress.

## No longer needed

None. No module, import, declaration or DAG dependency is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The source changed during dispatch: the queue reported six holes, but the current module
has only the disputed unconditional compactness witness introduced by D3.
STATEMENT-DISPUTED: that witness has no finite-type, field or admissibility hypotheses,
and its own documentation says it is false. The arbitrary-field Brown statement also
lacks the field finiteness needed for compactness. Its existing diagnostic counterexample
and all proved finite-field and conditional results are preserved.

An attempted correction withdrew that false split and restored the original parent hole.
The module compiled, but preflight refused it because a declaration with a proof body
must keep its proof. Nothing was pushed from that attempt. The final packet retains
both declarations unchanged and delivers the independent compilation repair. Resolving
the false split requires maintainer/human action on the statement and this gate.

LeanFinder found only generic derived-category truncation results; Loogle found no
compact-object match. msearch grep and direct searches of Mathlib, WeilConjectures and
Sheaf found the finite-field compactness theorem and conditional Ext criteria.
They do not establish the unconditional disputed witness; no weaker replacement or new
unproved statement is introduced.

## Second reading by G2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
