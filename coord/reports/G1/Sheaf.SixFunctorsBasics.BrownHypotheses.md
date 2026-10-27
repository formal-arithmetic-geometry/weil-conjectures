## What changed

Repaired compilation performance in `Sheaf.SixFunctorsBasics.BrownHypotheses` while
preserving every public statement, definition body, import and attribute. The initial
unchanged restored archive exceeded the 60-second file limit at 65.5 seconds; the
profiling run also exceeded it. The finite-field assembly now applies the structural
theorem, objectwise finite-field compactness, and the Noetherian Brown criterion
directly, using the actual admissibility predicate unchanged. The redundant private
`brownHypotheses_finiteIntermediateField` and both coefficient-disjunction conversions
are removed. Explicit instances identify the installed structure morphism with aX.

The private `compact_of_iso` now uses the existing
`isCompactObject_iff_isCompactObj` and `BrownRepresentability.IsCompactObj.of_iso` API.
Its private Hom universe agrees with the coproduct indexing universe, which is exactly
what its sole call in the Brown criterion needs. No public universe binder changes.
The finite-field node's proof and proof origin follow the simpler assembly.

Validation: `lcompile.py` compiled the final module cleanly in 52.0 seconds
(exit code 0). Development profiler options were removed.

Change record: `coord/changes/G1-brown-finite-field-assembly-performance.md`.
Source searches found no external references to either private helper in lean/ or
quarantine/. Both direct importers (`Sheaf.Paper.LocalizingExceptionalAdjoint` and
`Sheaf.Paper.ExceptionalInverseImageExistence`) use the identical public interface;
no consumer adaptation is required. No other Lean module is changed.

## Proved and sorry left

Holes closed: none (0 of 1). Holes added: none. Split-off statements: none.
The sole remaining hole is `CategoryTheory.brownHypotheses`, node
`sk-lem-brown-hypotheses`; its signature and existing statement dispute are preserved.
All previously proved declarations remain proved, including
`CategoryTheory.brownHypotheses_of_finiteFieldDatum` and
`CategoryTheory.brownHypothesesFor_iff` with their simplified proofs.
This is a compilation-performance repair, not a proof of the disputed theorem.

## No longer needed

Removed the private `CategoryTheory.brownHypotheses_finiteIntermediateField` helper,
its explicit reordered coefficient predicate and both six-case conversions. The custom
direct-sum square in private `compact_of_iso` is replaced by the existing library API.
No module, import or DAG node is withdrawn. The structural, compactness and smallness
nodes remain needed, including the unit's compactness route. In particular none of the
quarantined parent/dependency attachments is deleted.

## Where the brief, the DAG or earlier work was wrong

The source was absent from lean/ at startup but was preserved in the quarantine path
listed in coord/rework.tsv. That archive was used, and the same source reappeared in
the shared lean/ tree during this session. The restored source did not initially meet
the per-file time limit; the submitted changes repair its proof elaboration rather
than just restoring or rebasing it.

The existing arbitrary-field Brown statement remains STATEMENT-DISPUTED: finite type
over an arbitrary positive-characteristic field does not imply the finite
cohomological-dimension hypotheses needed for compactness. The module already records
the infinite-transcendence-degree field obstruction. No new unrestricted compactness
lemma, arbitrary witness, weakened theorem, or claimed Lean field-cohomology proof is
introduced. The supported finite-field specialization and conditional Ext-bounded
integral criterion remain intact.

## Second reading by G1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
