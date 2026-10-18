## What changed

Proved `DerivedCategory.rlim_perfect_complete` with its original signature and all four
conclusions. The proof applies the existing pseudo-coherent inverse-ring reconstruction,
maximal-fibre perfectness, and nilpotent-torsion completeness declarations.

The local glue is proved: perfect complexes are pseudo-coherent by a finite-free chain
retract and the existing summand theorem; adic quotient transitions have square-zero kernels;
completeness gives the required ring inverse limit; restriction composition has the required
normalization; and scalars killed by a ring map annihilate derived restrictions. For the
uniform residue-field bound, the proved ordinary module tensor comparison is lifted to
complexes and combined with the source K-flat single-module tensor comparison and bounded
flat Tor amplitude. Compatibility follows directly from the Roos triangle and adjunction
unit formula. The zero complex and reversed initial support endpoints are covered by
replacing the lower endpoint by its minimum with the upper endpoint.

Updated the existing DAG proof, dependencies and origin to this implementation. The local
helpers are proved parts of those steps; three existing shared helpers are reused from
`PseudoCoherentNormalizedAlgebraTower` after exposing them in place. A private
`ScalarReductionModel` record retains
exactly the two marked bounded-above flat models and their scalar-reduction isomorphism.
The generic reconstruction is projected to that interface before specializing the rings;
this avoids the kernel repeatedly checking the much larger specialized witness statement.
The record has ordinary fields and is produced in a proved existential statement, with no
object defined by choosing from an unproved existence statement.

There are no new modules, new nodes, changed theorem types, or changed definition bodies.
The unclaimed `PseudoCoherentNormalizedAlgebraTower` module now exposes its existing
`adic_quotient_limit`, `adic_step_nilpotent`, and
`restrictScalarsComp_derived_factors` helpers. The assigned module imports and uses them,
removing the two duplicate adic proofs named in the return and its local specialization of
the restriction-composition proof. Their statements and proofs in the original module are
unchanged. This repairs the return of head `792f0bb85`; the current shared source still has
the original single sorry in `rlim_perfect_complete`. The helper visibility change and
consumer checks are recorded in `coord/changes/C2-rlim-shared-adic-helpers.md`. The unused
public import removal is recorded in
`coord/changes/C2-rlim-perfect-proof-imports.md`; the downstream check finds zero consumers.
Both repaired modules compile cleanly with standard limits and no profiling settings:
`PseudoCoherentNormalizedAlgebraTower` in 26.1 seconds and `RlimPerfectComplete` in
6.5 seconds, using `lcompile.py --all`. All added imports pass the import-cycle check.
A mechanical comparison
confirms that the theorem signature and all five original defining expressions are unchanged.

## Proved and sorry left

Closed the original hole `DerivedCategory.rlim_perfect_complete`
(`lem-weil-pbc-rlim-perfect-complete`): 1 of 1 local holes closed.
No sorry remains in either delivered Lean module. The adapted dependency already had
zero holes; exposing its helpers adds and closes zero holes. Added holes: zero. Split-offs: zero.
The imported reconstruction, maximal-fibre criterion and completeness statements retain
their existing proof obligations; this delivery proves the assigned theorem from them.

## No longer needed

Removed the local duplicate proofs `adic_quotient_limit`, `adic_step_nilpotent`, and
`restrictScalarsComp_derived_factors`; their existing shared implementations are now used.

Removed imports:

- `Sheaf.Algebra.Homology.KFlatTelescopeClosure`
  (`lem-pc-kflat-closure`): source bounded-above flat K-flatness and the source single-module
  comparison suffice; no sheaf-level telescope closure is needed.
- `Sheaf.Algebra.Homology.DerivedChangeOfRings`
  (`lem-pur-derived-change-of-rings`): the theorem's definitions and signature only require
  restriction and supplied adjunctions. The proof uses the ordinary module tensor comparison
  and the source K-flat model instead.
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients`: its unproved general
  coefficient comparison is unnecessary for the concrete tensor computation.
- `Sheaf.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral`
  (`def-pc-perfect-ring-complex`): the statement already uses the source `IsPerfect` over the
  same universe, and no general-universe perfect predicate is used.

Removed the first two nodes' obsolete top-level tool approvals. The perfect-complex
*definition node* remains a mathematical proof dependency for the source predicate's
meaning; only its separate general-universe module import is unnecessary. The change-of-rings
node remains a statement dependency describing derived extension, but is no longer used by
the implemented proof. These are direct dependency removals; transitive imports in existing
reconstruction modules are not claimed to have disappeared. No unit statement or unit proof
step is bypassed.

## Where the brief, the DAG or earlier work was wrong

No statement was false or repaired. The planned sheaf-level K-flat and derived-change-of-rings
route was unnecessarily general for module complexes. The existing source library already
computes the needed derived tensors. The planned strict-model argument for compatibility
can be replaced by the identity inherent in the supplied Roos triangle. No arbitrary
comparison map or choice of unidentified data is added. Directly specializing the full
reconstruction witness statement caused kernel timeouts; projecting its generic conclusion
to the small flat-model record fixes this without changing the source statement, splitting
files, or raising compilation limits.

The returned delivery duplicated two existing private helper statements. The repair
exposes those existing theorems in their original module and uses them by import.
It also reuses the existing more general restriction-composition helper. No duplicate
statement is retained under a different name.

## Second reading by C2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
