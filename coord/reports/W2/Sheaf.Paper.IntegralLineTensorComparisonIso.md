## What changed

Proved `WeilConjectures.integralLineTensorComparison_iso` in
`Sheaf.Paper.IntegralLineTensorComparisonIso`, preserving its signature and all public imports.
Only proof imports were added. The proof collapses total tensor with the degree-zero line to
termwise tensor. The line evaluation inverse pair makes this an exact equivalence. The
Roos/intrinsic completeness equivalence and `CochainComplex.principalCompletionMap` transport
the actual normalized principal-cone unit, including its zero homotopy. A pure-tensor
calculation checks that the image uniformizer endomorphism is the canonical one.
Naturality of the published completion unit then proves the requested assertion.

The item's DAG proof and proof dependencies now describe this route. All changes are in
this module and its node; no definition, theorem statement, visibility or public import changed.
The unit route for `sk-thm-sf-dual-perfect` is unchanged.

## Proved and sorry left

Closed the one original hole: `WeilConjectures.integralLineTensorComparison_iso`
(node `lem-sf-integral-line-tensor-comparison-iso`). Proved 1 of 1 sorries in the item.
Zero sorries remain in the item; zero holes added and zero split off.
Existing dependency theorems, including `integralLineTensorComparison_representative`, are
used as declared; their statements and proofs are unchanged. The file compiles through
`lcompile.py` within the 60-second file limit; delivery runs its independent axiom probe.

## No longer needed

No original import was removed: the sole public import supplies the unchanged statement.
The old direct proof dependency `lem-weil-finite-free-completed-scalar-comparison`
(`Sheaf.Paper.FiniteFreeCompletedScalarComparison`) is unnecessary: the existing normalized
Roos/intrinsic unit criterion applies directly, with no identity-extension specialization.
The old direct dependency `lem-pur-acyclic-kflat-tensor-arbitrary`
(`Sheaf.Algebra.Homology.AcyclicKFlatTensor`) is unnecessary: the existing representative
and exact-equivalence APIs supply the required K-flat and quasi-isomorphism calculations.
The old direct dependency `lem-pur-integral-operations-well-defined`
(`Sheaf.Paper.IntegralOperationsWellDefined`) is not used directly: the resolving localization
and completion-unit APIs in `IntegralDerivedOperationsOnSlices` are sufficient. This module
remains transitively necessary, and none of these declarations or modules is withdrawn.
No module is claimed globally pruned. No new dependency on the quarantined
`Sheaf.Paper.CompletedLineTensorCoherence` is retained.

## Where the brief, the DAG or earlier work was wrong

The planned quotient-tower argument can be replaced below the unit level by the existing
normalized principal-cone argument. This preserves the specified comparison morphism;
no arbitrary map to a derived limit is identified from its projections. The old docstring
records the original quotient-tower route; an inline proof comment explains this equivalent
route. The invertibility hypothesis on l is retained verbatim, although the proof needs
no such restriction. The shared checkout quarantined `CompletedLineTensorCoherence` during
this session, so an initially explored completeness API from that module was not retained.
No statement dispute, definition repair, consumer adaptation or new node is needed.

## Second reading by W2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
