## What changed

Restored Sheaf.Paper.ModelCompactComparisonUnit from its quarantine archive.
Repaired the removed compactCohomologyFrobeniusComparison call using the exact
trivial-square comparison used by current weilCompactCohomology. Updated the old
WeilBoundedConstructibleOfEnd spelling to WeilBoundedConstructible, retaining its
meaning for arbitrary endomorphisms and every theorem hypothesis.

The proof identifies the explicit proper-unit composite with compactPullback,
applies the published identity-removal theorem, uses naturality, and specializes
globalOperator_eq with frobeniusCoefficientIterate_one. No source-library file is
edited. The existing node records this proof. The change record is
coord/changes/Y2-model-compact-comparison-upstream-api.md.

## Proved and sorry left

The archived module has one hole, closed by the delivered proof:
AlgebraicGeometry.ProEtale.CondensedRing.modelCompactComparison_eq_properUnit
(lem-zl-model-compact-comparison-unit). Holes closed: 1; holes added: 0; split off: 0;
remaining sorry declarations in the delivered module: none. The private helper
compactSupportProperUnit_eq_compactPullback is also proved.

Compilation used lcompile.py and the required deliver3.py compile/axiom/preflight
pipeline. Early feedback found two elaboration issues: NatTrans.ext leaves an
equality of component functions, handled by funext; and map_id must be qualified
as CategoryTheory.Functor.map_id in the cast simplification. Both are repaired. The final warning cleanup scopes the unused-section-variable and unused-variable
linters to this theorem only, preserving the explicit include of algClosure,
qcModel and sepModel and the hr binder verbatim. The existing statement retains
these hypotheses although this proof does not need them.
The initial inconsistent dependency overlay was transient: subsequent requests
reached the actual item and gave proof diagnostics in 5.5, 6.1 and 18.0 seconds.


## No longer needed

Removed private imports Sheaf.AlgebraicGeometry.SchemeFrobeniusFiniteRadicial,
Sheaf.Paper.BoundedConstructiblePushforwardRestriction,
Sheaf.AlgebraicGeometry.CoefficientBoundedConstructibleProEtale,
Mathlib.AlgebraicGeometry.Morphisms.Finite and
Mathlib.AlgebraicGeometry.Morphisms.Proper. Current canonical construction imports
provide the required API. The source library already proves the iterate instances,
so this item no longer needs a separate use of lem-weil-pbc-finite-composition;
its node proof_deps and steps remove that use. No module is withdrawn and no
source-library declaration or proof is deleted. The geometric Frobenius and
restricted-functor nodes remain recorded for their actual mathematical roles.
No unit route is bypassed: the unit realized record has no assigned step here.

## Where the brief, the DAG or earlier work was wrong

The assigned active source is quarantined (the current rework row records its
archive). Its upstream name references predate the current source-library API.
The old literal four-factor expansion is now implemented through the general
trivial-square comparison; the library proves the required equality already.
The trace formula itself is neither used nor invoked as an assumption.
The active-source-only downstream count omits the archived GeneralCondensedWeilRealization
importer, which was checked separately. No new nodes are needed.

## Second reading by Y2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
