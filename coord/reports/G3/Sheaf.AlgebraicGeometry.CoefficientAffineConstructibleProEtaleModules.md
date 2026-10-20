## What changed

Restored `Sheaf.AlgebraicGeometry.CoefficientAffineConstructibleProEtaleModules`
from its assigned quarantine archive. Replaced the unavailable
`LocallyClosedStratification` name by the existing upstream `Scheme.Stratification`
in `AlgebraicGeometry.Scheme.IsCoefficientAffineLocallyConstructibleProEtaleModuleSheaf`.
The compile of the original archive failed on that name; the repaired module
compiled cleanly on the server (5.2 seconds). The unchanged archived consumer
`CoefficientBoundedConstructibleProEtale` also compiled against the repaired module
(3.3 seconds); that temporary consumer copy is not part of the delivery.

The replacement retains the same finite locally closed partition, immersed
schemes and constructibility condition. In particular it agrees with Stacks
proetale.tex, definition-constructible (Tag 09AJ), also for non-Noetherian schemes.
Empty schemes, empty opens and strata, the zero ring, and infinite Noetherian
coefficient rings remain allowed. The local constant modules are still finitely
presented, not finite sets. The fixed-scalar pullback construction and all public
imports remain verbatim. No consumer requires an adaptation to the item's public
signatures. The archived consumers and all three DAG parents remain needed.

Updated only the item's `lean.note` to document this API repair. Change record:
`coord/changes/G3-coefficient-affine-constructible-stratification-api.md`.

Searches: LeanFinder returned general Noetherian and spectral-space results;
Loogle and Mathlib grep found no stratification declaration. The existing
`WeilConjectures.ConstructibleSheaf.Defs` supplies exactly the required
`Scheme.Stratification`; no new construction or proof dependency was introduced.

## Proved and sorry left

This is an assigned zero-hole definition repair. Original explicit holes: 0.
Holes closed: none. Holes added: none. Holes remaining: none.
Both `AlgebraicGeometry.Scheme.coefficientProEtaleFixedModulePullback` and
`AlgebraicGeometry.Scheme.IsCoefficientAffineLocallyConstructibleProEtaleModuleSheaf`
are genuine definitions, with no `sorry` fields or chosen unproved witnesses.
No decomposition or proof-completion claim is made.

## No longer needed

None. No import, declaration, module, DAG dependency or unit step is removed.
The archive itself is preserved and is not listed for deletion.

## Where the brief, the DAG or earlier work was wrong

The archive still referred to `LocallyClosedStratification`, removed by the
upstream name migration. Replacing that occurrence is necessary for compilation;
simply restoring the archive would not repair it. The DAG's mathematical statement
and its Lean attachment remain correct. The current def-constructible-stratification
record confirms that the old structure already extended the constructible upstream
`Topology.Stratification`; the explicit constructibility conjunct is retained.

## Second reading by G3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
